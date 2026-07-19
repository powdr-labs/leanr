import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.Dense.DomainBatch
import ApcOptimizer.Implementation.Dense.OneHotAnnihilate

set_option autoImplicit false

/-! # Dense domain-constant subexpression folding (Task 3)

`VarId`-native port of `DomainFold.domainFoldPass`. The pass folds every wholly-in-group
subexpression that is constant on the group's surviving joint values to that constant, keeping the
group's variables. It is **fact-free** (`(domainFoldPass pw).withFacts`), but its target list is built
with a `mergeSort`/`dedupHash` canonicalisation whose ordering is the `Variable` order — which cannot
be reproduced purely over `VarId`s. So the pass is built **directly** (like `denseDomainBatchPass`),
with `reg` available, materialising `reg.resolve` on the cold target-building path (sort key + dedup),
while the hot fold/enumeration path stays ID-native (reusing `Dense/DomainBatch.lean`'s engine). It
inherits `domainFoldPass`'s `PassCorrect` through the decode equality `hout`.

The domain-enumeration primitives (`denseRootsIn`, `denseEnvOfFast`, the box scan, the inverted index)
are reused verbatim from `Dense/DomainBatch.lean`. This file adds the fold-specific layer:
`denseFindDomainAlg`/`denseGroupDoms` (domains), `denseGroupSurvivorsE` (survivors),
`denseConstOnSurvs`/`denseFoldRewrite`/`denseFoldOut` (the rewrite), and both the direct and indexed
fold loops, each with a `_decode` correspondence and coverage preservation. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Small dense expression predicates -/

/-- Dense `Expression.hasVar`. -/
def DenseExpr.hasVar : DenseExpr p → Bool
  | .const _ => false
  | .var _ => true
  | .add a b => a.hasVar || b.hasVar
  | .mul a b => a.hasVar || b.hasVar

theorem VarRegistry.decodeExpr_hasVar (reg : VarRegistry) (e : DenseExpr p) :
    (reg.decodeExpr e).hasVar = e.hasVar := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => rw [VarRegistry.decodeExpr, Expression.hasVar, DenseExpr.hasVar, iha, ihb]
  | mul a b iha ihb => rw [VarRegistry.decodeExpr, Expression.hasVar, DenseExpr.hasVar, iha, ihb]

/-- Dense `Expression.anyVarIn` (mirrors `Expression.anyVarIn`, through `denseContainsFast`). -/
def DenseExpr.anyVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.anyVarIn xs || b.anyVarIn xs
  | .mul a b => a.anyVarIn xs || b.anyVarIn xs

theorem denseExpr_anyVarIn_decode (reg : VarRegistry) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    (reg.decodeExpr e).anyVarIn (xs.map reg.resolve) = e.anyVarIn xs := by
  induction e with
  | const n => rfl
  | var i =>
      have hiv : reg.Valid i := hc i (by simp [DenseExpr.vars])
      show Expression.anyVarIn (xs.map reg.resolve) (.var (reg.resolve i)) = denseContainsFast xs i
      exact denseContainsFast_decode reg xs hxv i hiv
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      show Expression.anyVarIn (xs.map reg.resolve) ((reg.decodeExpr a).add (reg.decodeExpr b))
        = (a.add b).anyVarIn xs
      rw [Expression.anyVarIn, DenseExpr.anyVarIn, iha ha, ihb hb]
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      show Expression.anyVarIn (xs.map reg.resolve) ((reg.decodeExpr a).mul (reg.decodeExpr b))
        = (a.mul b).anyVarIn xs
      rw [Expression.anyVarIn, DenseExpr.anyVarIn, iha ha, ihb hb]

/-- Dense `Expression.hasConstFoldableNode` (mirrors `Expression.hasConstFoldableNode`). -/
def DenseExpr.hasConstFoldableNode : DenseExpr p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b => !(DenseExpr.add a b).hasVar || a.hasConstFoldableNode || b.hasConstFoldableNode
  | .mul a b => !(DenseExpr.mul a b).hasVar || a.hasConstFoldableNode || b.hasConstFoldableNode

theorem VarRegistry.decodeExpr_hasConstFoldableNode (reg : VarRegistry) (e : DenseExpr p) :
    (reg.decodeExpr e).hasConstFoldableNode = e.hasConstFoldableNode := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb =>
      show (Expression.add (reg.decodeExpr a) (reg.decodeExpr b)).hasConstFoldableNode
        = (DenseExpr.add a b).hasConstFoldableNode
      simp only [Expression.hasConstFoldableNode, DenseExpr.hasConstFoldableNode,
        Expression.hasVar, DenseExpr.hasVar, reg.decodeExpr_hasVar, iha, ihb]
  | mul a b iha ihb =>
      show (Expression.mul (reg.decodeExpr a) (reg.decodeExpr b)).hasConstFoldableNode
        = (DenseExpr.mul a b).hasConstFoldableNode
      simp only [Expression.hasConstFoldableNode, DenseExpr.hasConstFoldableNode,
        Expression.hasVar, DenseExpr.hasVar, reg.decodeExpr_hasVar, iha, ihb]

/-! ## Dense `findDomainAlg`, `coveredBy`, `coveredCsOf` -/

/-- Dense `findDomainAlg` (mirrors `findDomainAlg`). Returns a variable-free `List (ZMod p)`, so the
    dense result is *identical* to the spec one on decoded inputs. -/
def denseFindDomainAlg (all : List (DenseExpr p)) (i : VarId) : Option (List (ZMod p)) :=
  match all with
  | [] => none
  | c :: rest =>
    if c.mentions i then
      match denseRootsIn i c with
      | some d => some d
      | none => denseFindDomainAlg rest i
    else denseFindDomainAlg rest i

theorem denseFindDomainAlg_decode (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) :
    ∀ (all : List (DenseExpr p)), (∀ c ∈ all, c.CoveredBy reg) →
      findDomainAlg (all.map reg.decodeExpr) (reg.resolve i) = denseFindDomainAlg all i := by
  intro all
  induction all with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro hcov
      have hcc : c.CoveredBy reg := hcov c (List.mem_cons_self ..)
      have hcr : ∀ c' ∈ rest, c'.CoveredBy reg := fun c' h => hcov c' (List.mem_cons_of_mem _ h)
      show findDomainAlg (reg.decodeExpr c :: rest.map reg.decodeExpr) (reg.resolve i)
        = denseFindDomainAlg (c :: rest) i
      rw [findDomainAlg, denseFindDomainAlg, (reg.decodeExpr_mentions hi c hcc).symm]
      by_cases hm : c.mentions i = true
      · rw [if_pos hm, if_pos hm, denseRootsIn_decode reg hi c hcc]
        cases denseRootsIn i c with
        | some d => rfl
        | none => exact ih hcr
      · rw [if_neg hm, if_neg hm]; exact ih hcr

/-- Dense `coveredBy` (mirrors `coveredBy`). -/
def denseCoveredBy (xs : List VarId) (c : DenseExpr p) : Bool :=
  c.hasVar && c.varsInF xs

theorem denseCoveredBy_decode (reg : VarRegistry) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (c : DenseExpr p) (hc : c.CoveredBy reg) :
    coveredBy (xs.map reg.resolve) (reg.decodeExpr c) = denseCoveredBy xs c := by
  unfold coveredBy denseCoveredBy
  rw [reg.decodeExpr_hasVar, denseExpr_varsInF_decode reg xs hxv c hc]

/-- Dense `coveredCsOf` (mirrors `coveredCsOf`). -/
def denseCoveredCsOf (d : DenseConstraintSystem p) (xs : List VarId) : List (DenseExpr p) :=
  d.algebraicConstraints.filter (denseCoveredBy xs)

theorem denseCoveredCsOf_decode (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x) :
    coveredCsOf (reg.decodeCS d) (xs.map reg.resolve)
      = (denseCoveredCsOf d xs).map reg.decodeExpr := by
  unfold coveredCsOf denseCoveredCsOf
  show ((d.algebraicConstraints.map reg.decodeExpr).filter (coveredBy (xs.map reg.resolve)))
    = (d.algebraicConstraints.filter (denseCoveredBy xs)).map reg.decodeExpr
  rw [← filter_map_comm reg.decodeExpr (denseCoveredBy xs) (coveredBy (xs.map reg.resolve))
    d.algebraicConstraints (fun c hc => (denseCoveredBy_decode reg xs hxv c (hcov.1 c hc)).symm)]

/-! ## Dense `groupDoms` -/

/-- Dense `groupDoms` (mirrors `groupDoms`). -/
def denseGroupDoms (es : List (DenseExpr p)) :
    List VarId → Option (List (VarId × List (ZMod p)))
  | [] => some []
  | i :: rest =>
    match denseFindDomainAlg es i, denseGroupDoms es rest with
    | some d, some ds => some ((i, d) :: ds)
    | _, _ => none

theorem denseGroupDoms_decode (reg : VarRegistry) (es : List (DenseExpr p))
    (hes : ∀ c ∈ es, c.CoveredBy reg) :
    ∀ (xs : List VarId), (∀ x ∈ xs, reg.Valid x) →
      groupDoms (es.map reg.decodeExpr) (xs.map reg.resolve)
        = (denseGroupDoms es xs).map (fun ds => ds.map (fun kd => (reg.resolve kd.1, kd.2))) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons i rest ih =>
      intro hxv
      have hiv : reg.Valid i := hxv i (List.mem_cons_self ..)
      have hrv : ∀ x ∈ rest, reg.Valid x := fun x h => hxv x (List.mem_cons_of_mem _ h)
      show groupDoms (es.map reg.decodeExpr) (reg.resolve i :: rest.map reg.resolve)
        = (denseGroupDoms es (i :: rest)).map _
      rw [groupDoms, denseGroupDoms, denseFindDomainAlg_decode reg hiv es hes, ih hrv]
      cases denseFindDomainAlg es i <;> cases denseGroupDoms es rest <;> rfl

/-! ## Dense enumeration of assignments and survivors -/

/-- Dense `assignments` (mirrors `assignments`). -/
def denseAssignments : List (VarId × List (ZMod p)) → List (List (VarId × ZMod p))
  | [] => [[]]
  | (i, d) :: rest => (denseAssignments rest).flatMap (fun a => d.map (fun v => (i, v) :: a))

theorem denseAssignments_decode (reg : VarRegistry) :
    ∀ (doms : List (VarId × List (ZMod p))),
      assignments (doms.map (fun kd => (reg.resolve kd.1, kd.2)))
        = (denseAssignments doms).map (fun a => a.map (fun kv => (reg.resolve kv.1, kv.2))) := by
  intro doms
  induction doms with
  | nil => rfl
  | cons kd rest ih =>
      obtain ⟨i, d⟩ := kd
      show assignments ((reg.resolve i, d) :: rest.map (fun kd => (reg.resolve kd.1, kd.2)))
        = (denseAssignments ((i, d) :: rest)).map _
      simp only [assignments, denseAssignments, ih, List.map_flatMap, List.flatMap_map,
        List.map_map, Function.comp_def, List.map_cons]

/-- Every dense assignment has the domains' keys, in order (mirrors `assignments_keys`). -/
theorem denseAssignments_keys :
    ∀ (doms : List (VarId × List (ZMod p))) (a : List (VarId × ZMod p)),
      a ∈ denseAssignments doms → a.map Prod.fst = doms.map Prod.fst := by
  intro doms
  induction doms with
  | nil => intro a h; simp only [denseAssignments, List.mem_singleton] at h; subst h; rfl
  | cons kd rest ih =>
      obtain ⟨i, d⟩ := kd
      intro a h
      simp only [denseAssignments, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a', ha', v, hv, rfl⟩ := h
      simp [ih a' ha']

/-- Evaluating the decoded expression under `envOf`/`evalFast` on the decoded point equals evaluating
    the dense expression under `denseEnvOfFast`. -/
theorem denseEvalFast_decode (reg : VarRegistry) (e : DenseExpr p) (hc : e.CoveredBy reg)
    (s : List (VarId × ZMod p)) (hs : ∀ kv ∈ s, reg.Valid kv.1) :
    (reg.decodeExpr e).evalFast (envOf (s.map (fun kv => (reg.resolve kv.1, kv.2))))
      = e.eval (denseEnvOfFast s) := by
  rw [Expression.evalFast_eq, ← envOfFast_eq]
  exact denseExpr_eval_decode reg e hc s hs

/-- Dense `groupSurvivorsE`, mirroring the *spec* (post-`groupSurvivorsE_eq`) direct filter form (the
    survivor set is what matters for byte-identity; the compiled fast path is a pure speedup). -/
def denseGroupSurvivorsE (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    List (List (VarId × ZMod p)) :=
  (denseAssignments doms).filter (fun a => es.all (fun c => decide (c.eval (denseEnvOfFast a) = 0)))

theorem denseGroupSurvivorsE_decode (reg : VarRegistry) (es : List (DenseExpr p))
    (hes : ∀ c ∈ es, c.CoveredBy reg) (doms : List (VarId × List (ZMod p)))
    (hdv : ∀ kd ∈ doms, reg.Valid kd.1) :
    groupSurvivorsE (es.map reg.decodeExpr) (doms.map (fun kd => (reg.resolve kd.1, kd.2)))
      = (denseGroupSurvivorsE es doms).map (fun a => a.map (fun kv => (reg.resolve kv.1, kv.2))) := by
  rw [groupSurvivorsE_eq, denseAssignments_decode reg doms]
  refine (filter_map_comm (fun a => a.map (fun kv => (reg.resolve kv.1, kv.2)))
    (fun a => es.all (fun c => decide (c.eval (denseEnvOfFast a) = 0)))
    (fun a => (es.map reg.decodeExpr).all (fun c => decide (c.evalFast (envOf a) = 0)))
    (denseAssignments doms) ?_).symm
  intro a ha
  have hak : a.map Prod.fst = doms.map Prod.fst := denseAssignments_keys doms a ha
  have hav : ∀ kv ∈ a, reg.Valid kv.1 := by
    intro kv hkv
    have hm : kv.1 ∈ a.map Prod.fst := List.mem_map.2 ⟨kv, hkv, rfl⟩
    rw [hak] at hm
    obtain ⟨kd, hkd, he⟩ := List.mem_map.1 hm
    rw [← he]; exact hdv kd hkd
  show es.all (fun c => decide (c.eval (denseEnvOfFast a) = 0))
    = (es.map reg.decodeExpr).all
        (fun c => decide (c.evalFast (envOf (a.map (fun kv => (reg.resolve kv.1, kv.2)))) = 0))
  rw [List.all_map]
  refine list_all_congr (fun c hc => ?_)
  simp only [Function.comp_apply, denseEvalFast_decode reg c (hes c hc) a hav]

/-! ## Dense `constOnSurvs` -/

/-- Dense `constOnSurvs` (mirrors `constOnSurvs`); returns a variable-free `Option (ZMod p)`. -/
def denseConstOnSurvs (survs : List (List (VarId × ZMod p))) (e : DenseExpr p) : Option (ZMod p) :=
  match survs with
  | [] => none
  | s₀ :: rest =>
    let v₀ := e.eval (denseEnvOfFast s₀)
    if (s₀ :: rest).all (fun s => decide (e.eval (denseEnvOfFast s) = v₀)) then some v₀ else none

theorem denseConstOnSurvs_decode (reg : VarRegistry) (survs : List (List (VarId × ZMod p)))
    (hsv : ∀ s ∈ survs, ∀ kv ∈ s, reg.Valid kv.1) (e : DenseExpr p) (hc : e.CoveredBy reg) :
    constOnSurvs (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))) (reg.decodeExpr e)
      = denseConstOnSurvs survs e := by
  cases survs with
  | nil => rfl
  | cons s₀ rest =>
      have hs0v : ∀ kv ∈ s₀, reg.Valid kv.1 := hsv s₀ (List.mem_cons_self ..)
      have hv0 : (reg.decodeExpr e).evalFast (envOf (s₀.map (fun kv => (reg.resolve kv.1, kv.2))))
          = e.eval (denseEnvOfFast s₀) := denseEvalFast_decode reg e hc s₀ hs0v
      show (match (s₀ :: rest).map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))) with
            | [] => none
            | s₀' :: rest' =>
              let v₀ := (reg.decodeExpr e).evalFast (envOf s₀')
              if (s₀' :: rest').all (fun s => decide ((reg.decodeExpr e).evalFast (envOf s) = v₀))
              then some v₀ else none)
        = denseConstOnSurvs (s₀ :: rest) e
      simp only [List.map_cons]
      unfold denseConstOnSurvs
      rw [hv0]
      have halleq : (s₀.map (fun kv => (reg.resolve kv.1, kv.2))
              :: rest.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))).all
            (fun s => decide ((reg.decodeExpr e).evalFast (envOf s) = e.eval (denseEnvOfFast s₀)))
          = (s₀ :: rest).all (fun s => decide (e.eval (denseEnvOfFast s) = e.eval (denseEnvOfFast s₀))) := by
        rw [show (s₀.map (fun kv => (reg.resolve kv.1, kv.2))
              :: rest.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
            = (s₀ :: rest).map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))) from rfl,
          List.all_map]
        refine list_all_congr (fun s hs => ?_)
        simp only [Function.comp_apply, denseEvalFast_decode reg e hc s (hsv s hs)]
      rw [halleq]

/-! ## The dense fold rewrite -/

/-- Dense `foldRewriteGo` (mirrors `foldRewriteGo`; `varsIn` via the dense `varsInF`). -/
def denseFoldRewriteGo (xs : List VarId) (survs : List (List (VarId × ZMod p))) :
    DenseExpr p → DenseExpr p
  | .const c => .const c
  | .var y => .var y
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then
        match denseConstOnSurvs survs (.add a b) with
        | some c => .const c
        | none => .add (denseFoldRewriteGo xs survs a) (denseFoldRewriteGo xs survs b)
      else .add (denseFoldRewriteGo xs survs a) (denseFoldRewriteGo xs survs b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then
        match denseConstOnSurvs survs (.mul a b) with
        | some c => .const c
        | none => .mul (denseFoldRewriteGo xs survs a) (denseFoldRewriteGo xs survs b)
      else .mul (denseFoldRewriteGo xs survs a) (denseFoldRewriteGo xs survs b)

theorem denseFoldRewriteGo_decode (reg : VarRegistry) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (survs : List (List (VarId × ZMod p))) (hsv : ∀ s ∈ survs, ∀ kv ∈ s, reg.Valid kv.1)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    reg.decodeExpr (denseFoldRewriteGo xs survs e)
      = foldRewriteGo (xs.map reg.resolve)
          (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))) (reg.decodeExpr e) := by
  induction e with
  | const c => rfl
  | var y => rfl
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      have hcond : ((reg.decodeExpr a).add (reg.decodeExpr b)).varsIn (xs.map reg.resolve)
          = (DenseExpr.add a b).varsInF xs := by
        rw [← Expression.varsInF_eq]
        exact denseExpr_varsInF_decode reg xs hxv (a.add b) hc
      have hconst : constOnSurvs (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
            ((reg.decodeExpr a).add (reg.decodeExpr b))
          = denseConstOnSurvs survs (a.add b) :=
        denseConstOnSurvs_decode reg survs hsv (a.add b) hc
      show reg.decodeExpr (denseFoldRewriteGo xs survs (a.add b))
        = foldRewriteGo (xs.map reg.resolve)
            (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
            ((reg.decodeExpr a).add (reg.decodeExpr b))
      rw [foldRewriteGo, denseFoldRewriteGo, hcond]
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin, if_pos hin, hconst]
        cases denseConstOnSurvs survs (a.add b) with
        | some c => rfl
        | none =>
            show reg.decodeExpr ((denseFoldRewriteGo xs survs a).add (denseFoldRewriteGo xs survs b))
              = Expression.add _ _
            rw [VarRegistry.decodeExpr, iha ha, ihb hb]
      · rw [if_neg (by simpa using hin), if_neg (by simpa using hin)]
        show reg.decodeExpr ((denseFoldRewriteGo xs survs a).add (denseFoldRewriteGo xs survs b))
          = Expression.add _ _
        rw [VarRegistry.decodeExpr, iha ha, ihb hb]
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      have hcond : ((reg.decodeExpr a).mul (reg.decodeExpr b)).varsIn (xs.map reg.resolve)
          = (DenseExpr.mul a b).varsInF xs := by
        rw [← Expression.varsInF_eq]
        exact denseExpr_varsInF_decode reg xs hxv (a.mul b) hc
      have hconst : constOnSurvs (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
            ((reg.decodeExpr a).mul (reg.decodeExpr b))
          = denseConstOnSurvs survs (a.mul b) :=
        denseConstOnSurvs_decode reg survs hsv (a.mul b) hc
      show reg.decodeExpr (denseFoldRewriteGo xs survs (a.mul b))
        = foldRewriteGo (xs.map reg.resolve)
            (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
            ((reg.decodeExpr a).mul (reg.decodeExpr b))
      rw [foldRewriteGo, denseFoldRewriteGo, hcond]
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin, if_pos hin, hconst]
        cases denseConstOnSurvs survs (a.mul b) with
        | some c => rfl
        | none =>
            show reg.decodeExpr ((denseFoldRewriteGo xs survs a).mul (denseFoldRewriteGo xs survs b))
              = Expression.mul _ _
            rw [VarRegistry.decodeExpr, iha ha, ihb hb]
      · rw [if_neg (by simpa using hin), if_neg (by simpa using hin)]
        show reg.decodeExpr ((denseFoldRewriteGo xs survs a).mul (denseFoldRewriteGo xs survs b))
          = Expression.mul _ _
        rw [VarRegistry.decodeExpr, iha ha, ihb hb]

/-- Folding never introduces a `VarId` (mirrors `foldRewriteGo_vars`). -/
theorem denseFoldRewriteGo_vars (xs : List VarId) (survs : List (List (VarId × ZMod p)))
    (e : DenseExpr p) : ∀ i ∈ (denseFoldRewriteGo xs survs e).vars, i ∈ e.vars := by
  induction e with
  | const c => intro i hi; exact absurd (show i ∈ ([] : List VarId) from hi) (by simp)
  | var y => intro i hi; exact hi
  | add a b iha ihb =>
      unfold denseFoldRewriteGo
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]
        cases denseConstOnSurvs survs (a.add b) with
        | none =>
            intro i hi
            simp only [DenseExpr.vars, List.mem_append] at hi ⊢
            rcases hi with hi | hi
            · exact Or.inl (iha i hi)
            · exact Or.inr (ihb i hi)
        | some c => intro i hi; simp [DenseExpr.vars] at hi
      · rw [if_neg (by simpa using hin)]
        intro i hi
        simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inl (iha i hi)
        · exact Or.inr (ihb i hi)
  | mul a b iha ihb =>
      unfold denseFoldRewriteGo
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]
        cases denseConstOnSurvs survs (a.mul b) with
        | none =>
            intro i hi
            simp only [DenseExpr.vars, List.mem_append] at hi ⊢
            rcases hi with hi | hi
            · exact Or.inl (iha i hi)
            · exact Or.inr (ihb i hi)
        | some c => intro i hi; simp [DenseExpr.vars] at hi
      · rw [if_neg (by simpa using hin)]
        intro i hi
        simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inl (iha i hi)
        · exact Or.inr (ihb i hi)

/-- Dense `foldRewrite` (mirrors `foldRewrite`, gated by `anyVarIn`/`hasConstFoldableNode`). -/
def denseFoldRewrite (xs : List VarId) (survs : List (List (VarId × ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs || e.hasConstFoldableNode then denseFoldRewriteGo xs survs e else e

theorem denseFoldRewrite_decode (reg : VarRegistry) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (survs : List (List (VarId × ZMod p))) (hsv : ∀ s ∈ survs, ∀ kv ∈ s, reg.Valid kv.1)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    reg.decodeExpr (denseFoldRewrite xs survs e)
      = foldRewrite (xs.map reg.resolve)
          (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))) (reg.decodeExpr e) := by
  unfold denseFoldRewrite foldRewrite
  rw [denseExpr_anyVarIn_decode reg xs hxv e hc, reg.decodeExpr_hasConstFoldableNode e]
  by_cases hg : (e.anyVarIn xs || e.hasConstFoldableNode) = true
  · rw [if_pos hg, if_pos hg]
    exact denseFoldRewriteGo_decode reg xs hxv survs hsv e hc
  · rw [if_neg (by simpa using hg), if_neg (by simpa using hg)]

theorem denseFoldRewrite_vars (xs : List VarId) (survs : List (List (VarId × ZMod p)))
    (e : DenseExpr p) : ∀ i ∈ (denseFoldRewrite xs survs e).vars, i ∈ e.vars := by
  intro i hi
  unfold denseFoldRewrite at hi
  split at hi
  · exact denseFoldRewriteGo_vars xs survs e i hi
  · exact hi

theorem denseFoldRewrite_covered (reg : VarRegistry) (xs : List VarId)
    (survs : List (List (VarId × ZMod p))) {e : DenseExpr p} (hc : e.CoveredBy reg) :
    (denseFoldRewrite xs survs e).CoveredBy reg :=
  fun i hi => hc i (denseFoldRewrite_vars xs survs e i hi)

/-! ## The folded output -/

/-- Dense `foldOut` (mirrors `foldOut`). -/
def denseFoldOut (d : DenseConstraintSystem p) (xs : List VarId)
    (survs : List (List (VarId × ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map (denseFoldRewrite xs survs)
        ++ denseCoveredCsOf d xs,
    busInteractions := d.busInteractions.map
      (fun bi => { bi with
        multiplicity := denseFoldRewrite xs survs bi.multiplicity,
        payload := bi.payload.map (denseFoldRewrite xs survs) }) }

theorem denseFoldOut_decode (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x) (survs : List (List (VarId × ZMod p)))
    (hsv : ∀ s ∈ survs, ∀ kv ∈ s, reg.Valid kv.1) :
    reg.decodeCS (denseFoldOut d xs survs)
      = foldOut (reg.decodeCS d) (xs.map reg.resolve)
          (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))) := by
  have hFR : ∀ e, e.CoveredBy reg → reg.decodeExpr (denseFoldRewrite xs survs e)
      = foldRewrite (xs.map reg.resolve) (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
          (reg.decodeExpr e) :=
    fun e he => denseFoldRewrite_decode reg xs hxv survs hsv e he
  have halg : ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map (denseFoldRewrite xs survs)
        ++ denseCoveredCsOf d xs).map reg.decodeExpr
      = ((d.algebraicConstraints.map reg.decodeExpr).filter (fun c => !coveredBy (xs.map reg.resolve) c)).map
          (foldRewrite (xs.map reg.resolve) (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))))
        ++ coveredCsOf (reg.decodeCS d) (xs.map reg.resolve) := by
    rw [List.map_append]
    congr 1
    · rw [← filter_map_comm reg.decodeExpr (fun c => !denseCoveredBy xs c)
          (fun c => !coveredBy (xs.map reg.resolve) c) d.algebraicConstraints
          (fun c hc => by simp only [denseCoveredBy_decode reg xs hxv c (hcov.1 c hc)]),
        List.map_map, List.map_map]
      exact List.map_congr_left (fun c hc => hFR c (hcov.1 c (List.mem_of_mem_filter hc)))
    · exact (denseCoveredCsOf_decode reg d hcov xs hxv).symm
  have hbis : (d.busInteractions.map
        (fun bi => { bi with
          multiplicity := denseFoldRewrite xs survs bi.multiplicity,
          payload := bi.payload.map (denseFoldRewrite xs survs) })).map reg.decodeBI
      = (d.busInteractions.map reg.decodeBI).map (·.mapExpr
          (foldRewrite (xs.map reg.resolve) (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))))) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun bi hbi => reg.decodeBI_mapExpr_covered hFR bi (hcov.2 bi hbi))
  exact congr (congrArg ConstraintSystem.mk halg) hbis

theorem denseFoldOut_covered (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (xs : List VarId) (survs : List (List (VarId × ZMod p))) :
    (denseFoldOut d xs survs).CoveredBy reg := by
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · have he' : e ∈ (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseFoldRewrite xs survs) ++ denseCoveredCsOf d xs := he
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact denseFoldRewrite_covered reg xs survs (hcov.1 c (List.mem_of_mem_filter hc))
    · have h' : e ∈ d.algebraicConstraints.filter (denseCoveredBy xs) := h
      exact hcov.1 e (List.mem_of_mem_filter h')
  · have hbi' : bi ∈ d.busInteractions.map
        (fun bi => { bi with
          multiplicity := denseFoldRewrite xs survs bi.multiplicity,
          payload := bi.payload.map (denseFoldRewrite xs survs) }) := hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    obtain ⟨hm, hp⟩ := hcov.2 bi0 hbi0
    refine ⟨denseFoldRewrite_covered reg xs survs hm, fun e he => ?_⟩
    have he' : e ∈ bi0.payload.map (denseFoldRewrite xs survs) := he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he'
    exact denseFoldRewrite_covered reg xs survs (hp e0 he0)

/-! ## The no-op gate `systemHasFoldable` -/

/-- Dense `Expression.hasFoldable` (mirrors `Expression.hasFoldable`). -/
def DenseExpr.hasFoldable (xs : List VarId) (survs : List (List (VarId × ZMod p))) :
    DenseExpr p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b =>
      ((DenseExpr.add a b).varsInF xs && (denseConstOnSurvs survs (.add a b)).isSome) ||
        a.hasFoldable xs survs || b.hasFoldable xs survs
  | .mul a b =>
      ((DenseExpr.mul a b).varsInF xs && (denseConstOnSurvs survs (.mul a b)).isSome) ||
        a.hasFoldable xs survs || b.hasFoldable xs survs

theorem denseExpr_hasFoldable_decode (reg : VarRegistry) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (survs : List (List (VarId × ZMod p))) (hsv : ∀ s ∈ survs, ∀ kv ∈ s, reg.Valid kv.1)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    (reg.decodeExpr e).hasFoldable (xs.map reg.resolve)
        (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
      = e.hasFoldable xs survs := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      have hvars : ((reg.decodeExpr a).add (reg.decodeExpr b)).varsIn (xs.map reg.resolve)
          = (DenseExpr.add a b).varsInF xs := by
        rw [← Expression.varsInF_eq]
        exact denseExpr_varsInF_decode reg xs hxv (a.add b) hc
      have hconst : (constOnSurvs (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
            ((reg.decodeExpr a).add (reg.decodeExpr b))).isSome
          = (denseConstOnSurvs survs (a.add b)).isSome :=
        congrArg Option.isSome (denseConstOnSurvs_decode reg survs hsv (a.add b) hc)
      simp only [VarRegistry.decodeExpr, Expression.hasFoldable, DenseExpr.hasFoldable,
        hvars, hconst, iha ha, ihb hb]
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      have hvars : ((reg.decodeExpr a).mul (reg.decodeExpr b)).varsIn (xs.map reg.resolve)
          = (DenseExpr.mul a b).varsInF xs := by
        rw [← Expression.varsInF_eq]
        exact denseExpr_varsInF_decode reg xs hxv (a.mul b) hc
      have hconst : (constOnSurvs (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
            ((reg.decodeExpr a).mul (reg.decodeExpr b))).isSome
          = (denseConstOnSurvs survs (a.mul b)).isSome :=
        congrArg Option.isSome (denseConstOnSurvs_decode reg survs hsv (a.mul b) hc)
      simp only [VarRegistry.decodeExpr, Expression.hasFoldable, DenseExpr.hasFoldable,
        hvars, hconst, iha ha, ihb hb]

/-- Dense `systemHasFoldable` (mirrors `systemHasFoldable`). -/
def denseSystemHasFoldable (d : DenseConstraintSystem p) (xs : List VarId)
    (survs : List (List (VarId × ZMod p))) : Bool :=
  d.algebraicConstraints.any (fun c => !denseCoveredBy xs c && c.hasFoldable xs survs) ||
    d.busInteractions.any (fun bi =>
      bi.multiplicity.hasFoldable xs survs || bi.payload.any (fun e => e.hasFoldable xs survs))

theorem denseSystemHasFoldable_decode (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (survs : List (List (VarId × ZMod p))) (hsv : ∀ s ∈ survs, ∀ kv ∈ s, reg.Valid kv.1) :
    systemHasFoldable (reg.decodeCS d) (xs.map reg.resolve)
        (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2))))
      = denseSystemHasFoldable d xs survs := by
  simp only [systemHasFoldable, denseSystemHasFoldable, VarRegistry.decodeCS]
  congr 1
  · rw [List.any_map]
    refine list_any_congr (fun c hc => ?_)
    have hcc : c.CoveredBy reg := hcov.1 c hc
    simp only [Function.comp_apply, denseCoveredBy_decode reg xs hxv c hcc,
      denseExpr_hasFoldable_decode reg xs hxv survs hsv c hcc]
  · rw [List.any_map]
    refine list_any_congr (fun bi hbi => ?_)
    have hbc : denseBICovered reg bi := hcov.2 bi hbi
    obtain ⟨hm, hp⟩ := hbc
    simp only [Function.comp_apply]
    congr 1
    · exact denseExpr_hasFoldable_decode reg xs hxv survs hsv bi.multiplicity hm
    · show (bi.payload.map reg.decodeExpr).any (fun e => e.hasFoldable (xs.map reg.resolve)
            (survs.map (fun s => s.map (fun kv => (reg.resolve kv.1, kv.2)))))
        = bi.payload.any (fun e => e.hasFoldable xs survs)
      rw [List.any_map]
      exact list_any_congr (fun e he =>
        denseExpr_hasFoldable_decode reg xs hxv survs hsv e (hp e he))

/-! ## `denseGroupDoms` key structure -/

/-- Dense `groupDoms` yields the target keys, in order (mirrors `groupDoms_fst`). -/
theorem denseGroupDoms_fst (es : List (DenseExpr p)) :
    ∀ (xs : List VarId) (doms : List (VarId × List (ZMod p))),
      denseGroupDoms es xs = some doms → doms.map Prod.fst = xs := by
  intro xs
  induction xs with
  | nil => intro doms h; simp only [denseGroupDoms, Option.some.injEq] at h; subst h; rfl
  | cons i rest ih =>
      intro doms h
      rw [denseGroupDoms] at h
      cases hd : denseFindDomainAlg es i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some d =>
          cases hr : denseGroupDoms es rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds =>
              rw [hd, hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp [ih ds hr]

/-! ## The dense direct fold loop -/

/-- One dense direct fold step (mirrors `foldStepWith`; only the output system, no `PassCorrect`). -/
def denseFoldStepWith (d : DenseConstraintSystem p) (xs : List VarId) (es : List (DenseExpr p)) :
    DenseConstraintSystem p :=
  match denseGroupDoms es xs with
  | none => d
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      if 1 ≤ (denseGroupSurvivorsE es doms).length
          && denseSystemHasFoldable d xs (denseGroupSurvivorsE es doms) then
        denseFoldOut d xs (denseGroupSurvivorsE es doms)
      else d
    else d

theorem denseFoldStepWith_covered (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (xs : List VarId) (es : List (DenseExpr p)) :
    (denseFoldStepWith d xs es).CoveredBy reg := by
  unfold denseFoldStepWith
  split
  · exact hcov
  · rename_i doms heq
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hs : (1 ≤ (denseGroupSurvivorsE es doms).length
          && denseSystemHasFoldable d xs (denseGroupSurvivorsE es doms)) = true
      · rw [if_pos hs]; exact denseFoldOut_covered reg d hcov xs (denseGroupSurvivorsE es doms)
      · rw [if_neg (by simpa using hs)]; exact hcov
    · rw [if_neg hp]; exact hcov

/-- Every survivor point key of `denseGroupSurvivorsE es doms` is a domain key. -/
theorem denseGroupSurvivorsE_keys (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p)))
    {s : List (VarId × ZMod p)} (hs : s ∈ denseGroupSurvivorsE es doms) :
    s.map Prod.fst = doms.map Prod.fst :=
  denseAssignments_keys doms s (List.mem_of_mem_filter hs)

/-- The dense direct fold loop (mirrors `foldLoopDirect`; only the output system). -/
def denseFoldLoopDirect : List (List VarId) → DenseConstraintSystem p → DenseConstraintSystem p
  | [], d => d
  | xs :: rest, d => denseFoldLoopDirect rest (denseFoldStepWith d xs (denseCoveredCsOf d xs))

/-! ## Ordered dense inverted index (mirrors `CoveredIndex.coveredIdx` + `coveredIdx_eq_filter`)

The indexed fold path needs the covered set **exactly** (ordered), so `denseCoveredIdx` restores the
items' original order (via `mergeSort` on positions) and equals the plain filter whenever every
`Q`-item shares a variable with `xs`. The `Nat`/`HashSet Nat` combinatorics are reused verbatim from
the spec `CoveredIndex`; only the bucket key type (`VarId`) changes. -/

variable {α : Type}

/-- Ordered dense covered items for target `xs` (mirrors `CoveredIndex.coveredIdx`). -/
def denseCoveredIdx (idx : DenseCovIndex) (arr : Array α) (Q : α → Bool) (xs : List VarId) :
    List α :=
  let uniq := ((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList
  (uniq.mergeSort (· ≤ ·)).filterMap (fun i =>
    if h : i < arr.size then (if Q arr[i] then some arr[i] else none) else none)

/-- Inserting a position into dense buckets never removes an existing membership. -/
theorem denseInner_getD_mono (i : Nat) (vs : List VarId) (w : VarId) (j : Nat) :
    ∀ (m : Std.HashMap VarId (List Nat)), j ∈ m.getD w [] →
    j ∈ (vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m).getD w [] := by
  induction vs with
  | nil => intro m hj; simpa using hj
  | cons v0 rest ih =>
    intro m hj
    simp only [List.foldl_cons]
    apply ih
    rw [Std.HashMap.getD_insert]
    by_cases h : (v0 == w) = true
    · rw [if_pos h]
      have hvw : v0 = w := eq_of_beq h
      subst hvw
      exact List.mem_cons_of_mem _ hj
    · rw [if_neg h]; exact hj

/-- After inserting `i` into every dense bucket of `vs`, `i` is in the bucket of each `v ∈ vs`. -/
theorem denseInner_getD_self (i : Nat) (vs : List VarId) (v : VarId) :
    ∀ (m : Std.HashMap VarId (List Nat)), v ∈ vs →
    i ∈ (vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m).getD v [] := by
  induction vs with
  | nil => intro m hv; simp at hv
  | cons v0 rest ih =>
    intro m hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · apply denseInner_getD_mono
      rw [Std.HashMap.getD_insert, if_pos (by simp)]
      exact List.mem_cons_self
    · exact ih _ hv

/-- **Dense index completeness (buckets).** Every item at position `i` with variable `v` bucketed
    under `v` (mirrors `CoveredIndex.buildStep_bucket_complete`). -/
theorem denseBuildStep_bucket_complete (varsOf : α → List VarId) :
    ∀ (l : List (α × Nat)) (a : α) (i : Nat), (a, i) ∈ l → ∀ (v : VarId), v ∈ varsOf a →
      i ∈ (l.foldr (denseBuildStep varsOf) ⟨∅, []⟩).buckets.getD v [] := by
  intro l
  induction l with
  | nil => intro a i hai; simp at hai
  | cons ai0 rest ih =>
    intro a i hai v hv
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hai with heq | hmem
    · rw [← heq]
      cases hvs : varsOf a with
      | nil => rw [hvs] at hv; simp at hv
      | cons w0 ws =>
        rw [denseBuildStep_buckets_cons varsOf (a, i) _ w0 ws hvs]
        exact denseInner_getD_self i (w0 :: ws) v _ (by rw [← hvs]; exact hv)
    · have hrec : i ∈ (rest.foldr (denseBuildStep varsOf) ⟨∅, []⟩).buckets.getD v [] := ih a i hmem v hv
      cases hvs : varsOf ai0.1 with
      | nil => rw [denseBuildStep_buckets_nil varsOf ai0 _ hvs]; exact hrec
      | cons w0 ws =>
        rw [denseBuildStep_buckets_cons varsOf ai0 _ w0 ws hvs]
        exact denseInner_getD_mono ai0.2 (w0 :: ws) v i _ hrec

/-- A position bucketed under a variable of `xs` is a dense candidate. -/
theorem denseMem_candidates (idx : DenseCovIndex) (xs : List VarId) (v : VarId) (i : Nat)
    (hv : v ∈ xs) (hi : i ∈ idx.buckets.getD v []) : i ∈ denseCandidates idx xs :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨v, hv, hi⟩)

/-- **`denseCoveredIdx` equals the plain filter** whenever every `Q`-item shares a variable with
    `xs` (mirrors `CoveredIndex.coveredIdx_eq_filter`). -/
theorem denseCoveredIdx_eq_filter (varsOf : α → List VarId) (items : List α)
    (Q : α → Bool) (xs : List VarId)
    (hcomplete : ∀ (i : Nat) (hi : i < items.length),
      Q items[i] = true → ∃ v ∈ varsOf items[i], v ∈ xs) :
    denseCoveredIdx (denseCovBuild varsOf items) items.toArray Q xs = items.filter Q := by
  rw [denseCoveredIdx]
  simp only [List.size_toArray, List.getElem_toArray]
  set cand := denseCandidates (denseCovBuild varsOf items) xs with hcand
  set gI : Nat → Option α :=
    (fun i => if h : i < items.length then (if Q items[i] then some items[i] else none) else none)
    with hgI
  set sortedL := ((cand.foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).mergeSort (· ≤ ·)
    with hsortedL
  have F1 : ∀ i, i ∈ sortedL ↔ i ∈ cand := by
    intro i
    rw [hsortedL, List.mem_mergeSort, Std.HashSet.mem_toList, CoveredIndex.mem_foldl_insert]
    simp [Std.HashSet.not_mem_empty]
  have hnodupUniq : ((cand.foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).Nodup :=
    Std.HashSet.distinct_toList.imp (fun {a b} h => by simpa using h)
  have F2 : sortedL.Nodup := by
    rw [hsortedL]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hnodupUniq
  have F3 : sortedL.Pairwise (· ≤ ·) := by
    rw [hsortedL]; exact List.sortedLE_mergeSort.pairwise
  have F4 : ∀ (i : Nat) (hi : i < items.length), Q items[i] = true → i ∈ cand := by
    intro i hi hQ
    obtain ⟨v, hvvars, hvxs⟩ := hcomplete i hi hQ
    have hz : (items.zipIdx)[i]? = some (items[i], i) := by
      rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hi]; simp
    have hmem : (items[i], i) ∈ items.zipIdx := List.mem_of_getElem? hz
    have hbucket := denseBuildStep_bucket_complete varsOf items.zipIdx items[i] i hmem v hvvars
    rw [hcand]
    exact denseMem_candidates (denseCovBuild varsOf items) xs v i hvxs hbucket
  set keepB : Nat → Bool := (fun i => (gI i).isSome) with hkeepB
  have hkeep_lt : ∀ i, keepB i = true → i < items.length := by
    intro i hk
    by_contra hcon
    simp only [hkeepB, hgI, dif_neg hcon, Option.isSome_none, Bool.false_eq_true] at hk
  have hkeep_Q : ∀ i, keepB i = true → ∃ (_ : i < items.length), Q items[i] = true := by
    intro i hk
    have hlt := hkeep_lt i hk
    refine ⟨hlt, ?_⟩
    by_contra hQc
    simp only [hkeepB, hgI, dif_pos hlt, if_neg hQc, Option.isSome_none, Bool.false_eq_true] at hk
  have L1 : ∀ (l : List Nat), l.filterMap gI = (l.filter keepB).filterMap gI := by
    intro l
    induction l with
    | nil => rfl
    | cons a rest ih =>
      by_cases hk : keepB a = true
      · rw [List.filter_cons_of_pos hk]
        cases hga : gI a with
        | none => rw [hkeepB] at hk; simp [hga] at hk
        | some b => rw [List.filterMap_cons_some hga, List.filterMap_cons_some hga, ih]
      · rw [List.filter_cons_of_neg hk]
        have hga : gI a = none := by
          by_contra hne
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hne
          exact hk (by simp [hkeepB, hb])
        rw [List.filterMap_cons_none hga, ih]
  have claim1 : (List.range items.length).filterMap gI = items.filter Q := by
    have hrange : List.range items.length = items.zipIdx.map Prod.snd := by
      rw [List.zipIdx_map_snd, List.range_eq_range']
    rw [hrange, List.filterMap_map]
    rw [CoveredIndex.filterMap_congr' items.zipIdx
      (f := gI ∘ Prod.snd) (g := fun q => if Q q.1 then some q.1 else none)
      (by
        rintro ⟨a, j⟩ hp
        obtain ⟨_, hlt, heq⟩ := List.mem_zipIdx (k := 0) hp
        have hlt' : j < items.length := by simpa using hlt
        have heq' : items[j]'hlt' = a := by simpa using heq.symm
        simp only [Function.comp_apply, hgI, dif_pos hlt', heq'])]
    rw [CoveredIndex.filterMap_if_some]
    show ((items.zipIdx.filter (Q ∘ Prod.fst)).map Prod.fst) = items.filter Q
    rw [← List.filter_map, List.zipIdx_map_fst]
  have L2 : sortedL.filter keepB = (List.range items.length).filter keepB := by
    refine List.Perm.eq_of_sortedLE
      (List.Pairwise.sublist List.filter_sublist F3).sortedLE
      (List.Pairwise.sublist List.filter_sublist List.pairwise_le_range).sortedLE
      ((List.perm_ext_iff_of_nodup
        (List.Nodup.sublist List.filter_sublist F2)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)).mpr ?_)
    intro i
    rw [List.mem_filter, List.mem_filter, F1 i, List.mem_range]
    constructor
    · rintro ⟨hcandi, hk⟩; exact ⟨hkeep_lt i hk, hk⟩
    · rintro ⟨_, hk⟩
      obtain ⟨hlt', hQ⟩ := hkeep_Q i hk
      exact ⟨F4 i hlt' hQ, hk⟩
  calc sortedL.filterMap gI
      = (sortedL.filter keepB).filterMap gI := L1 sortedL
    _ = ((List.range items.length).filter keepB).filterMap gI := by rw [L2]
    _ = (List.range items.length).filterMap gI := (L1 _).symm
    _ = items.filter Q := claim1

/-! ## The dense fold index and the index-local no-op gate -/

/-- The dense analogue of `FoldIdx` (plain data; correctness rides on the correspondence). -/
structure DenseFoldIdx (p : ℕ) where
  idx : DenseCovIndex
  arr : Array (DenseExpr p)
  bisIdx : DenseCovIndex
  arrBis : Array (BusInteraction (DenseExpr p))
  cfCs : List (DenseExpr p)
  cfBis : List (BusInteraction (DenseExpr p))

/-- Build the dense fold index for a system (mirrors `FoldIdx.mk'`). -/
def DenseFoldIdx.mk' (d : DenseConstraintSystem p) : DenseFoldIdx p where
  idx := denseCovBuild DenseExpr.vars d.algebraicConstraints
  arr := d.algebraicConstraints.toArray
  bisIdx := denseCovBuild denseBIVars d.busInteractions
  arrBis := d.busInteractions.toArray
  cfCs := d.algebraicConstraints.filter (fun c => c.hasConstFoldableNode)
  cfBis := d.busInteractions.filter (fun bi =>
    bi.multiplicity.hasConstFoldableNode || bi.payload.any (fun e => e.hasConstFoldableNode))

/-- Refresh the dense fold index after an accepted fold (mirrors `FoldIdx.refresh`: rebuild the
    constraint side, reuse the interaction buckets stale). -/
def DenseFoldIdx.refresh (old : DenseFoldIdx p) (ro : DenseConstraintSystem p) : DenseFoldIdx p where
  idx := denseCovBuild DenseExpr.vars ro.algebraicConstraints
  arr := ro.algebraicConstraints.toArray
  bisIdx := old.bisIdx
  arrBis := ro.busInteractions.toArray
  cfCs := ro.algebraicConstraints.filter (fun c => c.hasConstFoldableNode)
  cfBis := ro.busInteractions.filter (fun bi =>
    bi.multiplicity.hasConstFoldableNode || bi.payload.any (fun e => e.hasConstFoldableNode))

/-- The dense index-local no-op gate (mirrors `systemHasFoldableIdx`). -/
def denseSystemHasFoldableIdx (fidx : DenseFoldIdx p) (xs : List VarId)
    (survs : List (List (VarId × ZMod p))) : Bool :=
  (((xs.flatMap (fun v => fidx.idx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arr.size then
      let c := fidx.arr[i]
      !denseCoveredBy xs c && c.hasFoldable xs survs
    else false)) ||
  (((xs.flatMap (fun v => fidx.bisIdx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arrBis.size then
      let bi := fidx.arrBis[i]
      bi.multiplicity.hasFoldable xs survs || bi.payload.any (fun e => e.hasFoldable xs survs)
    else false)) ||
  (fidx.cfCs.any (fun c => !c.anyVarIn xs)) ||
  (fidx.cfBis.any (fun bi =>
    !(bi.multiplicity.anyVarIn xs || bi.payload.any (fun e => e.anyVarIn xs))))

/-- One index-local flatMap/`any` term corresponds (shared `List Nat`, decode-corresponding
    per-position predicate). -/
theorem denseIdxScan_corr {α β : Type} (reg : VarRegistry) (dec : α → β)
    (bkt_d : Std.HashMap VarId (List Nat)) (bkt_s : Std.HashMap Variable (List Nat))
    (l : List α) (P_d : α → Bool) (P_s : β → Bool) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (hbkt : ∀ i, reg.Valid i → bkt_d.getD i [] = bkt_s.getD (reg.resolve i) [])
    (hP : ∀ a ∈ l, P_d a = P_s (dec a)) :
    (((xs.map reg.resolve).flatMap (fun v => bkt_s.getD v [])).foldl (·.insert ·)
        (∅ : Std.HashSet Nat)).toList.any
        (fun i => if h : i < (l.map dec).toArray.size then P_s (l.map dec).toArray[i] else false)
      = ((xs.flatMap (fun v => bkt_d.getD v [])).foldl (·.insert ·)
        (∅ : Std.HashSet Nat)).toList.any
        (fun i => if h : i < l.toArray.size then P_d l.toArray[i] else false) := by
  have hcand : xs.flatMap (fun v => bkt_d.getD v [])
      = (xs.map reg.resolve).flatMap (fun v => bkt_s.getD v []) :=
    denseFlatMapGetD reg ⟨bkt_d, []⟩ ⟨bkt_s, []⟩ hbkt xs hxv
  rw [← hcand]
  refine list_any_congr (fun i _ => ?_)
  by_cases hlt : i < l.length
  · rw [dif_pos (by simp only [List.size_toArray, List.length_map]; exact hlt),
      dif_pos (by simpa using hlt)]
    simp only [List.getElem_toArray, List.getElem_map]
    exact (hP l[i] (l.getElem_mem hlt)).symm
  · rw [dif_neg (by simp only [List.size_toArray, List.length_map]; exact hlt),
      dif_neg (by simpa using hlt)]

/-! ## The dense indexed fold loop -/

/-- The `.out` of one indexed fold step (mirrors `foldStep`; index-served covered set + indexed gate). -/
theorem foldStep_out [Fact p.Prime] (bs : BusSemantics p) (cs : ConstraintSystem p)
    (fidx : FoldIdx cs) (xs : List Variable) :
    (foldStep bs cs fidx xs).1.out =
      (match groupDoms (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) xs with
       | none => cs
       | some doms =>
         if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
           (if 1 ≤ (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms).length
                && systemHasFoldableIdx fidx xs
                    (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms)
            then foldOut cs xs
                (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms)
            else cs)
           else cs) := by
  unfold foldStep
  simp only []
  split
  · rename_i hdoms; rw [hdoms]
  · rename_i doms hdoms
    conv_rhs => rw [hdoms]
    simp only [apply_ite (fun r : Σ' (r : PassResult cs bs), FoldIdx r.out => r.1.out)]

/-- The dense indexed fold step (mirrors `foldStep`; returns the output system and refreshed index). -/
def denseFoldStep (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    DenseConstraintSystem p × DenseFoldIdx p :=
  match denseGroupDoms (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs with
  | none => (d, fidx)
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      if 1 ≤ (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms).length
          && denseSystemHasFoldableIdx fidx xs
              (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms) then
        (denseFoldOut d xs (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms),
         fidx.refresh (denseFoldOut d xs
            (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms)))
      else (d, fidx)
    else (d, fidx)

/-- The dense indexed fold loop (mirrors `foldLoop`; only the output system). -/
def denseFoldLoop : List (List VarId) → DenseConstraintSystem p → DenseFoldIdx p →
    DenseConstraintSystem p
  | [], d, _ => d
  | xs :: rest, d, fidx =>
    denseFoldLoop rest (denseFoldStep d fidx xs).1 (denseFoldStep d fidx xs).2

/-- The `.out` of the indexed fold loop on a cons. -/
theorem foldLoop_out_cons [Fact p.Prime] (bs : BusSemantics p) (xs : List Variable)
    (rest : List (List Variable)) (cs : ConstraintSystem p) (fidx : FoldIdx cs) :
    (foldLoop bs (xs :: rest) cs fidx).out
      = (foldLoop bs rest (foldStep bs cs fidx xs).1.out (foldStep bs cs fidx xs).2).out := rfl

/-- `foldLoop`'s `.out` is stable under transporting the index along a system equality. -/
theorem foldLoop_out_transport [Fact p.Prime] (bs : BusSemantics p) (rest : List (List Variable))
    {cs1 cs2 : ConstraintSystem p} (h : cs1 = cs2) (fidx : FoldIdx cs2) :
    (foldLoop bs rest cs1 (h ▸ fidx)).out = (foldLoop bs rest cs2 fidx).out := by
  subst h; rfl

/-- A dense expression with a variable has a nonempty `vars` list. -/
theorem denseExpr_hasVar_vars_ne_nil (c : DenseExpr p) (h : c.hasVar = true) : c.vars ≠ [] := by
  induction c with
  | const n => simp [DenseExpr.hasVar] at h
  | var y => simp [DenseExpr.vars]
  | add a b iha ihb =>
    intro hnil
    rw [DenseExpr.vars, List.append_eq_nil_iff] at hnil
    simp only [DenseExpr.hasVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact iha h hnil.1
    · exact ihb h hnil.2
  | mul a b iha ihb =>
    intro hnil
    rw [DenseExpr.vars, List.append_eq_nil_iff] at hnil
    simp only [DenseExpr.hasVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact iha h hnil.1
    · exact ihb h hnil.2

/-- `denseContainsFast` soundness. -/
theorem denseContainsFast_sound (xs : List VarId) (v : VarId) (h : denseContainsFast xs v = true) :
    v ∈ xs := by
  induction xs with
  | nil => simp [denseContainsFast] at h
  | cons x rest ih =>
    simp only [denseContainsFast, Bool.or_eq_true] at h
    rcases h with h | h
    · exact List.mem_cons.2 (Or.inl (eq_of_beq h))
    · exact List.mem_cons.2 (Or.inr (ih h))

/-- `DenseExpr.varsInF` soundness (every variable lies in `xs`). -/
theorem denseVarsInF_sound (xs : List VarId) :
    ∀ (c : DenseExpr p), c.varsInF xs = true → ∀ v ∈ c.vars, v ∈ xs := by
  intro c
  induction c with
  | const n => intro _ v hv; simp [DenseExpr.vars] at hv
  | var y =>
      intro h v hv
      simp only [DenseExpr.vars, List.mem_singleton] at hv; subst hv
      exact denseContainsFast_sound xs v h
  | add a b iha ihb =>
      intro h v hv
      simp only [DenseExpr.varsInF, Bool.and_eq_true] at h
      simp only [DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv
  | mul a b iha ihb =>
      intro h v hv
      simp only [DenseExpr.varsInF, Bool.and_eq_true] at h
      simp only [DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv

/-- A `denseCoveredBy`-item shares a variable with the target `xs`. -/
theorem denseCoveredBy_shares_var (xs : List VarId) (c : DenseExpr p) (h : denseCoveredBy xs c = true) :
    ∃ v ∈ c.vars, v ∈ xs := by
  rw [denseCoveredBy, Bool.and_eq_true] at h
  obtain ⟨hhv, hvin⟩ := h
  obtain ⟨v, hmem⟩ := List.exists_mem_of_ne_nil c.vars (denseExpr_hasVar_vars_ne_nil c hhv)
  exact ⟨v, hmem, denseVarsInF_sound xs c hvin v hmem⟩

/-- The output system of `denseFoldStep` (its first component), as a plain match/if. -/
theorem denseFoldStep_fst (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    (denseFoldStep d fidx xs).1 =
      (match denseGroupDoms (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs with
       | none => d
       | some doms =>
         if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
           (if 1 ≤ (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms).length
                && denseSystemHasFoldableIdx fidx xs
                    (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms)
            then denseFoldOut d xs
                (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms)
            else d)
           else d) := by
  unfold denseFoldStep
  split
  · rfl
  · simp only [apply_ite Prod.fst]

theorem denseFoldStep_covered (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (fidx : DenseFoldIdx p) (xs : List VarId) : (denseFoldStep d fidx xs).1.CoveredBy reg := by
  rw [denseFoldStep_fst]
  split
  · exact hcov
  · rename_i doms _
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hs : (1 ≤ (denseGroupSurvivorsE
            (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms).length
          && denseSystemHasFoldableIdx fidx xs
            (denseGroupSurvivorsE (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) doms)) = true
      · rw [if_pos hs]; exact denseFoldOut_covered reg d hcov xs _
      · rw [if_neg (by simpa using hs)]; exact hcov
    · rw [if_neg hp]; exact hcov

theorem denseFoldStep_snd_idx (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : fidx.idx = denseCovBuild DenseExpr.vars d.algebraicConstraints) :
    (denseFoldStep d fidx xs).2.idx
      = denseCovBuild DenseExpr.vars (denseFoldStep d fidx xs).1.algebraicConstraints := by
  unfold denseFoldStep; split
  · exact hidx
  · split_ifs <;> first | rfl | exact hidx

theorem denseFoldStep_snd_arr (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (harr : fidx.arr = d.algebraicConstraints.toArray) :
    (denseFoldStep d fidx xs).2.arr = (denseFoldStep d fidx xs).1.algebraicConstraints.toArray := by
  unfold denseFoldStep; split
  · exact harr
  · split_ifs <;> first | rfl | exact harr

theorem denseFoldStep_snd_arrBis (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (harrBis : fidx.arrBis = d.busInteractions.toArray) :
    (denseFoldStep d fidx xs).2.arrBis = (denseFoldStep d fidx xs).1.busInteractions.toArray := by
  unfold denseFoldStep; split
  · exact harrBis
  · split_ifs <;> first | rfl | exact harrBis

theorem denseFoldStep_snd_cfCs (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hcf : fidx.cfCs = d.algebraicConstraints.filter (fun c => c.hasConstFoldableNode)) :
    (denseFoldStep d fidx xs).2.cfCs
      = (denseFoldStep d fidx xs).1.algebraicConstraints.filter (fun c => c.hasConstFoldableNode) := by
  unfold denseFoldStep; split
  · exact hcf
  · split_ifs <;> first | rfl | exact hcf

theorem denseFoldStep_snd_cfBis (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hcf : fidx.cfBis = d.busInteractions.filter (fun bi =>
      bi.multiplicity.hasConstFoldableNode || bi.payload.any (fun e => e.hasConstFoldableNode))) :
    (denseFoldStep d fidx xs).2.cfBis
      = (denseFoldStep d fidx xs).1.busInteractions.filter (fun bi =>
          bi.multiplicity.hasConstFoldableNode || bi.payload.any (fun e => e.hasConstFoldableNode)) := by
  unfold denseFoldStep; split
  · exact hcf
  · split_ifs <;> first | rfl | exact hcf

theorem foldStep_snd_bisIdx [Fact p.Prime] (bs : BusSemantics p) (cs : ConstraintSystem p)
    (fidx : FoldIdx cs) (xs : List Variable) : (foldStep bs cs fidx xs).2.bisIdx = fidx.bisIdx := by
  unfold foldStep; simp only []
  split
  · rfl
  · rename_i doms _
    simp only []
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hg : (1 ≤ (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms).length
          && systemHasFoldableIdx fidx xs
              (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms)) = true
      · rw [if_pos hg]; rfl
      · rw [if_neg hg]
    · rw [if_neg hp]

theorem foldStep_snd_arrBis [Fact p.Prime] (bs : BusSemantics p) (cs : ConstraintSystem p)
    (fidx : FoldIdx cs) (xs : List Variable) (harrBis : fidx.arrBis = cs.busInteractions.toArray) :
    (foldStep bs cs fidx xs).2.arrBis = (foldStep bs cs fidx xs).1.out.busInteractions.toArray := by
  unfold foldStep; simp only []
  split
  · exact harrBis
  · rename_i doms _
    simp only []
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hg : (1 ≤ (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms).length
          && systemHasFoldableIdx fidx xs
              (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms)) = true
      · rw [if_pos hg]; rfl
      · rw [if_neg hg]; exact harrBis
    · rw [if_neg hp]; exact harrBis

/-! ## Target-list construction (cold path)

The spec pass builds a `svSet`/`targets` list whose `mergeSort`/`dedupHash` canonicalisation is in the
`Variable` order — irreproducible over bare `VarId`s. So the dense pass materialises `reg.resolve` on
this cold path (once per constraint), and we prove the built dense targets decode to the spec targets.
`List.map_mergeSort` handles the sort; a `dedupHash` commutation lemma (proven from its `foldl`) the
dedup. -/

/-- `map reg.resolve` is injective on valid-id lists. -/
theorem map_resolve_inj (reg : VarRegistry) :
    ∀ (t0 t : List VarId), (∀ x ∈ t0, reg.Valid x) → (∀ x ∈ t, reg.Valid x) →
      t0.map reg.resolve = t.map reg.resolve → t0 = t := by
  intro t0
  induction t0 with
  | nil => intro t _ _ h; cases t with | nil => rfl | cons b tr => simp at h
  | cons a rest ih =>
      intro t hv0 hvt h
      cases t with
      | nil => simp at h
      | cons b tr =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hab, hrest⟩ := h
          have ha : reg.Valid a := hv0 a (List.mem_cons_self ..)
          have hb : reg.Valid b := hvt b (List.mem_cons_self ..)
          have hab' : a = b := reg.resolve_inj ha hb hab
          subst hab'
          rw [ih tr (fun x hx => hv0 x (List.mem_cons_of_mem _ hx))
            (fun x hx => hvt x (List.mem_cons_of_mem _ hx)) hrest]

/-- `==` on valid-id lists commutes with `map reg.resolve`. -/
theorem beq_map_resolve (reg : VarRegistry) (t0 t : List VarId) (hv0 : ∀ x ∈ t0, reg.Valid x)
    (hvt : ∀ x ∈ t, reg.Valid x) :
    (t0 == t) = ((t0.map reg.resolve) == (t.map reg.resolve)) := by
  by_cases h : t0 = t
  · subst h; simp
  · have h2 : t0.map reg.resolve ≠ t.map reg.resolve :=
      fun he => h (map_resolve_inj reg t0 t hv0 hvt he)
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h2]

/-- The `dedupHash` fold, related under `map reg.resolve` (both the list and the seen-set). -/
theorem dedupHash_foldl_rel (reg : VarRegistry) :
    ∀ (m : List (List VarId)), (∀ xs ∈ m, ∀ x ∈ xs, reg.Valid x) →
      ∀ (ld : List (List VarId)) (sd : Std.HashSet (List VarId))
        (ls : List (List Variable)) (ss : Std.HashSet (List Variable)),
        ld.map (fun xs => xs.map reg.resolve) = ls →
        (∀ t : List VarId, (∀ x ∈ t, reg.Valid x) → sd.contains t = ss.contains (t.map reg.resolve)) →
        (m.foldl (fun st t => if st.2.contains t then st else (t :: st.1, st.2.insert t)) (ld, sd)).1.map
            (fun xs => xs.map reg.resolve)
          = ((m.map (fun xs => xs.map reg.resolve)).foldl
              (fun st t => if st.2.contains t then st else (t :: st.1, st.2.insert t)) (ls, ss)).1
        ∧ (∀ t : List VarId, (∀ x ∈ t, reg.Valid x) →
            (m.foldl (fun st t => if st.2.contains t then st else (t :: st.1, st.2.insert t)) (ld, sd)).2.contains t
              = ((m.map (fun xs => xs.map reg.resolve)).foldl
                  (fun st t => if st.2.contains t then st else (t :: st.1, st.2.insert t)) (ls, ss)).2.contains
                  (t.map reg.resolve)) := by
  intro m
  induction m with
  | nil => intro _ ld sd ls ss hl hc; exact ⟨hl, hc⟩
  | cons t0 rest ih =>
      intro hv ld sd ls ss hl hc
      have hv0 : ∀ x ∈ t0, reg.Valid x := hv t0 (List.mem_cons_self ..)
      have hvr : ∀ xs ∈ rest, ∀ x ∈ xs, reg.Valid x := fun xs h => hv xs (List.mem_cons_of_mem _ h)
      have hcontains : sd.contains t0 = ss.contains (t0.map reg.resolve) := hc t0 hv0
      simp only [List.map_cons, List.foldl_cons]
      by_cases hct : sd.contains t0 = true
      · rw [if_pos hct, if_pos (by rw [← hcontains]; exact hct)]
        exact ih hvr ld sd ls ss hl hc
      · rw [if_neg hct, if_neg (by rw [← hcontains]; simpa using hct)]
        refine ih hvr (t0 :: ld) (sd.insert t0) ((t0.map reg.resolve) :: ls) (ss.insert (t0.map reg.resolve))
          (by simp [hl]) (fun t ht => ?_)
        rw [Std.HashSet.contains_insert, Std.HashSet.contains_insert, hc t ht, beq_map_resolve reg t0 t hv0 ht]

/-- **`dedupHash` commutes with `map reg.resolve`** on valid-id lists. -/
theorem dedupHash_map_resolve (reg : VarRegistry) (l : List (List VarId))
    (hv : ∀ xs ∈ l, ∀ x ∈ xs, reg.Valid x) :
    (dedupHash l).map (fun xs => xs.map reg.resolve)
      = dedupHash (l.map (fun xs => xs.map reg.resolve)) := by
  unfold dedupHash
  rw [← List.map_reverse]
  exact (dedupHash_foldl_rel reg l.reverse
    (fun xs h x hx => hv xs (List.mem_reverse.1 h) x hx) [] ∅ [] ∅ rfl
    (fun t _ => by simp)).1

/-- `==` on valid ids commutes with `reg.resolve`. -/
theorem beq_resolve (reg : VarRegistry) {i j : VarId} (hi : reg.Valid i) (hj : reg.Valid j) :
    (j == i) = (reg.resolve j == reg.resolve i) := by
  by_cases h : j = i
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h,
      beq_eq_false_iff_ne.mpr (fun he => h (reg.resolve_inj hj hi he))]

/-- The single-variable-constraint set (mirrors the spec pass's inline `svSet`). -/
def denseSvSet (d : DenseConstraintSystem p) : Std.HashSet VarId :=
  d.algebraicConstraints.foldl (init := ∅) fun s c =>
    match c.vars.dedup with
    | [x] => s.insert x
    | _ => s

/-- `denseSvSet` corresponds to the spec `svSet` fold under `resolve`. -/
theorem denseSvSet_fold_corr (reg : VarRegistry) :
    ∀ (dcs : List (DenseExpr p)), (∀ c ∈ dcs, c.CoveredBy reg) →
      ∀ (sd : Std.HashSet VarId) (ss : Std.HashSet Variable),
        (∀ i, reg.Valid i → sd.contains i = ss.contains (reg.resolve i)) →
        ∀ i, reg.Valid i →
          (dcs.foldl (fun s c => match c.vars.dedup with | [x] => s.insert x | _ => s) sd).contains i
            = ((dcs.map reg.decodeExpr).foldl
                (fun s c => match c.vars.dedup with | [x] => s.insert x | _ => s) ss).contains
                (reg.resolve i) := by
  intro dcs
  induction dcs with
  | nil => intro _ sd ss hc i hi; exact hc i hi
  | cons c rest ih =>
      intro hcov sd ss hc i hi
      have hcc : c.CoveredBy reg := hcov c (List.mem_cons_self ..)
      have hcr : ∀ c' ∈ rest, c'.CoveredBy reg := fun c' h => hcov c' (List.mem_cons_of_mem _ h)
      have hvd : (reg.decodeExpr c).vars.dedup = (c.vars.dedup).map reg.resolve := by
        rw [reg.decodeExpr_vars c, reg.map_dedup_resolve c.vars hcc]
      simp only [List.map_cons, List.foldl_cons]
      rw [hvd]
      cases hcd : c.vars.dedup with
      | nil => exact ih hcr sd ss hc i hi
      | cons a t =>
          cases t with
          | nil =>
              have hav : reg.Valid a := hcc a (List.mem_dedup.1 (hcd ▸ List.mem_cons_self ..))
              refine ih hcr (sd.insert a) (ss.insert (reg.resolve a)) (fun k hk => ?_) i hi
              rw [Std.HashSet.contains_insert, Std.HashSet.contains_insert, hc k hk, beq_resolve reg hk hav]
          | cons b t' => exact ih hcr sd ss hc i hi

theorem denseSvSet_corr (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (i : VarId) (hi : reg.Valid i) :
    (denseSvSet d).contains i
      = ((d.algebraicConstraints.map reg.decodeExpr).foldl
          (fun (s : Std.HashSet Variable) (c : Expression p) => match c.vars.dedup with | [x] => s.insert x | _ => s) ∅).contains (reg.resolve i) := by
  exact denseSvSet_fold_corr reg d.algebraicConstraints hcov.1 ∅ ∅ (fun k _ => by simp) i hi

/-- The dense target list (mirrors the spec pass's inline `targets`), sorting by the resolved
    `Variable` order so it decodes to the spec target list. -/
def denseTargets (reg : VarRegistry) (d : DenseConstraintSystem p) : List (List VarId) :=
  dedupHash (d.algebraicConstraints.filterMap (fun c =>
    let vs := c.vars.dedup
    if 2 ≤ vs.length && vs.length ≤ 8 && vs.all ((denseSvSet d).contains ·) then
      some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
    else none))

/-- **`denseTargets` decodes to the spec pass's `targets`.** -/
theorem denseTargets_corr (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseTargets reg d).map (fun xs => xs.map reg.resolve)
      = dedupHash ((reg.decodeCS d).algebraicConstraints.filterMap (fun c =>
          let vs := c.vars.dedup
          if 2 ≤ vs.length && vs.length ≤ 8 && vs.all
              (((d.algebraicConstraints.map reg.decodeExpr).foldl
                (fun (s : Std.HashSet Variable) (c : Expression p) => match c.vars.dedup with | [x] => s.insert x | _ => s) ∅).contains ·) then
            some (vs.mergeSort (fun a b => compare a b != .gt))
          else none)) := by
  -- entries of the pre-dedup dense list are valid-id lists (sorted vars of covered constraints)
  have hpreValid : ∀ xs ∈ d.algebraicConstraints.filterMap (fun c =>
        let vs := c.vars.dedup
        if 2 ≤ vs.length && vs.length ≤ 8 && vs.all ((denseSvSet d).contains ·) then
          some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
        else none), ∀ x ∈ xs, reg.Valid x := by
    intro xs hxs x hx
    rw [List.mem_filterMap] at hxs
    obtain ⟨c, hc, hcg⟩ := hxs
    by_cases hcond : 2 ≤ (c.vars.dedup).length && (c.vars.dedup).length ≤ 8
        && (c.vars.dedup).all ((denseSvSet d).contains ·)
    · rw [if_pos hcond] at hcg
      obtain rfl := Option.some.inj hcg
      have : x ∈ c.vars.dedup := (List.mem_mergeSort).1 hx
      exact hcov.1 c hc x (List.mem_dedup.1 this)
    · rw [if_neg (by simpa using hcond)] at hcg; exact absurd hcg (by simp)
  unfold denseTargets
  rw [dedupHash_map_resolve reg _ hpreValid]
  congr 1
  -- the filterMap correspondence
  rw [show (reg.decodeCS d).algebraicConstraints = d.algebraicConstraints.map reg.decodeExpr from rfl,
    List.filterMap_map]
  rw [List.map_filterMap]
  refine List.filterMap_congr (fun c hc => ?_)
  have hcc : c.CoveredBy reg := hcov.1 c hc
  have hvd : (reg.decodeExpr c).vars.dedup = (c.vars.dedup).map reg.resolve := by
    rw [reg.decodeExpr_vars c, reg.map_dedup_resolve c.vars hcc]
  have hdedupv : ∀ x ∈ c.vars.dedup, reg.Valid x := fun x hx => hcc x (List.mem_dedup.1 hx)
  simp only [Function.comp_apply]
  -- condition correspondence
  have hcond : (2 ≤ (c.vars.dedup).length && (c.vars.dedup).length ≤ 8
        && (c.vars.dedup).all ((denseSvSet d).contains ·))
      = (2 ≤ (reg.decodeExpr c).vars.dedup.length && (reg.decodeExpr c).vars.dedup.length ≤ 8
        && (reg.decodeExpr c).vars.dedup.all
            (((d.algebraicConstraints.map reg.decodeExpr).foldl
              (fun (s : Std.HashSet Variable) (c : Expression p) => match c.vars.dedup with | [x] => s.insert x | _ => s) ∅).contains ·)) := by
    rw [hvd, List.length_map, List.all_map]
    congr 1
    refine list_all_congr (fun x hx => ?_)
    have hxv : reg.Valid x := hdedupv x hx
    simp only [Function.comp_apply, denseSvSet_corr reg d hcov x hxv]
  rw [hcond]
  by_cases hs : (2 ≤ (reg.decodeExpr c).vars.dedup.length && (reg.decodeExpr c).vars.dedup.length ≤ 8
      && (reg.decodeExpr c).vars.dedup.all
          (((d.algebraicConstraints.map reg.decodeExpr).foldl
            (fun (s : Std.HashSet Variable) (c : Expression p) => match c.vars.dedup with | [x] => s.insert x | _ => s) ∅).contains ·)) = true
  · rw [if_pos hs, if_pos hs, Option.map_some, hvd]
    congr 1
    exact List.map_mergeSort (fun a _ b _ => rfl)
  · rw [if_neg hs, if_neg hs, Option.map_none]

theorem foldStep_fst_derivs [Fact p.Prime] (bs : BusSemantics p) (cs : ConstraintSystem p)
    (fidx : FoldIdx cs) (xs : List Variable) : (foldStep bs cs fidx xs).1.derivs = [] := by
  unfold foldStep
  simp only []
  split
  · rfl
  · rename_i doms _
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hg : (1 ≤ (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms).length
          && systemHasFoldableIdx fidx xs
              (groupSurvivorsE (CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs) doms)) = true
      · rw [if_pos hg]
      · rw [if_neg hg]
    · rw [if_neg hp]

theorem foldLoop_derivs [Fact p.Prime] (bs : BusSemantics p) :
    ∀ (targets : List (List Variable)) (cs : ConstraintSystem p) (fidx : FoldIdx cs),
      (foldLoop bs targets cs fidx).derivs = [] := by
  intro targets
  induction targets with
  | nil => intro cs fidx; rfl
  | cons xs rest ih =>
      intro cs fidx
      show ((foldStep bs cs fidx xs).1.derivs
        ++ (foldLoop bs rest (foldStep bs cs fidx xs).1.out (foldStep bs cs fidx xs).2).derivs) = []
      simp only [foldStep_fst_derivs, ih, List.nil_append]

theorem denseFoldLoopDirect_covered (reg : VarRegistry) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p), d.CoveredBy reg →
      (denseFoldLoopDirect targets d).CoveredBy reg := by
  intro targets
  induction targets with
  | nil => intro d hcov; exact hcov
  | cons xs rest ih =>
      intro d hcov
      exact ih _ (denseFoldStepWith_covered reg d hcov xs (denseCoveredCsOf d xs))

theorem denseFoldLoop_covered (reg : VarRegistry) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p),
      d.CoveredBy reg → (denseFoldLoop targets d fidx).CoveredBy reg := by
  intro targets
  induction targets with
  | nil => intro d fidx hcov; exact hcov
  | cons xs rest ih =>
      intro d fidx hcov
      exact ih _ _ (denseFoldStep_covered reg d hcov fidx xs)

/-- `dedupHash`'s fold only ever prepends processed elements. -/
theorem mem_dedupHash_foldl {α : Type} [BEq α] [Hashable α] :
    ∀ (m : List α) (ld : List α) (sd : Std.HashSet α) (x : α),
      x ∈ (m.foldl (fun st t => if st.2.contains t then st else (t :: st.1, st.2.insert t)) (ld, sd)).1 →
      x ∈ ld ∨ x ∈ m := by
  intro m
  induction m with
  | nil => intro ld sd x h; exact Or.inl h
  | cons t rest ih =>
      intro ld sd x h
      simp only [List.foldl_cons] at h
      by_cases hc : sd.contains t = true
      · rw [if_pos hc] at h
        rcases ih ld sd x h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rw [if_neg hc] at h
        rcases ih (t :: ld) (sd.insert t) x h with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- `dedupHash` keeps a subset. -/
theorem mem_dedupHash {α : Type} [BEq α] [Hashable α] (l : List α) (x : α) (h : x ∈ dedupHash l) :
    x ∈ l := by
  unfold dedupHash at h
  rcases mem_dedupHash_foldl l.reverse [] ∅ x h with h | h
  · simp at h
  · exact List.mem_reverse.1 h

/-- Every id in a dense target is valid. -/
theorem denseTargets_valid (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    ∀ xs ∈ denseTargets reg d, ∀ x ∈ xs, reg.Valid x := by
  intro xs hxs x hx
  have hxs' := mem_dedupHash _ xs hxs
  rw [List.mem_filterMap] at hxs'
  obtain ⟨c, hc, hcg⟩ := hxs'
  by_cases hcond : 2 ≤ (c.vars.dedup).length && (c.vars.dedup).length ≤ 8
      && (c.vars.dedup).all ((denseSvSet d).contains ·)
  · rw [if_pos hcond] at hcg
    obtain rfl := Option.some.inj hcg
    exact hcov.1 c hc x (List.mem_dedup.1 ((List.mem_mergeSort).1 hx))
  · rw [if_neg (by simpa using hcond)] at hcg; exact absurd hcg (by simp)

/-! ## The dense pass -/

/-- The dense domain-fold transform (mirrors `domainFoldPass`; direct build with `reg`). -/
def denseDomainFoldF (pw : PrimeWitness p) (reg : VarRegistry) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if pw.isPrime = true then
    if domainFoldIndexThreshold ≤ d.algebraicConstraints.length then
      denseFoldLoop (denseTargets reg d) d (DenseFoldIdx.mk' d)
    else denseFoldLoopDirect (denseTargets reg d) d
  else d

theorem denseDomainFoldF_covered (reg : VarRegistry) (pw : PrimeWitness p)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseDomainFoldF pw reg d).CoveredBy reg := by
  unfold denseDomainFoldF
  by_cases hpB : pw.isPrime = true
  · rw [if_pos hpB]
    by_cases hth : domainFoldIndexThreshold ≤ d.algebraicConstraints.length
    · rw [if_pos hth]; exact denseFoldLoop_covered reg _ d _ hcov
    · rw [if_neg hth]; exact denseFoldLoopDirect_covered reg _ d hcov
  · rw [if_neg hpB]; exact hcov
