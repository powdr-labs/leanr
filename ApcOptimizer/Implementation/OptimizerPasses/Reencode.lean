import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold

set_option autoImplicit false

/-! # Witness re-encoding — dense expression ops and the build/step/loop/pass layer.

Impl-only: no theorem is stated here. Correctness and the `ofExtending` wiring live in
`Proofs/Reencode.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Override `denv` on the keys of `pairs` (first match wins). -/
def denseEnvExt : List (VarId × ZMod p) → (VarId → ZMod p) → VarId → ZMod p
  | [], denv, y => denv y
  | (x, v) :: rest, denv, y => if y = x then v else denseEnvExt rest denv y

/-- `DenseExpr.eval` with the ring operations passed in. -/
def DenseExpr.evalWith (add mul : ZMod p → ZMod p → ZMod p) (denv : VarId → ZMod p) :
    DenseExpr p → ZMod p
  | .const n => n
  | .var i => denv i
  | .add a b => add (a.evalWith add mul denv) (b.evalWith add mul denv)
  | .mul a b => mul (a.evalWith add mul denv) (b.evalWith add mul denv)

/-- `DenseExpr.eval`, deriving the field operations once per call instead of per node. -/
def DenseExpr.evalFast (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  let addI : Add (ZMod p) := inferInstance
  let mulI : Mul (ZMod p) := inferInstance
  e.evalWith addI.add mulI.mul denv

/-- `b · (b − 1)`. -/
def denseBoolConstraint (b : VarId) : DenseExpr p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

/-- Substitution defined only on the group `xs`, backed by `hm`. -/
def denseGroupSubst (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    VarId → Option (DenseExpr p) :=
  fun y => if denseContainsFast xs y then hm[y]? else none

/-- The `{0,1}` domain box of the fresh bits. -/
def denseBitBox (bits : List VarId) : List (VarId × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-! ## Degree-aware group rewriting -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. -/
def denseIndicatorExpr (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

/-- Interpolate a subexpression over the bit patterns from its precomputed per-pattern values. -/
def denseInterpOfV (patts : List (List (VarId × ZMod p))) (vals : List (ZMod p)) : DenseExpr p :=
  match vals with
  | [] => .const 0
  | v₀ :: _ =>
    if vals.all (fun v => decide (v = v₀)) then .const v₀
    else (patts.zip vals).foldl (fun acc av =>
      .add acc (.mul (denseIndicatorExpr av.1) (.const av.2))) (.const 0)

/-- Take `cand` if its variables lie in the bits and it agrees with the substitution values on
    every pattern; otherwise fall back to the plain substitution `sub`. -/
def denseCandSelect (bits : List VarId) (patts : List (List (VarId × ZMod p)))
    (sub cand : DenseExpr p) (vals : List (ZMod p)) : DenseExpr p :=
  if cand.varsInF bits &&
      (patts.zip vals).all (fun av => decide (cand.evalFast (denseEnvOfFast av.1) = av.2))
  then cand
  else sub

/-- Interpolation candidate with the checked fallback to plain substitution. -/
def denseGroupRewriteCand (bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  let sub := e.substF σfn
  let vals := patts.map (fun aβ => sub.evalFast (denseEnvOfFast aβ))
  denseCandSelect bits patts sub ((denseInterpOfV patts vals).fold) vals

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else. -/
def denseGroupRewrite (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var y =>
      if denseContainsFast xs y then denseGroupRewriteCand bits σfn patts (.var y) else .var y
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.add a b)
      else .add (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.mul a b)
      else .mul (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)

/-! ## Bounded rewrite degree -/

/-- The exact degree when it is at most `limit`, with early exit above the bound. -/
def DenseExpr.degreeWithin (limit : Nat) : DenseExpr p → Option Nat
  | .const _ => some 0
  | .var _ => if 1 ≤ limit then some 1 else none
  | .add a b =>
      match a.degreeWithin limit with
      | none => none
      | some da =>
          match b.degreeWithin limit with
          | none => none
          | some db => some (max da db)
  | .mul a b =>
      match a.degreeWithin limit with
      | none => none
      | some da =>
          match b.degreeWithin limit with
          | none => none
          | some db => if da + db ≤ limit then some (da + db) else none

theorem DenseExpr.degreeWithin_eq (limit : Nat) (e : DenseExpr p) :
    e.degreeWithin limit = if e.degree ≤ limit then some e.degree else none := by
  induction e with
  | const => simp [DenseExpr.degreeWithin, DenseExpr.degree]
  | var => simp [DenseExpr.degreeWithin, DenseExpr.degree]
  | add a b iha ihb =>
      simp only [DenseExpr.degreeWithin, DenseExpr.degree, iha, ihb]
      by_cases ha : a.degree ≤ limit <;> by_cases hb : b.degree ≤ limit <;>
        simp [ha, hb]
  | mul a b iha ihb =>
      simp only [DenseExpr.degreeWithin, DenseExpr.degree, iha, ihb]
      by_cases ha : a.degree ≤ limit <;> by_cases hb : b.degree ≤ limit <;>
        simp [ha, hb] <;> omega

/-- Degree-only twin of `denseGroupRewrite`, without constructing mixed enclosing nodes. -/
def denseGroupRewriteDegreeWithin (limit : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p))) :
    DenseExpr p → Option Nat
  | .const n => (DenseExpr.const n : DenseExpr p).degreeWithin limit
  | .var y =>
      if denseContainsFast xs y then
        (denseGroupRewriteCand bits σfn patts (.var y)).degreeWithin limit
      else (DenseExpr.var y : DenseExpr p).degreeWithin limit
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then
        (denseGroupRewriteCand bits σfn patts (.add a b)).degreeWithin limit
      else
        match denseGroupRewriteDegreeWithin limit xs bits σfn patts a with
        | none => none
        | some da =>
            match denseGroupRewriteDegreeWithin limit xs bits σfn patts b with
            | none => none
            | some db => some (max da db)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then
        (denseGroupRewriteCand bits σfn patts (.mul a b)).degreeWithin limit
      else
        match denseGroupRewriteDegreeWithin limit xs bits σfn patts a with
        | none => none
        | some da =>
            match denseGroupRewriteDegreeWithin limit xs bits σfn patts b with
            | none => none
            | some db => if da + db ≤ limit then some (da + db) else none

theorem denseGroupRewriteDegreeWithin_eq (limit : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (e : DenseExpr p) :
    denseGroupRewriteDegreeWithin limit xs bits σfn patts e =
      (denseGroupRewrite xs bits σfn patts e).degreeWithin limit := by
  induction e with
  | const => rfl
  | var y =>
      simp only [denseGroupRewriteDegreeWithin, denseGroupRewrite]
      split <;> rfl
  | add a b iha ihb =>
      simp only [denseGroupRewriteDegreeWithin, denseGroupRewrite]
      split
      · rfl
      · simp only [DenseExpr.degreeWithin, iha, ihb]
  | mul a b iha ihb =>
      simp only [denseGroupRewriteDegreeWithin, denseGroupRewrite]
      split
      · rfl
      · simp only [DenseExpr.degreeWithin, iha, ihb]

/-- Whether rewriting `e` exceeds `limit`; the final system degree guard remains authoritative. -/
def denseGroupRewriteDegreeOver (limit : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (e : DenseExpr p) : Bool :=
  decide (limit < (denseGroupRewrite xs bits σfn patts e).degree)

def denseGroupRewriteDegreeOverFast (limit : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (e : DenseExpr p) : Bool :=
  (denseGroupRewriteDegreeWithin limit xs bits σfn patts e).isNone

@[csimp] theorem denseGroupRewriteDegreeOver_eq_fast :
    @denseGroupRewriteDegreeOver = @denseGroupRewriteDegreeOverFast := by
  funext p limit xs bits σfn patts e
  simp only [denseGroupRewriteDegreeOver, denseGroupRewriteDegreeOverFast,
    denseGroupRewriteDegreeWithin_eq, DenseExpr.degreeWithin_eq]
  split <;> simp_all

/-! ## The re-encoded system -/

/-- The re-encoded system: substitute the group everywhere, drop the now-covered constraints, and
    add booleanity constraints for the bits. -/
def denseReencodeOut (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))))
        ++ bits.map denseBoolConstraint,
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity :=
        denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))
          bi.multiplicity,
      payload := bi.payload.map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))) }) }

/-! ## The group's surviving values -/

/-- All covered constraints zero at a point (ring ops hoisted out of the per-point eval). -/
def denseSurvZeroCW (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (a : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWith add mul a ie = 0))

/-- The surviving group values: enumerate the group's domains, keep those satisfying the covered
    constraints. -/
def denseGroupSurvivorsE (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    List (List (VarId × ZMod p)) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces =>
    (denseAssignments doms).filter
      (denseSurvZeroCW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul ces)
  | none =>
    (denseAssignments doms).filter
      (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0)))

/-! ## The checked re-encoding certificate -/

/-- All checked side conditions for one re-encoding step. The freshness conjunct is deliberately
    last: it is the only `O(bits × system)` one, so short-circuiting runs it only for groups that
    already passed the cheap checks. -/
def denseCheckReencode (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  match denseGroupDoms (denseCoveredCsOf d xs) xs with
  | none => false
  | some doms =>
    let es := denseCoveredCsOf d xs
    let survs := denseGroupSurvivorsE es doms
    let patts := denseAssignments (denseBitBox bits)
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ survs.length) &&
    decide (bits.length < xs.length) &&
    decide (bits.Nodup) &&
    -- the substituted group variables only mention bits
    xs.all (fun x =>
      ((DenseExpr.var x).substF (denseGroupSubst xs hm)).vars.all (fun v => bits.contains v)) &&
    -- completeness: every surviving group value is hit by some bit pattern
    survs.all (fun s => patts.any (fun aβ =>
      xs.all (fun x =>
        decide (((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)
          = denseEnvOfFast s x)))) &&
    -- soundness: every bit pattern's image satisfies the covered constraints
    patts.all (fun aβ => es.all (fun c =>
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0))) &&
    -- freshness: no bit occurs anywhere in the system
    bits.all (fun b =>
      d.algebraicConstraints.all (fun c => !c.mentions b) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b)))

/-! ## Derived-variable methods for the fresh bits

Each bit is recovered from the group by a decision tree over the bit patterns: at the first
pattern whose interpolation image equals the group's values, output that pattern's bit. -/

/-- The interpolation image of group variable `x` at pattern `aβ` (a field constant). -/
def denseImgVal (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (aβ : List (VarId × ZMod p)) (x : VarId) : ZMod p :=
  ((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`, as nested `ifEqZero`. -/
def denseMatchCM (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) : DenseComputationMethod p :=
  match xs with
  | [] => thenM
  | x :: rest =>
      .ifEqZero (.add (.var x) (.const (-(imgFn x)))) (denseMatchCM rest imgFn thenM elseM) elseM

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit. -/
def denseBitCM (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) : DenseComputationMethod p :=
  match patts with
  | [] => .const 0
  | aβ :: rest =>
      denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b)) (denseBitCM rest xs hm b)

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs. -/
def denseInterpPoly (pz : List (List (VarId × ZMod p) × List (VarId × ZMod p))) (x : VarId) :
    DenseExpr p :=
  pz.foldl (fun acc az => .add acc (.mul (denseIndicatorExpr az.1) (.const (denseEnvOfFast az.2 x))))
    (.const 0)

/-- Does the expression share a variable with `xs`? -/
def DenseExpr.sharesVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.sharesVarIn xs || b.sharesVarIn xs
  | .mul a b => a.sharesVarIn xs || b.sharesVarIn xs

/-! ## The build/step/loop/pass layer -/

/-- One expression root relevant to the re-encoding degree pre-gate. -/
structure DenseReencodeUse (p : ℕ) where
  expr : DenseExpr p
  vars : List VarId
  identity : Bool

structure DenseReencodeUseBuild (p : ℕ) where
  roots : Array (DenseReencodeUse p)
  buckets : Std.HashMap VarId (List Nat)

/-- Per-invocation root postings and reusable candidate-union scratch. -/
structure DenseReencodeUsePlan (p : ℕ) where
  roots : Array (DenseReencodeUse p)
  buckets : Std.HashMap VarId (Array Nat)
  marks : Array Nat
  generation : Nat
  enabled : Bool
  directRejects : Nat

def denseReencodeEmptyUsePlan : DenseReencodeUsePlan p :=
  ⟨#[], ∅, #[], 0, false, 0⟩

def denseReencodeAddUse (st : DenseReencodeUseBuild p) (e : DenseExpr p)
    (vs : List VarId) (identity : Bool) : DenseReencodeUseBuild p :=
  let i := st.roots.size
  { roots := st.roots.push ⟨e, vs, identity⟩
    buckets := vs.foldl (fun m v => m.insert v (i :: m.getD v [])) st.buckets }

def denseReencodeFreezeUseBuckets (buckets : Std.HashMap VarId (List Nat)) :
    Std.HashMap VarId (Array Nat) :=
  buckets.fold (fun out v positions => out.insert v positions.toArray) ∅

/-- Build all algebraic and bus-expression root postings. Constraint variables reuse `csVs`. -/
def denseBuildReencodeUsePlan (d : DenseConstraintSystem p) (csVs : List (List VarId)) :
    DenseReencodeUsePlan p :=
  let stCs := (d.algebraicConstraints.zip csVs).foldl (init := ⟨#[], ∅⟩)
    fun st cv => denseReencodeAddUse st cv.1 cv.2 true
  let st := d.busInteractions.foldl (init := stCs) fun st bi =>
    let mvs := HashedDedup.hashedDedup (hash ·) bi.multiplicity.vars
    let st := denseReencodeAddUse st bi.multiplicity mvs false
    bi.payload.foldl (init := st) fun st e =>
      denseReencodeAddUse st e (HashedDedup.hashedDedup (hash ·) e.vars) false
  { roots := st.roots
    buckets := denseReencodeFreezeUseBuckets st.buckets
    marks := Array.replicate st.roots.size 0
    generation := 0
    enabled := true
    directRejects := 0 }

/-- Check one use-plan posting after deduplicating it with the generation-stamped scratch array. -/
def denseDegPreRejectUse (b : DegreeBound) (roots : Array (DenseReencodeUse p))
    (xs bits : List VarId) (σ : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (generation pos : Nat)
    (marks : Array Nat) : Bool × Array Nat :=
  if marks[pos]? == some generation then (false, marks)
  else
    let marks := marks.setIfInBounds pos generation
    match roots[pos]? with
    | none => (false, marks)
    | some use =>
        if use.vars.any (denseContainsFast xs) &&
            !(use.identity && denseVarsInListF xs use.vars) then
          let limit := if use.identity then b.identities else b.busInteractions
          (denseGroupRewriteDegreeOver limit xs bits σ patts use.expr, marks)
        else (false, marks)

def denseDegPreRejectPostingGo (b : DegreeBound) (roots : Array (DenseReencodeUse p))
    (xs bits : List VarId) (σ : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (generation : Nat)
    (positions : Array Nat) (marks : Array Nat) (i : Nat) :
    Nat → Bool × Array Nat
  | 0 => (false, marks)
  | fuel + 1 =>
      match positions[i]? with
      | none => (false, marks)
      | some pos =>
          let checked := denseDegPreRejectUse b roots xs bits σ patts generation pos marks
          if checked.1 then checked
          else denseDegPreRejectPostingGo b roots xs bits σ patts generation positions checked.2
            (i + 1) fuel

def denseDegPreRejectBuckets (b : DegreeBound) (roots : Array (DenseReencodeUse p))
    (buckets : Std.HashMap VarId (Array Nat))
    (xs bits : List VarId) (σ : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (generation : Nat) :
    List VarId → Array Nat → Bool × Array Nat
  | [], marks => (false, marks)
  | x :: rest, marks =>
      let positions := buckets.getD x #[]
      let checked := denseDegPreRejectPostingGo b roots xs bits σ patts generation positions marks
        0 positions.size
      if checked.1 then checked
      else denseDegPreRejectBuckets b roots buckets xs bits σ patts generation rest checked.2

/-- Indexed degree pre-gate. Each root is rechecked from its stored exact variable list. -/
def denseDegPreRejectIndexed (b : DegreeBound) (plan : DenseReencodeUsePlan p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    Bool × DenseReencodeUsePlan p :=
  match plan with
  | ⟨roots, buckets, marks, generation₀, enabled, directRejects⟩ =>
      let generation := generation₀ + 1
      let checked := denseDegPreRejectBuckets b roots buckets xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) generation xs marks
      (checked.1, ⟨roots, buckets, checked.2, generation, enabled, directRejects⟩)

/-- Build the inverted index (`VarId`-keyed twin of `CoveredIndex.buildPruned`), skipping items
    with more than `maxVars` distinct variables. -/
def denseBuildPruned {α : Type} (varsOf : α → List VarId) (maxVars : Nat) (items : List α) :
    DenseCovIndex :=
  items.zipIdx.foldr (fun ai idx =>
    if (HashedDedup.hashedEraseDups (hash ·) (varsOf ai.1)).length ≤ maxVars then
      denseBuildStep varsOf ai idx
    else idx) ⟨∅, []⟩

/-- Register the `k` fresh bit variables `freshBase ++ "_0", …, freshBase ++ "_(k-1)"` into `reg`,
    in order. -/
def denseRegisterBits (reg : VarRegistry) (freshBase : String) (k : Nat) :
    VarRegistry × List VarId :=
  (List.range k).foldl
    (fun (acc : VarRegistry × List VarId) (j : Nat) =>
      let (r, bs) := acc
      let (r', i) := r.register ({ name := freshBase ++ "_" ++ toString j } : Variable)
      (r', bs ++ [i]))
    (reg, [])

/-- Construct the bits and the substitution map for a candidate group (proof-free — the checked
    certificate re-verifies everything). Registers fresh bits only on the single accepting path. -/
def denseBuildReencode (reg : VarRegistry) (useIdx : Bool) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (xs : List VarId) (freshBase : String) :
    VarRegistry × Option (List VarId × Std.HashMap VarId (DenseExpr p)) :=
  let es := if useIdx then denseCoveredIdx csIdx arrCs (denseCoveredBy xs) xs
    else arrCs.foldr (fun c acc => if denseCoveredBy xs c then c :: acc else acc) []
  match denseGroupDoms es xs with
  | none => (reg, none)
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ 256 then
      if es.length == xs.length && es.all (fun c => c.vars.eraseDups.length == 1)
          && xs.length ≤ Nat.clog 2 boxSize then
        -- single-var-only covered set (one per variable): survivors = box; unencodable
        (reg, none)
      else
      let survs := denseGroupSurvivorsE es doms
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let (reg1, bits) := denseRegisterBits reg freshBase k
          let patts := denseAssignments (denseBitBox bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          (reg1, some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (denseInterpPoly pz x).fold)))))
        else (reg, none)
      else (reg, none)
    else (reg, none)

/-- Degree pre-gate (untrusted): rewrite only the items sharing a variable with the group and fire
    when a rewritten item already exceeds the bound. -/
def denseDegPreReject (b : DegreeBound) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  let σ := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  d.algebraicConstraints.any (fun c =>
    c.sharesVarIn xs && !denseCoveredBy xs c &&
      decide (b.identities < (denseGroupRewrite xs bits σ patts c).degree)) ||
  d.busInteractions.any (fun bi =>
    (bi.multiplicity.sharesVarIn xs &&
      decide (b.busInteractions < (denseGroupRewrite xs bits σ patts bi.multiplicity).degree)) ||
    bi.payload.any (fun e =>
      e.sharesVarIn xs &&
        decide (b.busInteractions < (denseGroupRewrite xs bits σ patts e).degree)))

/-- One checked re-encoding step (identity if construction or the certificate fails). Applies the
    gates in order, minting fresh bits and rewriting `d` only on full acceptance. -/
def denseReencodeStep (b : DegreeBound) (useIdx : Bool)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (varSet : Std.HashSet VarId)
    (usePlan : DenseReencodeUsePlan p) (xs : List VarId) (freshBase : String) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p × DenseCovIndex ×
      Array (DenseExpr p) × Std.HashSet VarId × DenseReencodeUsePlan p :=
  if xs.all (fun x => reg.isInput x) then
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => varSet.contains i
      | none => false) then
    -- fresh-name collision: `denseCheckReencode` would reject after the full freshness scan anyway
    (reg, d, [], csIdx, arrCs, varSet, usePlan)
  else
  match denseBuildReencode reg useIdx csIdx arrCs xs freshBase with
  | (reg1, none) => (reg1, d, [], csIdx, arrCs, varSet, usePlan)
  | (reg1, some (bits, hm)) =>
    let pre := if usePlan.enabled then denseDegPreRejectIndexed b usePlan xs bits hm
      else (denseDegPreReject b d xs bits hm, usePlan)
    -- Degree pre-gate: reject early what the final `withinDegreeB` gate would reject anyway.
    if pre.1 then
      let nextPlan :=
        if useIdx && !pre.2.enabled then
          let rejects := pre.2.directRejects + 1
          -- Accepted OpenVM rewrites are cheaper direct; amortize setup over repeated rejections.
          if 64 ≤ rejects then
            denseBuildReencodeUsePlan d
              (d.algebraicConstraints.map
                (fun c => HashedDedup.hashedDedup (hash ·) c.vars))
          else { pre.2 with directRejects := rejects }
        else pre.2
      (reg1, d, [], csIdx, arrCs, varSet, nextPlan)
    else
    if xs.all (fun x => varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOut d xs bits hm
      if ro.withinDegreeB b then
        -- `d` changed: rebuild the index and variable set for `ro`.
        let roCsVs :=
          ro.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
        (reg1, ro,
         bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)),
         (if useIdx then denseBuildPruned DenseExpr.vars 8 ro.algebraicConstraints else ⟨∅, []⟩),
         ro.algebraicConstraints.toArray,
         Std.HashSet.ofList ro.occ,
         (if pre.2.enabled then denseBuildReencodeUsePlan ro roCsVs
          else denseReencodeEmptyUsePlan))
      else (reg1, d, [], csIdx, arrCs, varSet, pre.2)
    else (reg1, d, [], csIdx, arrCs, varSet, pre.2)
    else (reg1, d, [], csIdx, arrCs, varSet, pre.2)
    else (reg1, d, [], csIdx, arrCs, varSet, pre.2)
    else (reg1, d, [], csIdx, arrCs, varSet, pre.2)
  else (reg, d, [], csIdx, arrCs, varSet, usePlan)

/-- Process the candidate groups sequentially, threading the registry, index, and variable set. -/
def denseReencodeLoop (b : DegreeBound) (useIdx : Bool) :
    List (List VarId) → Nat → VarRegistry → DenseConstraintSystem p → DenseCovIndex →
      Array (DenseExpr p) → Std.HashSet VarId → DenseReencodeUsePlan p →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p
  | [], _, reg, d, _, _, _, _ => (reg, d, [])
  | xs :: rest, idx, reg, d, csIdx, arrCs, varSet, usePlan =>
    let (reg1, d1, derivs1, csIdx1, arrCs1, varSet1, usePlan1) :=
      denseReencodeStep b useIdx reg d csIdx arrCs varSet usePlan xs
        (s!"rnc{d.algebraicConstraints.length}_{d.busInteractions.length}_{idx}")
    let (reg2, d2, derivs2) :=
      denseReencodeLoop b useIdx rest (idx + 1) reg1 d1 csIdx1 arrCs1 varSet1 usePlan1
    (reg2, d2, derivs1 ++ derivs2)

/-- The allocation-minimal direct step used below the covered-index threshold. -/
def denseReencodeStepDirect (b : DegreeBound)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (arrCs : Array (DenseExpr p))
    (varSet : Std.HashSet VarId) (xs : List VarId) (freshBase : String) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p ×
      Array (DenseExpr p) × Std.HashSet VarId :=
  if xs.all (fun x => reg.isInput x) then
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => varSet.contains i
      | none => false) then
    (reg, d, [], arrCs, varSet)
  else
  match denseBuildReencode reg false ⟨∅, []⟩ arrCs xs freshBase with
  | (reg1, none) => (reg1, d, [], arrCs, varSet)
  | (reg1, some (bits, hm)) =>
    if denseDegPreReject b d xs bits hm then (reg1, d, [], arrCs, varSet)
    else
    if xs.all (fun x => varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun bb => decide ((reg1.resolve bb).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOut d xs bits hm
      if ro.withinDegreeB b then
        (reg1, ro,
         bits.map (fun bb => (bb, denseBitCM (denseAssignments (denseBitBox bits)) xs hm bb)),
         ro.algebraicConstraints.toArray,
         Std.HashSet.ofList ro.occ)
      else (reg1, d, [], arrCs, varSet)
    else (reg1, d, [], arrCs, varSet)
    else (reg1, d, [], arrCs, varSet)
    else (reg1, d, [], arrCs, varSet)
    else (reg1, d, [], arrCs, varSet)
  else (reg, d, [], arrCs, varSet)

def denseReencodeLoopDirect (b : DegreeBound) :
    List (List VarId) → Nat → VarRegistry → DenseConstraintSystem p →
      Array (DenseExpr p) → Std.HashSet VarId →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p
  | [], _, reg, d, _, _ => (reg, d, [])
  | xs :: rest, idx, reg, d, arrCs, varSet =>
    let (reg1, d1, derivs1, arrCs1, varSet1) :=
      denseReencodeStepDirect b reg d arrCs varSet xs
        (s!"rnc{d.algebraicConstraints.length}_{d.busInteractions.length}_{idx}")
    let (reg2, d2, derivs2) :=
      denseReencodeLoopDirect b rest (idx + 1) reg1 d1 arrCs1 varSet1
    (reg2, d2, derivs1 ++ derivs2)

/-- Witness re-encoding. When a group of variables `xs` is so constrained that only a few value
    combinations survive, mint `Nat.clog 2 #survivors` fresh boolean bits, rewrite each group
    variable as an interpolation polynomial over the bits, drop the now-covered constraints, and add
    booleanity constraints — e.g. a group with 3 surviving combinations becomes 2 bits, cutting the
    variable count. The transform is shaped for `DenseVerifiedPassW.ofExtending`; `facts` is unused
    (reencode is fact-free). -/
def denseReencodeF (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bsem : BusSemantics p) (_facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    -- Each constraint's deduped variable list, shared between `svSet` and `targets`.
    let csVs := d.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
    let svSet : Std.HashSet VarId := csVs.foldl (init := ∅) fun s vs =>
      match vs with
      | [x] => s.insert x
      | _ => s
    let targets := dedupHash (csVs.filterMap (fun vs =>
      if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
        -- Sort by the resolved `Variable`'s order: `denseReencodeLoop` below is a greedy,
        -- order-sensitive accept/reject sequence, so the group order determines the outcome.
        some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
      else none))
    let useIdx := 8192 ≤ d.algebraicConstraints.length
    if useIdx then
      denseReencodeLoop b true targets 0 reg d
        (denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints)
        d.algebraicConstraints.toArray
        (Std.HashSet.ofList d.occ)
        denseReencodeEmptyUsePlan
    else
      denseReencodeLoopDirect b targets 0 reg d d.algebraicConstraints.toArray
        (Std.HashSet.ofList d.occ)
  else (reg, d, [])

end ApcOptimizer.Dense
