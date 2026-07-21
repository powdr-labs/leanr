import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.Rewrite

set_option autoImplicit false

/-! # Dense finite-domain-table construction (Task 3 — DomainBatch, part 1)

Dense, `VarId`-native port of the domain-derivation layer of
`OptimizerPasses/DomainBatch.lean`: the table of finite domains derived from product-of-affine-factor
constraints (`rootsIn`) and from fact-bounded bus payload slots (`interactionDomainF`).

`FiniteDomain p` is variable-free, so it is reused verbatim (values are *equal*, not decoded). The
runtime dense table is a plain `Std.HashMap VarId (FiniteDomain p)` (no soundness field); its
correctness flows through the correspondence proved here: the dense table decodes, value-for-value
under `resolve`, to the spec `DomainTable`'s `map` on the decoded system. The fact-consuming
`interactionDomainF` reuses the *unchanged* `facts : BusFacts p bs` (keyed by bus IDs + field
patterns, VM-neutral) via `denseInteractionBound` from `Dense/DigitFold.lean` — the DigitFold
fact-layer template.

Only the domain-derivation layer is ported here; the joint enumeration (`collectForced`/`forcedOver`/
`compileE`/`scanBox`) and the pass itself are later chunks. Nothing is wired into the pipeline. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense `rootsIn`

`rootsIn` returns a variable-free `List (ZMod p)`, so the dense mirror produces the *same* value; the
correspondence is `rootsIn (resolve i) (decodeExpr e) = denseRootsIn i e`. The only variable
comparison is `y = x` in the single-term case, decided identically by `resolve`-injectivity on valid
ids. -/

/-- Dense `rootsOfTerms` (mirrors `rootsOfTerms`). -/
def denseRootsOfTerms (i : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → Option (List (ZMod p))
  | [] => if c = 0 then none else some []
  | [(j, a)] =>
      let r := -(a⁻¹ * c)
      if j = i ∧ a ≠ 0 ∧ a * r + c = 0 then some [r] else none
  | _ :: _ :: _ => none

/-- Dense `affineRootsIn` (mirrors `affineRootsIn`), through `denseLinearize` + `DenseLinExpr.norm`. -/
def denseAffineRootsIn (i : VarId) (e : DenseExpr p) : Option (List (ZMod p)) :=
  (denseLinearize e).bind (fun l => denseRootsOfTerms i l.norm.const l.norm.terms)

/-- Dense `rootsIn` (mirrors `rootsIn`): affine roots, recursing into a product's factors. -/
def denseRootsIn (i : VarId) : DenseExpr p → Option (List (ZMod p))
  | .const n => denseAffineRootsIn i (.const n)
  | .var j => denseAffineRootsIn i (.var j)
  | .add a b => denseAffineRootsIn i (.add a b)
  | .mul a b =>
    match denseAffineRootsIn i (.mul a b) with
    | some r => some r
    | none =>
      match denseRootsIn i a, denseRootsIn i b with
      | some ra, some rb => some (ra ++ rb)
      | _, _ => none

/-! ## The dense domain table

A plain runtime structure wrapping `Std.HashMap VarId (FiniteDomain p)`; correctness comes from the
correspondence, not a carried invariant. -/

/-- Finite domains for `VarId`s (runtime-only; no soundness field). -/
structure DenseDomainTable (p : ℕ) where
  map : Std.HashMap VarId (FiniteDomain p)

/-- The empty dense domain table. -/
def DenseDomainTable.empty : DenseDomainTable p := ⟨∅⟩

/-- Insert an entailed domain, keeping the smaller of two candidate domains (mirrors
    `DomainTable.insertEntry`'s keep-smaller data logic). -/
def DenseDomainTable.insertEntry (T : DenseDomainTable p) (i : VarId) (d : FiniteDomain p) :
    DenseDomainTable p :=
  let keep : Bool := match T.map[i]? with
    | some d0 => decide (d.size < d0.size)
    | none => true
  if keep then ⟨T.map.insert i d⟩ else T

/-- The table's domains for a `VarId` list, all-or-nothing (mirrors `DomainTable.doms`). -/
def DenseDomainTable.doms (T : DenseDomainTable p) :
    List VarId → Option (List (VarId × FiniteDomain p))
  | [] => some []
  | i :: is =>
    match T.map[i]?, T.doms is with
    | some d, some rest => some ((i, d) :: rest)
    | _, _ => none

/-! ## `.map`-extraction helpers and the insert correspondence -/

/-- The `.map` field of the dense `insertEntry`. -/
theorem DenseDomainTable.insertEntry_map (T : DenseDomainTable p) (i : VarId) (d : FiniteDomain p) :
    (T.insertEntry i d).map
      = (if (match T.map[i]? with | some d0 => decide (d.size < d0.size) | none => (true : Bool))
             = true
         then T.map.insert i d else T.map) := by
  unfold DenseDomainTable.insertEntry
  rw [apply_ite DenseDomainTable.map]

/-! ## Constraint-sourced domains -/

/-- Dense inner `addVars` for constraints (mirrors `addConstraintDoms.addVars`). -/
def denseAddConstraintVars (c : DenseExpr p) :
    List VarId → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | i :: is, T =>
    match denseRootsIn i c with
    | some d => denseAddConstraintVars c is (T.insertEntry i (.explicit d))
    | none => denseAddConstraintVars c is T

/-- Dense constraint-sourced domains (mirrors `addConstraintDoms`). -/
def denseAddConstraintDoms : List (DenseExpr p) → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | c :: rest, T =>
    let vs := c.vars.dedup
    denseAddConstraintDoms rest (if vs.length ≤ 3 then denseAddConstraintVars c vs T else T)

/-! ## Bus-sourced range domains -/

/-- The raw-variable payload entries of a dense interaction (mirrors `payloadRawVars`). -/
def densePayloadRawVars (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.payload.filterMap (fun e => match e with | .var i => some i | _ => none)

/-- A bus obligation's range domain for `i`, kept symbolically (mirrors `interactionDomainF`), using
    the DigitFold fact-layer `denseInteractionBound` on the unchanged `facts`. -/
def denseInteractionDomainF (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) : Option (FiniteDomain p) :=
  match denseInteractionBound bs facts bi i with
  | none => none
  | some bound => if bound ≤ maxDomainBound then some (.range bound) else none

/-- Dense inner `addVars` for bus obligations (mirrors `addBusDoms.addVars`). -/
def denseAddBusVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    List VarId → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | i :: is, T =>
    match denseInteractionDomainF bs facts bi i with
    | some d => denseAddBusVars bs facts bi is (T.insertEntry i d)
    | none => denseAddBusVars bs facts bi is T

/-- Dense bus-sourced domains (mirrors `addBusDoms`). -/
def denseAddBusDoms (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | bi :: rest, T =>
    denseAddBusDoms bs facts rest (denseAddBusVars bs facts bi (densePayloadRawVars bi).dedup T)

/-! ## Dense enumeration engine (Task 3 — DomainBatch, part 2)

The joint box-scan enumeration, re-instantiated over `VarId` keys / `List (VarId × ZMod p)` points.
The compiled predicates (`IExpr`/`CBi`) and the symbolic `FiniteDomain` enumeration are
*variable-free* and reused verbatim from the spec; only the *key type* of the enumerated points and
the environment/compile leaves change. Every dense def here is ID-native (no `Variable` materialized
on the scan's hot path). Its correspondence to the spec engine — the survivor point's *values* agree
and its *keys map by `resolve`* — is proved for chunk 3's `forcedOver` to consume.

Throughout, a dense point `pt : List (VarId × ZMod p)` decodes to the spec point
`pt.map (fun kv => (reg.resolve kv.1, kv.2))` (keys resolved, values unchanged). -/

/-- Enumeration-time `VarId` lookup, mirroring `envOfFast`; compares `VarId`s directly. -/
def denseEnvOfFast : List (VarId × ZMod p) → VarId → ZMod p
  | [], _ => 0
  | (x, v) :: rest, y => if (y == x) = true then v else denseEnvOfFast rest y

/-- `containsFast`, over `VarId`s (the `envOfFast` discriminator trick), for the covered-item scans. -/
def denseContainsFast (xs : List VarId) (y : VarId) : Bool :=
  match xs with
  | [] => false
  | x :: rest => (y == x) || denseContainsFast rest y

/-! ### Index-compiled evaluation over dense points

`IExpr`/`CBi` are variable-free, so the *same* compiled term is produced dense and spec; only its
*evaluation* changes key type. `lookupIx` ignores keys, so the dense evaluators agree with the spec
ones on the decoded point. -/

/-- Positional lookup in a dense assignment (mirrors `lookupIx`; ignores keys). -/
def denseLookupIx : List (VarId × ZMod p) → Nat → ZMod p
  | [], _ => 0
  | (_, v) :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIx rest i

/-- `IExpr.evalWith` over a dense point (mirrors `IExpr.evalWith`; positional). -/
def denseIExprEvalWith (add mul : ZMod p → ZMod p → ZMod p) (pt : List (VarId × ZMod p)) :
    IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIx pt i
  | .add a b => add (denseIExprEvalWith add mul pt a) (denseIExprEvalWith add mul pt b)
  | .mul a b => mul (denseIExprEvalWith add mul pt a) (denseIExprEvalWith add mul pt b)

/-- `CBi.evalWith` over a dense point (mirrors `CBi.evalWith`). -/
def denseCBiEvalWith (add mul : ZMod p → ZMod p → ZMod p) (cbi : CBi p)
    (pt : List (VarId × ZMod p)) : BusInteraction (ZMod p) :=
  { busId := cbi.busId,
    multiplicity := denseIExprEvalWith add mul pt cbi.mult,
    payload := cbi.payload.map (fun ie => denseIExprEvalWith add mul pt ie) }

/-- `survivesAllCW` over a dense point (mirrors `survivesAllCW`). -/
def denseSurvivesAllCW (add mul : ZMod p → ZMod p → ZMod p) (isZero : ZMod p → Bool)
    (bs : BusSemantics p) (ces : List (IExpr p)) (cbis : List (CBi p))
    (pt : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWith add mul pt ie)) &&
    cbis.all (fun cbi =>
      let v := denseCBiEvalWith add mul cbi pt
      isZero v.multiplicity || !bs.violatesConstraint v)

/-! ### Compiling dense items to `IExpr`/`CBi`

The compiled term is *identical* to the spec's on the decoded item, provided the keys are valid: the
only variable-typed step is `denseVarIx`, which finds the same position as `varIx` on the resolved
keys by `resolve`-injectivity. -/

/-- First position of `y` in dense `keys` (mirrors `varIx`). -/
def denseVarIx (keys : List VarId) (y : VarId) : Option Nat :=
  match keys with
  | [] => none
  | x :: rest => if (y == x) = true then some 0 else (denseVarIx rest y).map (· + 1)

/-- Compile a dense expression against dense `keys` (mirrors `compileE`). -/
def denseCompileE (keys : List VarId) : DenseExpr p → Option (IExpr p)
  | .const n => some (.const n)
  | .var y => (denseVarIx keys y).map .ix
  | .add a b =>
    match denseCompileE keys a, denseCompileE keys b with
    | some ia, some ib => some (.add ia ib)
    | _, _ => none
  | .mul a b =>
    match denseCompileE keys a, denseCompileE keys b with
    | some ia, some ib => some (.mul ia ib)
    | _, _ => none

/-- Compile a list of dense expressions, all-or-nothing (mirrors `compileEs`). -/
def denseCompileEs (keys : List VarId) : List (DenseExpr p) → Option (List (IExpr p))
  | [] => some []
  | e :: rest =>
    match denseCompileE keys e, denseCompileEs keys rest with
    | some ie, some irest => some (ie :: irest)
    | _, _ => none

/-- Compile a dense bus interaction (mirrors `compileBi`). -/
def denseCompileBi (keys : List VarId) (bi : BusInteraction (DenseExpr p)) : Option (CBi p) :=
  match denseCompileE keys bi.multiplicity, denseCompileEs keys bi.payload with
  | some m, some pl => some ⟨bi.busId, m, pl⟩
  | _, _ => none

/-- Compile a list of dense interactions, all-or-nothing (mirrors `compileBis`). -/
def denseCompileBis (keys : List VarId) : List (BusInteraction (DenseExpr p)) →
    Option (List (CBi p))
  | [] => some []
  | bi :: rest =>
    match denseCompileBi keys bi, denseCompileBis keys rest with
    | some cbi, some crest => some (cbi :: crest)
    | _, _ => none

/-! ### `DenseExpr.eval` congruence

`DenseExpr.eval` depends only on the values of the variables that occur — reused by the value-only
enumeration engine (`DomainBatchRuntime`) and its correspondence proofs. -/

/-- `DenseExpr.eval` depends only on the values of the variables that occur. -/
theorem DenseExpr.eval_congr (e : DenseExpr p) (f g : VarId → ZMod p)
    (h : ∀ i ∈ e.vars, f i = g i) : e.eval f = e.eval g := by
  induction e with
  | const n => rfl
  | var i => exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at h
      simp only [DenseExpr.eval, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]
  | mul a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at h
      simp only [DenseExpr.eval, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]

/-! ## Dense `varsInF` (Task 3 — DomainBatch, part 3)

The covered-set predicates that `forcedOver` filters items by. Their only variable comparisons go
through `denseContainsFast`, so a decoded item's `varsInF` on the resolved target set agrees with the
dense item's `varsInF` on the dense target set. -/

/-- `Expression.varsInF`, over `VarId`s (mirrors `Expression.varsInF`). -/
def DenseExpr.varsInF (xs : List VarId) : DenseExpr p → Bool
  | .const _ => true
  | .var y => denseContainsFast xs y
  | .add a b => a.varsInF xs && b.varsInF xs
  | .mul a b => a.varsInF xs && b.varsInF xs

/-- `BusInteraction.varsInF`, over `VarId`s (mirrors `BusInteraction.varsInF`). -/
def denseBIVarsInF (xs : List VarId) (bi : BusInteraction (DenseExpr p)) : Bool :=
  bi.multiplicity.varsInF xs && bi.payload.all (fun e => e.varsInF xs)

/-! ## Dense `biInformative` (mirrors `biInformative`)

The informativeness gate on a covered obligation, through `DenseExpr.isVar`/`.constValue?` (both
decode-invariant, unconditionally) and the DigitFold fact-layer `denseInteractionBound`. -/

/-- Dense `biInformative` (mirrors `biInformative`). -/
def denseBiInformative (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  bi.payload.any (fun e => !(e.isVar || e.constValue?.isSome)) ||
  bi.payload.any (fun e => match e with
    | .var i => (denseInteractionBound bs facts bi i).isNone
    | _ => false)

/-! ## Dense inverted index (mirrors `CoveredIndex`)

The `VarId`-keyed inverted index `forcedOver` uses to find covered items in O(local). Its correctness
flows through the correspondence proved here: the dense candidate list (buckets under a target's
variables, plus the variable-less positions) is the *same* `List Nat` as the spec's on the resolved
target, so the dedup `HashSet` and its `toList` are identical, and the per-position `Q` re-check maps
decode-for-decode. Bucket/varless correspondence is the DigitFold/Gauss "HashMap-fold-under-`resolve`"
pattern over the `build` fold. -/

/-- The dense inverted index (mirrors `CoveredIndex.CovIndex`). -/
structure DenseCovIndex where
  buckets : Std.HashMap VarId (List Nat)
  varless : List Nat

/-- One dense index-build step (mirrors `CoveredIndex.buildStep`). -/
def denseBuildStep {α : Type} (varsOf : α → List VarId) (ai : α × Nat) (idx : DenseCovIndex) :
    DenseCovIndex :=
  match varsOf ai.1 with
  | [] => ⟨idx.buckets, ai.2 :: idx.varless⟩
  | vs => ⟨vs.foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets, idx.varless⟩

/-- Build the dense inverted index (mirrors `CoveredIndex.build`). -/
def denseCovBuild {α : Type} (varsOf : α → List VarId) (items : List α) : DenseCovIndex :=
  items.zipIdx.foldr (denseBuildStep varsOf) ⟨∅, []⟩

/-- The dense candidate positions for target `xs` (mirrors `CoveredIndex.candidates`). -/
def denseCandidates (idx : DenseCovIndex) (xs : List VarId) : List Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])) ++ idx.varless

/-- The dense covered items for target `xs`, unordered (mirrors `CoveredIndex.coveredIdxUnord`). -/
def denseCoveredIdxUnord {α : Type} (idx : DenseCovIndex) (arr : Array α) (Q : α → Bool)
    (xs : List VarId) : List α :=
  (((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).filterMap
    (fun i => if h : i < arr.size then (if Q arr[i] then some arr[i] else none) else none)

/-! ### `buildStep` projection helpers (dense + spec varless) -/

theorem denseBuildStep_buckets_nil {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (h : varsOf ai.1 = []) : (denseBuildStep varsOf ai idx).buckets = idx.buckets := by
  simp only [denseBuildStep, h]

theorem denseBuildStep_buckets_cons {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (w0 : VarId) (ws : List VarId) (h : varsOf ai.1 = w0 :: ws) :
    (denseBuildStep varsOf ai idx).buckets
      = (w0 :: ws).foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets := by
  simp only [denseBuildStep, h]

theorem denseBuildStep_varless_nil {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (h : varsOf ai.1 = []) :
    (denseBuildStep varsOf ai idx).varless = ai.2 :: idx.varless := by
  simp only [denseBuildStep, h]

theorem denseBuildStep_varless_cons {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (w0 : VarId) (ws : List VarId) (h : varsOf ai.1 = w0 :: ws) :
    (denseBuildStep varsOf ai idx).varless = idx.varless := by
  simp only [denseBuildStep, h]

theorem specBuildStep_varless_nil {α : Type} (varsOf : α → List Variable) (ai : α × Nat)
    (idx : CoveredIndex.CovIndex) (h : varsOf ai.1 = []) :
    (CoveredIndex.buildStep varsOf ai idx).varless = ai.2 :: idx.varless := by
  simp only [CoveredIndex.buildStep, h]

theorem specBuildStep_varless_cons {α : Type} (varsOf : α → List Variable) (ai : α × Nat)
    (idx : CoveredIndex.CovIndex) (w0 : Variable) (ws : List Variable) (h : varsOf ai.1 = w0 :: ws) :
    (CoveredIndex.buildStep varsOf ai idx).varless = idx.varless := by
  simp only [CoveredIndex.buildStep, h]

/-! ### The build correspondence -/

/-- `List.zipIdx` commutes with `List.map` on the elements (positions unchanged). -/
theorem map_zipIdx_dec {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat),
    (l.map f).zipIdx n = (l.zipIdx n).map (fun ai => (f ai.1, ai.2)) := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons a rest ih => intro n; simp only [List.map_cons, List.zipIdx_cons, ih]

/-- Folding the dense bucket-insert over `vs` and the spec bucket-insert over `vs.map resolve`
    preserves the bucket correspondence (`resolve` injective on valid ids). -/
theorem denseBucketFold_corr (reg : VarRegistry) (pos : Nat) :
    ∀ (vs : List VarId), (∀ v ∈ vs, reg.Valid v) →
      ∀ (md : Std.HashMap VarId (List Nat)) (ms : Std.HashMap Variable (List Nat)),
      (∀ i, reg.Valid i → md.getD i [] = ms.getD (reg.resolve i) []) →
      ∀ i, reg.Valid i →
        (vs.foldl (fun m v => m.insert v (pos :: m.getD v [])) md).getD i []
          = ((vs.map reg.resolve).foldl (fun m v => m.insert v (pos :: m.getD v [])) ms).getD (reg.resolve i) [] := by
  intro vs
  induction vs with
  | nil => intro _ md ms hinv i hi; exact hinv i hi
  | cons v rest ih =>
      intro hvv md ms hinv i hi
      have hvvh : reg.Valid v := hvv v (List.mem_cons_self ..)
      have hrv : ∀ v' ∈ rest, reg.Valid v' := fun v' h => hvv v' (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, List.foldl_cons]
      refine ih hrv _ _ ?_ i hi
      intro i' hi'
      rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert]
      by_cases hvi : v = i'
      · subst hvi
        simp only [beq_self_eq_true, if_true]
        rw [hinv v hvvh]
      · have hvi' : ¬ reg.resolve v = reg.resolve i' := fun he => hvi (reg.resolve_inj hvvh hi' he)
        rw [if_neg (by simpa using hvi), if_neg (by simpa using hvi')]
        exact hinv i' hi'

/-- The dense/spec build folds over a shared zipIdx list agree on `varless` (equal lists) and on
    every bucket (equal `List Nat`) under `resolve`. -/
theorem denseBuildStep_fold_corr {α β : Type} (reg : VarRegistry) (dec : α → β)
    (varsOf_d : α → List VarId) (varsOf_s : β → List Variable)
    (hvo : ∀ a, varsOf_s (dec a) = (varsOf_d a).map reg.resolve) :
    ∀ (l : List (α × Nat)), (∀ ai ∈ l, ∀ v ∈ varsOf_d ai.1, reg.Valid v) →
      (l.foldr (denseBuildStep varsOf_d) ⟨∅, []⟩).varless
          = ((l.map (fun ai => (dec ai.1, ai.2))).foldr (CoveredIndex.buildStep varsOf_s) ⟨∅, []⟩).varless
        ∧ (∀ i, reg.Valid i →
            (l.foldr (denseBuildStep varsOf_d) ⟨∅, []⟩).buckets.getD i []
              = ((l.map (fun ai => (dec ai.1, ai.2))).foldr (CoveredIndex.buildStep varsOf_s) ⟨∅, []⟩).buckets.getD (reg.resolve i) []) := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨rfl, fun i _ => by simp only [List.foldr_nil, List.map_nil, Std.HashMap.getD_empty]⟩
  | cons ai0 rest ih =>
      intro hv
      have hvrest : ∀ ai ∈ rest, ∀ v ∈ varsOf_d ai.1, reg.Valid v :=
        fun ai h => hv ai (List.mem_cons_of_mem _ h)
      have hv0 : ∀ v ∈ varsOf_d ai0.1, reg.Valid v := hv ai0 (List.mem_cons_self ..)
      obtain ⟨ihvarless, ihbuckets⟩ := ih hvrest
      have hvo0 : varsOf_s (dec ai0.1) = (varsOf_d ai0.1).map reg.resolve := hvo ai0.1
      simp only [List.foldr_cons, List.map_cons]
      cases hvs : varsOf_d ai0.1 with
      | nil =>
          have hvs' : varsOf_s (dec ai0.1) = [] := by rw [hvo0, hvs]; rfl
          refine ⟨?_, ?_⟩
          · rw [denseBuildStep_varless_nil varsOf_d ai0 _ hvs,
                specBuildStep_varless_nil varsOf_s (dec ai0.1, ai0.2) _ hvs', ihvarless]
          · intro i hi
            rw [denseBuildStep_buckets_nil varsOf_d ai0 _ hvs,
                CoveredIndex.buildStep_buckets_nil varsOf_s (dec ai0.1, ai0.2) _ hvs']
            exact ihbuckets i hi
      | cons w0 ws =>
          have hvs' : varsOf_s (dec ai0.1) = reg.resolve w0 :: ws.map reg.resolve := by
            rw [hvo0, hvs]; rfl
          refine ⟨?_, ?_⟩
          · rw [denseBuildStep_varless_cons varsOf_d ai0 _ w0 ws hvs,
                specBuildStep_varless_cons varsOf_s (dec ai0.1, ai0.2) _ (reg.resolve w0) (ws.map reg.resolve) hvs']
            exact ihvarless
          · intro i hi
            rw [denseBuildStep_buckets_cons varsOf_d ai0 _ w0 ws hvs,
                CoveredIndex.buildStep_buckets_cons varsOf_s (dec ai0.1, ai0.2) _ (reg.resolve w0) (ws.map reg.resolve) hvs']
            exact denseBucketFold_corr reg ai0.2 (w0 :: ws) (by rw [← hvs]; exact hv0) _ _ ihbuckets i hi

/-- **The dense inverted index decodes to `CoveredIndex.build`**: `varless` equal, and every bucket
    equal (as `List Nat`) under `resolve`, given the item vars decode and are valid. -/
theorem denseCovBuild_corr {α β : Type} (reg : VarRegistry) (dec : α → β)
    (varsOf_d : α → List VarId) (varsOf_s : β → List Variable)
    (hvo : ∀ a, varsOf_s (dec a) = (varsOf_d a).map reg.resolve)
    (items_d : List α) (hitems : ∀ a ∈ items_d, ∀ v ∈ varsOf_d a, reg.Valid v) :
    (denseCovBuild varsOf_d items_d).varless = (CoveredIndex.build varsOf_s (items_d.map dec)).varless
      ∧ (∀ i, reg.Valid i → (denseCovBuild varsOf_d items_d).buckets.getD i []
          = (CoveredIndex.build varsOf_s (items_d.map dec)).buckets.getD (reg.resolve i) []) := by
  unfold denseCovBuild CoveredIndex.build
  rw [map_zipIdx_dec dec items_d 0]
  refine denseBuildStep_fold_corr reg dec varsOf_d varsOf_s hvo items_d.zipIdx ?_
  intro ai hai v hv
  have hmem : ai.1 ∈ items_d := by
    have h1 : ai.1 ∈ (items_d.zipIdx).map Prod.fst := List.mem_map.2 ⟨ai, hai, rfl⟩
    rwa [List.zipIdx_map_fst] at h1
  exact hitems ai.1 hmem v hv

/-- The dense candidate list is the *same* `List Nat` as the spec candidate list on the resolved
    target (varless + buckets equal). -/
theorem denseFlatMapGetD (reg : VarRegistry) (idx_d : DenseCovIndex) (idx_s : CoveredIndex.CovIndex)
    (hbuckets : ∀ i, reg.Valid i → idx_d.buckets.getD i [] = idx_s.buckets.getD (reg.resolve i) []) :
    ∀ (xs : List VarId), (∀ x ∈ xs, reg.Valid x) →
      xs.flatMap (fun v => idx_d.buckets.getD v [])
        = (xs.map reg.resolve).flatMap (fun v => idx_s.buckets.getD v []) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x rest ih =>
      intro hxv
      have hxvh : reg.Valid x := hxv x (List.mem_cons_self ..)
      have hrv : ∀ x' ∈ rest, reg.Valid x' := fun x' h => hxv x' (List.mem_cons_of_mem _ h)
      rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, hbuckets x hxvh, ih hrv]

theorem denseCandidates_corr (reg : VarRegistry) (idx_d : DenseCovIndex)
    (idx_s : CoveredIndex.CovIndex) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (hvarless : idx_d.varless = idx_s.varless)
    (hbuckets : ∀ i, reg.Valid i → idx_d.buckets.getD i [] = idx_s.buckets.getD (reg.resolve i) []) :
    denseCandidates idx_d xs = CoveredIndex.candidates idx_s (xs.map reg.resolve) := by
  unfold denseCandidates CoveredIndex.candidates
  rw [hvarless]
  congr 1
  exact denseFlatMapGetD reg idx_d idx_s hbuckets xs hxv

/-- **`denseCoveredIdxUnord` decodes to `CoveredIndex.coveredIdxUnord`.** Given identical candidate
    lists (`hcand`) and a decode-corresponding predicate on the items, the dense covered list maps
    element-for-element to the spec covered list. -/
theorem denseCoveredIdxUnord_corr {α β : Type} (reg : VarRegistry) (dec : α → β)
    (idx_d : DenseCovIndex) (idx_s : CoveredIndex.CovIndex) (items_d : List α)
    (Q_d : α → Bool) (Q_s : β → Bool) (xs : List VarId)
    (hcand : denseCandidates idx_d xs = CoveredIndex.candidates idx_s (xs.map reg.resolve))
    (hQ : ∀ a ∈ items_d, Q_d a = Q_s (dec a)) :
    (denseCoveredIdxUnord idx_d items_d.toArray Q_d xs).map dec
      = CoveredIndex.coveredIdxUnord idx_s (items_d.map dec).toArray Q_s (xs.map reg.resolve) := by
  unfold denseCoveredIdxUnord
  simp only [CoveredIndex.coveredIdxUnord]
  rw [hcand, List.map_filterMap]
  refine CoveredIndex.filterMap_congr' _ (fun i _ => ?_)
  by_cases hlt : i < items_d.length
  · rw [dif_pos (show i < items_d.toArray.size by simpa using hlt),
        dif_pos (show i < (items_d.map dec).toArray.size by
          simp only [List.size_toArray, List.length_map]; exact hlt)]
    simp only [List.getElem_toArray, List.getElem_map]
    have hqeq : Q_s (dec items_d[i]) = Q_d items_d[i] := (hQ items_d[i] (items_d.getElem_mem hlt)).symm
    by_cases hq : Q_d items_d[i] = true
    · rw [if_pos hq, if_pos (hqeq.trans hq), Option.map_some]
    · rw [if_neg hq, if_neg (by rw [hqeq]; exact hq), Option.map_none]
  · rw [dif_neg (by simpa using hlt),
        dif_neg (by simp only [List.size_toArray, List.length_map]; exact hlt), Option.map_none]

/-! ### Dense `ForcedIdx` and its correspondence -/

/-- The dense analog of `ForcedIdx` (plain data — no soundness witnesses; correctness rides on the
    correspondence + inherited `PassCorrect`). -/
structure DenseForcedIdx (p : ℕ) where
  csIdx : DenseCovIndex
  arrCs : Array (DenseExpr p)
  bisIdx : DenseCovIndex
  arrBis : Array (BusInteraction (DenseExpr p))
  activeIdx : DenseCovIndex
  arrActive : Array (DenseExpr p)

/-- The dense domain-table `doms` list has keys `xs` (mirrors `DomainTable.doms_fst`). -/
theorem DenseDomainTable.doms_fst (T : DenseDomainTable p) :
    ∀ (xs : List VarId) (ds : List (VarId × FiniteDomain p)),
      T.doms xs = some ds → ds.map Prod.fst = xs := by
  intro xs
  induction xs with
  | nil => intro ds h; simp only [DenseDomainTable.doms, Option.some.injEq] at h; subst h; rfl
  | cons x rest ih =>
      intro ds h
      rw [DenseDomainTable.doms] at h
      cases hd : T.map[x]? with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some d =>
          cases hr : T.doms rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds' =>
              rw [hd, hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp [ih ds' hr]

/-! ### Dense covered-index soundness (membership of an enumerated item is a real covered item) -/

theorem denseCoveredIdxUnord_mem {α : Type} (idx : DenseCovIndex) (arr : Array α) (Q : α → Bool)
    (xs : List VarId) {e : α} (he : e ∈ denseCoveredIdxUnord idx arr Q xs) :
    ∃ i, ∃ _h : i < arr.size, arr[i] = e ∧ Q e = true := by
  rw [denseCoveredIdxUnord, List.mem_filterMap] at he
  obtain ⟨i, _hi, hfe⟩ := he
  by_cases h : i < arr.size
  · rw [dif_pos h] at hfe
    by_cases hq : Q arr[i]
    · rw [if_pos hq] at hfe
      have hei : arr[i] = e := Option.some.inj hfe
      exact ⟨i, h, hei, by rw [← hei]; exact hq⟩
    · rw [if_neg hq] at hfe; exact absurd hfe (by simp)
  · rw [dif_neg h] at hfe; exact absurd hfe (by simp)

theorem denseCoveredIdxUnord_mem_of_eq {α : Type} (idx : DenseCovIndex) (l : List α) (arr : Array α)
    (harr : arr = l.toArray) (Q : α → Bool) (xs : List VarId)
    {e : α} (he : e ∈ denseCoveredIdxUnord idx arr Q xs) : e ∈ l ∧ Q e = true := by
  subst harr
  obtain ⟨i, hi, hei, hq⟩ := denseCoveredIdxUnord_mem idx l.toArray Q xs he
  subst hei
  have hi' : i < l.length := by simpa using hi
  exact ⟨by simp [l.getElem_mem hi'], hq⟩

/-- Canonical dedup key of a dense variable set: the spec `varSetKey` on the resolved variables. -/
def denseVarSetKey (reg : VarRegistry) (xs : List VarId) : String := varSetKey (xs.map reg.resolve)

/-- Apply a dense solution map to a system, unless it is empty (mirrors the spec pass's
    `if σ.map.isEmpty then cs else cs.substF σ.fn`). Kept as a standalone function so the solution
    map is computed exactly once (as the argument). -/
def applyσ (dσ : DenseSolved p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if dσ.map.isEmpty then d else d.substF dσ.fn
