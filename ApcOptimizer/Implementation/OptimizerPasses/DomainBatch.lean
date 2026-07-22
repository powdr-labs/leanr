import ApcOptimizer.Implementation.OptimizerPasses.EnumEngine
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup
import ApcOptimizer.Implementation.OptimizerPasses.SearchBudgets
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

/-! ### `buildStep` bucket projection helpers -/

theorem denseBuildStep_buckets_nil {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (h : varsOf ai.1 = []) : (denseBuildStep varsOf ai idx).buckets = idx.buckets := by
  simp only [denseBuildStep, h]

theorem denseBuildStep_buckets_cons {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (w0 : VarId) (ws : List VarId) (h : varsOf ai.1 = w0 :: ws) :
    (denseBuildStep varsOf ai idx).buckets
      = (w0 :: ws).foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets := by
  simp only [denseBuildStep, h]

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

/-- Canonical dedup key of a dense variable set: its exact set identity as a sorted, duplicate-free
    `List VarId`. Registry injectivity makes a `VarId` a full variable identity, so `VarId`-set
    equality *is* set equality of the underlying `Variable`s — and, unlike a name-based key, two
    distinct variables with equal `name` but different `powdrId?` never collide. Sorting by the
    underlying index and dropping duplicates makes the list canonical, so the key is invariant under
    the order and multiplicity of `xs` and needs no registry lookup or string building. -/
def denseVarSetKey (xs : List VarId) : List VarId :=
  xs.dedup.mergeSort (fun a b => compare a.index b.index != .gt)

/-! ### Regression guards: the key is an exact `VarId` set (equal-name variables do not collide)

Construct two variables with the same `name` but different `powdrId?`: they are distinct `Variable`
identities, so the injective registry assigns them distinct `VarId`s. A name-based key would collide
them; the exact `VarId`-set key does not. The guards check distinctness, order-independence, and set
(duplicate-collapsing) semantics — with no reference to any legacy name key. -/

private def egRegA : VarRegistry × VarId :=
  VarRegistry.empty.register { name := "x", powdrId? := some 1 }
private def egRegB : VarRegistry × VarId :=
  egRegA.1.register { name := "x", powdrId? := some 2 }
private def egA : VarId := egRegA.2
private def egB : VarId := egRegB.2

-- (a) distinct equal-name variables get distinct singleton keys (a name key would collide them)
#guard denseVarSetKey [egA] != denseVarSetKey [egB]
-- (c) order-independence: the key does not depend on the order of `xs`
#guard denseVarSetKey [egA, egB] == denseVarSetKey [egB, egA]
-- (d) set semantics: duplicate ids collapse
#guard denseVarSetKey [egA, egA, egB] == denseVarSetKey [egA, egB]

/-- Apply a dense solution map to a system, unless it is empty (mirrors the spec pass's
    `if σ.map.isEmpty then cs else cs.substF σ.fn`). Kept as a standalone function so the solution
    map is computed exactly once (as the argument). -/
def applyσ (dσ : DenseSolved p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if dσ.map.isEmpty then d else d.substF dσ.fn
