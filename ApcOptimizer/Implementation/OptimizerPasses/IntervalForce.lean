import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense interval forcing: integer-window analysis of bounded affine slots (Task 3, impl-only)

Dense, `VarId`-native transliteration of `OldVariableBased/IntervalForce.lean`'s *runtime* content:
the signed-representative processed term (`PTerm`/`procTerms`/`maxSum`/`minSum`), the seed walk
(`pairDiff`/`findPartner`/`walk`), the per-slot seed extraction (`slotSeeds`), the per-invocation
bounds index (`BoundIdx`), the per-interaction/whole-system seed collection
(`interactionSeedsGo`/`interactionSeeds`/`allSeeds`), and the pass itself (`intervalForcePass`,
`:625`) — a **single-shot add-seeds** transform (`ConstraintSystem.addConstraints_correct` at
`:625`). This is **impl-only**: `srep_cast`, `procTerms_cast`, `procTerms_bounds`, `term_window`,
`intEval_window`, `int_window`, `intEval_perm`, `walk_sound`, `slotSeeds_sound`,
`interactionSeeds_sound`, `allSeeds_sound`, `BoundIdx.lookup_sound`, and every other theorem in the
spec file are proof-side and left for the prover; nothing here is wired into the `denseImpl`
selector. `intEval` is *not* ported — the runtime (`slotSeeds`/`walk`/`interactionSeeds`/`allSeeds`)
never calls it; it exists only to state the proof-side window lemmas, which the prover owns.

## Representation-independent reuse (per the standing convention)

`IntervalForce.srep : ZMod p → Int` and `IntervalForce.maxTerms : Nat` touch neither `Variable` nor
`Expression` — they are reused **unqualified**, exactly as `open`ed spec constants/helpers are
reused elsewhere (`IntervalForce.srep.eval`, `denseSlotSeeds` below). `PTerm` itself is *not*
reusable as-is: its `v` field is typed `Variable`, so a dense `DensePTerm` (`v : VarId`) is a new
structure, and every function over `List PTerm` (`procTerms`/`maxSum`/`minSum`/`findPartner`/`walk`)
needs a dense twin purely because the *container* type differs — none of these functions'
*bodies* are changed beyond that substitution.

## Reuse of existing dense machinery

* `densePairDiff v w := v − w` is textually identical to `BusUnify.lean`'s `denseEqExpr (.var v)
  (.var w)` — reused directly, no new expression builder.
* `denseLinearize`/`DenseLinExpr` (`Affine.lean`) and `DenseLinExpr.norm` (`Normalize.lean`) are the
  dense `linearize`/`LinExpr`/`LinExpr.norm`.
* `denseInteractionBound` (`DigitFold.lean:118`) is *exactly* the dense `interactionBound`
  (`DomainProp.lean`) `BoundIdx.insertVar` consumes — no re-derivation.
* `DenseExpr.bHash` (`Dedup.lean`) and `HashedDedup.hashedEraseDups` (`HashedDedup.lean`, already
  generic in the hashed element type) are the dense `Expression.bHash`/`HashedDedup.hashedEraseDups`
  `allSeeds` consumes.

## `BoundIdx` → a data-only `Std.HashMap VarId Nat`

The spec `BoundIdx` is a proof-carrying structure indexed by the interaction list `bis`, whose
`sound` field only backs `lookup_sound` (proof-side). Following the established `BoundsMap →
denseBuild` pattern (`DigitFold.lean`), the dense mirror drops the dependent type and the `sound`
field entirely: `denseBoundIdxInsertVar`/`denseBoundIdxAddBi`/`denseBoundIdxAddAll`/
`denseBoundIdxBuild` operate directly on a plain `Std.HashMap VarId Nat`, with the identical
insert-keep-smaller/per-interaction/whole-list recursion structure as `BoundIdx.insertVar`/`.addBi`/
`.addAll`/`.build`. Named with a `BoundIdx`-specific prefix (`denseBoundIdx*`) to avoid colliding
with `DigitFold.lean`'s *different* `BoundsMap`-derived `denseInsertEntry`/`denseAddVars`/
`denseAddAll`/`denseBuild` (a different fact-derived map, same general shape, unrelated pass). -/

namespace ApcOptimizer.Dense

open IntervalForce

variable {p : ℕ}

/-! ## Signed representatives and processed terms -/

/-- A dense processed affine term: signed integer coefficient, a proven strict bound for the
    variable's value, and the `VarId` itself. Mirrors `PTerm` (`OldVariableBased/IntervalForce.lean:62`). -/
structure DensePTerm where
  sc : Int
  bnd : Nat
  v : VarId

/-- Pair every term of a dense linear form with its variable's proven bound; `none` if any variable
    is unbounded. Mirrors `procTerms` (`:69`), reusing `IntervalForce.srep` (representation-
    independent). -/
def denseProcTerms (bnd : VarId → Option Nat) :
    List (VarId × ZMod p) → Option (List DensePTerm)
  | [] => some []
  | (v, c) :: rest =>
    match bnd v, denseProcTerms bnd rest with
    | some B, some pts => some (⟨srep c, B, v⟩ :: pts)
    | _, _ => none

/-- Upper window bound: each term contributes `max (sc·(B−1)) 0`. Mirrors `maxSum` (`:81`). -/
def denseMaxSum (pts : List DensePTerm) : Int :=
  (pts.map (fun t => max (t.sc * ((t.bnd : Int) - 1)) 0)).sum

/-- Lower window bound: each term contributes `min (sc·(B−1)) 0`. Mirrors `minSum` (`:85`). -/
def denseMinSum (pts : List DensePTerm) : Int :=
  (pts.map (fun t => min (t.sc * ((t.bnd : Int) - 1)) 0)).sum

/-! ## Seed extraction -/

/-- `v − w` as a dense expression. Mirrors `pairDiff` (`:203`), reusing `denseEqExpr`
    (`BusUnify.lean`). -/
def densePairDiff (v w : VarId) : DenseExpr p := denseEqExpr (.var v) (.var w)

/-- First term with signed coefficient `g`, and the list without it. Mirrors `findPartner`
    (`:211`). -/
def denseFindPartner (g : Int) : List DensePTerm → Option (DensePTerm × List DensePTerm)
  | [] => none
  | t :: rest =>
    if t.sc = g then some (t, rest)
    else
      match denseFindPartner g rest with
      | some (t', rest') => some (t', t :: rest')
      | none => none

/-- The walk over the term list: at each term, try the zero arm (against all other terms) and,
    for a positive coefficient, the pair arm against the first `−g` partner among the other terms.
    Mirrors `walk` (`:247`). -/
def denseWalk (B : Nat) (c0 : Int) : List DensePTerm → List DensePTerm → List (DenseExpr p)
  | _, [] => []
  | seen, t :: rest =>
    (if (0 < t.sc ∧ (B : Int) ≤ t.sc + (c0 + denseMinSum (seen ++ rest))) ∨
        (t.sc < 0 ∧ c0 + denseMaxSum (seen ++ rest) + t.sc < 0) then
      [DenseExpr.var t.v]
    else []) ++
    (if 0 < t.sc then
      match denseFindPartner (-t.sc) (seen ++ rest) with
      | some (t', others') =>
        if (B : Int) ≤ t.sc + (c0 + denseMinSum others') ∧
           c0 + denseMaxSum others' - t.sc < 0 ∧ t.v ≠ t'.v then
          [densePairDiff t.v t'.v]
        else []
      | none => []
    else []) ++
    denseWalk B c0 (t :: seen) rest

/-! ## Per-slot seeds -/

/-- All seeds forced by one bounded slot: linearize, merge like terms, pair each variable with its
    proven bound, check the integer window, and extract the pair/zero arms. Mirrors `slotSeeds`
    (`:385`), reusing `denseLinearize`/`DenseLinExpr.norm` and `IntervalForce.srep`/`.maxTerms`. -/
def denseSlotSeeds (bnd : VarId → Option Nat) (B : Nat) (e : DenseExpr p) : List (DenseExpr p) :=
  if p = 0 then []
  else
    match denseLinearize e with
    | none => []
    | some l =>
      if l.norm.terms.length ≤ maxTerms then
        match denseProcTerms bnd l.norm.terms with
        | none => []
        | some pts =>
          if srep l.norm.const + denseMaxSum pts ≤ (p : Int) - 1 ∧
             (B : Int) - (p : Int) ≤ srep l.norm.const + denseMinSum pts then
            denseWalk B (srep l.norm.const) [] pts
          else []
      else []

/-! ## The per-invocation bounds index (data-only `Std.HashMap VarId Nat`) -/

/-- Record the bound `denseInteractionBound bi x` (if any), keeping the smaller of duplicates.
    Mirrors `BoundIdx.insertVar` (`:470`), reusing `denseInteractionBound` (`DigitFold.lean:118`). -/
def denseBoundIdxInsertVar (bs : BusSemantics p) (facts : BusFacts p bs)
    (I : Std.HashMap VarId Nat) (bi : BusInteraction (DenseExpr p)) (x : VarId) :
    Std.HashMap VarId Nat :=
  match denseInteractionBound bs facts bi x with
  | none => I
  | some B =>
    if (match I[x]? with
        | some old => decide (B < old)
        | none => true) then
      I.insert x B
    else I

/-- Record every bare-variable slot bound of one interaction. Mirrors `BoundIdx.addBi` (`:493`). -/
def denseBoundIdxAddBi (bs : BusSemantics p) (facts : BusFacts p bs)
    (I : Std.HashMap VarId Nat) (bi : BusInteraction (DenseExpr p)) : Std.HashMap VarId Nat :=
  (bi.payload.filterMap (fun e =>
    match e with
    | .var x => some x
    | _ => none)).foldl (fun I x => denseBoundIdxInsertVar bs facts I bi x) I

/-- Fold `denseBoundIdxAddBi` over every interaction. Mirrors `BoundIdx.addAll` (`:500`). -/
def denseBoundIdxAddAll (bs : BusSemantics p) (facts : BusFacts p bs) :
    Std.HashMap VarId Nat → List (BusInteraction (DenseExpr p)) → Std.HashMap VarId Nat
  | I, [] => I
  | I, bi :: rest => denseBoundIdxAddAll bs facts (denseBoundIdxAddBi bs facts I bi) rest

/-- Build the bounds index from scratch. Mirrors `BoundIdx.build` (`:507`). -/
def denseBoundIdxBuild (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) : Std.HashMap VarId Nat :=
  denseBoundIdxAddAll bs facts ∅ bis

/-! ## The pass -/

/-- The per-slot seed walk of `denseInteractionSeeds`, with the constant-payload pattern `pat`
    computed once by the caller instead of once per slot. Mirrors `interactionSeedsGo` (`:526`). -/
def denseInteractionSeedsGo (bs : BusSemantics p) (facts : BusFacts p bs)
    (bnd : VarId → Option Nat) (bi : BusInteraction (DenseExpr p)) (mval : ZMod p)
    (pat : List (Option (ZMod p))) : List (DenseExpr p) :=
  (List.range bi.payload.length).flatMap (fun i =>
    match bi.payload[i]?, facts.slotBound bi.busId mval pat i with
    | some e, some B => denseSlotSeeds bnd B e
    | _, _ => [])

/-- All seeds of one interaction: every payload slot with a `slotBound`. Mirrors
    `interactionSeeds` (`:535`). -/
def denseInteractionSeeds (bs : BusSemantics p) (facts : BusFacts p bs)
    (bnd : VarId → Option Nat) (bi : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  match bi.multiplicity.constValue? with
  | none => []
  | some mval =>
    if mval = 0 then []
    else denseInteractionSeedsGo bs facts bnd bi mval (bi.payload.map DenseExpr.constValue?)

/-- All seeds over the system: every bounded interaction slot, plus every algebraic constraint
    consumed as a bound-`1` slot. Mirrors `allSeeds` (`:593`), reusing `DenseExpr.bHash`
    (`Dedup.lean`) and `HashedDedup.hashedEraseDups` (`HashedDedup.lean`). -/
def denseAllSeeds (bs : BusSemantics p) (facts : BusFacts p bs) (bnd : VarId → Option Nat)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  HashedDedup.hashedEraseDups DenseExpr.bHash
    (d.busInteractions.flatMap (denseInteractionSeeds bs facts bnd) ++
      d.algebraicConstraints.flatMap (fun c => denseSlotSeeds bnd 1 c))

/-- The dense transform: seed every equality/zero forced by the integer-window analysis of the
    system's bounded affine slots (and its constraints). Mirrors `intervalForcePass` (`:625`), same
    `Std.HashSet`/hash-bucket dedup shortcut noted in the spec's own comment (`d.occ` in place of
    `cs.vars`, `DenseExpr.bHash` in place of `Expression.bHash`). -/
def denseIntervalForceF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let idx := denseBoundIdxBuild bs facts d.busInteractions
  let seeds := denseAllSeeds bs facts (fun v => idx[v]?) d
  -- One hash set / one hash-bucket map instead of per-seed scans of the occurrence list and the
  -- constraint list (both O(system) per seed). Same Bools, so the output is unchanged.
  let varSet : Std.HashSet VarId := Std.HashSet.ofList d.occ
  let csBuckets : Std.HashMap UInt64 (List (DenseExpr p)) :=
    d.algebraicConstraints.foldl (fun m c => m.insert c.bHash (c :: m.getD c.bHash [])) ∅
  let new := (seeds.filter (fun e => e.vars.all (fun z => varSet.contains z))).filter
    (fun e => !(csBuckets.getD e.bHash []).contains e)
  if new.isEmpty then d
  else { d with algebraicConstraints := d.algebraicConstraints ++ new }

end ApcOptimizer.Dense
