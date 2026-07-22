import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense interval forcing: integer-window analysis of bounded affine slots (impl-only)

Runtime content for `intervalForce`: the signed-representative processed term
(`DensePTerm`/`denseProcTerms`/`denseMaxSum`/`denseMinSum`), the seed walk
(`densePairDiff`/`denseFindPartner`/`denseWalk`), the per-slot seed extraction (`denseSlotSeeds`),
the per-invocation bounds index (`denseBoundIdx*`), the per-interaction/whole-system seed
collection (`denseInteractionSeedsGo`/`denseInteractionSeeds`/`denseAllSeeds`), and the pass itself
(`denseIntervalForceF`) — a single-shot add-seeds transform. This file is **impl-only**: it carries
no soundness lemma, and nothing here is wired into a `DenseVerifiedPassW`/`DensePassCorrect`
wrapper (the prover's job). Integer-window evaluation is not needed here — the runtime
(`denseSlotSeeds`/`denseWalk`/`denseInteractionSeeds`/`denseAllSeeds`) never calls it; it would
exist only to state proof-side window lemmas.

## Representation-independent reuse

`IntervalForce.srep : ZMod p → Int` / `srep_cast` / `term_window` / `int_window` and
`IntervalForce.maxTerms : Nat` touch neither `VarId` nor `DenseExpr`; they live in the
representation-independent `IntervalForce` namespace below and are reused **unqualified** via `open
IntervalForce` (here, and by `BusPairCancelJustify.lean`, which reuses `srep`). `DensePTerm` carries
a `VarId` in its `v` field, so it (and every function over `List DensePTerm`) is its own structure,
not reused from anywhere.

## Reuse of existing dense machinery

* `densePairDiff v w := v − w` is exactly `BusUnify.lean`'s `denseEqExpr (.var v) (.var w)` — reused
  directly, no new expression builder.
* `denseLinearize`/`DenseLinExpr` (`Affine.lean`) and `DenseLinExpr.norm` (`Normalize.lean`).
* `denseInteractionBound` (`DigitFold.lean`) is what `denseBoundIdxInsertVar` consumes.
* `DenseExpr.bHash` (`Dedup.lean`) and `HashedDedup.hashedEraseDups` (`HashedDedup.lean`, already
  generic in the hashed element type) are what `denseAllSeeds` consumes for its dedup.

## The bounds index: a data-only `Std.HashMap VarId Nat`

`denseBoundIdxInsertVar`/`denseBoundIdxAddBi`/`denseBoundIdxAddAll`/`denseBoundIdxBuild` operate
directly on a plain `Std.HashMap VarId Nat` (insert-keep-smaller/per-interaction/whole-list
recursion), carrying no proof field. Named with a `BoundIdx`-specific prefix (`denseBoundIdx*`) to
avoid colliding with `DigitFold.lean`'s *different* `denseInsertEntry`/`denseAddVars`/`denseAddAll`/
`denseBuild` (a different fact-derived map, same general shape, unrelated pass). -/

namespace IntervalForce

variable {p : ℕ}

/-! ## Signed-representative and window arithmetic

`srep`/`srep_cast`/`term_window`/`int_window`/`maxTerms` touch only `Nat`/`Int`/`ZMod`; this
namespace is their shared, representation-independent home, consumed unqualified by the dense
pass, its proof, and `BusPairCancelJustify.lean` (which reuses `srep`). -/

/-- Signed minimal-magnitude integer representative of a field element: `c.val` when
    `c.val ≤ (p−1)/2`, else `c.val − p`. Scaled differences like `256·a − 256·b` thus get the
    small-magnitude coefficients `(256, −256)` rather than `(256, p−256)`. -/
def srep (c : ZMod p) : Int :=
  if c.val ≤ (p - 1) / 2 then (c.val : Int) else (c.val : Int) - (p : Int)

theorem srep_cast [NeZero p] (c : ZMod p) : ((srep c : Int) : ZMod p) = c := by
  unfold srep
  split_ifs
  · rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  · push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self, sub_zero]

/-- Each term's signed value lies in the window `[min (sc·(B−1)) 0, max (sc·(B−1)) 0]`. -/
theorem term_window (sc d B : Int) (h0 : 0 ≤ d) (hd : d < B) :
    min (sc * (B - 1)) 0 ≤ sc * d ∧ sc * d ≤ max (sc * (B - 1)) 0 := by
  rcases le_or_gt 0 sc with hsc | hsc
  · exact ⟨le_trans (min_le_right _ _) (mul_nonneg hsc h0),
      le_trans (mul_le_mul_of_nonneg_left (by omega) hsc) (le_max_left _ _)⟩
  · refine ⟨le_trans (min_le_left _ _)
      (mul_le_mul_of_nonpos_left (by omega) (le_of_lt hsc)), ?_⟩
    have h1 : sc * d ≤ sc * 0 := mul_le_mul_of_nonpos_left h0 (le_of_lt hsc)
    rw [mul_zero] at h1
    exact le_trans h1 (le_max_right _ _)

/-- If the signed-representative integer value `S` reduces to a field element `x` with
    `x.val < B`, and the window `[lo, hi] ∋ S` satisfies `hi ≤ p − 1` and `lo ≥ B − p`, then
    `S = x.val` holds over ℤ — in particular `0 ≤ S < B`. -/
theorem int_window [NeZero p] (S : Int) (B : Nat) (x : ZMod p)
    (hcast : ((S : Int) : ZMod p) = x) (hx : x.val < B)
    (hlo : (B : Int) - (p : Int) ≤ S) (hhi : S ≤ (p : Int) - 1) : S = (x.val : Int) := by
  have hdvd : (p : Int) ∣ (S - (x.val : Int)) := by
    have hz : ((S - (x.val : Int) : Int) : ZMod p) = 0 := by
      push_cast
      rw [hcast, ZMod.natCast_val, ZMod.cast_id, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  obtain ⟨k, hk⟩ := hdvd
  have hxv : (0 : Int) ≤ (x.val : Int) := Int.natCast_nonneg _
  have hxvB : ((x.val : Int)) < (B : Int) := by exact_mod_cast hx
  have hp : (0 : Int) < (p : Int) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  -- `S − x.val = p·k` with `S − x.val ∈ (−p, p)` forces `k = 0`.
  rcases lt_trichotomy k 0 with hkn | rfl | hkp
  · exfalso
    have h2 : (p : Int) * k ≤ (p : Int) * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp)
    rw [mul_neg_one] at h2
    generalize hX : (p : Int) * k = X at hk h2
    omega
  · omega
  · exfalso
    have h2 : (p : Int) * 1 ≤ (p : Int) * k :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp)
    rw [mul_one] at h2
    generalize hX : (p : Int) * k = X at hk h2
    omega

/-- Cap on the number of affine terms analyzed per slot (the walk is quadratic). -/
def maxTerms : Nat := 32

end IntervalForce

namespace ApcOptimizer.Dense

open IntervalForce

variable {p : ℕ}

/-! ## Signed representatives and processed terms -/

/-- A dense processed affine term: signed integer coefficient, a proven strict bound for the
    variable's value, and the `VarId` itself. -/
structure DensePTerm where
  sc : Int
  bnd : Nat
  v : VarId

/-- Pair every term of a dense linear form with its variable's proven bound; `none` if any variable
    is unbounded. Reuses `IntervalForce.srep` (representation-independent). -/
def denseProcTerms (bnd : VarId → Option Nat) :
    List (VarId × ZMod p) → Option (List DensePTerm)
  | [] => some []
  | (v, c) :: rest =>
    match bnd v, denseProcTerms bnd rest with
    | some B, some pts => some (⟨srep c, B, v⟩ :: pts)
    | _, _ => none

/-- Upper window bound: each term contributes `max (sc·(B−1)) 0`. -/
def denseMaxSum (pts : List DensePTerm) : Int :=
  (pts.map (fun t => max (t.sc * ((t.bnd : Int) - 1)) 0)).sum

/-- Lower window bound: each term contributes `min (sc·(B−1)) 0`. -/
def denseMinSum (pts : List DensePTerm) : Int :=
  (pts.map (fun t => min (t.sc * ((t.bnd : Int) - 1)) 0)).sum

/-! ## Seed extraction -/

/-- `v − w` as a dense expression. Reuses `denseEqExpr` (`BusUnify.lean`). -/
def densePairDiff (v w : VarId) : DenseExpr p := denseEqExpr (.var v) (.var w)

/-- First term with signed coefficient `g`, and the list without it. -/
def denseFindPartner (g : Int) : List DensePTerm → Option (DensePTerm × List DensePTerm)
  | [] => none
  | t :: rest =>
    if t.sc = g then some (t, rest)
    else
      match denseFindPartner g rest with
      | some (t', rest') => some (t', t :: rest')
      | none => none

/-- The walk over the term list: at each term, try the zero arm (against all other terms) and,
    for a positive coefficient, the pair arm against the first `−g` partner among the other terms. -/
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
    proven bound, check the integer window, and extract the pair/zero arms. Reuses
    `denseLinearize`/`DenseLinExpr.norm` and `IntervalForce.srep`/`.maxTerms`. -/
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
    Reuses `denseInteractionBound` (`DigitFold.lean`). -/
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

/-- Record every bare-variable slot bound of one interaction. -/
def denseBoundIdxAddBi (bs : BusSemantics p) (facts : BusFacts p bs)
    (I : Std.HashMap VarId Nat) (bi : BusInteraction (DenseExpr p)) : Std.HashMap VarId Nat :=
  (bi.payload.filterMap (fun e =>
    match e with
    | .var x => some x
    | _ => none)).foldl (fun I x => denseBoundIdxInsertVar bs facts I bi x) I

/-- Fold `denseBoundIdxAddBi` over every interaction. -/
def denseBoundIdxAddAll (bs : BusSemantics p) (facts : BusFacts p bs) :
    Std.HashMap VarId Nat → List (BusInteraction (DenseExpr p)) → Std.HashMap VarId Nat
  | I, [] => I
  | I, bi :: rest => denseBoundIdxAddAll bs facts (denseBoundIdxAddBi bs facts I bi) rest

/-- Build the bounds index from scratch. -/
def denseBoundIdxBuild (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) : Std.HashMap VarId Nat :=
  denseBoundIdxAddAll bs facts ∅ bis

/-! ## The pass -/

/-- The per-slot seed walk of `denseInteractionSeeds`, with the constant-payload pattern `pat`
    computed once by the caller instead of once per slot. -/
def denseInteractionSeedsGo (bs : BusSemantics p) (facts : BusFacts p bs)
    (bnd : VarId → Option Nat) (bi : BusInteraction (DenseExpr p)) (mval : ZMod p)
    (pat : List (Option (ZMod p))) : List (DenseExpr p) :=
  (List.range bi.payload.length).flatMap (fun i =>
    match bi.payload[i]?, facts.slotBound bi.busId mval pat i with
    | some e, some B => denseSlotSeeds bnd B e
    | _, _ => [])

/-- All seeds of one interaction: every payload slot with a `slotBound`. -/
def denseInteractionSeeds (bs : BusSemantics p) (facts : BusFacts p bs)
    (bnd : VarId → Option Nat) (bi : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  match bi.multiplicity.constValue? with
  | none => []
  | some mval =>
    if mval = 0 then []
    else denseInteractionSeedsGo bs facts bnd bi mval (bi.payload.map DenseExpr.constValue?)

/-- All seeds over the system: every bounded interaction slot, plus every algebraic constraint
    consumed as a bound-`1` slot. Reuses `DenseExpr.bHash` (`Dedup.lean`) and
    `HashedDedup.hashedEraseDups` (`HashedDedup.lean`). -/
def denseAllSeeds (bs : BusSemantics p) (facts : BusFacts p bs) (bnd : VarId → Option Nat)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  HashedDedup.hashedEraseDups DenseExpr.bHash
    (d.busInteractions.flatMap (denseInteractionSeeds bs facts bnd) ++
      d.algebraicConstraints.flatMap (fun c => denseSlotSeeds bnd 1 c))

/-- The dense transform: seed every equality/zero forced by the integer-window analysis of the
    system's bounded affine slots (and its constraints), using a `Std.HashSet`/hash-bucket dedup
    shortcut (`d.occ`, `DenseExpr.bHash`) instead of per-seed linear scans. -/
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
