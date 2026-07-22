import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense interval forcing (runtime, impl-only): integer-window analysis of bounded affine
slots. No soundness lemma here; the proof and wiring live in `IntervalForceProof.lean`. -/

namespace IntervalForce

variable {p : ℕ}

/-! ## Signed-representative and window arithmetic (representation-independent) -/

/-- Signed minimal-magnitude integer representative: `c.val` when `c.val ≤ (p−1)/2`, else
    `c.val − p`. Gives scaled differences small-magnitude coefficients like `(256, −256)`. -/
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

/-- A processed affine term: signed integer coefficient `sc`, strict value bound `bnd`, `VarId` `v`. -/
structure DensePTerm where
  sc : Int
  bnd : Nat
  v : VarId

/-- Pair every term of a dense linear form with its variable's bound; `none` if any is unbounded. -/
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

/-- `v − w` as a dense expression. -/
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
    bound, check the integer window, and extract the pair/zero arms. -/
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

/-- Record the bound `denseInteractionBound bi x` (if any), keeping the smaller of duplicates. -/
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
    consumed as a bound-`1` slot. -/
def denseAllSeeds (bs : BusSemantics p) (facts : BusFacts p bs) (bnd : VarId → Option Nat)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  HashedDedup.hashedEraseDups DenseExpr.bHash
    (d.busInteractions.flatMap (denseInteractionSeeds bs facts bnd) ++
      d.algebraicConstraints.flatMap (fun c => denseSlotSeeds bnd 1 c))

/-- Interval-force transform: from the integer-window analysis of the system's bounded affine
    slots, seed every forced equality or zero as a new constraint (e.g. if bounds prove `x = y`
    must hold, append `x - y = 0`). Single-shot; appends the deduplicated new seeds. -/
def denseIntervalForceF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let idx := denseBoundIdxBuild bs facts d.busInteractions
  let seeds := denseAllSeeds bs facts (fun v => idx[v]?) d
  -- Hash set / hash-bucket lookups replace per-seed linear scans of `d.occ` and the constraints.
  let varSet : Std.HashSet VarId := Std.HashSet.ofList d.occ
  let csBuckets : Std.HashMap UInt64 (List (DenseExpr p)) :=
    d.algebraicConstraints.foldl (fun m c => m.insert c.bHash (c :: m.getD c.bHash [])) ∅
  let new := (seeds.filter (fun e => e.vars.all (fun z => varSet.contains z))).filter
    (fun e => !(csBuckets.getD e.bHash []).contains e)
  if new.isEmpty then d
  else { d with algebraicConstraints := d.algebraicConstraints ++ new }

end ApcOptimizer.Dense
