import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Rewrite
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Dense width-0 / width-1 range-check conversion (impl-only)

Dense `VarId` definitions for width-0/width-1 range-check conversion: the booleanity builder
`boolC`, the recognizer `rangeEq?`, and the transform inside `zeroWidthRangePass`. **Impl-only**:
the `DensePassCorrect` proof and the pass wiring live in `ZeroWidthRangeProof.lean`.

Gated on `(1 : ZMod p) ≠ 0`, the transform appends the equivalent algebraic constraint for every
degenerate range check (`value = 0` for width-0, its booleanity `value·(value−1) = 0` for width-1
when `p` is prime — decided per-arm through the recognizer's `one` parameter) and then drops the
now-entailed interactions. It is **fact-consuming** (`zeroRangeEq`/`varRangeBus`). -/

namespace ZeroWidthRange

variable {p : ℕ}

/-- On a prime field, `x < 2` (as a value) is exactly booleanity.

    Representation-independent (`Nat`/`ZMod`) lemma, kept here at its value-level home so the dense
    proof tree (`ZeroWidthRangeProof.lean` / `RangeBoolProof.lean`) can consume it. -/
theorem val_lt_two_iff (hp : Nat.Prime p) (x : ZMod p) :
    x.val < 2 ↔ x * (x - 1) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hlt
    have : x.val = 0 ∨ x.val = 1 := by omega
    rcases this with h0 | h1
    · rw [ZMod.val_eq_zero] at h0; rw [h0]; ring
    · have hx1 : x = 1 := by
        have := (ZMod.natCast_rightInverse x).symm
        rw [this, h1]; norm_cast
      rw [hx1]; ring
  · intro hprod
    rcases mul_eq_zero.1 hprod with h0 | h1
    · rw [h0, ZMod.val_zero]; omega
    · have hx1 : x = 1 := by linear_combination h1
      rw [hx1, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt]; omega

end ZeroWidthRange

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense booleanity constraint -/

/-- `v·(v − 1)` as a dense expression. -/
def denseBoolC (v : DenseExpr p) : DenseExpr p := .mul v (.add v (.const (-1)))

/-! ## Dense recognizer -/

/-- Recognize a degenerate-width range check, returning its value slot (width-0, `c = 0`) or its
    booleanity constraint (width-1, `c = 1`, on a prime field). -/
def denseRangeEq? (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match bi.payload with
  | [v, c] =>
    if bi.multiplicity = DenseExpr.const 1 then
      if facts.zeroRangeEq bi.busId = true ∧ c = DenseExpr.const 0 then some v
      else if one = true ∧ facts.varRangeBus bi.busId = true ∧ c = DenseExpr.const 1
          ∧ v.degree ≤ 1 then some (denseBoolC v)
      else none
    else none
  | _ => none

/-! ## The dense transform -/

/-- The dense width-0/width-1 conversion transform: append the entailed constraints, then drop the
    now-entailed interactions (identity off a prime field). -/
def denseZeroWidthRangeF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    ({ d with algebraicConstraints :=
        d.algebraicConstraints ++ d.busInteractions.filterMap (denseRangeEq? pw.isPrime bs facts) }
      : DenseConstraintSystem p).filterBus
      (fun bi => (denseRangeEq? pw.isPrime bs facts bi).isNone)
  else d

end ApcOptimizer.Dense
