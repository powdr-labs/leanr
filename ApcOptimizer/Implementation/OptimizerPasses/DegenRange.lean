import ApcOptimizer.Implementation.OptimizerPasses.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Dense degenerate range checks → algebraic constraints

Impl-only recognizers for the `degenRange` pass (an `ofCheckRules` instance): a width-0 range
check forces its value slot to `0`; a width-1 check (on a prime field) makes its value boolean.
Rules, proofs and wiring in `Proofs/DegenRange.lean`. -/

namespace DegenRange

variable {p : ℕ}

/-- On a prime field, `x < 2` (value-level) is exactly booleanity `x·(x−1) = 0`. -/
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

end DegenRange

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `v·(v − 1)` as a dense expression. -/
def denseBoolC (v : DenseExpr p) : DenseExpr p := .mul v (.add v (.const (-1)))

/-- Recognizes a degenerate-width range check: width-0 (`c = 0`) forces its value slot to `0`;
    width-1 (`c = 1`, on a prime field) makes its value boolean, returning `v·(v−1) = 0`. -/
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

/-- The booleanity `x·(x−1)` of a width-1 (`bound = 2`) check whose value slot is a bare variable
    `x`. -/
def denseBoolCheck? {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = DenseExpr.const 1 ∧ bound = 2 then
      match bi.payload[valSlot]? with
      | some (DenseExpr.var x) => some (denseBoolC (DenseExpr.var x))
      | _ => none
    else none
  | none => none

end ApcOptimizer.Dense
