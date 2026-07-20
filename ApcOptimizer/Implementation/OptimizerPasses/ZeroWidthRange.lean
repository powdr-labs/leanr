import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Rewrite
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroWidthRange

set_option autoImplicit false

/-! # Dense width-0 / width-1 range-check conversion (Task 3, impl-only)

Dense, `VarId`-native transliteration of the *runtime* content of
`OldVariableBased/ZeroWidthRange.lean`: the booleanity builder `boolC` (`:43`), the recognizer
`rangeEq?` (`:76`), and the transform inside `zeroWidthRangePass` (`:144`). **Impl-only**: the
native `DensePassCorrect` proof and the pass wiring live in `ZeroWidthRangeProof.lean`.

Gated on `(1 : ZMod p) ≠ 0`, the transform appends the equivalent algebraic constraint for every
degenerate range check (`value = 0` for width-0, its booleanity `value·(value−1) = 0` for width-1
when `p` is prime — decided per-arm through the recognizer's `one` parameter) and then drops the
now-entailed interactions. It is **fact-consuming** (`zeroRangeEq`/`varRangeBus`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense booleanity constraint -/

/-- `v·(v − 1)` as a dense expression (mirrors `ZeroWidthRange.boolC`). -/
def denseBoolC (v : DenseExpr p) : DenseExpr p := .mul v (.add v (.const (-1)))

/-! ## Dense recognizer -/

/-- Dense `rangeEq?` (see `ZeroWidthRange.rangeEq?`). -/
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
    now-entailed interactions (identity off a prime field). Mirrors the transform inside
    `ZeroWidthRange.zeroWidthRangePass` (`:144`). -/
def denseZeroWidthRangeF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    ({ d with algebraicConstraints :=
        d.algebraicConstraints ++ d.busInteractions.filterMap (denseRangeEq? pw.isPrime bs facts) }
      : DenseConstraintSystem p).filterBus
      (fun bi => (denseRangeEq? pw.isPrime bs facts bi).isNone)
  else d

end ApcOptimizer.Dense
