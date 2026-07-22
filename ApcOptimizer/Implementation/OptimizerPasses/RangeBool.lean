import ApcOptimizer.Implementation.OptimizerPasses.ZeroWidthRange

set_option autoImplicit false

/-! # Dense width-1 range check → booleanity

Impl-only: recognizer `denseBoolCheck?` and transform `denseRangeBoolF`; correctness in
`RangeBoolProof.lean`. Split into add/drop sub-transforms so each half carries its own
`DensePassCorrect`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

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

/-- Step 1: add every recognised booleanity, interactions untouched. -/
def denseRangeBoolAddF {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { d with algebraicConstraints :=
      d.algebraicConstraints ++ d.busInteractions.filterMap (denseBoolCheck? facts) }

/-- Step 2: drop the now-entailed interactions. -/
def denseRangeBoolDropF {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (fun bi => (denseBoolCheck? facts bi).isNone)

/-- For a width-1 range check `x < 2` on a bare variable `x`, adds its booleanity `x·(x−1) = 0`
    as a constraint then drops the now-redundant check. Gated on a prime field. -/
def denseRangeBoolF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    if pw.isPrime = true then
      denseRangeBoolDropF facts (denseRangeBoolAddF facts d)
    else d
  else d

end ApcOptimizer.Dense
