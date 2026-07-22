import ApcOptimizer.Implementation.OptimizerPasses.ZeroWidthRange

set_option autoImplicit false

/-! # Dense width-1 range check → booleanity (impl-only)

Dense `VarId` definitions for the recognizer `boolCheck?` and the pass `rangeBoolPass`.
**Impl-only**: no correctness theorem is stated here.

## Two fixed steps, kept as two dense sub-transforms

The pass is exactly **two** steps: step 1 adds every recognised booleanity as an algebraic
constraint (interactions untouched); step 2 drops the now-entailed interactions via `filterBus`.
Kept here as two separate dense transforms — `denseRangeBoolAddF` (the add) and
`denseRangeBoolDropF` (the drop) — so the prover can certify each half separately (their own
`DensePassCorrect`) and compose with `.andThen`; `denseRangeBoolF` is their sequential application
under the same two gates (`(1 : ZMod p) ≠ 0`, `pw.isPrime = true`).

## Reuse

`denseBoolC` (`ZeroWidthRange.lean`) is the dense `v·(v−1)` booleanity builder, so no new
booleanity builder is introduced here. `facts.rangeCheckAt`/`DenseExpr.constValue?` are as in
`RangeForceZero.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The booleanity constraint of a width-1 (`bound = 2`) op-6 check whose value slot is a bare
    variable. Reuses `denseBoolC` (`ZeroWidthRange.lean`). -/
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

/-- The dense transform: replace every width-1 op-6 range check on a bare variable by its
    booleanity, then drop the check, gated by `(1 : ZMod p) ≠ 0` then `pw.isPrime = true` in that
    order. -/
def denseRangeBoolF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    if pw.isPrime = true then
      denseRangeBoolDropF facts (denseRangeBoolAddF facts d)
    else d
  else d

end ApcOptimizer.Dense
