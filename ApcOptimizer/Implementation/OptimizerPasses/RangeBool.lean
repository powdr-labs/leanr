import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.RangeBool
import ApcOptimizer.Implementation.OptimizerPasses.ZeroWidthRange

set_option autoImplicit false

/-! # Dense width-1 range check → booleanity (Task 3, impl-only)

Dense, `VarId`-native transliteration of `OldVariableBased/RangeBool.lean`'s *runtime* content:
the recognizer `boolCheck?` (`:26`) and the pass `rangeBoolPass` (`:85`). **Impl-only**:
`boolCheck?_spec`/`_stateless`/`_violates_iff` are proof-side and left for the prover; nothing here
is wired into the `denseImpl` selector.

## Two fixed steps, kept as two dense sub-transforms

The spec pass is exactly **two** `PassCorrect` steps composed by one `andThen` (`:85`): step 1 adds
every recognised booleanity as an algebraic constraint (interactions untouched); step 2 drops the
now-entailed interactions via `filterBus`. Mirrored here as two separate dense transforms —
`denseRangeBoolAddF` (the add) and `denseRangeBoolDropF` (the drop) — so the prover can certify each
half separately (their own `DensePassCorrect`) and compose with `.andThen`, exactly as the spec
composes its two `PassCorrect` halves; `denseRangeBoolF` is their sequential application under the
same two gates (`(1 : ZMod p) ≠ 0`, `pw.isPrime = true`) the spec uses.

## Reuse

`denseBoolC` (`ZeroWidthRange.lean`) is the dense `v·(v−1)` booleanity builder — `boolCheck?`'s
constraint is `ZeroWidthRange.boolC`, so no new booleanity builder is introduced here.
`facts.rangeCheckAt`/`DenseExpr.constValue?` are as in `RangeForceZero.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The booleanity constraint of a width-1 (`bound = 2`) op-6 check whose value slot is a bare
    variable. Mirrors `RangeBool.boolCheck?` (`OldVariableBased/RangeBool.lean:26`), reusing
    `denseBoolC` (`ZeroWidthRange.lean`) in place of `ZeroWidthRange.boolC`. -/
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

/-- Step 1: add every recognised booleanity, interactions untouched. Mirrors the `out1`
    construction inside `RangeBool.rangeBoolPass` (`:85`). -/
def denseRangeBoolAddF {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { d with algebraicConstraints :=
      d.algebraicConstraints ++ d.busInteractions.filterMap (denseBoolCheck? facts) }

/-- Step 2: drop the now-entailed interactions. Mirrors `out1.filterBus keep` inside
    `RangeBool.rangeBoolPass` (`:85`). -/
def denseRangeBoolDropF {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (fun bi => (denseBoolCheck? facts bi).isNone)

/-- The dense transform: replace every width-1 op-6 range check on a bare variable by its
    booleanity, then drop the check. Mirrors `RangeBool.rangeBoolPass` (`:85`), same two gates
    (`(1 : ZMod p) ≠ 0`, then `pw.isPrime = true`) in the same order. -/
def denseRangeBoolF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    if pw.isPrime = true then
      denseRangeBoolDropF facts (denseRangeBoolAddF facts d)
    else d
  else d

end ApcOptimizer.Dense
