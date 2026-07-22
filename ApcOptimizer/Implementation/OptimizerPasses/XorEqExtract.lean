import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack

set_option autoImplicit false

/-! # Dense bitwise-XOR constant-operand equality extraction

Impl-only: the constant-operand XOR recognizer `denseXorEq?`, the OR/AND generalization
`denseBoolEq?` (with `denseSimpleTarget`/`denseOpIs`), and the transform `denseXorEqExtractF`;
correctness in `Proofs/XorEqExtract.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The entailed equality from a constant-operand XOR interaction. -/
def denseXorEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if bi.multiplicity = DenseExpr.const 1 then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if op = DenseExpr.const spec.xorOp then
          if o1 = DenseExpr.const 0 then some (denseEqExpr r o2)
          else if o2 = DenseExpr.const 0 then some (denseEqExpr r o1)
          else if 256 ≤ p ∧ spec.bound = 256 ∧ o1 = DenseExpr.const 255 then
            some (denseEqExpr r (denseComplExpr o2))
          else if 256 ≤ p ∧ spec.bound = 256 ∧ o2 = DenseExpr.const 255 then
            some (denseEqExpr r (denseComplExpr o1))
          else none
        else none
      | none => none
    else none

/-- A substitution target Gauss can inline freely: a constant. -/
def denseSimpleTarget (e : DenseExpr p) : Bool := e.constValue?.isSome

/-- Does `op` match the (optional) op-selector value `o`? -/
def denseOpIs (o : Option (ZMod p)) (op : DenseExpr p) : Bool :=
  match o with
  | some v => decide (op = DenseExpr.const v)
  | none => false

/-- The entailed equality from a constant-zero-operand OR/AND interaction (result pinned to a
    constant). -/
def denseBoolEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if bi.multiplicity = DenseExpr.const 1 then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if denseOpIs spec.orOp op then
          if o1 = DenseExpr.const 0 then
            (if denseSimpleTarget o2 then some (denseEqExpr r o2) else none)
          else if o2 = DenseExpr.const 0 then
            (if denseSimpleTarget o1 then some (denseEqExpr r o1) else none)
          else none
        else if denseOpIs spec.andOp op then
          if o1 = DenseExpr.const 0 ∨ o2 = DenseExpr.const 0 then some r
          else none
        else none
      | none => none
    else none

/-- For a byte XOR/OR/AND interaction with a constant operand, extracts the resulting equality on
    the result cell — e.g. `0 XOR b = r` gives `r = b`, `255 XOR b = r` gives `r = 255 − b` — and
    adds it as an algebraic constraint. Gated on `(1 : ZMod p) ≠ 0`. -/
def denseXorEqExtractF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := d.busInteractions.filterMap (denseXorEq? bs facts)
      ++ d.busInteractions.filterMap (denseBoolEq? bs facts)
    { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
