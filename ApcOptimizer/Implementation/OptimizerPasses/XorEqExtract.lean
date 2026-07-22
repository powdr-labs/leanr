import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack

set_option autoImplicit false

/-! # Dense bitwise-XOR constant-operand equality extraction

The constant-operand XOR recognizer `denseXorEq?`, the OR/AND generalization `denseBoolEq?` (with
its `denseSimpleTarget`/`denseOpIs` ingredients), and the pass `denseXorEqExtractF`, which appends
both recognizers' outputs to the algebraic constraints in a single shot.

## Reuse (no new arithmetic-expression builders)

* `subE z e := z + (-1)·e` is textually identical to `BusUnify.lean`'s `denseEqExpr e2 e1 := e2 +
  (-1)·e1` (`denseEqExpr z e`) — reused directly, no new `denseSubE`.
* `complE e := 255 - e` is textually identical to `ByteCheckPack.lean`'s `denseComplExpr` — reused
  directly, no new `denseComplE`.
* `facts.byteXorSpec`/`ByteXorSpec.decode`/`.encode` are representation-independent (`{α : Type} →
  …`) and are consulted unqualified at `α := DenseExpr p` — no dense twin needed. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Constant-operand XOR recognizer -/

/-- The entailed equality from a constant-operand XOR interaction, recognized through the VM-neutral
    `byteXorSpec`, reusing `denseEqExpr` (`BusUnify.lean`) for `subE` and `denseComplExpr`
    (`ByteCheckPack.lean`) for `complE`. -/
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

/-! ## OR / AND constant-operand extraction -/

/-- A substitution target Gauss can inline without disturbing anything: a *constant*. Reuses
    `DenseExpr.constValue?` (`DropPasses.lean`). -/
def denseSimpleTarget (e : DenseExpr p) : Bool := e.constValue?.isSome

/-- Does `op` match the (optional) op-selector value `o`? -/
def denseOpIs (o : Option (ZMod p)) (op : DenseExpr p) : Bool :=
  match o with
  | some v => decide (op = DenseExpr.const v)
  | none => false

/-- The entailed equality from a constant-**zero**-operand OR/AND interaction, emitted only when
    the result is pinned to a *constant*. -/
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

/-! ## The dense transform -/

/-- Extract every constant-operand XOR/OR/AND equality and add it as an algebraic constraint.
    Gated on `(1 : ZMod p) ≠ 0`. -/
def denseXorEqExtractF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := d.busInteractions.filterMap (denseXorEq? bs facts)
      ++ d.busInteractions.filterMap (denseBoolEq? bs facts)
    { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
