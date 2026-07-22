import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense byte-check pair splitting

Runtime transform for `splitBytePair`; the pass is wrapped in `Proofs/SplitBytePair.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognize a packed pair byte check (decoded op `= pairOp`, result `0`, multiplicity `1`) on a
    `byteXorSpec` bus, returning `(busId, spec, a, b)`. -/
def denseAsBytePair (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    Option (Nat × ByteXorSpec p × DenseExpr p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | some (op, o1, o2, r) =>
        if bi.multiplicity = DenseExpr.const 1 ∧ op = DenseExpr.const spec.pairOp
            ∧ r = DenseExpr.const 0 then some (bi.busId, spec, o1, o2) else none
    | none => none

/-- Split one interaction: a recognized packed pair becomes its two single-value checks (in
    decode order `a` then `b`); anything else passes through unchanged. -/
def denseSplitOne (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : List (BusInteraction (DenseExpr p)) :=
  match denseAsBytePair bs facts bi with
  | some (busId, spec, a, b) => [denseMkByteCheck spec busId a, denseMkByteCheck spec busId b]
  | none => [bi]

/-- Explodes every packed pair byte check into its two single-value checks, in place: a `[x, y]`
    pair check on a byte-XOR bus becomes separate byte checks on `x` and `y`. Every other
    interaction keeps its position. -/
def denseSplitBytePairF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    { d with busInteractions := d.busInteractions.flatMap (denseSplitOne bs facts) }
  else d

end ApcOptimizer.Dense
