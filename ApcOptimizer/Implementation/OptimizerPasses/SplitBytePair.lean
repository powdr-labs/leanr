import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense byte-check pair splitting

Explodes every packed pair byte check into its two single-value checks (`denseAsBytePair`,
`denseSplitOne`, and the pass's computed output `denseSplitBytePairF`). This file is **impl-only**:
it carries no `DensePassCorrect`/`DenseVerifiedPassW` wrapper here. The runtime transform
`denseSplitBytePairF` is shaped like `denseByteCheckPackF` (`ByteCheckPack.lean`): unconditional in
`p` (gated only by a `(1 : ZMod p) ≠ 0` self-check), consuming `facts` directly with no fresh
variables, so it can be wrapped directly with `DenseVerifiedPassW.of`.

## Notes

* `denseMkByteCheck` (`BusPairCancelCheck.lean`) is reused unchanged as the emitter for each of the
  two split singles.
* `ByteXorSpec`/`BusFacts.byteXorSpec`/`spec.decode` are representation-independent (their
  signatures only mention `Nat`/`ZMod p`/payload lists, never `Variable`/`Expression`), so
  `denseAsBytePair` consults them unqualified.

## Ordering

`denseSplitOne` emits the split pair in the order `[denseMkByteCheck spec busId a,
denseMkByteCheck spec busId b]` — operand order `a` then `b` (the pair's own decode order).
`denseSplitBytePairF` `flatMap`s `denseSplitOne` over `d.busInteractions` in original list order:
every untouched interaction keeps its position and every split pair is emitted in place of the one
packed interaction it replaces, singles in decode order. -/

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

/-- The runtime transform: explode every packed pair byte check into its two single-value checks,
    in place, preserving the order of every other interaction. VM-neutral: with a trivial
    `BusFacts`, `byteXorSpec` is `none` everywhere, so `denseAsBytePair` never fires and the
    `flatMap` is the identity up to `[bi]`-singleton unwrapping. -/
def denseSplitBytePairF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    { d with busInteractions := d.busInteractions.flatMap (denseSplitOne bs facts) }
  else d

end ApcOptimizer.Dense
