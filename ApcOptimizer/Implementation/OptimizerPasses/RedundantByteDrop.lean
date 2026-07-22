import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify

set_option autoImplicit false

/-! # Dense redundant byte-check removal

Runtime recognizer and transform for `redundantByteDrop`; the pass is wrapped in
`RedundantByteDropProof.lean`. Unlike `denseSvCheck?` (`ByteCheckPack.lean`), the recognizer here
ignores the dropped check's own multiplicity, returns a *list* of justified operands, and also
recognizes the packed-pair shape. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The operands whose byte-ness *implies* this interaction's acceptance (at any multiplicity),
    recognized through the VM-neutral `byteXorSpec` (byte bound `256`): the XOR self-check and
    zero/NOT mirrors, the OR-identity zero mirrors, and the packed pair (`pairOp`, `r = 0`, two
    operands); `none` otherwise. -/
def denseByteCheckOperands? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (List (DenseExpr p)) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | none => none
      | some (op, o1, o2, r) =>
        if op.constValue? == some spec.xorOp then
          if o1 == o2 && r.constValue? == some 0 then some [o1]
          else if o2.constValue? == some 0 && o1 == r then some [o1]
          else if o1.constValue? == some 0 && o2 == r then some [o2]
          else if decide (256 ≤ p) && o2.constValue? == some 255 && denseIsByteCompl o1 r then
            some [o1]
          else if decide (256 ≤ p) && o1.constValue? == some 255 && denseIsByteCompl o2 r then
            some [o2]
          else none
        else if spec.orOp.any (fun oop => op.constValue? == some oop) then
          -- OR identity (`x | 0 = x`): exactly a byte check on the survivor.
          if o2.constValue? == some 0 && o1 == r then some [o1]
          else if o1.constValue? == some 0 && o2 == r then some [o2]
          else none
        else if op.constValue? == some spec.pairOp && r.constValue? == some 0 then some [o1, o2]
        else none
    else none

/-- The justification base: the interactions this pass can never drop (not recognized as byte
    checks). Justifying only against these makes the drop non-circular. -/
def denseByteDropBase (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseByteCheckOperands? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized byte check whose operands are all byte-justified from the
    constraints and the justification base. -/
def denseByteDropKeep (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (all : List (DenseExpr p)) (rest : List (BusInteraction (DenseExpr p)))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseByteCheckOperands? bs facts bi with
  | some ops => !(ops.all (fun e => denseByteJustified 256 pw.isPrime all bs facts rest e))
  | none => true

/-- Drops a byte-check interaction when all its operands are already proven to be bytes elsewhere —
    from the constraints and the un-droppable base interactions — so the check is redundant
    (`denseRedundantByteDropPass`). -/
def denseRedundantByteDropF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseByteDropKeep pw bs facts d.algebraicConstraints (denseByteDropBase bs facts d))

end ApcOptimizer.Dense
