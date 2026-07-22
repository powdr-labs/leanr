import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify

set_option autoImplicit false

/-! # Dense redundant byte-check removal

Runtime recognizer and transform for `redundantByteDrop`; the pass is wrapped in
`Proofs/RedundantByteDrop.lean`. Unlike `denseSvCheck?` (`ByteCheckPack.lean`), the recognizer here
ignores the dropped check's own multiplicity, returns a *list* of justified operands, and also
recognizes the packed-pair shape. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The operands whose byte-ness *implies* this interaction's acceptance (at any multiplicity):
    the checked operands of any fold-recognized shape, packed pair included (`denseByteShape?`);
    `none` otherwise. -/
def denseByteCheckOperands? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (List (DenseExpr p)) :=
  (denseByteShape? denseCmpFolded bs facts bi).map fun (sh, _, o1, o2) => sh.operands o1 o2

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
