import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Dense subsumed pure-range-check removal

Recognizes a pure single-value range check whose bound is already entailed by a stronger-or-equal
retained check on the same variable, and drops it. No `DenseVerifiedPassW`/`DensePassCorrect`
wrapper is built here — the runtime transform `denseSubsumedCheckDropF` is shaped like
`denseBoxTautoDropF` (`Dense/FlagFoldDrops.lean`) MINUS a `PrimeWitness`/`facts`-selection gate
(this pass is unconditional in `p` and consumes `facts` directly), so it is wrapped directly with
`DenseVerifiedPassW.of`.

## Reuse map (not re-derived)

* `denseFindVarBound` (`Dense/RootPairUnify.lean`, itself built from `denseInteractionBound` /
  `Dense/DigitFold.lean`) is reused unchanged as the non-circular justification base for
  `dropKeep`, not re-derived.
* `DenseExpr.constValue?` (`Dense/DropPasses.lean`) is consumed through `facts.rangeCheckAt`.
* `DenseConstraintSystem.filterBus` (`Dense/Rewrite.lean`) is what the pass's `.out` is built from.
* `BusFacts`/`BusSemantics` are representation-independent (their signatures only mention `Nat`/
  `ZMod p`/patterns, never `Variable`/`Expression`), so `facts.rangeCheckAt` is consumed directly,
  unchanged. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognise a pure single-value range check (`facts.rangeCheckAt`) at multiplicity `1` whose
    value slot holds a bare variable: returns the checked variable, its slot, and its bound. -/
def denseSubsumedCheckOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (VarId × Nat × Nat) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = DenseExpr.const 1 then
      match bi.payload[valSlot]? with
      | some (DenseExpr.var x) => some (x, valSlot, bound)
      | _ => none
    else none
  | none => none

/-- The justification base: interactions this pass never drops (not recognised as pure checks). -/
def denseSubsumedCheckDropBase (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseSubsumedCheckOf bs facts bi).isNone)

/-- Keep `bi` unless it is a recognised pure check whose variable is already bounded `< bound` by a
    retained (base) interaction. -/
def denseSubsumedCheckDropKeep (bs : BusSemantics p) (facts : BusFacts p bs)
    (base : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseSubsumedCheckOf bs facts bi with
  | some (x, _, bound) =>
    match denseFindVarBound bs facts base x with
    | some b' => !decide (b' ≤ bound)
    | none => true
  | none => true

/-- The runtime transform: drop every pure single-value range check whose bound is already
    entailed by a stronger-or-equal retained stateless check on the same variable. -/
def denseSubsumedCheckDropF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseSubsumedCheckDropKeep bs facts (denseSubsumedCheckDropBase bs facts d))

end ApcOptimizer.Dense
