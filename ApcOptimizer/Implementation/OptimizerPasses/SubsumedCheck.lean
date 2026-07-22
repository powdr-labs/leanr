import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Dense subsumed pure-range-check removal (Task 3 — impl)

Dense, `VarId`-native transliteration of the reference `SubsumedCheck` pass's *runtime*
definitions (`checkOf`, `dropBase`, `dropKeep`, and the pass's computed output). This file is
**impl-only**: no theorem/lemma from the spec file is ported (`checkOf_spec`, `checkOf_stateless`,
`checkOf_accepted`, and the pass's `filterBusEntailed_correct`-built `PassCorrect` proof are all
proof-side, the prover's job), and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here
— the runtime transform `denseSubsumedCheckDropF` is shaped like `denseBoxTautoDropF`
(`Dense/FlagFoldDrops.lean`) MINUS a `PrimeWitness`/`facts`-selection gate (this pass, like its
spec counterpart, is unconditional in `p` and consumes `facts` directly), so the prover wraps it
directly with `DenseVerifiedPassW.ofNative`.

## Reuse map (not re-derived)

* `denseFindVarBound` (`Dense/RootPairUnify.lean`, itself built from `denseInteractionBound` /
  `Dense/DigitFold.lean`) is *exactly* the dense `findVarBound` (`DomainProp.lean:590`) the spec
  `dropKeep` consumes for its non-circular justification base — reused unchanged, not re-derived.
* `DenseExpr.constValue?` (`Dense/DropPasses.lean`) is the dense `Expression.constValue?`, used
  (through `facts.rangeCheckAt`) exactly as the spec `checkOf` uses it.
* `DenseConstraintSystem.filterBus` (`Dense/Rewrite.lean`) is the dense `ConstraintSystem.filterBus`
  the pass's `.out` is built from.
* `BusFacts`/`BusSemantics` are representation-independent (their signatures only mention `Nat`/
  `ZMod p`/patterns, never `Variable`/`Expression`), so `facts.rangeCheckAt` is consumed directly,
  unchanged, exactly as the spec pass does. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognise a pure single-value range check (`facts.rangeCheckAt`) at multiplicity `1` whose
    value slot holds a bare variable: returns the checked variable, its slot, and its bound.
    Mirrors `SubsumedCheck.checkOf`. -/
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

/-- The justification base: interactions this pass never drops (not recognised as pure checks).
    Mirrors `SubsumedCheck.dropBase`. -/
def denseSubsumedCheckDropBase (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseSubsumedCheckOf bs facts bi).isNone)

/-- Keep `bi` unless it is a recognised pure check whose variable is already bounded `< bound` by a
    retained (base) interaction. Mirrors `SubsumedCheck.dropKeep`. -/
def denseSubsumedCheckDropKeep (bs : BusSemantics p) (facts : BusFacts p bs)
    (base : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseSubsumedCheckOf bs facts bi with
  | some (x, _, bound) =>
    match denseFindVarBound bs facts base x with
    | some b' => !decide (b' ≤ bound)
    | none => true
  | none => true

/-- The runtime transform: drop every pure single-value range check whose bound is already
    entailed by a stronger-or-equal retained stateless check on the same variable. Mirrors
    `SubsumedCheck.subsumedCheckDropPass`'s computed output (dropping its `PassCorrect` term). -/
def denseSubsumedCheckDropF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseSubsumedCheckDropKeep bs facts (denseSubsumedCheckDropBase bs facts d))

end ApcOptimizer.Dense
