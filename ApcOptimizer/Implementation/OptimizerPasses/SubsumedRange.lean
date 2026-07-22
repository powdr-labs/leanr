import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Dense subsumed range-check removal (Task 3 — impl)

Dense, `VarId`-native transliteration of the reference `SubsumedRange` pass's *runtime*
definitions (`rangeCheck?`, `dropBase`, `dropKeep`, and the pass's computed output). This file is
**impl-only**: no theorem/lemma from the spec file is ported (`rangeCheck?_spec`,
`rangeCheck?_stateless`, `rangeCheck?_accepted`, and the pass's `filterBusEntailed_correct`-built
`PassCorrect` proof are all proof-side, the prover's job), and no `DenseVerifiedPassW`/
`DensePassCorrect` wrapper is built here — the runtime transform `denseSubsumedRangeDropF` is
shaped like `denseSubsumedCheckDropF` (`SubsumedCheck.lean`): this pass, like its spec counterpart,
is unconditional in `p` and consumes `facts` directly, so the prover wraps it directly with
`DenseVerifiedPassW.ofNative`.

## Reuse map (not re-derived)

* `denseFindVarBound` (`Dense/RootPairUnify.lean`, itself built from `denseInteractionBound` /
  `Dense/DigitFold.lean`) is *exactly* the dense `findVarBound` (`DomainProp.lean:590`) the spec
  `dropKeep` consumes for its non-circular justification base — reused unchanged, not re-derived.
* `DenseExpr.constValue?` (`Dense/DropPasses.lean`) is the dense `Expression.constValue?`, used
  exactly as the spec `rangeCheck?` uses it.
* `DenseConstraintSystem.filterBus` (`Dense/Rewrite.lean`) is the dense `ConstraintSystem.filterBus`
  the pass's `.out` is built from.
* `BusFacts`/`BusSemantics` are representation-independent (their signatures only mention `Nat`/
  `ZMod p`/patterns, never `Variable`/`Expression`), so `facts.varRangeBus` is consumed directly,
  unchanged, exactly as the spec pass does. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognize a single-variable range check `[x, width]` (multiplicity `1`) on a `varRangeBus`
    bus whose width is a *satisfiable* constant (`width.val ≤ 17`), returning the checked variable
    and the width constant. Mirrors `SubsumedRange.rangeCheck?`. -/
def denseSubsumedRangeCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (VarId × ZMod p) :=
  match bi.payload with
  | [v, c] =>
    match v with
    | DenseExpr.var x =>
      match c.constValue? with
      | some cv =>
        if facts.varRangeBus bi.busId = true ∧ bi.multiplicity = DenseExpr.const 1
            ∧ cv.val ≤ 17 then some (x, cv) else none
      | none => none
    | _ => none
  | _ => none

/-- The justification base: interactions this pass can never drop (not recognized as
    single-variable range checks). Mirrors `SubsumedRange.dropBase`. -/
def denseSubsumedRangeDropBase (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseSubsumedRangeCheck? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized range check `[x, w]` whose variable is already bounded
    `< 2^w` by a retained (base) interaction. Mirrors `SubsumedRange.dropKeep`. -/
def denseSubsumedRangeDropKeep (bs : BusSemantics p) (facts : BusFacts p bs)
    (base : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseSubsumedRangeCheck? bs facts bi with
  | some (x, cv) =>
    match denseFindVarBound bs facts base x with
    | some b' => !decide (b' ≤ 2 ^ cv.val)
    | none => true
  | none => true

/-- The runtime transform: drop every variable range check whose bound is already entailed by a
    stronger-or-equal retained stateless check on the same variable. Mirrors
    `SubsumedRange.subsumedRangeDropPass`'s computed output (dropping its `PassCorrect` term). -/
def denseSubsumedRangeDropF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseSubsumedRangeDropKeep bs facts (denseSubsumedRangeDropBase bs facts d))

end ApcOptimizer.Dense
