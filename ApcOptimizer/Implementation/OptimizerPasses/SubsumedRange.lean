import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Dense subsumed range-check removal

Runtime definitions for `subsumedRangeDrop`: `denseSubsumedRangeCheck?`, `denseSubsumedRangeDropBase`,
`denseSubsumedRangeDropKeep`, and the pass's computed output `denseSubsumedRangeDropF`. This file is
**impl-only**: it carries no soundness lemma, and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper
is built here — the runtime transform is shaped like `denseSubsumedCheckDropF`
(`SubsumedCheck.lean`): unconditional in `p`, consuming `facts` directly, so the prover wraps it
directly with `DenseVerifiedPassW.of`.

## Reuse map

* `denseFindVarBound` (`RootPairUnify.lean`, itself built from `denseInteractionBound`,
  `DigitFold.lean`) is the non-circular justification base `denseSubsumedRangeDropKeep` consumes,
  reused unchanged.
* `DenseExpr.constValue?` (`DropPasses.lean`).
* `DenseConstraintSystem.filterBus` (`Rewrite.lean`) is what the pass's output is built from.
* `BusFacts`/`BusSemantics` are representation-independent (their signatures only mention `Nat`/
  `ZMod p`/patterns), so `facts.varRangeBus` is consumed directly, unchanged. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognize a single-variable range check `[x, width]` (multiplicity `1`) on a `varRangeBus`
    bus whose width is a *satisfiable* constant (`width.val ≤ 17`), returning the checked variable
    and the width constant. -/
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
    single-variable range checks). -/
def denseSubsumedRangeDropBase (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseSubsumedRangeCheck? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized range check `[x, w]` whose variable is already bounded
    `< 2^w` by a retained (base) interaction. -/
def denseSubsumedRangeDropKeep (bs : BusSemantics p) (facts : BusFacts p bs)
    (base : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseSubsumedRangeCheck? bs facts bi with
  | some (x, cv) =>
    match denseFindVarBound bs facts base x with
    | some b' => !decide (b' ≤ 2 ^ cv.val)
    | none => true
  | none => true

/-- The runtime transform: drop every variable range check whose bound is already entailed by a
    stronger-or-equal retained stateless check on the same variable. -/
def denseSubsumedRangeDropF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseSubsumedRangeDropKeep bs facts (denseSubsumedRangeDropBase bs facts d))

end ApcOptimizer.Dense
