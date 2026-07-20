import ApcOptimizer.Implementation.OptimizerPasses.BoxRewriteProof
import ApcOptimizer.Implementation.OptimizerPasses.FxSubstProof

set_option autoImplicit false

/-! # Dense `flagFold` composite assembly (Task 3, busUnify cluster, chunk S5)

This module assembles the four native dense flagFold sub-passes into the single
`DenseVerifiedPassW` composite `denseFlagFoldPass'`, mirroring the spec's `flagFoldPass'`
(`OptimizerPasses/BoxRewrite.lean`):

```
fxSubstPass → boxRewritePass b → boxTautoDropPass → pointwiseDupDropPass
```

The four dense sub-passes are all landed native proofs:

* `denseFxSubstPass pw` — `Dense/FxSubstNativeProof.lean` (part A, facts-consuming).
* `denseBoxRewritePass pw b` — `Dense/BoxRewriteNativeProof.lean` (part B, takes the box bound `b`,
  carries NO own degree guard).
* `denseBoxTautoDropPass pw` — `Dense/FlagFoldDropsNativeProof.lean` (part C).
* `densePointwiseDupDropPass pw` — `Dense/FlagFoldDropsNativeProof.lean` (part D).

## Composition and the single degree guard

Composition uses the existing dense chain combinator `DenseVerifiedPassW.andThen`
(`Dense/Pass.lean`), which threads the registry, concatenates dense derivations, and composes the
per-sub-pass `PassCorrect` certificates — exactly the plumbing the spec's `VerifiedPassW.andThen`
performs (the dense sub-passes are already `DenseVerifiedPassW`, so no `.withFacts` lifting is
needed, unlike the spec's fact-free `VerifiedPass` sub-passes).

Crucially, **no per-sub-pass `guardDegree` is inserted here**: box-rewrite intermediates
legitimately exceed the degree bound by design (see `FlagFold.lean:982`), so guarding a sub-pass
would wrongly abort the chain. The whole composite is wrapped under ONE `guardDegree` at the
selector (`denseImpl`, `Implementation/Optimizer.lean`), matching the spec's
`(flagFoldPass' pw b).guardDegree b` schedule entry. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- **The native dense `flagFold` composite** — the dense mirror of the spec's `flagFoldPass'`
    (`OptimizerPasses/BoxRewrite.lean`). Substitute the entailed nonlinear interpolations
    (`fxSubst`), rewrite the over-bound survivors multilinearly (`boxRewrite b`), then collect the
    box tautologies (`boxTautoDrop`) and pointwise stateless-check duplicates (`pointwiseDupDrop`),
    composed left-to-right with the dense chain combinator `DenseVerifiedPassW.andThen`. Each
    sub-pass carries its own native `DensePassCorrect` (through `ofNative`); the composite's
    correctness is their `PassCorrect.andThen` composition, threaded by `andThen`. Unguarded here —
    the whole chain runs under ONE `guardDegree b` at the selector, since box-rewrite intermediates
    legitimately exceed the bound. -/
def denseFlagFoldPass' (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  (denseFxSubstPass pw).andThen (denseBoxRewritePass pw b)
    |>.andThen (denseBoxTautoDropPass pw)
    |>.andThen (densePointwiseDupDropPass pw)

end ApcOptimizer.Dense
