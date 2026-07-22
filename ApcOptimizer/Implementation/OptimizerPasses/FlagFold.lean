import ApcOptimizer.Implementation.OptimizerPasses.BoxRewriteProof
import ApcOptimizer.Implementation.OptimizerPasses.FxSubstProof

set_option autoImplicit false

/-! # Dense `flagFold` composite assembly

This module assembles the four dense flagFold sub-passes into the single `DenseVerifiedPassW`
composite `denseFlagFoldPass'`:

```
fxSubstPass → boxRewritePass b → boxTautoDropPass → pointwiseDupDropPass
```

The four dense sub-passes, each with its own `DensePassCorrect` proof:

* `denseFxSubstPass pw` — `FxSubstProof.lean` (part A, facts-consuming).
* `denseBoxRewritePass pw b` — `BoxRewriteProof.lean` (part B, takes the box bound `b`, carries NO
  own degree guard).
* `denseBoxTautoDropPass pw` — `FlagFoldDropsProof.lean` (part C).
* `densePointwiseDupDropPass pw` — `FlagFoldDropsProof.lean` (part D).

## Composition and the single degree guard

Composition uses the dense chain combinator `DenseVerifiedPassW.andThen` (`Pass.lean`), which
threads the registry, concatenates dense derivations, and composes the per-sub-pass
`DensePassCorrect` certificates.

Crucially, **no per-sub-pass `guardDegree` is inserted here**: box-rewrite intermediates
legitimately exceed the degree bound by design (see `BoxRewrite.lean`), so guarding a sub-pass
would wrongly abort the chain. The whole composite is wrapped under ONE `guardDegree` at its
`("flagFold", …)` entry in `cleanupPasses` (`Implementation/Optimizer.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- **The dense `flagFold` composite.** Substitute the entailed nonlinear interpolations
    (`fxSubst`), rewrite the over-bound survivors multilinearly (`boxRewrite b`), then collect the
    box tautologies (`boxTautoDrop`) and pointwise stateless-check duplicates (`pointwiseDupDrop`),
    composed left-to-right with the dense chain combinator `DenseVerifiedPassW.andThen`. Each
    sub-pass carries its own `DensePassCorrect` (through `of`); the composite's correctness is
    their composition, threaded by `andThen`. Unguarded here — the whole chain runs under ONE
    `guardDegree b` at its `cleanupPasses` entry, since box-rewrite intermediates legitimately
    exceed the bound. -/
def denseFlagFoldPass' (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  (denseFxSubstPass pw).andThen (denseBoxRewritePass pw b)
    |>.andThen (denseBoxTautoDropPass pw)
    |>.andThen (densePointwiseDupDropPass pw)

end ApcOptimizer.Dense
