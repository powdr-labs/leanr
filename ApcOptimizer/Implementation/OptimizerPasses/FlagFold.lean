import ApcOptimizer.Implementation.OptimizerPasses.BoxRewriteProof
import ApcOptimizer.Implementation.OptimizerPasses.FxSubstProof

set_option autoImplicit false

/-! # Dense `flagFold` composite assembly

Assembles the four dense flagFold sub-passes into `denseFlagFoldPass'`:
`fxSubst → boxRewrite b → boxTautoDrop → pointwiseDupDrop`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The dense `flagFold` composite: substitute entailed nonlinear interpolations (`fxSubst`),
    rewrite over-bound survivors multilinearly (`boxRewrite b`), then drop box tautologies
    (`boxTautoDrop`) and pointwise stateless-check duplicates (`pointwiseDupDrop`). Unguarded here —
    box-rewrite intermediates legitimately exceed the bound — so the whole chain runs under ONE
    `guardDegree b` at its `cleanupPasses` entry. -/
def denseFlagFoldPass' (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  (denseFxSubstPass pw).andThen (denseBoxRewritePass pw b)
    |>.andThen (denseBoxTautoDropPass pw)
    |>.andThen (densePointwiseDupDropPass pw)

end ApcOptimizer.Dense
