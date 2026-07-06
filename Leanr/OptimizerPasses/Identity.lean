import Leanr.OptimizerPasses.Basic

set_option autoImplicit false

variable {p : ℕ}

/-! # The identity pass

The trivial optimization pass: it returns the constraint system unchanged. It exists as the
template for real passes and as the seed of the pipeline while no optimization is implemented
yet. A real pass looks just like this — a `VerifiedPass p` — but transforms the system and
proves the transformation `PassCorrect` instead of leaning on `VerifiedPass.id`. -/

/-- The identity optimization pass. -/
def identityPass : VerifiedPass p :=
  VerifiedPass.id
