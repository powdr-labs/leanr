import Leanr.OptimizerPasses.Basic
import Leanr.OptimizerPasses.Identity
import Leanr.OptimizerPasses.ConstantFold
import Leanr.OptimizerPasses.ConstantSubst
import Leanr.OptimizerPasses.TrivialConstraint
import Leanr.OptimizerPasses.ZeroMultBus
import Leanr.OptimizerPasses.Affine
import Leanr.OptimizerPasses.Normalize
import Leanr.OptimizerPasses.DomainProp

set_option autoImplicit false

variable {p : ℕ}

/-! # The circuit optimizer

Assembles the optimization passes (from `Leanr/OptimizerPasses/`) into the public `optimizer`,
using the scaffolding in `Leanr/OptimizerPasses/Basic.lean`. The optimizer's signature is fixed at
`ConstraintSystem p → BusSemantics p → ConstraintSystem p` so the size/effectiveness tooling and
the snapshot test can use it directly; correctness travels separately via `pipeline`'s carried
proof.

**To add an optimization:** write a `VerifiedPass` in a new file under `Leanr/OptimizerPasses/`,
import it here, and `.andThen` it into `pipeline` below. That is the only edit needed here; the
correctness proof follows automatically from the pass's own `PassCorrect`. -/

/-- The optimization pipeline: the sequence of verified passes that make up the optimizer.
    Fold once, then iterate the cleanup cycle to a fixpoint: solve one linear constraint for a
    unit-coefficient variable and substitute it away, substitute one variable forced by
    finite-domain enumeration (boolean/one-hot case analysis; prime `p` only), re-fold, drop
    trivially-true constraints, drop zero-multiplicity bus interactions. (Affine substitution
    subsumes constant substitution.) Extend it by composing passes with `.andThen`. -/
def pipeline : VerifiedPass p :=
  constantFoldPass.andThen
    ((((((affineSubstPass.andThen domainPropPass).andThen normalizePass).andThen
      constantFoldPass).andThen trivialConstraintDropPass).andThen zeroMultBusDropPass).iterate 24)

/-- The circuit optimizer: run the pipeline and project out the resulting constraint system. -/
def optimizer (cs : ConstraintSystem p) (busSemantics : BusSemantics p) : ConstraintSystem p :=
  (pipeline cs busSemantics).val

/-- The optimizer maintains correctness. This is just the proof carried by `pipeline`. -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) optimizer :=
  fun cs busSemantics => (pipeline cs busSemantics).property
