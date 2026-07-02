import Leanr.OptimizerPasses.Basic
import Leanr.OptimizerPasses.FactPass
import Leanr.OptimizerPasses.Identity
import Leanr.OptimizerPasses.ConstantFold
import Leanr.OptimizerPasses.ConstantSubst
import Leanr.OptimizerPasses.TrivialConstraint
import Leanr.OptimizerPasses.ZeroMultBus
import Leanr.OptimizerPasses.Affine
import Leanr.OptimizerPasses.Normalize
import Leanr.OptimizerPasses.DomainProp
import Leanr.OptimizerPasses.TautoBus
import Leanr.OptimizerPasses.MonicScale
import Leanr.OptimizerPasses.MemoryUnify

set_option autoImplicit false

variable {p : ℕ}

/-! # The circuit optimizer

Assembles the optimization passes (from `Leanr/OptimizerPasses/`) into the public `optimizer`,
using the scaffolding in `Leanr/OptimizerPasses/Basic.lean` and `FactPass.lean`. The fact-free
`optimizer` keeps the signature `ConstraintSystem p → BusSemantics p → ConstraintSystem p` so the
size/effectiveness tooling can use it directly; `optimizerWith` additionally consumes proven
`BusFacts` about the given semantics (see `Leanr/BusFacts.lean`) — correctness is identical
(`optimizerWith_correct` states the same two clauses per instance), the facts only widen what
the passes can decide.

**To add an optimization:** write a `VerifiedPass` (or fact-aware `VerifiedPassW`) in a new file
under `Leanr/OptimizerPasses/`, import it here, and `.andThen` it into `pipeline` below. That is
the only edit needed here; the correctness proof follows automatically from the pass's own
`PassCorrect`. -/

/-- The optimization pipeline: the sequence of verified passes that make up the optimizer.
    Fold once, then iterate the cleanup cycle to a fixpoint: solve one linear constraint for a
    unit-coefficient variable and substitute it away, substitute one variable forced by
    finite-domain enumeration (boolean/one-hot case analysis, bus-fact domains, probed bus
    obligations; prime `p` only), re-fold, drop trivially-true constraints, drop
    zero-multiplicity bus interactions, drop stateless interactions whose constant message
    satisfies the bus table, and add the receive-equals-send equations entailed by the memory
    discipline. (Affine substitution subsumes constant substitution.) Finally,
    canonicalize: scale every constraint's affine factors to monic form (zero-set preserving)
    and re-fold. Extend it by composing passes with `.andThen`. -/
def pipeline : VerifiedPassW p :=
  constantFoldPass.withFacts.andThen
    (((((((((affineSubstPass.withFacts.andThen domainPropPass).andThen
      normalizePass.withFacts).andThen constantFoldPass.withFacts).andThen
      trivialConstraintDropPass.withFacts).andThen zeroMultBusDropPass.withFacts).andThen
      tautoBusDropPass.withFacts).andThen memoryUnifyPass).iterate 32).andThen
      (monicScalePass.withFacts.andThen constantFoldPass.withFacts))

/-- The fact-aware circuit optimizer: run the pipeline with proven knowledge about the bus
    semantics and project out the resulting constraint system. -/
def optimizerWith (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    ConstraintSystem p :=
  (pipeline cs bs facts).val

/-- The fact-aware optimizer is correct: its output is equivalent to its input and preserves
    invariants — the same two clauses `optimizerMaintainsCorrectness` demands, stated per
    instance because nontrivial facts are tied to one semantics. -/
theorem optimizerWith_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    ((optimizerWith cs bs facts).equivalentTo cs bs) ∧
      (cs.guaranteesInvariants bs → (optimizerWith cs bs facts).guaranteesInvariants bs) :=
  (pipeline cs bs facts).property

/-- The fact-free circuit optimizer (public signature fixed for the tooling/snapshot). -/
def optimizer (cs : ConstraintSystem p) (busSemantics : BusSemantics p) : ConstraintSystem p :=
  optimizerWith cs busSemantics (BusFacts.trivial busSemantics)

/-- The optimizer maintains correctness. This is just the proof carried by `pipeline`. -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) optimizer :=
  fun cs busSemantics => (pipeline cs busSemantics (BusFacts.trivial busSemantics)).property
