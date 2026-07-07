import Leanr.Implementation.OptimizerPasses.Basic
import Leanr.Implementation.OptimizerPasses.FactPass
import Leanr.Implementation.OptimizerPasses.Identity
import Leanr.Implementation.OptimizerPasses.ConstantFold
import Leanr.Implementation.OptimizerPasses.TrivialConstraint
import Leanr.Implementation.OptimizerPasses.ZeroMultBus
import Leanr.Implementation.OptimizerPasses.Affine
import Leanr.Implementation.OptimizerPasses.Gauss
import Leanr.Implementation.OptimizerPasses.Normalize
import Leanr.Implementation.OptimizerPasses.DomainProp
import Leanr.Implementation.OptimizerPasses.DomainBatch
import Leanr.Implementation.OptimizerPasses.TautoBus
import Leanr.Implementation.OptimizerPasses.MonicScale
import Leanr.Implementation.OptimizerPasses.MemoryUnify
import Leanr.Implementation.OptimizerPasses.BusUnify
import Leanr.Implementation.OptimizerPasses.Reencode

set_option autoImplicit false

variable {p : ℕ}

/-! # The circuit optimizer pipeline (implementation)

Assembles the optimization passes (from `Leanr/Implementation/OptimizerPasses/`) into the
fact-aware `optimizerWithBusFacts`, using the scaffolding in
`Leanr/Implementation/OptimizerPasses/Basic.lean` and `FactPass.lean`. `optimizerWithBusFacts`
consumes proven `BusFacts` about the given semantics (see `Leanr/Implementation/BusFacts.lean`);
`BusFacts.trivial` recovers the fact-free `optimizer`, which keeps the signature
`ConstraintSystem p → BusSemantics p → ConstraintSystem p` so the size/effectiveness tooling can
use it directly.

This file is *implementation* — it needs no audit. The correctness theorems that make up the
audited surface (`optimizerWithBusFacts_maintainsCorrectness`, `optimizer_maintainsCorrectness`,
and the OpenVM instance `openVmOptimizer`) live in `Leanr/Optimizer.lean`; each is a projection of
the per-instance `optimizerWithBusFacts_correct` / `optimizerWithBusFacts_respectsDegree` proved
here.

**To add an optimization:** write a `VerifiedPass` (or fact-aware `VerifiedPassW`) in a new file
under `Leanr/Implementation/OptimizerPasses/`, import it here, and `.andThen` it into `pipeline`
below. That is the only edit needed here; the correctness proof follows automatically from the
pass's own `PassCorrect`. -/

/-- The optimization pipeline: the sequence of verified passes that make up the optimizer.
    Fold once, then iterate the cleanup cycle (`iters` times; see `pipeline` for the default):
    batch-eliminate every variable solvable from a linear constraint with a unit-coefficient
    pivot (`gaussElimPass` — one simultaneous substitution per cycle), normalize and fold,
    substitute one variable forced by finite-domain enumeration (boolean/one-hot case
    analysis, bus-fact domains, probed bus obligations; prime `p` only), re-normalize and
    re-fold, drop trivially-true constraints, drop zero-multiplicity bus interactions, drop
    stateless interactions whose constant message satisfies the bus table, and add the
    receive-equals-send equations entailed by the memory discipline. Finally, canonicalize:
    scale every constraint's affine factors to monic form (zero-set preserving) and re-fold.
    Extend it by composing passes with `.andThen`. -/
def cleanupCycle : VerifiedPassW p :=
  gaussElimPass.withFacts.guardDegree
    |>.andThen normalizePass.withFacts.guardDegree
    |>.andThen constantFoldPass.withFacts.guardDegree
    |>.andThen domainBatchPass.guardDegree
    |>.andThen normalizePass.withFacts.guardDegree
    |>.andThen constantFoldPass.withFacts.guardDegree
    |>.andThen trivialConstraintDropPass.withFacts.guardDegree
    |>.andThen zeroMultBusDropPass.withFacts.guardDegree
    |>.andThen tautoBusDropPass.withFacts.guardDegree
    |>.andThen busUnifyPass.guardDegree
    |>.andThen reencodePass.withFacts.guardDegree

theorem cleanupCycle_respectsDeg : RespectsDeg (cleanupCycle (p := p)) := by
  repeat' apply VerifiedPassW.andThen_respectsDeg
  all_goals exact VerifiedPassW.guardDegree_respectsDeg _

def pipelineIters (iters : Nat) : VerifiedPassW p :=
  constantFoldPass.withFacts.guardDegree
    |>.andThen (cleanupCycle.iterateStable iters)
    |>.andThen monicScalePass.withFacts.guardDegree
    |>.andThen constantFoldPass.withFacts.guardDegree

theorem pipelineIters_respectsDeg (iters : Nat) :
    RespectsDeg (pipelineIters (p := p) iters) := by
  unfold pipelineIters
  repeat' apply VerifiedPassW.andThen_respectsDeg
  · exact VerifiedPassW.guardDegree_respectsDeg _
  · exact VerifiedPassW.iterateStable_respectsDeg cleanupCycle_respectsDeg iters
  · exact VerifiedPassW.guardDegree_respectsDeg _
  · exact VerifiedPassW.guardDegree_respectsDeg _

/-- `pipelineIters` with the default cleanup-cycle count. -/
def pipeline : VerifiedPassW p := pipelineIters 32

/-- The fact-aware circuit optimizer: run the pipeline with proven knowledge about the bus
    semantics and project out the resulting constraint system. `iters` bounds the number of
    cleanup cycles (each cycle substitutes at most one variable per substitution pass, so large
    parsed circuits need more than the snapshot default). -/
def optimizerWithBusFacts (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (iters : Nat := 32) : ConstraintSystem p :=
  (pipelineIters iters cs bs facts).val

/-- The fact-aware optimizer is correct: its output `refines` its input (sound, and complete for
    the input's intended executions) and preserves invariants — the same two clauses
    `optimizerMaintainsCorrectness` demands, stated per instance because nontrivial facts are tied
    to one semantics. -/
theorem optimizerWithBusFacts_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (iters : Nat := 32) :
    ((optimizerWithBusFacts cs bs facts iters).refines cs bs) ∧
      (cs.guaranteesInvariants bs → (optimizerWithBusFacts cs bs facts iters).guaranteesInvariants bs) :=
  (pipelineIters iters cs bs facts).property

/-- The fact-free circuit optimizer: the fixed signature
    `ConstraintSystem p → BusSemantics p → ConstraintSystem p` consumed by the size/effectiveness
    tooling and by the top-level `optimizer_maintainsCorrectness` (in `Leanr/Optimizer.lean`). -/
def optimizer (cs : ConstraintSystem p) (busSemantics : BusSemantics p) : ConstraintSystem p :=
  optimizerWithBusFacts cs busSemantics (BusFacts.trivial busSemantics)

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (iters : Nat := 32)
    (h : cs.withinDegree bs.degreeBound) :
    (optimizerWithBusFacts cs bs facts iters).withinDegree bs.degreeBound :=
  pipelineIters_respectsDeg iters cs bs facts h
