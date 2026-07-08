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
import Leanr.Implementation.OptimizerPasses.BusMerge
import Leanr.Implementation.OptimizerPasses.DisconnectedComponent
import Leanr.Implementation.OptimizerPasses.Reencode

set_option autoImplicit false

variable {p : ℕ}

/-! # The circuit optimizer pipeline (implementation)

Assembles the optimization passes (from `Leanr/Implementation/OptimizerPasses/`) into the
fact-aware `optimizerWithBusFacts`, using the scaffolding in
`Leanr/Implementation/OptimizerPasses/Basic.lean` and `FactPass.lean`. Given proven `BusFacts`
about a bus semantics (see `Leanr/Implementation/BusFacts.lean`) and an iteration bound,
`optimizerWithBusFacts` is a circuit-to-circuit map.

This file is *implementation* — it needs no audit. The user-facing optimizer definitions
(`simpleOptimizer`, `openVmOptimizer`) and the correctness theorems that make up the audited
surface live in `Leanr/Optimizer.lean`; each theorem is a projection of the per-instance
`optimizerWithBusFacts_correct` / `optimizerWithBusFacts_respectsDegree` proved here.

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
    stateless interactions whose constant message satisfies the bus table, merge pairs of
    stateless lookups into one carrying their combined obligation (proven bus facts, e.g. two
    single-byte range checks into one two-byte check), and add the receive-equals-send equations
    entailed by the memory discipline. Finally, canonicalize:
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
    |>.andThen mergeTuplePass.guardDegree
    |>.andThen mergeLookupPass.guardDegree
    |>.andThen busUnifyPass.guardDegree
    |>.andThen disconnectedComponentPass.withFacts.guardDegree
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

/-- The fact-aware circuit optimizer, as a circuit-to-circuit map: given proven `BusFacts` about a
    bus semantics (which fixes the implicit `bs`) and an iteration bound, run the pipeline and
    project out the resulting constraint system. `iters` bounds the number of cleanup cycles (each
    cycle substitutes at most one variable per substitution pass, so large parsed circuits need
    more than the snapshot default). -/
def optimizerWithBusFacts {bs : BusSemantics p} (facts : BusFacts p bs) (iters : Nat := 32)
    (cs : ConstraintSystem p) : ConstraintSystem p :=
  (pipelineIters iters cs bs facts).val

/-- The fact-aware optimizer is correct: its output `refines` its input (sound, and complete for
    the input's intended executions) and preserves invariants — the same two clauses
    `optimizerMaintainsCorrectness` demands, stated per instance because nontrivial facts are tied
    to one semantics. -/
theorem optimizerWithBusFacts_correct {bs : BusSemantics p} (facts : BusFacts p bs)
    (iters : Nat := 32) (cs : ConstraintSystem p) :
    ((optimizerWithBusFacts facts iters cs).refines cs bs) ∧
      (cs.guaranteesInvariants bs → (optimizerWithBusFacts facts iters cs).guaranteesInvariants bs) :=
  (pipelineIters iters cs bs facts).property

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree {bs : BusSemantics p} (facts : BusFacts p bs)
    (iters : Nat := 32) (cs : ConstraintSystem p)
    (h : cs.withinDegree bs.degreeBound) :
    (optimizerWithBusFacts facts iters cs).withinDegree bs.degreeBound :=
  pipelineIters_respectsDeg iters cs bs facts h
