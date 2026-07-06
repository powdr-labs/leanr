import Leanr.OptimizerPasses.Basic
import Leanr.OptimizerPasses.FactPass
import Leanr.OptimizerPasses.Identity
import Leanr.OptimizerPasses.ConstantFold
import Leanr.OptimizerPasses.TrivialConstraint
import Leanr.OptimizerPasses.ZeroMultBus
import Leanr.OptimizerPasses.Affine
import Leanr.OptimizerPasses.Gauss
import Leanr.OptimizerPasses.Normalize
import Leanr.OptimizerPasses.DomainProp
import Leanr.OptimizerPasses.DomainBatch
import Leanr.OptimizerPasses.TautoBus
import Leanr.OptimizerPasses.MonicScale
import Leanr.OptimizerPasses.MemoryUnify
import Leanr.OptimizerPasses.BusUnify
import Leanr.OptimizerPasses.Reencode

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
def optimizerWith (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (iters : Nat := 32) : ConstraintSystem p :=
  (pipelineIters iters cs bs facts).val

/-- The fact-aware optimizer is correct: its output `refines` its input (sound, and complete for
    the input's intended executions) and preserves invariants — the same two clauses
    `optimizerMaintainsCorrectness` demands, stated per instance because nontrivial facts are tied
    to one semantics. -/
theorem optimizerWith_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (iters : Nat := 32) :
    ((optimizerWith cs bs facts iters).refines cs bs) ∧
      (cs.guaranteesInvariants bs → (optimizerWith cs bs facts iters).guaranteesInvariants bs) :=
  (pipelineIters iters cs bs facts).property

/-- The fact-free circuit optimizer (public signature fixed for the tooling/snapshot). -/
def optimizer (cs : ConstraintSystem p) (busSemantics : BusSemantics p) : ConstraintSystem p :=
  optimizerWith cs busSemantics (BusFacts.trivial busSemantics)

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWith_respectsDegree (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (iters : Nat := 32)
    (h : cs.withinDegree bs.degreeBound) :
    (optimizerWith cs bs facts iters).withinDegree bs.degreeBound :=
  pipelineIters_respectsDeg iters cs bs facts h

/-- The optimizer respects the zkVM's degree bound. -/
theorem optimizer_respectsDegreeBound : optimizerRespectsDegreeBound (p := p) optimizer :=
  fun cs bs h => pipelineIters_respectsDeg 32 cs bs (BusFacts.trivial bs) h

/-- The optimizer maintains correctness: its output is equivalent to the input and preserves
    invariants (both carried by `pipeline`), and it respects the degree bound. -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) optimizer :=
  ⟨fun cs busSemantics => (pipeline cs busSemantics (BusFacts.trivial busSemantics)).property,
   optimizer_respectsDegreeBound⟩
