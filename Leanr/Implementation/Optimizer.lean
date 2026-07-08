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
import Leanr.Implementation.OptimizerPasses.BusPairCancel
import Leanr.Implementation.OptimizerPasses.DisconnectedComponent
import Leanr.Implementation.OptimizerPasses.Reencode
import Leanr.Implementation.OptimizerPasses.DomainFold

set_option autoImplicit false

variable {p : ℕ}

/-! # The circuit optimizer pipeline (implementation)

Assembles the optimization passes (from `Leanr/Implementation/OptimizerPasses/`) into the
fact-aware `optimizerWithBusFacts`, using the scaffolding in
`Leanr/Implementation/OptimizerPasses/Basic.lean` and `FactPass.lean`. Given proven `BusFacts`
about a bus semantics (see `Leanr/Implementation/BusFacts.lean`),
`optimizerWithBusFacts` is a circuit-to-circuit map.

This file is *implementation* — it needs no audit. The user-facing optimizer definitions
(`simpleOptimizer`, `openVmOptimizer`) and the correctness theorems that make up the audited
surface live in `Leanr/Optimizer.lean`; each theorem is a projection of the per-instance
`optimizerWithBusFacts_correct` / `optimizerWithBusFacts_respectsDegree` proved here.

**To add an optimization:** write a `VerifiedPass` (or fact-aware `VerifiedPassW`) in a new file
under `Leanr/Implementation/OptimizerPasses/`, import it here, and `.andThen` it into `cleanupCycle`
below. That is the only edit needed here; the correctness proof follows automatically from the
pass's own `PassCorrect`. -/

/-- The optimization pipeline: the sequence of verified passes that make up the optimizer.
    Fold once, then iterate the cleanup cycle to a fixpoint (`iterateToFixpoint`, no budget):
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
    |>.andThen domainFoldPass.withFacts.guardDegree
    |>.andThen busUnifyPass.guardDegree
    |>.andThen (VerifiedPassW.guardDegree (iterateToFixpoint busPairCancelPass))
    |>.andThen disconnectedComponentPass.withFacts.guardDegree
    |>.andThen reencodePass.withFacts.guardDegree

theorem cleanupCycle_respectsDeg : RespectsDeg (cleanupCycle (p := p)) := by
  repeat' apply VerifiedPassW.andThen_respectsDeg
  all_goals exact VerifiedPassW.guardDegree_respectsDeg _

def pipeline : VerifiedPassW p :=
  constantFoldPass.withFacts.guardDegree
    |>.andThen (iterateToFixpoint cleanupCycle)
    |>.andThen monicScalePass.withFacts.guardDegree
    |>.andThen constantFoldPass.withFacts.guardDegree

theorem pipeline_respectsDeg : RespectsDeg (pipeline (p := p)) := by
  unfold pipeline
  repeat' apply VerifiedPassW.andThen_respectsDeg
  · exact VerifiedPassW.guardDegree_respectsDeg _
  · exact iterateToFixpoint_respectsDeg cleanupCycle_respectsDeg
  · exact VerifiedPassW.guardDegree_respectsDeg _
  · exact VerifiedPassW.guardDegree_respectsDeg _

/-- The fact-aware circuit optimizer: given proven `BusFacts` about a bus semantics (which fixes the
    implicit `bs`), run the pipeline and return the resulting constraint system together with the
    `Derivations` for its newly-introduced variables. The cleanup loop (`iterateToFixpoint`) takes no
    iteration count: it runs the cleanup cycle until it stops strictly shrinking the lexicographic
    size key `(vars, bus, constraints)`, provably terminating on that well-founded measure — no
    budget to set, and no cap a large basic block could exceed. -/
def optimizerWithBusFacts {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p) : ConstraintSystem p × Derivations p :=
  let r := pipeline cs bs facts
  (r.out, r.derivs)

/-- The fact-aware optimizer is correct: its output `refines` its input (sound, and complete for
    the input's intended executions with the returned witness-reconstruction data) and preserves
    invariants — the same clauses `optimizerMaintainsCorrectness` demands, stated per instance
    because nontrivial facts are tied to one semantics. -/
theorem optimizerWithBusFacts_correct {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p) :
    ((optimizerWithBusFacts facts cs).1.refines cs bs (optimizerWithBusFacts facts cs).2) ∧
      (cs.guaranteesInvariants bs → (optimizerWithBusFacts facts cs).1.guaranteesInvariants bs) :=
  ⟨(pipeline cs bs facts).correct.toRefines, (pipeline cs bs facts).correct.2.1⟩

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p)
    (h : cs.withinDegree bs.degreeBound) :
    (optimizerWithBusFacts facts cs).1.withinDegree bs.degreeBound :=
  pipeline_respectsDeg cs bs facts h
