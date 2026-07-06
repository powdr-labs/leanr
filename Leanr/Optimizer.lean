import Leanr.OptimizerPasses.Basic
import Leanr.OptimizerPasses.FactPass
import Leanr.OptimizerPasses.Identity

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

**Trivial baseline.** No optimization is wired in yet: `pipeline` is the identity pass, so the
optimizer returns its input unchanged. Correctness (`optimizer_maintainsCorrectness`) and
degree-safety (`optimizer_respectsDegreeBound`) are nevertheless established here through the
framework — this is the "prove the trivial optimizer correct" milestone, and the fixed target
that every real pass added later must preserve.

**To add an optimization:** write a `VerifiedPass` (or fact-aware `VerifiedPassW`) in a new file
under `Leanr/OptimizerPasses/`, import it here, and `.andThen` it into `pipeline` below. That is
the only edit needed here; the correctness proof follows automatically from the pass's own
`PassCorrect`. -/

/-- The optimization pipeline: the sequence of verified passes that make up the optimizer.
    Trivial for now — the identity pass. Extend it by composing passes with `.andThen`. -/
def pipeline : VerifiedPassW p := identityPass.withFacts

theorem pipeline_respectsDeg : RespectsDeg (pipeline (p := p)) :=
  fun _ _ _ h => h

/-- The fact-aware circuit optimizer: run the pipeline with proven knowledge about the bus
    semantics and project out the resulting constraint system. `iters` bounds the number of
    cleanup cycles once real passes are wired in; the trivial pipeline ignores it. -/
def optimizerWith (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (_iters : Nat := 32) : ConstraintSystem p :=
  (pipeline cs bs facts).val

/-- The fact-aware optimizer is correct: its output `refines` its input (sound, and complete for
    the input's intended executions) and preserves invariants — the same two clauses
    `optimizerMaintainsCorrectness` demands, stated per instance because nontrivial facts are tied
    to one semantics. -/
theorem optimizerWith_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (iters : Nat := 32) :
    ((optimizerWith cs bs facts iters).refines cs bs) ∧
      (cs.guaranteesInvariants bs → (optimizerWith cs bs facts iters).guaranteesInvariants bs) :=
  (pipeline cs bs facts).property

/-- The fact-free circuit optimizer (public signature fixed for the tooling/snapshot). -/
def optimizer (cs : ConstraintSystem p) (busSemantics : BusSemantics p) : ConstraintSystem p :=
  optimizerWith cs busSemantics (BusFacts.trivial busSemantics)

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWith_respectsDegree (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (iters : Nat := 32)
    (h : cs.withinDegree bs.degreeBound) :
    (optimizerWith cs bs facts iters).withinDegree bs.degreeBound :=
  pipeline_respectsDeg cs bs facts h

/-- The optimizer respects the zkVM's degree bound. -/
theorem optimizer_respectsDegreeBound : optimizerRespectsDegreeBound (p := p) optimizer :=
  fun cs bs h => pipeline_respectsDeg cs bs (BusFacts.trivial bs) h

/-- The optimizer maintains correctness: its output refines the input and preserves invariants
    (both carried by `pipeline`), and it respects the degree bound. -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) optimizer :=
  ⟨fun cs busSemantics => (pipeline cs busSemantics (BusFacts.trivial busSemantics)).property,
   optimizer_respectsDegreeBound⟩
