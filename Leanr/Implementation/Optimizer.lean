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

/-! ## Evaluation depends only on a system's variables

Two assignments that agree on `cs.vars` are interchangeable for `satisfies`, `admissible`, and
`sideEffects`. These lift the per-expression `Expression.eval_congr` / `BusInteraction.eval_congr`
(proved among the passes) to the system level; the completeness bridge below uses them to swap the
abstract per-pass witness for the concrete `witgen` output the spec now names. -/

/-- A bus interaction of `cs` evaluates the same under assignments agreeing on `cs.vars`. -/
theorem ConstraintSystem.busEval_congr {cs : ConstraintSystem p} {f g : Variable → ZMod p}
    (h : ∀ x ∈ cs.vars, f x = g x) {bi : BusInteraction (Expression p)}
    (hbi : bi ∈ cs.busInteractions) : bi.eval f = bi.eval g :=
  BusInteraction.eval_congr bi f g (fun x hx => by
    simp only [BusInteraction.vars, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨e, he, hx⟩
    · exact h x (ConstraintSystem.mem_vars_of_mult hbi hx)
    · exact h x (ConstraintSystem.mem_vars_of_payload hbi he hx))

theorem ConstraintSystem.satisfies_congr {cs : ConstraintSystem p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.satisfies bs f ↔ cs.satisfies bs g := by
  have imp : ∀ e1 e2 : Variable → ZMod p, (∀ x ∈ cs.vars, e1 x = e2 x) →
      cs.satisfies bs e1 → cs.satisfies bs e2 := by
    intro e1 e2 hh hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · rw [← Expression.eval_congr c e1 e2
        (fun x hx => hh x (ConstraintSystem.mem_vars_of_constraint hc hx))]
      exact hsat.1 c hc
    · have hbe : bi.eval e1 = bi.eval e2 := ConstraintSystem.busEval_congr hh hbi
      show (bi.eval e2).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval e2) = false
      rw [← hbe]
      exact hsat.2 bi hbi
  exact ⟨imp f g h, imp g f (fun x hx => (h x hx).symm)⟩

theorem ConstraintSystem.admissible_congr {cs : ConstraintSystem p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.admissible bs f ↔ cs.admissible bs g := by
  have hmap : (cs.busInteractions.map (fun bi => bi.eval f))
      = (cs.busInteractions.map (fun bi => bi.eval g)) :=
    List.map_congr_left (fun bi hbi => ConstraintSystem.busEval_congr h hbi)
  unfold ConstraintSystem.admissible
  rw [hmap]

theorem ConstraintSystem.sideEffects_congr {cs : ConstraintSystem p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.sideEffects bs f = cs.sideEffects bs g := by
  unfold ConstraintSystem.sideEffects
  refine List.map_congr_left (fun bi hbi => ?_)
  simp only [ConstraintSystem.busEval_congr h (List.mem_of_mem_filter hbi)]

/-- The fact-aware optimizer is correct: its output is a sound replacement for its input (soundness
    plus invariant preservation) and a complete replacement for the input's intended (real-trace)
    executions — running `witgen` on any admissible input trace reproduces a valid witness. These
    are the clauses `Optimizer.isCorrect` demands, stated per instance because nontrivial facts are
    tied to one semantics. -/
theorem optimizerWithBusFacts_correct {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p) :
    (optimizerWithBusFacts facts cs).1.isSoundReplacementOf cs bs ∧
      (optimizerWithBusFacts facts cs).1.isCompleteReplacementOf cs bs (optimizerWithBusFacts facts cs).2 := by
  refine ⟨(pipeline cs bs facts).correct.toSound, ?_⟩
  intro hpow env hadm hsat
  obtain ⟨_himpl, _hinv, _hS, hcomp⟩ := (pipeline cs bs facts).correct
  obtain ⟨env', hsat', hadm', hse, hA, hR⟩ := hcomp env hadm hsat
  have hrec : (pipeline cs bs facts).out.reconstructs (pipeline cs bs facts).derivs env' := by
    have hrec0 : cs.reconstructs [] env :=
      fun u hu hunone => absurd (hpow u hu) (by simp [hunone])
    simpa using hR [] hrec0
  have hagree : ∀ v ∈ (pipeline cs bs facts).out.vars,
      Derivations.witgen (pipeline cs bs facts).derivs env v = env' v := by
    intro v hv
    cases hpw : v.powdrId? with
    | some w =>
        simp only [Derivations.witgen, hpw]
        exact (hA v (by simp [hpw])).symm
    | none =>
        obtain ⟨cm, hm, hxpow, heq⟩ := hrec v hv hpw
        simp only [Derivations.witgen, hpw, hm]
        rw [← heq]
        exact ComputationMethod.eval_congr cm env env' (fun x hx => (hA x (hxpow x hx)).symm)
  refine ⟨(ConstraintSystem.satisfies_congr hagree).mpr hsat',
    (ConstraintSystem.admissible_congr hagree).mpr hadm', ?_⟩
  show cs.sideEffects bs env
      ≈ (pipeline cs bs facts).out.sideEffects bs (Derivations.witgen (pipeline cs bs facts).derivs env)
  rw [ConstraintSystem.sideEffects_congr hagree]
  exact hse

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p)
    (h : cs.withinDegree bs.degreeBound) :
    (optimizerWithBusFacts facts cs).1.withinDegree bs.degreeBound :=
  pipeline_respectsDeg cs bs facts h
