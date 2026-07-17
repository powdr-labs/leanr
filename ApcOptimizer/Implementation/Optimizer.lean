import ApcOptimizer.Implementation.OptimizerPasses.Basic
import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.Identity
import ApcOptimizer.Implementation.OptimizerPasses.ConstantFold
import ApcOptimizer.Implementation.OptimizerPasses.TrivialConstraint
import ApcOptimizer.Implementation.OptimizerPasses.ZeroMultBus
import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus
import ApcOptimizer.Implementation.OptimizerPasses.MonicScale
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancel
import ApcOptimizer.Implementation.OptimizerPasses.BytePack
import ApcOptimizer.Implementation.OptimizerPasses.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.DisconnectedComponent
import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.ZeroRegister
import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse
import ApcOptimizer.Implementation.OptimizerPasses.CarryBranch
import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify
import ApcOptimizer.Implementation.OptimizerPasses.BoxRewrite
import ApcOptimizer.Implementation.OptimizerPasses.RedundantByteDrop
import ApcOptimizer.Implementation.OptimizerPasses.ZeroWidthRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.XorEqExtract
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapse

set_option autoImplicit false

variable {p : ℕ}

/-! # The circuit optimizer pipeline (implementation)

Assembles the optimization passes (from `ApcOptimizer/Implementation/OptimizerPasses/`) into the
fact-aware `optimizerWithBusFacts`, using the scaffolding in
`ApcOptimizer/Implementation/OptimizerPasses/Basic.lean` and `FactPass.lean`. Given proven `BusFacts`
about a bus semantics (see `ApcOptimizer/Implementation/BusFacts.lean`),
`optimizerWithBusFacts` is a circuit-to-circuit map.

This file is *implementation* — it needs no audit. The user-facing optimizer definitions
(`simpleOptimizer`, `openVmOptimizer`) and the correctness theorems that make up the audited
surface live in `ApcOptimizer/Optimizer.lean`; each theorem is a projection of the per-instance
`optimizerWithBusFacts_correct` / `optimizerWithBusFacts_respectsDegree` proved here.

**To add an optimization:** write a `VerifiedPass` (or fact-aware `VerifiedPassW`) in a new file
under `ApcOptimizer/Implementation/OptimizerPasses/`, import it here, and add one `(name, pass)`
entry to the `cleanupPasses` list below. That is the only edit needed here; the correctness proof
follows automatically from the pass's own `PassCorrect`. -/

/-- The optimizer runs in three stages: a **prelude** (this list) once, then the `cleanupPasses`
    cycle iterated to a fixpoint, then a **coda** (`codaPasses`) once. These three lists are the
    single source of truth for the pass sequence — `pipeline` folds them and the `profile` CLI
    command (`Main.lean`) times the same lists — so the optimizer and the profiler cannot drift
    apart. The prelude is a single constant-fold that canonicalizes the freshly-parsed system. The
    `String` labels name each pass in the profiler's timing report (irrelevant to behaviour). -/
def preludePasses : List (String × VerifiedPassW p) :=
  [ ("constFold0", constantFoldPass.withFacts.guardDegree) ]

/-- The cleanup-cycle passes as a **labelled list** (one of the three stages; see `preludePasses`).

    Iterate this cycle to a fixpoint (`iterateToFixpoint`, no budget): batch-eliminate every
    variable solvable from a linear constraint with a unit-coefficient pivot (`gaussElimPass` — one
    simultaneous substitution per cycle), normalize and fold, substitute one variable forced by
    finite-domain enumeration (boolean/one-hot case analysis, bus-fact domains, probed bus
    obligations; prime `p` only), re-normalize and re-fold, drop trivially-true constraints, drop
    zero-multiplicity bus interactions, drop stateless interactions whose constant message satisfies
    the bus table, and add the receive-equals-send equations entailed by the memory discipline.

    **To add an optimization:** write a `VerifiedPass` (or fact-aware `VerifiedPassW`) in a new file
    under `ApcOptimizer/Implementation/OptimizerPasses/`, import it above, and add one
    `(name, pass.….guardDegree)` entry to this list. That is the only edit needed here; the
    correctness proof follows automatically from the pass's own `PassCorrect`, and the profiler
    picks up the new label for free (it consumes this same list). -/
def cleanupPasses : List (String × VerifiedPassW p) :=
  -- One primality decision per optimizer run, threaded to every prime-gated pass below (they read
  -- the `Bool` in O(1) instead of re-running `decide (Nat.Prime p)` per invocation per iteration).
  let pw := PrimeWitness.of p
  [ ("zeroWidthRange", (ZeroWidthRange.zeroWidthRangePass pw).guardDegree),
    ("xorEqExtract", XorEqExtract.xorEqExtractPass.guardDegree),
    ("carryBranch", (carryBranchPass pw).guardDegree),
    ("gauss", gaussElimPass.withFacts.guardDegree),
    ("normalize1", normalizePass.withFacts.guardDegree),
    ("constFold1", constantFoldPass.withFacts.guardDegree),
    ("domainBatch", (domainBatchPass pw).guardDegree),
    ("normalize2", normalizePass.withFacts.guardDegree),
    ("constFold2", constantFoldPass.withFacts.guardDegree),
    ("zeroRegister", zeroRegisterPass.guardDegree),
    ("digitFold", DigitFold.digitFoldPass.guardDegree),
    ("oneHotAnnihilate", OneHotAnnihilate.oneHotAnnihilatePass.guardDegree),
    ("hintCollapse", (hintCollapsePass pw).guardDegree),
    ("rootPairUnify", (rootPairUnifyPass pw).guardDegree),
    ("flagUnify", (flagUnifyPass pw).guardDegree),
    ("flagFold", (flagFoldPass' pw).guardDegree),
    ("dedup", dedupPass.withFacts.guardDegree),
    ("trivialConstr", trivialConstraintDropPass.withFacts.guardDegree),
    ("zeroMultBus", zeroMultBusDropPass.withFacts.guardDegree),
    ("tautoBus", tautoBusDropPass.withFacts.guardDegree),
    ("domainFold", (domainFoldPass pw).withFacts.guardDegree),
    ("busUnify", busUnifyPass.guardDegree),
    ("busPairCancel", VerifiedPassW.guardDegree (busPairCancelPass pw false)),
    ("bytePack", VerifiedPassW.guardDegree (iterateToFixpoint ByteCheckPack.byteCheckPackPass)),
    ("disconnected", disconnectedComponentPass.withFacts.guardDegree),
    ("reencode", reencodePass.withFacts.guardDegree) ]

/-- The coda passes (one of the three stages; see `preludePasses`): run once after the cleanup loop
    reaches its fixpoint — drop bytes made redundant by the cleaned-up system, rescale carries to
    monic form, and one final constant-fold. -/
def codaPasses : List (String × VerifiedPassW p) :=
  -- One primality decision per optimizer run (see `cleanupPasses`), for the prime-gated coda passes.
  let pw := PrimeWitness.of p
  [ ("busPairCancelLate", VerifiedPassW.guardDegree (busPairCancelPass pw true)),
    -- Explode packed pair byte checks into singles so `dedupLate` collapses the same value
    -- byte-checked in several pairs and `redundantByteDrop` becomes operand-granular; the
    -- survivors are re-packed by `bytePackLate` below (a pair with nothing to shed round-trips).
    ("splitBytePair", SplitBytePair.splitBytePairPass.guardDegree),
    ("dedupLate", dedupPass.withFacts.guardDegree),
    ("redundantByteDrop", (RedundantByteDrop.redundantByteDropPass pw).guardDegree),
    ("subsumedRange", SubsumedRange.subsumedRangeDropPass.guardDegree),
    ("subsumedCheck", SubsumedCheck.subsumedCheckDropPass.guardDegree),
    -- Tuple/range packing is layout-only and does not unblock other optimizations (powdr likewise
    -- runs global range packing once at the end), so it runs once here, out of the cleanup
    -- fixpoint, after `redundantByteDrop` has dropped droppable byte checks operand-granularly
    -- (packing a byte check early would hide it from the drop, leaving more bus interactions).
    -- The pass drains every packable pair internally, so it needs no fixpoint wrapper.
    ("tupleRange", tupleRangePass.guardDegree),
    ("bytePackLate", VerifiedPassW.guardDegree (iterateToFixpoint ByteCheckPack.byteCheckPackPass)),
    ("monicScale", monicScalePass.withFacts.guardDegree),
    ("constFoldEnd", constantFoldPass.withFacts.guardDegree),
    -- Collapse recognised `sltu x, 1` (seqz) LessThan gadgets to the two-line is-zero gadget,
    -- dropping the four `diff_marker`s + `diff_val`. Runs after `monicScale`, where the cluster
    -- has reached the recognised form.
    ("seqzCollapse", VerifiedPassW.guardDegree (iterateToFixpoint SeqzCollapse.seqzCollapsePass)) ]

/-- Fold a list of passes into one sequential pass (`andThen` left to right; identity on `[]`). -/
def chainPasses (l : List (VerifiedPassW p)) : VerifiedPassW p :=
  l.foldl VerifiedPassW.andThen (fun cs bs _ => ⟨cs, [], PassCorrect.refl cs bs⟩)

/-- The optimizer's cleanup cycle: the `cleanupPasses` folded together in order. See `cleanupPasses`
    for what each pass does and how to extend the cycle. -/
def cleanupCycle : VerifiedPassW p :=
  chainPasses (cleanupPasses.map (·.2))

/-- Folding degree-respecting passes with `andThen` yields a degree-respecting pass. -/
theorem foldl_andThen_respectsDeg :
    ∀ (l : List (VerifiedPassW p)) (init : VerifiedPassW p),
      RespectsDeg init → (∀ f ∈ l, RespectsDeg f) →
      RespectsDeg (l.foldl VerifiedPassW.andThen init)
  | [], _, hinit, _ => by simpa using hinit
  | g :: rest, init, hinit, hall => by
      rw [List.foldl_cons]
      exact foldl_andThen_respectsDeg rest (init.andThen g)
        (VerifiedPassW.andThen_respectsDeg hinit (hall g (List.mem_cons_self ..)))
        (fun f hf => hall f (List.mem_cons_of_mem _ hf))

/-- Any list of degree-respecting passes folds (`chainPasses`) to a degree-respecting pass. -/
theorem chainPasses_respectsDeg {l : List (VerifiedPassW p)} (h : ∀ f ∈ l, RespectsDeg f) :
    RespectsDeg (chainPasses l) := by
  unfold chainPasses
  exact foldl_andThen_respectsDeg _ _ (fun _ _ _ h => h) h

theorem cleanupCycle_respectsDeg : RespectsDeg (cleanupCycle (p := p)) := by
  unfold cleanupCycle
  refine chainPasses_respectsDeg (fun f hf => ?_)
  simp only [cleanupPasses, List.map_cons, List.map_nil] at hf
  fin_cases hf <;> exact VerifiedPassW.guardDegree_respectsDeg _

/-- The circuit optimizer: fold the prelude, iterate the cleanup cycle to a fixpoint
    (`iterateToFixpoint`, no budget), then fold the coda. `pipeline` and the profiler both consume
    `preludePasses` / `cleanupPasses` / `codaPasses`, so they stay in lockstep. -/
def pipeline : VerifiedPassW p :=
  chainPasses (preludePasses.map (·.2))
    |>.andThen (iterateToFixpoint cleanupCycle)
    |>.andThen (chainPasses (codaPasses.map (·.2)))

theorem pipeline_respectsDeg : RespectsDeg (pipeline (p := p)) := by
  unfold pipeline
  refine VerifiedPassW.andThen_respectsDeg (VerifiedPassW.andThen_respectsDeg
    (chainPasses_respectsDeg (fun f hf => ?_))
    (iterateToFixpoint_respectsDeg cleanupCycle_respectsDeg))
    (chainPasses_respectsDeg (fun f hf => ?_))
  · simp only [preludePasses, List.map_cons, List.map_nil] at hf
    fin_cases hf
    exact VerifiedPassW.guardDegree_respectsDeg _
  · simp only [codaPasses, List.map_cons, List.map_nil] at hf
    fin_cases hf <;> exact VerifiedPassW.guardDegree_respectsDeg _

/-- The fact-aware circuit optimizer: given proven `BusFacts` about a bus semantics (which fixes the
    implicit `bs`), run the pipeline and return the resulting constraint system together with the
    `Derivations` for its newly-introduced variables. The cleanup loop (`iterateToFixpoint`) takes no
    iteration count: it runs the cleanup cycle until it stops strictly shrinking the lexicographic
    size key `(vars, bus, constraints)`, provably terminating on that well-founded measure — no
    budget to set, and no cap a large basic block could exceed. -/
def optimizerWithBusFacts {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p) : ConstraintSystem p × Derivations p :=
  let r := pipeline cs bs facts
  -- Drop derivations for variables absent from the output: they are dead (`witgen` never reads them)
  -- and the spec requires every recorded derivation to name an output variable.
  (r.out, r.derivs.filter (fun d => decide (d.1 ∈ r.out.vars)))

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

/-- Filtering the derivations to those naming a variable in `out` leaves `methodFor` unchanged on any
    variable that *is* in `out` — every derivation for such a variable is kept, and a dropped
    derivation can only name a variable outside `out`, hence never the one being queried. -/
theorem Derivations.methodFor_filter {out : List Variable} {v : Variable} (hv : v ∈ out)
    (ds : Derivations p) :
    Derivations.methodFor (ds.filter (fun d => decide (d.1 ∈ out))) v
      = Derivations.methodFor ds v := by
  induction ds with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨u, cm⟩ := hd
    by_cases hu : u ∈ out
    · rw [List.filter_cons_of_pos (by simpa using hu)]
      simp only [Derivations.methodFor, ih]
    · rw [List.filter_cons_of_neg (by simpa using hu)]
      rw [ih, Derivations.methodFor]
      have hne : ¬ u = v := fun h => hu (h ▸ hv)
      simp [hne]

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
  obtain ⟨_himpl, _hinv, hS, hcomp⟩ := (pipeline cs bs facts).correct
  obtain ⟨env', hsat', hadm', hse, hA, hR⟩ := hcomp env hadm hsat
  have hrec : (pipeline cs bs facts).out.reconstructs cs.vars
      (pipeline cs bs facts).derivs env' := by
    have hrec0 : cs.reconstructs cs.vars [] env :=
      fun u hu hunone => absurd (hpow u hu) (by simp [hunone])
    simpa using hR cs.vars (fun v hv _ => hv) [] hrec0
  have hagree : ∀ v ∈ (pipeline cs bs facts).out.vars,
      Derivations.witgen (pipeline cs bs facts).derivs env v = env' v := by
    intro v hv
    cases hpw : v.powdrId? with
    | some w =>
        simp only [Derivations.witgen, hpw]
        exact (hA v (by simp [hpw])).symm
    | none =>
        obtain ⟨cm, hm, hxpow, _hxinput, heq⟩ := hrec v hv hpw
        simp only [Derivations.witgen, hpw, hm]
        rw [← heq]
        exact ComputationMethod.eval_congr cm env env' (fun x hx => (hA x (hxpow x hx)).symm)
  -- The returned derivations are `pipeline …`'s pruned to output variables; on output variables the
  -- pruning leaves `witgen` unchanged (`methodFor_filter`), so `hagree` transports to the pruned list.
  have hagree' : ∀ v ∈ (pipeline cs bs facts).out.vars,
      Derivations.witgen ((pipeline cs bs facts).derivs.filter
        (fun d => decide (d.1 ∈ (pipeline cs bs facts).out.vars))) env v = env' v := by
    intro v hv
    rw [show Derivations.witgen ((pipeline cs bs facts).derivs.filter
          (fun d => decide (d.1 ∈ (pipeline cs bs facts).out.vars))) env v
        = Derivations.witgen (pipeline cs bs facts).derivs env v by
      simp only [Derivations.witgen, Derivations.methodFor_filter hv]]
    exact hagree v hv
  refine ⟨?_, ?_, (ConstraintSystem.satisfies_congr hagree').mpr hsat',
    (ConstraintSystem.admissible_congr hagree').mpr hadm', ?_⟩
  · -- `ds` covers the output columns: reused ones exist in the input (`hS`), derived ones have a
    -- method reading only powdr-ID columns (from the reconstruction), preserved by the pruning.
    intro v hv
    cases hpw : v.powdrId? with
    | some w => exact hS v hv (by simp [hpw])
    | none =>
        obtain ⟨cm, hm, _hxpow, hxinput, _⟩ := hrec v hv hpw
        exact ⟨cm, (Derivations.methodFor_filter hv _).trans hm, hxinput⟩
  · -- Every recorded derivation names an output variable — that is exactly the pruning predicate.
    intro d hd
    simpa using (List.mem_filter.mp hd).2
  · show cs.sideEffects bs env
        ≈ (pipeline cs bs facts).out.sideEffects bs (Derivations.witgen
            ((pipeline cs bs facts).derivs.filter
              (fun d => decide (d.1 ∈ (pipeline cs bs facts).out.vars))) env)
    rw [ConstraintSystem.sideEffects_congr hagree']
    exact hse

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p)
    (h : cs.withinDegree bs.degreeBound) :
    (optimizerWithBusFacts facts cs).1.withinDegree bs.degreeBound :=
  pipeline_respectsDeg cs bs facts h
