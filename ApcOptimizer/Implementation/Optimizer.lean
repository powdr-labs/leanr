import ApcOptimizer.Implementation.OptimizerPasses.Basic
import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.MonicScale
import ApcOptimizer.Implementation.OptimizerPasses.MonicScaleProof
import ApcOptimizer.Implementation.OptimizerPasses.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.TupleRangeProof
import ApcOptimizer.Implementation.OptimizerPasses.DisconnectedComponent
import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse
import ApcOptimizer.Implementation.OptimizerPasses.RedundantByteDrop
import ApcOptimizer.Implementation.OptimizerPasses.RedundantByteDropProof
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedRangeProof
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheckProof
import ApcOptimizer.Implementation.OptimizerPasses.XorEqExtract
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePairProof
import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapse
import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapseProof
import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.RangeForceZero
import ApcOptimizer.Implementation.OptimizerPasses.RangeBool
import ApcOptimizer.Implementation.OptimizerPasses.IdentitySubst
import ApcOptimizer.Implementation.OptimizerPasses.IdentitySubstProof
import ApcOptimizer.Implementation.OptimizerPasses.DenseUmbrella

set_option autoImplicit false

open ApcOptimizer.Dense

variable {p : ℕ}

/-! # The circuit optimizer pipeline (implementation)

Assembles the passes (`OptimizerPasses/`) into the fact-aware `optimizerWithBusFacts`. The audited
correctness theorems in `ApcOptimizer/Optimizer.lean` are projections of `optimizerWithBusFacts_correct` /
`optimizerWithBusFacts_respectsDegree` proved here. To add a pass, see AGENTS.md → "Adding an optimization". -/

/-- Stage 1 of 3 (`preludePasses`, `cleanupPasses`, `codaPasses`): run once to canonicalize the
    freshly-parsed system. The three lists are the single source of truth for the pass sequence —
    `pipeline` folds them and the `profile` CLI (`Main.lean`) times the same lists, so they cannot
    drift. `String` labels name passes in the profiler only. -/
def preludePasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  [ ("constFold0", DenseVerifiedPassW.guardDegree b denseConstantFoldPass) ]

/-- Stage 2 of 3 (see `preludePasses`): the cleanup schedule, iterated to a fixpoint
    (`denseIterateToFixpoint`, no budget). Each entry's optimization is documented at its own
    definition. To add a pass, append one `(name, pass.guardDegree b)` entry here (AGENTS.md →
    "Adding an optimization"). -/
def cleanupPasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  -- One primality decision per run, threaded to every prime-gated pass (each reads the `Bool` in
  -- O(1) instead of re-running `decide (Nat.Prime p)`).
  let pw := PrimeWitness.of p
  [ ("zeroWidthRange", DenseVerifiedPassW.guardDegree b (denseZeroWidthRangePass pw)),
    ("rangeForceZero", DenseVerifiedPassW.guardDegree b denseRangeForceZeroPass),
    ("rangeBool", DenseVerifiedPassW.guardDegree b (denseRangeBoolPass pw)),
    ("xorEqExtract", DenseVerifiedPassW.guardDegree b denseXorEqExtractPass),
    ("carryBranch", DenseVerifiedPassW.guardDegree b (denseCarryBranchPass pw)),
    ("gauss", DenseVerifiedPassW.guardDegree b denseGaussElimPass),
    ("normalize1", DenseVerifiedPassW.guardDegree b denseNormalizePass),
    ("constFold1", DenseVerifiedPassW.guardDegree b denseConstantFoldPass),
    ("domainBatch", DenseVerifiedPassW.guardDegree b (denseDomainBatchPassV pw)),
    ("normalize2", DenseVerifiedPassW.guardDegree b denseNormalizePass),
    ("constFold2", DenseVerifiedPassW.guardDegree b denseConstantFoldPass),
    ("zeroRegister", DenseVerifiedPassW.guardDegree b denseZeroRegisterPass),
    ("intervalForce", DenseVerifiedPassW.guardDegree b denseIntervalForcePass),
    ("digitFold", DenseVerifiedPassW.guardDegree b denseDigitFoldPass),
    ("oneHotAnnihilate", DenseVerifiedPassW.guardDegree b denseOneHotAnnihilatePass),
    ("hintCollapse", DenseVerifiedPassW.guardDegree b (denseHintCollapsePass pw)),
    ("rootPairUnify", DenseVerifiedPassW.guardDegree b (denseRootPairUnifyPass pw)),
    ("flagUnify", DenseVerifiedPassW.guardDegree b (denseFlagUnifyPass pw)),
    ("flagFold", DenseVerifiedPassW.guardDegree b (denseFlagFoldPass' pw b)),
    ("dedup", DenseVerifiedPassW.guardDegree b denseDedupPass),
    ("trivialConstr", DenseVerifiedPassW.guardDegree b denseTrivialConstraintDropPass),
    ("zeroMultBus", DenseVerifiedPassW.guardDegree b denseZeroMultBusDropPass),
    ("tautoBus", DenseVerifiedPassW.guardDegree b denseTautoBusDropPass),
    ("domainFold", DenseVerifiedPassW.guardDegree b (denseDomainFoldPassV pw)),
    ("busUnify", DenseVerifiedPassW.guardDegree b denseBusUnifyPass),
    ("busPairCancel", DenseVerifiedPassW.guardDegree b (denseBusPairCancelPass pw false)),
    ("bytePack", DenseVerifiedPassW.guardDegree b denseByteCheckPackPass),
    ("disconnected", DenseVerifiedPassW.guardDegree b denseDisconnectedPass),
    ("reencode", DenseVerifiedPassW.guardDegree b (denseReencodePass pw b)) ]

/-- Stage 3 of 3 (see `preludePasses`): run once after the cleanup fixpoint. Order matters — the
    inline notes below flag the non-obvious sequencing; each pass's own definition documents what it
    does. -/
def codaPasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  let pw := PrimeWitness.of p
  [ ("busPairCancelLate", DenseVerifiedPassW.guardDegree b (denseBusPairCancelPass pw true)),
    -- Explode packed pair byte checks into singles so `dedupLate`/`redundantByteDrop` act
    -- operand-granularly; `bytePackLate` re-packs the survivors.
    ("splitBytePair", DenseVerifiedPassW.guardDegree b denseSplitBytePairPass),
    -- Rename OR-identity results to their operand before drop/pack, exposing degenerate byte checks
    -- (`[or, x, x, 0]`) for `dedupLate`/`redundantByteDrop`/`bytePackLate`.
    ("identitySubst", DenseVerifiedPassW.guardDegree b denseIdentitySubstPass),
    ("dedupLate", DenseVerifiedPassW.guardDegree b denseDedupPass),
    ("redundantByteDrop", DenseVerifiedPassW.guardDegree b (denseRedundantByteDropPass pw)),
    ("subsumedRange", DenseVerifiedPassW.guardDegree b denseSubsumedRangeDropPass),
    ("subsumedCheck", DenseVerifiedPassW.guardDegree b denseSubsumedCheckDropPass),
    -- Layout-only packing, run after `redundantByteDrop` (packing earlier would hide byte checks
    -- from the drop). Drains every packable pair internally, so no fixpoint wrapper.
    ("tupleRange", DenseVerifiedPassW.guardDegree b denseTupleRangePass),
    ("bytePackLate", DenseVerifiedPassW.guardDegree b denseByteCheckPackPass),
    ("monicScale", DenseVerifiedPassW.guardDegree b denseMonicScalePass),
    ("constFoldEnd", DenseVerifiedPassW.guardDegree b denseConstantFoldPass),
    -- After `monicScale`, where the seqz cluster reaches its recognised form.
    ("seqzCollapse", DenseVerifiedPassW.guardDegree b denseSeqzCollapsePass) ]

/-! ## The dense pipeline

Runs over the dense `VarId` representation: prelude chain, cleanup fixpoint, coda chain, wrapped
between a single encode at entry and a single decode at output (no decode between passes). -/

theorem denseCleanupChain_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (denseChain ((cleanupPasses (p := p) b).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [cleanupPasses, List.map_cons, List.map_nil] at hf
  fin_cases hf <;> exact DenseVerifiedPassW.guardDegree_respectsDeg _

theorem densePreludeChain_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (denseChain ((preludePasses (p := p) b).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [preludePasses, List.map_cons, List.map_nil] at hf
  fin_cases hf
  exact DenseVerifiedPassW.guardDegree_respectsDeg _

theorem denseCodaChain_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (denseChain ((codaPasses (p := p) b).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [codaPasses, List.map_cons, List.map_nil] at hf
  fin_cases hf <;> exact DenseVerifiedPassW.guardDegree_respectsDeg _

/-- The dense pipeline body: prelude chain, then the cleanup cycle to a fixpoint
    (`denseIterateToFixpoint`, no budget — runs until the lexicographic dense size key stops
    shrinking), then the coda chain. -/
def densePipeline (b : DegreeBound) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.andThen (denseChain ((preludePasses b).map (·.2)))
    (DenseVerifiedPassW.andThen
      (denseIterateToFixpoint (denseChain ((cleanupPasses b).map (·.2))))
      (denseChain ((codaPasses b).map (·.2))))

theorem densePipeline_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (densePipeline (p := p) b) := by
  unfold densePipeline
  exact DenseVerifiedPassW.andThen_respectsDeg (densePreludeChain_respectsDeg b)
    (DenseVerifiedPassW.andThen_respectsDeg
      (denseIterateToFixpoint_respectsDeg (denseCleanupChain_respectsDeg b))
      (denseCodaChain_respectsDeg b))

/-- The circuit optimizer: encode once into the dense `VarId` representation, run `densePipeline`,
    then decode the result and its derivations once. `decode ∘ encode = id` turns the dense
    pipeline's `PassCorrect` into one against the original system. -/
def pipeline (b : DegreeBound) : VerifiedPassW p := fun cs bs facts =>
  let e := VarRegistry.empty.encodeCS cs
  let r := densePipeline b e.1 e.2 (VarRegistry.empty.encodeCS_covered cs) bs facts
  ⟨r.reg'.decodeCS r.out, r.reg'.decodeDerivs r.derivs, by
    have hc := r.correct
    rw [(VarRegistry.empty.decodeCS_encodeCS cs : e.1.decodeCS e.2 = cs)] at hc
    exact hc⟩

theorem pipeline_respectsDeg (b : DegreeBound) : RespectsDeg b (pipeline (p := p) b) := by
  intro cs bs facts hin
  exact densePipeline_respectsDeg b (VarRegistry.empty.encodeCS cs).1
    (VarRegistry.empty.encodeCS cs).2 (VarRegistry.empty.encodeCS_covered cs) bs facts
    (by rw [VarRegistry.empty.decodeCS_encodeCS cs]; exact hin)

/-- The fact-aware circuit optimizer: given proven `BusFacts` (which fixes the implicit `bs`), run
    the pipeline and return the output system with the `Derivations` for its new variables. -/
def optimizerWithBusFacts {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : ConstraintSystem p) : ConstraintSystem p × Derivations p :=
  let r := pipeline b cs bs facts
  -- Drop derivations for variables absent from the output: dead, and the spec requires every
  -- recorded derivation to name an output variable.
  (r.out, r.derivs.filter (fun d => decide (d.1 ∈ r.out.vars)))

/-! ## Evaluation depends only on a system's variables

Two assignments agreeing on `cs.vars` are interchangeable for `satisfies`/`admissible`/`sideEffects`.
The completeness proof below uses these to swap the abstract per-pass witness for `witgen`'s output. -/

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

/-- Pruning derivations to those naming a variable in `out` leaves `methodFor` unchanged on any
    variable in `out`. -/
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

/-- The fact-aware optimizer is correct: its output soundly replaces the input and completely
    replaces the input's real-trace executions (`witgen` on any admissible input trace reproduces a
    valid witness) — the clauses `Optimizer.isCorrect` demands. -/
theorem optimizerWithBusFacts_correct {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : ConstraintSystem p) :
    (optimizerWithBusFacts b facts cs).1.isSoundReplacementOf cs bs ∧
      (optimizerWithBusFacts b facts cs).1.isCompleteReplacementOf cs bs (optimizerWithBusFacts b facts cs).2 := by
  refine ⟨(pipeline b cs bs facts).correct.toSound, ?_⟩
  intro hpow env hadm hsat
  obtain ⟨_himpl, _hinv, hS, hcomp⟩ := (pipeline b cs bs facts).correct
  obtain ⟨env', hsat', hadm', hse, hA, hR⟩ := hcomp env hadm hsat
  have hrec : (pipeline b cs bs facts).out.reconstructs cs.vars
      (pipeline b cs bs facts).derivs env' := by
    have hrec0 : cs.reconstructs cs.vars [] env :=
      fun u hu hunone => absurd (hpow u hu) (by simp [hunone])
    simpa using hR cs.vars (fun v hv _ => hv) [] hrec0
  have hagree : ∀ v ∈ (pipeline b cs bs facts).out.vars,
      Derivations.witgen (pipeline b cs bs facts).derivs env v = env' v := by
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
  -- Pruning leaves `witgen` unchanged on output vars (`methodFor_filter`), so `hagree` transports.
  have hagree' : ∀ v ∈ (pipeline b cs bs facts).out.vars,
      Derivations.witgen ((pipeline b cs bs facts).derivs.filter
        (fun d => decide (d.1 ∈ (pipeline b cs bs facts).out.vars))) env v = env' v := by
    intro v hv
    rw [show Derivations.witgen ((pipeline b cs bs facts).derivs.filter
          (fun d => decide (d.1 ∈ (pipeline b cs bs facts).out.vars))) env v
        = Derivations.witgen (pipeline b cs bs facts).derivs env v by
      simp only [Derivations.witgen, Derivations.methodFor_filter hv]]
    exact hagree v hv
  refine ⟨?_, ?_, (ConstraintSystem.satisfies_congr hagree').mpr hsat',
    (ConstraintSystem.admissible_congr hagree').mpr hadm', ?_⟩
  · -- `ds` covers the output columns: reused ones exist in the input (`hS`); derived ones have a
    -- method reading only powdr-ID columns, preserved by the pruning.
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
        ≈ (pipeline b cs bs facts).out.sideEffects bs (Derivations.witgen
            ((pipeline b cs bs facts).derivs.filter
              (fun d => decide (d.1 ∈ (pipeline b cs bs facts).out.vars))) env)
    rw [ConstraintSystem.sideEffects_congr hagree']
    exact hse

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree {bs : BusSemantics p} (b : DegreeBound)
    (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (h : cs.withinDegree b) :
    (optimizerWithBusFacts b facts cs).1.withinDegree b :=
  pipeline_respectsDeg b cs bs facts h
