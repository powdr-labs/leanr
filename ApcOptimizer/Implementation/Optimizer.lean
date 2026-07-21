import ApcOptimizer.Implementation.OptimizerPasses.Basic
import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Identity
import ApcOptimizer.Implementation.OptimizerPasses.ConstantFold
import ApcOptimizer.Implementation.OptimizerPasses.TrivialConstraint
import ApcOptimizer.Implementation.OptimizerPasses.ZeroMultBus
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Affine
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus
import ApcOptimizer.Implementation.OptimizerPasses.MonicScale
import ApcOptimizer.Implementation.OptimizerPasses.MonicScaleProof
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.BusPairCancel
import ApcOptimizer.Implementation.OptimizerPasses.BytePack
import ApcOptimizer.Implementation.OptimizerPasses.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.DisconnectedComponent
import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroRegister
import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.CarryBranch
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.FlagUnify
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.BoxRewrite
import ApcOptimizer.Implementation.OptimizerPasses.RedundantByteDrop
import ApcOptimizer.Implementation.OptimizerPasses.RedundantByteDropProof
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroWidthRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedRangeProof
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheckProof
import ApcOptimizer.Implementation.OptimizerPasses.XorEqExtract
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePairProof
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapse
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

Assembles the optimization passes (from `ApcOptimizer/Implementation/OptimizerPasses/`) into the
fact-aware `optimizerWithBusFacts`, using the scaffolding in
`ApcOptimizer/Implementation/OptimizerPasses/Basic.lean` and `FactPass.lean`. Given proven `BusFacts`
about a bus semantics (see `ApcOptimizer/Implementation/BusFacts.lean`),
`optimizerWithBusFacts` is a circuit-to-circuit map.

This file is *implementation* — it needs no audit. The user-facing optimizer definitions
(`simpleOptimizer`, `openVmOptimizer`) and the correctness theorems that make up the audited
surface live in `ApcOptimizer/Optimizer.lean`; each theorem is a projection of the per-instance
`optimizerWithBusFacts_correct` / `optimizerWithBusFacts_respectsDegree` proved here.

**To add an optimization:** write a pass in a new file under
`ApcOptimizer/Implementation/OptimizerPasses/`, import it here, and add one dense entry to the
`cleanupPasses` list below — a native `DenseVerifiedPassW`, or, until it is ported to a native dense
proof, `DenseVerifiedPassW.ofSpec (pass.….guardDegree b)`. That is the only edit needed here; the
correctness proof follows automatically from the pass's own `PassCorrect`. -/

/-- The optimizer runs in three stages: a **prelude** (this list) once, then the `cleanupPasses`
    cycle iterated to a fixpoint, then a **coda** (`codaPasses`) once. All three lists are dense —
    each entry is a `DenseVerifiedPassW` over the `VarId` representation — and together are the single
    source of truth for the pass sequence: `pipeline` runs them between one encode at entry and one
    decode at output, and the `profile` CLI command (`Main.lean`) steps the same lists, so the
    optimizer and the profiler cannot drift apart. The prelude is a single constant-fold that
    canonicalizes the freshly-parsed system. The `String` labels name each pass in the profiler's
    timing report (irrelevant to behaviour). -/
def preludePasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  [ ("constFold0", DenseVerifiedPassW.guardDegree b denseConstantFoldPass) ]

/-- The canonical labelled **dense** cleanup schedule (one of the three stages; see `preludePasses`)
    — the **single source of truth** for both the optimizer and the profiler: `pipeline` iterates the
    dense fixpoint (`denseIterateToFixpoint`) over the chain of this list, and the `profile` CLI
    command (`Main.lean`) steps this same list, so the two cannot drift apart.

    Iterate this cycle to a fixpoint (`denseIterateToFixpoint`, no budget) over the dense `VarId`
    representation: batch-eliminate every variable solvable from a linear constraint with a
    unit-coefficient pivot (`denseGaussElimPass` — one simultaneous substitution per cycle),
    normalize and fold, substitute one variable forced by finite-domain enumeration
    (boolean/one-hot case analysis, bus-fact domains, probed bus obligations; prime `p` only),
    re-normalize and re-fold, drop trivially-true constraints, drop zero-multiplicity bus
    interactions, drop stateless interactions whose constant message satisfies the bus table, and add
    the receive-equals-send equations entailed by the memory discipline.

    **To add an optimization:** write a pass in a new file under
    `ApcOptimizer/Implementation/OptimizerPasses/`, import it above, and add one
    `(name, X.guardDegree b)` entry to this list — a `DenseVerifiedPassW`, or
    `DenseVerifiedPassW.ofSpec (pass.….guardDegree b)` for a `Variable`-based pass (correct by
    construction, but it round-trips through the `Variable` form each iteration, so a dense pass
    is preferred). That is the only edit needed here; correctness follows from the pass's own
    bundled proof, and the profiler picks up the new label for free (it steps this same list). -/
def cleanupPasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  -- One primality decision per optimizer run, threaded to every prime-gated pass below (they read
  -- the `Bool` in O(1) instead of re-running `decide (Nat.Prime p)` per invocation per iteration).
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

/-- The coda passes (one of the three stages; see `preludePasses`): run once after the cleanup loop
    reaches its fixpoint — drop bytes made redundant by the cleaned-up system, rescale carries to
    monic form, and one final constant-fold. -/
def codaPasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  -- One primality decision per optimizer run (see `cleanupPasses`), for the prime-gated coda passes.
  let pw := PrimeWitness.of p
  [ ("busPairCancelLate", DenseVerifiedPassW.guardDegree b (denseBusPairCancelPass pw true)),
    -- Explode packed pair byte checks into singles so `dedupLate` collapses the same value
    -- byte-checked in several pairs and `redundantByteDrop` becomes operand-granular; the
    -- survivors are re-packed by `bytePackLate` below (a pair with nothing to shed round-trips).
    ("splitBytePair", DenseVerifiedPassW.guardDegree b denseSplitBytePairPass),
    -- Rename each OR-identity result to its operand *before* the drop/pack stages: the renamed
    -- interactions become degenerate byte checks (`[or, x, x, 0]`, exactly "x is a byte") that
    -- `dedupLate` collapses, `redundantByteDrop` drops when justified elsewhere, and
    -- `bytePackLate` packs pairwise. (In the cleanup cycle the rename instead explodes the
    -- re-encoding; the coda has no reencode, so here it only exposes the degenerate checks.)
    ("identitySubst", DenseVerifiedPassW.guardDegree b denseIdentitySubstPass),
    ("dedupLate", DenseVerifiedPassW.guardDegree b denseDedupPass),
    ("redundantByteDrop", DenseVerifiedPassW.guardDegree b (denseRedundantByteDropPass pw)),
    ("subsumedRange", DenseVerifiedPassW.guardDegree b denseSubsumedRangeDropPass),
    ("subsumedCheck", DenseVerifiedPassW.guardDegree b denseSubsumedCheckDropPass),
    -- Tuple/range packing is layout-only and does not unblock other optimizations (powdr likewise
    -- runs global range packing once at the end), so it runs once here, out of the cleanup
    -- fixpoint, after `redundantByteDrop` has dropped droppable byte checks operand-granularly
    -- (packing a byte check early would hide it from the drop, leaving more bus interactions).
    -- The pass drains every packable pair internally, so it needs no fixpoint wrapper.
    ("tupleRange", DenseVerifiedPassW.ofSpec (tupleRangePass.guardDegree b)),
    ("bytePackLate", DenseVerifiedPassW.guardDegree b denseByteCheckPackPass),
    ("monicScale", DenseVerifiedPassW.guardDegree b denseMonicScalePass),
    ("constFoldEnd", DenseVerifiedPassW.guardDegree b denseConstantFoldPass),
    -- Collapse recognised `sltu x, 1` (seqz) LessThan gadgets to the two-line is-zero gadget,
    -- dropping the four `diff_marker`s + `diff_val`. Runs after `monicScale`, where the cluster
    -- has reached the recognised form.
    ("seqzCollapse", DenseVerifiedPassW.ofSpec (VerifiedPassW.guardDegree b (iterateToFixpoint SeqzCollapse.seqzCollapsePass))) ]

/-! ## The dense pipeline

The whole pipeline runs over the dense `VarId` representation: the prelude chain, then the cleanup
cycle iterated to a fixpoint, then the coda chain. `pipeline` wraps that dense body between a single
encode at the optimizer entry and a single decode at its output; no decode runs between passes. The
profiler (`Main.lean`) steps the same three lists between the same single encode and decode. -/

/-- The dense cleanup cycle respects the degree bound (every scheduled entry is literally a
    `DenseVerifiedPassW.guardDegree`-wrapped dense pass). -/
theorem denseCleanupChain_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (denseChain ((cleanupPasses (p := p) b).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [cleanupPasses, List.map_cons, List.map_nil] at hf
  fin_cases hf <;> exact DenseVerifiedPassW.guardDegree_respectsDeg _

/-- The dense prelude chain respects the degree bound (its single entry is a
    `guardDegree`-wrapped dense pass). -/
theorem densePreludeChain_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (denseChain ((preludePasses (p := p) b).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [preludePasses, List.map_cons, List.map_nil] at hf
  fin_cases hf
  exact DenseVerifiedPassW.guardDegree_respectsDeg _

/-- The dense coda chain respects the degree bound (each entry is a degree-guarded pass — either a
    native `guardDegree`-wrapped dense pass or an `ofSpec`-wrapped degree-guarded spec pass). -/
theorem denseCodaChain_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (denseChain ((codaPasses (p := p) b).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [codaPasses, List.map_cons, List.map_nil] at hf
  fin_cases hf <;>
    first
      | exact DenseVerifiedPassW.guardDegree_respectsDeg _
      | exact DenseVerifiedPassW.ofSpec_respectsDeg (VerifiedPassW.guardDegree_respectsDeg _)

/-- The all-dense pipeline body over the `VarId` representation: fold the prelude chain, iterate the
    cleanup cycle to a fixpoint (`denseIterateToFixpoint`, no budget — it runs until the lexicographic
    dense size key stops strictly shrinking), then fold the coda chain. Slotted into `pipeline`
    between a single encode at entry and a single decode at output. -/
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

/-- The circuit optimizer: encode the freshly-parsed system into the dense `VarId` representation
    once, run the all-dense `densePipeline` (prelude chain, cleanup fixpoint, coda chain), then decode
    the result and its derivations once. The round trip `decode ∘ encode = id` turns the dense
    pipeline's `PassCorrect` into one against the original system. The profiler (`Main.lean`) steps
    the same three lists between the same single encode and decode, so it times exactly the passes
    the optimizer runs. -/
def pipeline (b : DegreeBound) : VerifiedPassW p := fun cs bs facts =>
  -- Encode the input exactly once (bind the pair; `e.1`/`e.2` project the shared value).
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

/-- The fact-aware circuit optimizer: given proven `BusFacts` about a bus semantics (which fixes the
    implicit `bs`), run the pipeline and return the resulting constraint system together with the
    `Derivations` for its newly-introduced variables. The cleanup loop (`iterateToFixpoint`) takes no
    iteration count: it runs the cleanup cycle until it stops strictly shrinking the lexicographic
    size key `(vars, bus, constraints)`, provably terminating on that well-founded measure — no
    budget to set, and no cap a large basic block could exceed. -/
def optimizerWithBusFacts {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : ConstraintSystem p) : ConstraintSystem p × Derivations p :=
  let r := pipeline b cs bs facts
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
  -- The returned derivations are `pipeline …`'s pruned to output variables; on output variables the
  -- pruning leaves `witgen` unchanged (`methodFor_filter`), so `hagree` transports to the pruned list.
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
