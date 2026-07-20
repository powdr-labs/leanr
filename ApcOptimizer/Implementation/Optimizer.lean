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
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroWidthRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.XorEqExtract
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapse
import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.RangeForceZero
import ApcOptimizer.Implementation.OptimizerPasses.RangeBool
import ApcOptimizer.Implementation.OptimizerPasses.IdentitySubst
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
def preludePasses (b : DegreeBound) : List (String × VerifiedPassW p) :=
  [ ("constFold0", constantFoldPass.withFacts.guardDegree b) ]

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
def cleanupPasses (b : DegreeBound) : List (String × VerifiedPassW p) :=
  -- One primality decision per optimizer run, threaded to every prime-gated pass below (they read
  -- the `Bool` in O(1) instead of re-running `decide (Nat.Prime p)` per invocation per iteration).
  let pw := PrimeWitness.of p
  [ ("zeroWidthRange", (ZeroWidthRange.zeroWidthRangePass pw).guardDegree b),
    ("rangeForceZero", RangeForceZero.rangeForceZeroPass.guardDegree b),
    ("rangeBool", (RangeBool.rangeBoolPass pw).guardDegree b),
    ("xorEqExtract", XorEqExtract.xorEqExtractPass.guardDegree b),
    ("carryBranch", (carryBranchPass pw).guardDegree b),
    ("gauss", gaussElimPass.withFacts.guardDegree b),
    ("normalize1", normalizePass.withFacts.guardDegree b),
    ("constFold1", constantFoldPass.withFacts.guardDegree b),
    ("domainBatch", (domainBatchPass pw).guardDegree b),
    ("normalize2", normalizePass.withFacts.guardDegree b),
    ("constFold2", constantFoldPass.withFacts.guardDegree b),
    ("zeroRegister", zeroRegisterPass.guardDegree b),
    ("intervalForce", IntervalForce.intervalForcePass.guardDegree b),
    ("digitFold", DigitFold.digitFoldPass.guardDegree b),
    ("oneHotAnnihilate", OneHotAnnihilate.oneHotAnnihilatePass.guardDegree b),
    ("hintCollapse", (hintCollapsePass pw).guardDegree b),
    ("rootPairUnify", (rootPairUnifyPass pw).guardDegree b),
    ("flagUnify", (flagUnifyPass pw).guardDegree b),
    ("flagFold", (flagFoldPass' pw b).guardDegree b),
    ("dedup", dedupPass.withFacts.guardDegree b),
    ("trivialConstr", trivialConstraintDropPass.withFacts.guardDegree b),
    ("zeroMultBus", zeroMultBusDropPass.withFacts.guardDegree b),
    ("tautoBus", tautoBusDropPass.withFacts.guardDegree b),
    ("domainFold", (domainFoldPass pw).withFacts.guardDegree b),
    ("busUnify", busUnifyPass.guardDegree b),
    ("busPairCancel", VerifiedPassW.guardDegree b (busPairCancelPass pw false)),
    ("bytePack", VerifiedPassW.guardDegree b (iterateToFixpoint ByteCheckPack.byteCheckPackPass)),
    ("disconnected", disconnectedComponentPass.withFacts.guardDegree b),
    ("reencode", (reencodePass b).withFacts.guardDegree b) ]

/-- The coda passes (one of the three stages; see `preludePasses`): run once after the cleanup loop
    reaches its fixpoint — drop bytes made redundant by the cleaned-up system, rescale carries to
    monic form, and one final constant-fold. -/
def codaPasses (b : DegreeBound) : List (String × VerifiedPassW p) :=
  -- One primality decision per optimizer run (see `cleanupPasses`), for the prime-gated coda passes.
  let pw := PrimeWitness.of p
  [ ("busPairCancelLate", VerifiedPassW.guardDegree b (busPairCancelPass pw true)),
    -- Explode packed pair byte checks into singles so `dedupLate` collapses the same value
    -- byte-checked in several pairs and `redundantByteDrop` becomes operand-granular; the
    -- survivors are re-packed by `bytePackLate` below (a pair with nothing to shed round-trips).
    ("splitBytePair", SplitBytePair.splitBytePairPass.guardDegree b),
    -- Rename each OR-identity result to its operand *before* the drop/pack stages: the renamed
    -- interactions become degenerate byte checks (`[or, x, x, 0]`, exactly "x is a byte") that
    -- `dedupLate` collapses, `redundantByteDrop` drops when justified elsewhere, and
    -- `bytePackLate` packs pairwise. (In the cleanup cycle the rename instead explodes the
    -- re-encoding; the coda has no reencode, so here it only exposes the degenerate checks.)
    ("identitySubst", IdentitySubst.identitySubstPass.guardDegree b),
    ("dedupLate", dedupPass.withFacts.guardDegree b),
    ("redundantByteDrop", (RedundantByteDrop.redundantByteDropPass pw).guardDegree b),
    ("subsumedRange", SubsumedRange.subsumedRangeDropPass.guardDegree b),
    ("subsumedCheck", SubsumedCheck.subsumedCheckDropPass.guardDegree b),
    -- Tuple/range packing is layout-only and does not unblock other optimizations (powdr likewise
    -- runs global range packing once at the end), so it runs once here, out of the cleanup
    -- fixpoint, after `redundantByteDrop` has dropped droppable byte checks operand-granularly
    -- (packing a byte check early would hide it from the drop, leaving more bus interactions).
    -- The pass drains every packable pair internally, so it needs no fixpoint wrapper.
    ("tupleRange", tupleRangePass.guardDegree b),
    ("bytePackLate", VerifiedPassW.guardDegree b (iterateToFixpoint ByteCheckPack.byteCheckPackPass)),
    ("monicScale", monicScalePass.withFacts.guardDegree b),
    ("constFoldEnd", constantFoldPass.withFacts.guardDegree b),
    -- Collapse recognised `sltu x, 1` (seqz) LessThan gadgets to the two-line is-zero gadget,
    -- dropping the four `diff_marker`s + `diff_val`. Runs after `monicScale`, where the cluster
    -- has reached the recognised form.
    ("seqzCollapse", VerifiedPassW.guardDegree b (iterateToFixpoint SeqzCollapse.seqzCollapsePass)) ]

/-- Fold a list of passes into one sequential pass (`andThen` left to right; identity on `[]`). -/
def chainPasses (l : List (VerifiedPassW p)) : VerifiedPassW p :=
  l.foldl VerifiedPassW.andThen (fun cs bs _ => ⟨cs, [], PassCorrect.refl cs bs⟩)

/-- The optimizer's cleanup cycle: the `cleanupPasses` folded together in order. See `cleanupPasses`
    for what each pass does and how to extend the cycle. -/
def cleanupCycle (b : DegreeBound) : VerifiedPassW p :=
  chainPasses ((cleanupPasses b).map (·.2))

/-- Folding degree-respecting passes with `andThen` yields a degree-respecting pass. -/
theorem foldl_andThen_respectsDeg {b : DegreeBound} :
    ∀ (l : List (VerifiedPassW p)) (init : VerifiedPassW p),
      RespectsDeg b init → (∀ f ∈ l, RespectsDeg b f) →
      RespectsDeg b (l.foldl VerifiedPassW.andThen init)
  | [], _, hinit, _ => by simpa using hinit
  | g :: rest, init, hinit, hall => by
      rw [List.foldl_cons]
      exact foldl_andThen_respectsDeg rest (init.andThen g)
        (VerifiedPassW.andThen_respectsDeg hinit (hall g (List.mem_cons_self ..)))
        (fun f hf => hall f (List.mem_cons_of_mem _ hf))

/-- Any list of degree-respecting passes folds (`chainPasses`) to a degree-respecting pass. -/
theorem chainPasses_respectsDeg {b : DegreeBound} {l : List (VerifiedPassW p)}
    (h : ∀ f ∈ l, RespectsDeg b f) : RespectsDeg b (chainPasses l) := by
  unfold chainPasses
  exact foldl_andThen_respectsDeg _ _ (fun _ _ _ h => h) h

theorem cleanupCycle_respectsDeg (b : DegreeBound) : RespectsDeg b (cleanupCycle (p := p) b) := by
  unfold cleanupCycle
  refine chainPasses_respectsDeg (fun f hf => ?_)
  simp only [cleanupPasses, List.map_cons, List.map_nil] at hf
  fin_cases hf <;> exact VerifiedPassW.guardDegree_respectsDeg _

/-! ## Dense cleanup stage (Task 3, Checkpoint 1)

The cleanup stage runs over the dense `VarId` representation: encode once at the start of cleanup,
iterate the dense cleanup cycle to its fixpoint, decode once after. `denseCleanupPasses` is derived
from `cleanupPasses` (the single source of truth) by wrapping each entry as a dense pass; entries
are replaced by true dense implementations one at a time (monsters first). `denseCleanupAdapter` is
the one verified encode/decode adapter Checkpoint 1 permits around the whole fixpoint — a
`VerifiedPassW` that slots into `pipeline` between the (still spec-level) prelude and coda. -/

/-- Every scheduled cleanup pass respects the degree bound (each is `guardDegree`-wrapped). -/
theorem cleanupPasses_respectsDeg (b : DegreeBound) :
    ∀ f ∈ ((cleanupPasses (p := p) b).map (·.2)), RespectsDeg b f := by
  intro f hf
  simp only [cleanupPasses, List.map_cons, List.map_nil] at hf
  fin_cases hf <;> exact VerifiedPassW.guardDegree_respectsDeg _

/-- The dense implementation of a cleanup pass, selected by label: a **true dense** pass where one
    exists (degree-guarded), else the generic `ofSpec` adapter (development scaffolding, replaced
    pass by pass). The label dispatch is temporary scaffolding; the finished checkpoint replaces it
    with one canonical dense schedule. New cleanup passes (and `xorEqExtract`, whose spec algorithm
    was rewritten upstream so its former dense commutation port was dropped, pending a native
    rebuild) flow through `ofSpec` automatically. -/
def denseImpl (b : DegreeBound) (pw : PrimeWitness p) (name : String) (fallback : VerifiedPassW p) :
    DenseVerifiedPassW p :=
  if name == "constFold1" || name == "constFold2" then
    DenseVerifiedPassW.guardDegree b denseConstantFoldPass
  else if name == "trivialConstr" then
    DenseVerifiedPassW.guardDegree b denseTrivialConstraintDropPass
  else if name == "zeroMultBus" then
    DenseVerifiedPassW.guardDegree b denseZeroMultBusDropPass
  else if name == "tautoBus" then
    DenseVerifiedPassW.guardDegree b denseTautoBusDropPass
  else if name == "normalize1" || name == "normalize2" then
    DenseVerifiedPassW.guardDegree b denseNormalizePass
  else if name == "dedup" then
    DenseVerifiedPassW.guardDegree b denseDedupPass
  else if name == "digitFold" then
    DenseVerifiedPassW.guardDegree b denseDigitFoldPass
  else if name == "gauss" then
    DenseVerifiedPassW.guardDegree b denseGaussElimPass
  else if name == "domainBatch" then
    DenseVerifiedPassW.guardDegree b (denseDomainBatchPassV pw)
  else if name == "oneHotAnnihilate" then
    DenseVerifiedPassW.guardDegree b denseOneHotAnnihilatePass
  else if name == "zeroRegister" then
    DenseVerifiedPassW.guardDegree b denseZeroRegisterPass
  else if name == "carryBranch" then
    DenseVerifiedPassW.guardDegree b (denseCarryBranchPass pw)
  else if name == "zeroWidthRange" then
    DenseVerifiedPassW.guardDegree b (denseZeroWidthRangePass pw)
  else if name == "domainFold" then
    DenseVerifiedPassW.guardDegree b (denseDomainFoldPassV pw)
  else if name == "busUnify" then
    DenseVerifiedPassW.guardDegree b denseBusUnifyPass
  else if name == "rootPairUnify" then
    DenseVerifiedPassW.guardDegree b (denseRootPairUnifyPass pw)
  else if name == "flagUnify" then
    DenseVerifiedPassW.guardDegree b (denseFlagUnifyPass pw)
  else if name == "flagFold" then
    DenseVerifiedPassW.guardDegree b (denseFlagFoldPass' pw b)
  else if name == "busPairCancel" then
    DenseVerifiedPassW.guardDegree b (denseBusPairCancelPass pw false)
  else if name == "bytePack" then
    DenseVerifiedPassW.guardDegree b denseByteCheckPackPass
  else if name == "hintCollapse" then
    DenseVerifiedPassW.guardDegree b (denseHintCollapsePass pw)
  else if name == "disconnected" then
    DenseVerifiedPassW.guardDegree b denseDisconnectedPass
  else if name == "reencode" then
    DenseVerifiedPassW.guardDegree b (denseReencodePass pw b)
  else DenseVerifiedPassW.ofSpec fallback

/-- `DenseRespectsDeg` is preserved by an `if`-`then`-`else` whose branches both respect the bound. -/
theorem denseRespectsDeg_ite {bnd : DegreeBound} {c : Prop} [Decidable c]
    {a b : DenseVerifiedPassW p}
    (ha : DenseRespectsDeg bnd a) (hb : DenseRespectsDeg bnd b) :
    DenseRespectsDeg bnd (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

set_option maxHeartbeats 800000 in
theorem denseImpl_respectsDeg (b : DegreeBound) (pw : PrimeWitness p) (name : String)
    {fallback : VerifiedPassW p} (h : RespectsDeg b fallback) :
    DenseRespectsDeg b (denseImpl b pw name fallback) := by
  unfold denseImpl
  repeat' apply denseRespectsDeg_ite
  all_goals first
    | exact DenseVerifiedPassW.guardDegree_respectsDeg _
    | exact DenseVerifiedPassW.ofSpec_respectsDeg h

/-- The dense cleanup pass list: each `cleanupPasses` entry as a dense pass (single source of truth
    derived from the spec schedule via `denseImpl`). The primality witness is computed **once** here
    and threaded to every prime-gated dense pass (mirroring `cleanupPasses`). -/
def denseCleanupPasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  let pw := PrimeWitness.of p
  (cleanupPasses b).map (fun e => (e.1, denseImpl b pw e.1 e.2))

/-- The dense cleanup stage as a spec `VerifiedPassW`: encode the input from an empty registry, run
    the dense cleanup cycle to its fixpoint, decode the result and its derivations. Correct because
    the round trip `decode ∘ encode = id` turns the dense fixpoint's `PassCorrect` into one against
    the original system. -/
def denseCleanupAdapter (b : DegreeBound) : VerifiedPassW p := fun cs bs facts =>
  -- Encode the input exactly once (bind the pair; `e.1`/`e.2` project the shared value).
  let e := VarRegistry.empty.encodeCS cs
  let r := denseIterateToFixpoint (denseChain ((denseCleanupPasses b).map (·.2)))
    e.1 e.2 (VarRegistry.empty.encodeCS_covered cs) bs facts
  ⟨r.reg'.decodeCS r.out, r.reg'.decodeDerivs r.derivs, by
    have hc := r.correct
    rw [(VarRegistry.empty.decodeCS_encodeCS cs : e.1.decodeCS e.2 = cs)] at hc
    exact hc⟩

/-- The dense cleanup cycle respects the degree bound (each entry is a degree-respecting dense
    pass — `guardDegree` of a true dense pass or `ofSpec` of a degree-respecting spec pass). -/
theorem denseCleanupChain_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (denseChain ((denseCleanupPasses (p := p) b).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [denseCleanupPasses, List.map_map] at hf
  rw [List.mem_map] at hf
  obtain ⟨e, he, rfl⟩ := hf
  exact denseImpl_respectsDeg _ _ e.1 (cleanupPasses_respectsDeg b e.2 (List.mem_map.2 ⟨e, he, rfl⟩))

theorem denseCleanupAdapter_respectsDeg (b : DegreeBound) :
    RespectsDeg b (denseCleanupAdapter (p := p) b) := by
  intro cs bs facts hin
  refine denseIterateToFixpoint_respectsDeg (denseCleanupChain_respectsDeg b)
    (VarRegistry.empty.encodeCS cs).1 (VarRegistry.empty.encodeCS cs).2
    (VarRegistry.empty.encodeCS_covered cs) bs facts ?_
  rw [VarRegistry.empty.decodeCS_encodeCS cs]
  exact hin

/-- The circuit optimizer: fold the prelude, run the dense cleanup stage to a fixpoint
    (`denseCleanupAdapter`, which encodes once, iterates the dense cleanup cycle, decodes once),
    then fold the coda. (The profiler does not yet step `denseCleanupPasses` — see `preludePasses`;
    that lockstep is a Checkpoint-1 deliverable.) -/
def pipeline (b : DegreeBound) : VerifiedPassW p :=
  chainPasses ((preludePasses b).map (·.2))
    |>.andThen (denseCleanupAdapter b)
    |>.andThen (chainPasses ((codaPasses b).map (·.2)))

theorem pipeline_respectsDeg (b : DegreeBound) : RespectsDeg b (pipeline (p := p) b) := by
  unfold pipeline
  refine VerifiedPassW.andThen_respectsDeg (VerifiedPassW.andThen_respectsDeg
    (chainPasses_respectsDeg (fun f hf => ?_))
    (denseCleanupAdapter_respectsDeg b))
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
