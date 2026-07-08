import Leanr.Spec
import Leanr.Implementation.Variable

set_option autoImplicit false

variable {p : ℕ}

/-! # Optimizer scaffolding

The reusable framework for building the circuit optimizer out of small, individually-proven
optimization *passes*. Nothing here is specific to a particular optimization; concrete passes
live in `Leanr/Implementation/OptimizerPasses/`, and the pipeline that assembles them into the
`optimizer` lives in `Leanr/Implementation/Optimizer.lean` (with the audited correctness theorems
in `Leanr/Optimizer.lean`).

This module provides:

* the relation glue for the spec's notions (`≈` on `BusState`, `ConstraintSystem.implies`,
  `ConstraintSystem.impliesAdmissible`, `ConstraintSystem.refines`) — reflexivity and transitivity
  — which is what lets passes *compose* without re-proving a growing monolith;
* `PassCorrect`, the per-step correctness obligation;
* `VerifiedPass`, a pass bundled with its own `PassCorrect` proof (so a pass cannot be written
  without discharging its obligations), and `VerifiedPass.andThen`/`VerifiedPass.id` to compose
  and seed pipelines.

These proofs are purely structural; none of them need `p` to be prime. -/

/-! ## Equivalence is an equivalence relation -/

/-- `≈` on `BusState` is reflexive: every message trivially has the same net multiplicity in a
    state as in itself. -/
theorem BusState.equiv_refl (s : BusState p) : s ≈ s :=
  fun _ => rfl

/-- `≈` on `BusState` is symmetric. -/
theorem BusState.equiv_symm {s t : BusState p} (h : s ≈ t) : t ≈ s :=
  fun message => (h message).symm

/-- `≈` on `BusState` is transitive. -/
theorem BusState.equiv_trans {s t u : BusState p} (h1 : s ≈ t) (h2 : t ≈ u) : s ≈ u :=
  fun message => (h1 message).trans (h2 message)

/-- Any constraint system implies itself: the same satisfying assignment works and its side
    effects are (reflexively) equal. -/
theorem ConstraintSystem.implies_refl (cs : ConstraintSystem p) (busSemantics : BusSemantics p) :
    cs.implies cs busSemantics :=
  fun env hsat => ⟨env, hsat, BusState.equiv_refl _⟩

/-- `implies` is transitive: chain the witness assignments and the side-effect equalities. -/
theorem ConstraintSystem.implies_trans {a b c : ConstraintSystem p} {busSemantics : BusSemantics p}
    (h1 : a.implies b busSemantics) (h2 : b.implies c busSemantics) : a.implies c busSemantics :=
  fun env hsat =>
    let ⟨env', hb, hab⟩ := h1 env hsat
    let ⟨env'', hc, hbc⟩ := h2 env' hb
    ⟨env'', hc, BusState.equiv_trans hab hbc⟩

/-! ## Verified passes

A single optimization step, packaged with its correctness proof. `VerifiedPass` is a function
that, given a constraint system and bus semantics, returns a new constraint system **together
with a proof** that it (a) `refines` the input and (b) preserves invariants. Because the
proof is part of the return value, there is no separate theorem to weaken: a pass simply cannot
be written down without discharging its obligations.

Passes compose with `VerifiedPass.andThen` (run one, then the next), which threads the two proofs
through `PassCorrect.andThen` (soundness via `implies_trans`, reconstruction by concatenating
derivations) and the composition of invariant-preservation.

**To add an optimization:** create a `VerifiedPass` for it in a new file under
`Leanr/Implementation/OptimizerPasses/`, then `.andThen` it into `pipeline` in
`Leanr/Implementation/Optimizer.lean`. Prove `PassCorrect` for your transformation; do not change
`Spec.lean` or the glue above. -/

/-- The per-pass correctness obligation. `out` is sound (`implies cs`), preserves invariants, adds
    no new powdr-ID column, and satisfies the completeness direction: every admissible satisfying
    assignment of `cs` extends to one of `out` with equal side effects that keeps every input-column
    value and reconstructs `out`'s derived variables from the input columns. `dsLocal` are the
    derivations this step introduces; reconstruction is threaded through any incoming `dsIn`, so
    passes compose simply by concatenating derivations. -/
def PassCorrect (cs out : ConstraintSystem p) (dsLocal : Derivations p) (bs : BusSemantics p) :
    Prop :=
  out.implies cs bs ∧
  (cs.guaranteesInvariants bs → out.guaranteesInvariants bs) ∧
  (∀ v ∈ out.vars, v.powdrId?.isSome → v ∈ cs.vars) ∧
  (∀ env, cs.admissible bs env → cs.satisfies bs env →
    ∃ env', out.satisfies bs env' ∧ out.admissible bs env' ∧
      cs.sideEffects bs env ≈ out.sideEffects bs env' ∧
      (∀ v, v.powdrId?.isSome → env' v = env v) ∧
      (∀ dsIn, cs.reconstructs dsIn env → out.reconstructs (dsIn ++ dsLocal) env'))

/-- Reflexivity: the unchanged system with no new derivations is correct. -/
theorem PassCorrect.refl (cs : ConstraintSystem p) (bs : BusSemantics p) :
    PassCorrect cs cs [] bs :=
  ⟨cs.implies_refl bs, _root_.id, fun _ hv _ => hv,
   fun env hadm hsat =>
     ⟨env, hsat, hadm, BusState.equiv_refl _, fun _ _ => rfl,
      fun dsIn hrec => by rwa [List.append_nil]⟩⟩

/-- Sequential composition: derivations concatenate, soundness/invariants compose, and the threaded
    reconstruction chains (`dsIn ↦ dsIn ++ df ↦ (dsIn ++ df) ++ dg = dsIn ++ (df ++ dg)`). -/
theorem PassCorrect.andThen {cs mid out : ConstraintSystem p} {bs : BusSemantics p}
    {df dg : Derivations p} (hf : PassCorrect cs mid df bs) (hg : PassCorrect mid out dg bs) :
    PassCorrect cs out (df ++ dg) bs := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨ConstraintSystem.implies_trans hg1 hf1, fun h => hg2 (hf2 h),
    fun v hv hpw => hf3 v (hg3 v hv hpw) hpw, fun env hadm hsat => ?_⟩
  obtain ⟨env1, hs1, ha1, he1, hpw1, hr1⟩ := hf4 env hadm hsat
  obtain ⟨env2, hs2, ha2, he2, hpw2, hr2⟩ := hg4 env1 ha1 hs1
  refine ⟨env2, hs2, ha2, BusState.equiv_trans he1 he2,
    fun v hpw => by rw [hpw2 v hpw, hpw1 v hpw], fun dsIn hrec => ?_⟩
  have := hr2 (dsIn ++ df) (hr1 dsIn hrec)
  rwa [List.append_assoc] at this

/-- Build `PassCorrect` for a pass whose completeness witness is the input assignment itself and
    which introduces no new variables (`out.vars ⊆ cs.vars`) — the shape of every pass except the
    column-introducing re-encoder. It emits no derivations. -/
theorem PassCorrect.ofEnvEq {cs out : ConstraintSystem p} {bs : BusSemantics p}
    (hsound : out.implies cs bs)
    (hinv : cs.guaranteesInvariants bs → out.guaranteesInvariants bs)
    (hsub : ∀ v ∈ out.vars, v ∈ cs.vars)
    (hcomp : ∀ env, cs.admissible bs env → cs.satisfies bs env →
      out.satisfies bs env ∧ out.admissible bs env ∧
        cs.sideEffects bs env ≈ out.sideEffects bs env) :
    PassCorrect cs out [] bs := by
  refine ⟨hsound, hinv, fun v hv _ => hsub v hv, fun env hadm hsat => ?_⟩
  obtain ⟨ho1, ho2, ho3⟩ := hcomp env hadm hsat
  refine ⟨env, ho1, ho2, ho3, fun _ _ => rfl, fun dsIn hrec => ?_⟩
  rw [List.append_nil]
  exact fun v hvout hvnone => hrec v (hsub v hvout) hvnone

/-- Bridge to the audited spec: a threaded `PassCorrect` (with incoming derivations `[]`) gives the
    spec's `refines` — soundness, plus completeness whose witness `derivesWitness` (when the input's
    columns all carry powdr IDs, so it has no unaccounted derived variables). -/
theorem PassCorrect.toRefines {cs out : ConstraintSystem p} {ds : Derivations p}
    {bs : BusSemantics p} (h : PassCorrect cs out ds bs) : out.refines cs bs ds := by
  obtain ⟨himpl, _hinv, hS, hcomp⟩ := h
  refine ⟨himpl, fun env hadm hsat => ?_⟩
  obtain ⟨env', hsat', hadm', hse, hA, hR⟩ := hcomp env hadm hsat
  refine ⟨env', hsat', hadm', hse, fun hpow => ⟨fun v hvout hvpow => ⟨hS v hvout hvpow, hA v hvpow⟩, ?_⟩⟩
  have hrec0 : cs.reconstructs [] env :=
    fun v hv hvnone => absurd (hpow v hv) (by simp [hvnone])
  simpa using hR [] hrec0

/-- The result of a verified pass: the transformed system, the derivations it introduces, and the
    correctness proof. -/
structure PassResult {p : ℕ} (cs : ConstraintSystem p) (bs : BusSemantics p) where
  out : ConstraintSystem p
  derivs : Derivations p
  correct : PassCorrect cs out derivs bs

/-- A proof-carrying optimization pass: maps a constraint system to a new one and the derivations it
    introduces, bundled with a `PassCorrect` proof. -/
abbrev VerifiedPass (p : ℕ) :=
  (cs : ConstraintSystem p) → (bs : BusSemantics p) → PassResult cs bs

/-- The identity pass: returns the system unchanged, correct by reflexivity. -/
def VerifiedPass.id : VerifiedPass p :=
  fun cs bs => ⟨cs, [], PassCorrect.refl cs bs⟩

/-- Sequential composition: run `f`, then run `g` on its output; concatenate derivations. -/
def VerifiedPass.andThen (f g : VerifiedPass p) : VerifiedPass p :=
  fun cs bs =>
    let r1 := f cs bs
    let r2 := g r1.out bs
    ⟨r2.out, r1.derivs ++ r2.derivs, r1.correct.andThen r2.correct⟩

/-- Iterate a pass `n` times. Used to run local, one-step passes (e.g. "substitute one variable")
    to a fixpoint: each application is a `VerifiedPass`, so the composite is correct by construction.
    A pass that finds nothing to do returns its input unchanged, so extra iterations are harmless. -/
def VerifiedPass.iterate (f : VerifiedPass p) : Nat → VerifiedPass p
  | 0 => VerifiedPass.id
  | n + 1 => (f.iterate n).andThen f

/-! ## Variable-set membership

Helpers for discharging the `out.vars ⊆ cs.vars` obligation of `PassCorrect.ofEnvEq`: a variable of
a sub-expression is a variable of the whole system, and vice versa. -/

/-- Membership in `cs.vars`: a variable occurs in some constraint, some multiplicity, or some
    payload expression. -/
theorem ConstraintSystem.mem_vars {cs : ConstraintSystem p} {x : Variable} :
    x ∈ cs.vars ↔
      (∃ c ∈ cs.algebraicConstraints, x ∈ c.vars) ∨
      (∃ bi ∈ cs.busInteractions, x ∈ bi.multiplicity.vars ∨ ∃ e ∈ bi.payload, x ∈ e.vars) := by
  simp only [ConstraintSystem.vars, List.mem_append, List.mem_flatMap]

theorem ConstraintSystem.mem_vars_of_constraint {cs : ConstraintSystem p} {c : Expression p}
    {x : Variable} (hc : c ∈ cs.algebraicConstraints) (hx : x ∈ c.vars) : x ∈ cs.vars :=
  ConstraintSystem.mem_vars.2 (Or.inl ⟨c, hc, hx⟩)

theorem ConstraintSystem.mem_vars_of_mult {cs : ConstraintSystem p}
    {bi : BusInteraction (Expression p)} {x : Variable} (hbi : bi ∈ cs.busInteractions)
    (hx : x ∈ bi.multiplicity.vars) : x ∈ cs.vars :=
  ConstraintSystem.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inl hx⟩)

theorem ConstraintSystem.mem_vars_of_payload {cs : ConstraintSystem p}
    {bi : BusInteraction (Expression p)} {e : Expression p} {x : Variable}
    (hbi : bi ∈ cs.busInteractions) (he : e ∈ bi.payload) (hx : x ∈ e.vars) : x ∈ cs.vars :=
  ConstraintSystem.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inr ⟨e, he, hx⟩⟩)

/-! ## Decidable degree-bound check

`ConstraintSystem.withinDegree` (the spec's degree-bound property) is a `Prop`; the degree-guard
machinery needs a `Bool` twin to branch on. This is optimizer infrastructure, not part of the
audited spec, so it lives here rather than in `Spec.lean`. -/

/-- Decidable twin of `ConstraintSystem.withinDegree`. -/
def ConstraintSystem.withinDegreeB (s : ConstraintSystem p) (b : DegreeBound) : Bool :=
  s.algebraicConstraints.all (fun c => c.degree ≤ b.identities) &&
  s.busInteractions.all (fun bi =>
    decide (bi.multiplicity.degree ≤ b.busInteractions) &&
      bi.payload.all (fun e => e.degree ≤ b.busInteractions))

theorem ConstraintSystem.withinDegreeB_iff (s : ConstraintSystem p) (b : DegreeBound) :
    s.withinDegreeB b = true ↔ s.withinDegree b := by
  unfold ConstraintSystem.withinDegreeB ConstraintSystem.withinDegree
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hcm => by simpa using hc c hcm, fun bi hbm => ?_⟩
    have := hb bi hbm
    rw [Bool.and_eq_true, List.all_eq_true] at this
    exact ⟨by simpa using this.1, fun e he => by simpa using this.2 e he⟩
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hcm => by simpa using hc c hcm, fun bi hbm => ?_⟩
    rw [Bool.and_eq_true, List.all_eq_true]
    exact ⟨by simpa using (hb bi hbm).1, fun e he => by simpa using (hb bi hbm).2 e he⟩
