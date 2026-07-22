import ApcOptimizer.Spec
import ApcOptimizer.Implementation.Variable

set_option autoImplicit false

variable {p : ℕ}

/-! # Optimizer scaffolding

The reusable framework for building the optimizer out of small, individually-proven passes: the
relation glue (`≈`, `ConstraintSystem.implies`/`.reconstructs`), `PassCorrect`, and `VerifiedPass`
bundling a pass with its own `PassCorrect` proof. -/

theorem BusState.equiv_refl (s : BusState p) : s ≈ s :=
  fun _ => rfl

theorem BusState.equiv_symm {s t : BusState p} (h : s ≈ t) : t ≈ s :=
  fun message => (h message).symm

theorem BusState.equiv_trans {s t u : BusState p} (h1 : s ≈ t) (h2 : t ≈ u) : s ≈ u :=
  fun message => (h1 message).trans (h2 message)

/-- Soundness half of a replacement: every satisfying assignment of `self` maps to one of `other`
    with the same stateful side effects. The spec's `isSoundReplacementOf` is this plus invariant
    preservation. -/
def ConstraintSystem.implies (self other : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  ∀ env, self.satisfies busSemantics env →
    ∃ env', other.satisfies busSemantics env' ∧
      self.sideEffects busSemantics env ≈ other.sideEffects busSemantics env'

/-- Every no-powdr-ID variable of `cs` is computed by `ds`'s method for it, reading only powdr-ID
    variables from `inputVars`. Threaded through passes; the pipeline top uses it to match the
    spec's `witgen` output and `Derivations.cover`. -/
def ConstraintSystem.reconstructs (inputVars : List Variable) (cs : ConstraintSystem p)
    (ds : Derivations p) (e : Variable → ZMod p) : Prop :=
  ∀ v ∈ cs.vars, v.powdrId? = none →
    ∃ cm, Derivations.methodFor ds v = some cm ∧
      (∀ x ∈ cm.vars, x.powdrId?.isSome) ∧
      (∀ x ∈ cm.vars, x ∈ inputVars) ∧
      cm.eval e = e v

theorem ConstraintSystem.implies_refl (cs : ConstraintSystem p) (busSemantics : BusSemantics p) :
    cs.implies cs busSemantics :=
  fun env hsat => ⟨env, hsat, BusState.equiv_refl _⟩

theorem ConstraintSystem.implies_trans {a b c : ConstraintSystem p} {busSemantics : BusSemantics p}
    (h1 : a.implies b busSemantics) (h2 : b.implies c busSemantics) : a.implies c busSemantics :=
  fun env hsat =>
    let ⟨env', hb, hab⟩ := h1 env hsat
    let ⟨env'', hc, hbc⟩ := h2 env' hb
    ⟨env'', hc, BusState.equiv_trans hab hbc⟩

/-! ## Precomputed primality witness

`decide (Nat.Prime p)` is expensive (≈ √p trial division). `PrimeWitness p` computes it once and
carries the `Bool` with a proof that `true` entails `Nat.Prime p`; the pipeline threads one to each
prime-gated pass, which branches on it in O(1). -/

structure PrimeWitness (p : ℕ) where
  isPrime : Bool
  /-- `isPrime = true` entails `Nat.Prime p` — the fact prime-gated passes consume. -/
  correct : isPrime = true → Nat.Prime p

/-- The single `decide (Nat.Prime p)` per optimizer run. -/
def PrimeWitness.of (p : ℕ) : PrimeWitness p :=
  ⟨decide (Nat.Prime p), fun h => of_decide_eq_true h⟩

/-! ## Verified passes

A `VerifiedPass` maps a constraint system to a new one bundled with a `PassCorrect` proof, so a
pass cannot be written without discharging its obligations. Passes compose with `andThen`. -/

/-- The per-pass correctness obligation: `out` is sound (`implies cs`), preserves invariants, adds
    no new powdr-ID column, and is real-trace complete — every admissible satisfying assignment of
    `cs` extends to one of `out` with equal side effects, preserving input-column values and
    reconstructing `out`'s derived variables. `dsLocal` are the derivations this step introduces,
    concatenated onto any incoming `dsIn` so passes compose. -/
def PassCorrect (cs out : ConstraintSystem p) (dsLocal : Derivations p) (bs : BusSemantics p) :
    Prop :=
  out.implies cs bs ∧
  (cs.guaranteesInvariants bs → out.guaranteesInvariants bs) ∧
  (∀ v ∈ out.vars, v.powdrId?.isSome → v ∈ cs.vars) ∧
  (∀ env, cs.admissible bs env → cs.satisfies bs env →
    ∃ env', out.satisfies bs env' ∧ out.admissible bs env' ∧
      cs.sideEffects bs env ≈ out.sideEffects bs env' ∧
      (∀ v, v.powdrId?.isSome → env' v = env v) ∧
      (∀ inputVars, (∀ v ∈ cs.vars, v.powdrId?.isSome → v ∈ inputVars) →
        ∀ dsIn, cs.reconstructs inputVars dsIn env →
          out.reconstructs inputVars (dsIn ++ dsLocal) env'))

theorem PassCorrect.refl (cs : ConstraintSystem p) (bs : BusSemantics p) :
    PassCorrect cs cs [] bs :=
  ⟨cs.implies_refl bs, _root_.id, fun _ hv _ => hv,
   fun env hadm hsat =>
     ⟨env, hsat, hadm, BusState.equiv_refl _,
       ⟨fun _ _ => rfl, fun _ _ dsIn hrec => by rwa [List.append_nil]⟩⟩⟩

/-- Sequential composition: derivations concatenate, soundness/invariants compose, reconstruction
    chains. -/
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
    ⟨fun v hpw => by rw [hpw2 v hpw, hpw1 v hpw],
      fun inputVars hpowIn dsIn hrec => ?_⟩⟩
  have hmidIn : ∀ v ∈ mid.vars, v.powdrId?.isSome → v ∈ inputVars :=
    fun v hv hpw => hpowIn v (hf3 v hv hpw) hpw
  have := hr2 inputVars hmidIn (dsIn ++ df) (hr1 inputVars hpowIn dsIn hrec)
  rwa [List.append_assoc] at this

/-- `PassCorrect` for a pass whose completeness witness is the input assignment itself and which
    introduces no new variables (`out.vars ⊆ cs.vars`); emits no derivations. -/
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
  refine ⟨env, ho1, ho2, ho3, ⟨fun _ _ => rfl, fun _ _ dsIn hrec => ?_⟩⟩
  rw [List.append_nil]
  exact fun v hvout hvnone => hrec v (hsub v hvout) hvnone

/-- A `PassCorrect` gives the audited `isSoundReplacementOf`. The completeness half is discharged
    at the pipeline top (`Implementation/Optimizer.lean`). -/
theorem PassCorrect.toSound {cs out : ConstraintSystem p} {ds : Derivations p}
    {bs : BusSemantics p} (h : PassCorrect cs out ds bs) : out.isSoundReplacementOf cs bs :=
  ⟨h.1, h.2.1⟩

/-- The result of a verified pass: transformed system, introduced derivations, correctness proof. -/
structure PassResult {p : ℕ} (cs : ConstraintSystem p) (bs : BusSemantics p) where
  out : ConstraintSystem p
  derivs : Derivations p
  correct : PassCorrect cs out derivs bs

/-! ## Variable-set membership -/

/-- A variable of `cs.vars` occurs in some constraint, multiplicity, or payload expression. -/
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

A `Bool` twin of the spec's `ConstraintSystem.withinDegree` for the degree guard to branch on. -/

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
