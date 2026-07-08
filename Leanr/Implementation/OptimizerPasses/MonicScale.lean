import Leanr.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Monic scaling of constraint factors (canonicalization)

An algebraic constraint only matters through its **zero set**, so it may be rescaled by any
*unit* without changing satisfiability — unlike bus expressions, whose values are observable.
This pass canonicalizes every constraint by walking its product tree and scaling each affine
factor to *monic* form (leading coefficient `1`): substitution passes routinely leave factors
multiplied by inverse constants (e.g. a carry `256⁻¹·(b + c − a)` whose booleanity constraint
renders with huge `256⁻¹`-scaled coefficients), and monic scaling turns them back into the
small-coefficient form a hand-written circuit would use, e.g.
`(b + c − a) · (b + c − a − 256) = 0`.

Soundness is field-free: each scaling carries a *checked* unit certificate (`u * v = 1`, with
the ring's `Inv` only used to *propose* `v`), the rewritten factor evaluates to `u ·` the
original, and multiplying an expression by a unit preserves its zero set over any commutative
ring. A new small core (`ConstraintSystem.mapConstraintsIff_correct`) shows that rewriting
constraints by any pointwise zero-set-preserving map is `PassCorrect`. -/

variable {p : ℕ}

/-! ## Scaling with a unit certificate -/

/-- Scale an affine expression to monic form. Returns `(e', u, v)` with the intended invariants
    `e'.eval env = u * e.eval env` and `u * v = 1` (proved below); `(e, 1, 1)` when not
    applicable. -/
def monicScaleAffine (e : Expression p) : Expression p × ZMod p × ZMod p :=
  match linearize e with
  | none => (e, 1, 1)
  | some l =>
    match l.norm.terms with
    | (_, k) :: _ =>
        if k * k⁻¹ = 1 ∧ k ≠ 1 then ((l.norm.scale k⁻¹).toExpr, k⁻¹, k)
        else (e, 1, 1)
    | [] => (e, 1, 1)

theorem monicScaleAffine_eval (e : Expression p) (env : Variable → ZMod p) :
    (monicScaleAffine e).1.eval env = (monicScaleAffine e).2.1 * e.eval env := by
  unfold monicScaleAffine
  split
  · simp
  · rename_i l hlin
    split
    · rename_i y k rest ht
      split_ifs with hk
      · simp only
        rw [LinExpr.toExpr_eval, LinExpr.scale_eval, LinExpr.norm_eval,
            ← linearize_eval e l hlin]
      · simp
    · simp

theorem monicScaleAffine_unit (e : Expression p) :
    (monicScaleAffine e).2.1 * (monicScaleAffine e).2.2 = 1 := by
  unfold monicScaleAffine
  split
  · simp
  · split
    · rename_i y k rest ht
      split_ifs with hk
      · simpa [mul_comm] using hk.1
      · simp
    · simp

theorem monicScaleAffine_vars (e : Expression p) :
    ∀ z ∈ (monicScaleAffine e).1.vars, z ∈ e.vars := by
  intro z hz
  unfold monicScaleAffine at hz
  split at hz
  · exact hz
  · rename_i l hlin
    split at hz
    · rename_i y k rest ht
      split_ifs at hz with hk
      · have h1 := LinExpr.toExpr_vars _ z hz
        rw [LinExpr.scale_terms_fst] at h1
        exact linearize_vars e l hlin z (l.norm_terms_fst z h1)
      · exact hz
    · exact hz

/-- Scale the affine factors of a product tree to monic form, with the accumulated unit
    certificate. -/
def monicScale : Expression p → Expression p × ZMod p × ZMod p
  | .mul a b =>
      match linearize (.mul a b) with
      | some _ => monicScaleAffine (.mul a b)
      | none =>
          (.mul (monicScale a).1 (monicScale b).1,
           (monicScale a).2.1 * (monicScale b).2.1,
           (monicScale a).2.2 * (monicScale b).2.2)
  | e => monicScaleAffine e

theorem monicScale_eval (e : Expression p) (env : Variable → ZMod p) :
    (monicScale e).1.eval env = (monicScale e).2.1 * e.eval env := by
  induction e with
  | const n => exact monicScaleAffine_eval _ env
  | var y => exact monicScaleAffine_eval _ env
  | add a b _ _ => exact monicScaleAffine_eval _ env
  | mul a b iha ihb =>
      rw [monicScale]
      split
      · exact monicScaleAffine_eval _ env
      · show (Expression.mul (monicScale a).1 (monicScale b).1).eval env = _
        show (monicScale a).1.eval env * (monicScale b).1.eval env = _
        rw [iha, ihb]
        show _ = _ * (a.eval env * b.eval env)
        ring

theorem monicScale_unit (e : Expression p) :
    (monicScale e).2.1 * (monicScale e).2.2 = 1 := by
  induction e with
  | const n => exact monicScaleAffine_unit _
  | var y => exact monicScaleAffine_unit _
  | add a b _ _ => exact monicScaleAffine_unit _
  | mul a b iha ihb =>
      rw [monicScale]
      split
      · exact monicScaleAffine_unit _
      · show (monicScale a).2.1 * (monicScale b).2.1
            * ((monicScale a).2.2 * (monicScale b).2.2) = 1
        calc (monicScale a).2.1 * (monicScale b).2.1
              * ((monicScale a).2.2 * (monicScale b).2.2)
            = ((monicScale a).2.1 * (monicScale a).2.2)
              * ((monicScale b).2.1 * (monicScale b).2.2) := by ring
          _ = 1 := by rw [iha, ihb, one_mul]

/-- Unit scaling preserves the zero set (over any commutative ring). -/
theorem monicScale_zero_iff (e : Expression p) (env : Variable → ZMod p) :
    ((monicScale e).1.eval env = 0 ↔ e.eval env = 0) := by
  rw [monicScale_eval]
  constructor
  · intro h
    have := congrArg ((monicScale e).2.2 * ·) h
    simpa [← mul_assoc, mul_comm (monicScale e).2.2 (monicScale e).2.1,
           monicScale_unit e] using this
  · intro h
    rw [h, mul_zero]

theorem monicScale_vars (e : Expression p) : ∀ z ∈ (monicScale e).1.vars, z ∈ e.vars := by
  induction e with
  | const n => exact monicScaleAffine_vars _
  | var y => exact monicScaleAffine_vars _
  | add a b _ _ => exact monicScaleAffine_vars _
  | mul a b iha ihb =>
      intro z hz
      rw [monicScale] at hz
      split at hz
      · exact monicScaleAffine_vars _ z hz
      · simp only [Expression.vars, List.mem_append] at hz ⊢
        exact hz.imp (iha z) (ihb z)

/-! ## The correctness core: zero-set-preserving constraint rewrites -/

/-- Rewrite only the algebraic constraints. -/
def ConstraintSystem.mapConstraints (cs : ConstraintSystem p)
    (g : Expression p → Expression p) : ConstraintSystem p :=
  { cs with algebraicConstraints := cs.algebraicConstraints.map g }

theorem ConstraintSystem.mapConstraints_vars_subset (cs : ConstraintSystem p)
    {g : Expression p → Expression p}
    (hgv : ∀ (c : Expression p) (z : Variable), z ∈ (g c).vars → z ∈ c.vars) :
    ∀ z ∈ (cs.mapConstraints g).vars, z ∈ cs.vars := by
  intro z hz
  rw [ConstraintSystem.mem_vars] at hz ⊢
  rcases hz with ⟨c, hc, hzc⟩ | ⟨bi, hbi, hzbi⟩
  · simp only [ConstraintSystem.mapConstraints, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    exact Or.inl ⟨c0, hc0, hgv c0 z hzc⟩
  · exact Or.inr ⟨bi, hbi, hzbi⟩

/-- Rewriting constraints with any pointwise zero-set-preserving map is `PassCorrect`: the
    satisfying assignments are unchanged, and the (bus-only) side effects are untouched. -/
theorem ConstraintSystem.mapConstraintsIff_correct (cs : ConstraintSystem p)
    (bs : BusSemantics p) (g : Expression p → Expression p)
    (hg : ∀ (c : Expression p) (env : Variable → ZMod p), ((g c).eval env = 0 ↔ c.eval env = 0))
    (hgv : ∀ (c : Expression p) (z : Variable), z ∈ (g c).vars → z ∈ c.vars) :
    PassCorrect cs (cs.mapConstraints g) [] [] bs := by
  have hiff : ∀ env, (cs.mapConstraints g).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    simp only [ConstraintSystem.satisfies, ConstraintSystem.mapConstraints]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨fun c0 hc0 => ?_, hb⟩
      exact (hg c0 env).1 (hc _ (List.mem_map.2 ⟨c0, hc0, rfl⟩))
    · rintro ⟨hc, hb⟩
      refine ⟨fun c hc' => ?_, hb⟩
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
      exact (hg c0 env).2 (hc c0 hc0)
  have hside : ∀ env, (cs.mapConstraints g).sideEffects bs env = cs.sideEffects bs env :=
    fun _ => rfl
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.mapConstraints_vars_subset hgv) ?_
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    exact hinv env ((hiff env).1 hsat) bi hbi
  · intro env hadm hsat
    exact ⟨(hiff env).2 hsat, hadm, by rw [hside]; exact BusState.equiv_refl _⟩

/-! ## The pass -/

/-- The monic-scaling pass: canonicalize every constraint's affine factors to monic form. -/
def monicScalePass : VerifiedPass p := fun cs dsIn bs =>
  guardEmpty dsIn
   ⟨cs.mapConstraints (fun c => (monicScale c).1), [],
    cs.mapConstraintsIff_correct bs _ (fun c env => monicScale_zero_iff c env)
      (fun c z hz => monicScale_vars c z hz)⟩
