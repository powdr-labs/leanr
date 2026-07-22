import ApcOptimizer.Implementation.OptimizerPasses.MonicScale

set_option autoImplicit false

/-! # Soundness for the dense monic scaling of constraint factors

`DensePassCorrect` proof for `MonicScale.lean`, lifted through `DenseVerifiedPassW.of`. Field-free:
each scaling carries a checked unit certificate (`u * v = 1`), and multiplying a constraint by a
unit preserves its zero set; only `algebraicConstraints` is touched, so side effects and
admissibility are unchanged. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The monic-scaled affine expression evaluates to its unit multiplier times the original. -/
theorem denseMonicScaleAffine_eval (e : DenseExpr p) (denv : VarId → ZMod p) :
    (denseMonicScaleAffine e).1.eval denv = (denseMonicScaleAffine e).2.1 * e.eval denv := by
  unfold denseMonicScaleAffine
  split
  · simp
  · rename_i l hlin
    split
    · rename_i y k rest ht
      split_ifs with hk
      · simp only
        rw [DenseLinExpr.toExpr_eval, DenseLinExpr.scale_eval, DenseLinExpr.norm_eval,
            denseLinearize_eval e l hlin]
      · simp
    · simp

/-- The affine scaling's certificate is a genuine unit. -/
theorem denseMonicScaleAffine_unit (e : DenseExpr p) :
    (denseMonicScaleAffine e).2.1 * (denseMonicScaleAffine e).2.2 = 1 := by
  unfold denseMonicScaleAffine
  split
  · simp
  · split
    · rename_i y k rest ht
      split_ifs with hk
      · simpa [mul_comm] using hk.1
      · simp
    · simp

/-- Monic scaling of an affine expression introduces no new variable. -/
theorem denseMonicScaleAffine_vars (e : DenseExpr p) :
    ∀ z ∈ (denseMonicScaleAffine e).1.vars, z ∈ e.vars := by
  intro z hz
  unfold denseMonicScaleAffine at hz
  split at hz
  · exact hz
  · rename_i l hlin
    split at hz
    · rename_i y k rest ht
      split_ifs at hz with hk
      · have h1 := DenseLinExpr.toExpr_vars _ z hz
        rw [DenseLinExpr.scale_terms_fst] at h1
        exact denseLinearize_vars e l hlin z (l.norm_terms_fst z h1)
      · exact hz
    · exact hz

/-- The monic-scaled product tree evaluates to its accumulated unit multiplier times the original. -/
theorem denseMonicScale_eval (e : DenseExpr p) (denv : VarId → ZMod p) :
    (denseMonicScale e).1.eval denv = (denseMonicScale e).2.1 * e.eval denv := by
  induction e with
  | const n => exact denseMonicScaleAffine_eval _ denv
  | var y => exact denseMonicScaleAffine_eval _ denv
  | add a b _ _ => exact denseMonicScaleAffine_eval _ denv
  | mul a b iha ihb =>
      rw [denseMonicScale]
      split
      · exact denseMonicScaleAffine_eval _ denv
      · simp only [DenseExpr.eval]
        rw [iha, ihb]
        ring

/-- The product tree's accumulated certificate is a genuine unit. -/
theorem denseMonicScale_unit (e : DenseExpr p) :
    (denseMonicScale e).2.1 * (denseMonicScale e).2.2 = 1 := by
  induction e with
  | const n => exact denseMonicScaleAffine_unit _
  | var y => exact denseMonicScaleAffine_unit _
  | add a b _ _ => exact denseMonicScaleAffine_unit _
  | mul a b iha ihb =>
      rw [denseMonicScale]
      split
      · exact denseMonicScaleAffine_unit _
      · show (denseMonicScale a).2.1 * (denseMonicScale b).2.1
            * ((denseMonicScale a).2.2 * (denseMonicScale b).2.2) = 1
        calc (denseMonicScale a).2.1 * (denseMonicScale b).2.1
              * ((denseMonicScale a).2.2 * (denseMonicScale b).2.2)
            = ((denseMonicScale a).2.1 * (denseMonicScale a).2.2)
              * ((denseMonicScale b).2.1 * (denseMonicScale b).2.2) := by ring
          _ = 1 := by rw [iha, ihb, one_mul]

/-- Unit scaling preserves the zero set (over any commutative ring). -/
theorem denseMonicScale_zero_iff (e : DenseExpr p) (denv : VarId → ZMod p) :
    ((denseMonicScale e).1.eval denv = 0 ↔ e.eval denv = 0) := by
  rw [denseMonicScale_eval]
  constructor
  · intro h
    have := congrArg ((denseMonicScale e).2.2 * ·) h
    simpa [← mul_assoc, mul_comm (denseMonicScale e).2.2 (denseMonicScale e).2.1,
           denseMonicScale_unit e] using this
  · intro h
    rw [h, mul_zero]

/-- Monic scaling of a product tree introduces no new variable. -/
theorem denseMonicScale_vars (e : DenseExpr p) : ∀ z ∈ (denseMonicScale e).1.vars, z ∈ e.vars := by
  induction e with
  | const n => exact denseMonicScaleAffine_vars _
  | var y => exact denseMonicScaleAffine_vars _
  | add a b _ _ => exact denseMonicScaleAffine_vars _
  | mul a b iha ihb =>
      intro z hz
      rw [denseMonicScale] at hz
      split at hz
      · exact denseMonicScaleAffine_vars _ z hz
      · simp only [DenseExpr.vars, List.mem_append] at hz ⊢
        exact hz.imp (iha z) (ihb z)

/-- Monic-scaling correctness: every constraint becomes a unit multiple of itself, so the
    satisfying assignments coincide. -/
theorem denseMonicScaleF_correct (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d (denseMonicScaleF d) [] bs := by
  have hsatiff : ∀ denv, (denseMonicScaleF d).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    simp only [denseMonicScaleF, DenseConstraintSystem.mapConstraints,
      DenseConstraintSystem.satisfies]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨fun c0 hc0 => ?_, hb⟩
      exact (denseMonicScale_zero_iff c0 denv).1 (hc _ (List.mem_map.2 ⟨c0, hc0, rfl⟩))
    · rintro ⟨hc, hb⟩
      refine ⟨fun c hc' => ?_, hb⟩
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
      exact (denseMonicScale_zero_iff c0 denv).2 (hc c0 hc0)
  have hsub : ∀ i ∈ (denseMonicScaleF d).occ, i ∈ d.occ := by
    intro i hi
    simp only [DenseConstraintSystem.occ, denseMonicScaleF, DenseConstraintSystem.mapConstraints,
      List.mem_append, List.mem_flatMap] at hi ⊢
    rcases hi with ⟨c, hc, hic⟩ | hbus
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      exact Or.inl ⟨c0, hc0, denseMonicScale_vars c0 i hic⟩
    · exact Or.inr hbus
  refine DensePassCorrect.ofEnvEq ?_ ?_ hsub ?_
  · intro denv hsatout
    exact ⟨denv, (hsatiff denv).1 hsatout, BusState.equiv_refl _⟩
  · intro hinv denv hsatout bi hbi
    exact hinv denv ((hsatiff denv).1 hsatout) bi hbi
  · intro denv hadm hsat
    exact ⟨(hsatiff denv).2 hsat, hadm, BusState.equiv_refl _⟩

/-- The dense monic-scaling pass. -/
def denseMonicScalePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => denseMonicScaleF d)
    (fun _ _ _ => [])
    (fun _ _ _ d hcov => by
      obtain ⟨hac, hbi⟩ := hcov
      simp only [DenseConstraintSystem.CoveredBy, denseMonicScaleF,
        DenseConstraintSystem.mapConstraints]
      refine ⟨fun c hc => ?_, hbi⟩
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      intro i hi
      exact hac c0 hc0 i (denseMonicScale_vars c0 i hi))
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseMonicScaleF_correct bs reg.isInput d)

end ApcOptimizer.Dense
