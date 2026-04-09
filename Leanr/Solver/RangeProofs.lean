import Leanr.Solver
import Leanr.AffineExpression.Proofs
import Leanr.RangeConstraint.Proofs

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## Expression range constraint soundness -/

/-- Expression range constraint is sound. -/
theorem Expression.rangeConstraint_sound
    (e : Expression p) (rc_env : String → RangeConstraint p)
    (val_env : String → ZMod p)
    (h_env : ∀ v, (rc_env v).allowsValue (val_env v) = true) :
    (e.rangeConstraint rc_env).allowsValue (e.eval val_env) = true := by
  induction e with
  | const n =>
    simp [Expression.rangeConstraint, Expression.eval]
    exact RangeConstraint.coe_allowsValue n
  | var x =>
    simp [Expression.rangeConstraint, Expression.eval]
    exact h_env x
  | add e1 e2 ih1 ih2 =>
    simp only [Expression.rangeConstraint, Expression.eval]
    exact RangeConstraint.add_sound _ _ _ _ ih1 ih2
  | mul e1 e2 ih1 ih2 =>
    simp only [Expression.rangeConstraint, Expression.eval]
    exact RangeConstraint.mul_sound _ _ _ _ ih1 ih2

/-! ## deduce_variable_range_constraints_from_field soundness -/

/-- Each deduced (var, var_rc) pair has var_rc allowing val_env var,
    provided field_rc allows ae.eval val_env and all variable RCs are sound. -/
theorem deduce_variable_range_constraints_from_field_sound
    (ae : AffineExpression p)
    (field_rc : RangeConstraint p)
    (rc_env : String → RangeConstraint p) (val_env : String → ZMod p)
    (h_field : field_rc.allowsValue (ae.eval val_env) = true)
    (h_env : ∀ v, (rc_env v).allowsValue (val_env v) = true)
    (var : String) (var_rc : RangeConstraint p)
    (h_mem : (var, var_rc) ∈ deduce_variable_range_constraints_from_field ae field_rc rc_env) :
    var_rc.allowsValue (val_env var) = true := by
  unfold deduce_variable_range_constraints_from_field at h_mem
  rw [List.mem_filterMap] at h_mem
  obtain ⟨⟨v, coeff⟩, h_in, h_some⟩ := h_mem
  simp only at h_some
  by_cases h_coeff_zero : coeff = 0
  · simp [h_coeff_zero] at h_some
  · -- coeff ≠ 0
    have h_coeff_ne : coeff ≠ 0 := h_coeff_zero
    simp only [h_coeff_zero, ite_false] at h_some
    -- Get the TreeMap membership
    have h_tree_mem : ae.affine[v]? = some coeff :=
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp h_in
    -- Split on the match for solvedRangeConstraint
    rcases h_solved : ae.solvedRangeConstraint v rc_env with _ | rc_solved
    · rw [h_solved] at h_some; exact absurd h_some nofun
    · rw [h_solved] at h_some
      simp only [Option.some.injEq, Prod.mk.injEq] at h_some
      obtain ⟨h_var_eq, h_rc_eq⟩ := h_some
      subst h_var_eq; subst h_rc_eq
      -- Now we need: (field_rc.multiple coeff⁻¹ + rc_solved).allowsValue (val_env v) = true
      -- By deduce_variable_sound, with h_solved giving us the right RC
      obtain ⟨rc', h_rc'_eq, h_rc'_allows⟩ :=
        AffineExpression.solvedRangeConstraint_sound ae v coeff rc_env val_env
          (fun w hw => h_env w) h_tree_mem h_coeff_ne
      rw [h_solved] at h_rc'_eq
      cases h_rc'_eq
      -- rc_solved = rc', so rc_solved allows -(coeff⁻¹) * restEval
      have h_scaled : (field_rc.multiple coeff⁻¹).allowsValue (coeff⁻¹ * ae.eval val_env) = true :=
        RangeConstraint.multiple_sound field_rc coeff⁻¹ _ h_field
      have h_sum := RangeConstraint.add_sound
        (field_rc.multiple coeff⁻¹) rc_solved
        (coeff⁻¹ * ae.eval val_env) (-(coeff⁻¹) * ae.restEval v val_env)
        h_scaled h_rc'_allows
      -- Show the sum value equals val_env v
      have h_inv : coeff * coeff⁻¹ = 1 := mul_inv_cancel₀ h_coeff_ne
      have h_val_eq : val_env v =
          coeff⁻¹ * ae.eval val_env + -(coeff⁻¹) * ae.restEval v val_env := by
        rw [AffineExpression.eval_split ae v coeff val_env h_tree_mem]
        ring_nf; rw [h_inv]; ring
      rw [h_val_eq, show field_rc.multiple coeff⁻¹ + rc_solved =
          (field_rc.multiple coeff⁻¹).add rc_solved from rfl]
      exact h_sum

/-! ## updateRangeConstraint soundness -/

/-- If the current RC allows a value and the new RC allows the same value,
    then the updated (conjunction) RC also allows it. -/
theorem updateRangeConstraint_sound
    (state : SolverState p) (x : String) (rc : RangeConstraint p) (val : ZMod p)
    (h_cur : (state.getRangeConstraint x).allowsValue val = true)
    (h_new : rc.allowsValue val = true) :
    ((state.updateRangeConstraint x rc).1.getRangeConstraint x).allowsValue val = true := by
  unfold SolverState.updateRangeConstraint
  simp only
  split_ifs
  · exact h_cur
  · simp only [SolverState.getRangeConstraint, Std.HashMap.getElem?_insert, beq_self_eq_true, ite_true, Option.getD]
    exact RangeConstraint.conjunction_sound _ _ _ h_cur h_new
