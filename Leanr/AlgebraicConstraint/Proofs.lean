import Leanr.AlgebraicConstraint
import Leanr.AffineExpression.Proofs
import Leanr.Expression.Proofs

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- substituteAll preserves evaluation when the substitution map agrees with env. -/
theorem AlgebraicConstraint.substituteAll_eval
    (c : AlgebraicConstraint p)
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h : ∀ x v, m[x]? = some v → env x = v) :
    (c.substituteAll m).eval env = c.eval env := by
  cases c with
  | affine e => exact AffineExpression.substituteAll_eval e m env h
  | general e => exact Expression.substituteAll_eval e m env h

/-- If a constraint evaluates to zero under `env` and `solve?` succeeds,
    then `env` assigns the solved variable to the computed value. -/
theorem AlgebraicConstraint.solve?_sound {p : ℕ} [Fact (Nat.Prime p)]
    (c : AlgebraicConstraint p) (a : Assignment (p := p))
    (env : String → ZMod p)
    (h_solve : c.solve? = some a) (h_zero : c.eval env = 0) :
    env a.var = a.value := by
  cases c with
  | general e => simp [solve?] at h_solve
  | affine e =>
    simp only [solve?] at h_solve
    match h_list : e.affine.toList with
    | [] => simp [h_list] at h_solve
    | [(x, coeff)] =>
      simp only [h_list] at h_solve
      split at h_solve
      · contradiction
      · rename_i hc
        have ha := Option.some.inj h_solve
        rw [eval, AffineExpression.eval_eq_offset_add_sum] at h_zero
        simp [h_list] at h_zero
        have hci : coeff ≠ 0 := hc
        have key : env x = -coeff⁻¹ * e.offset := by
          have h1 : coeff * env x = -e.offset := by
            have := h_zero
            have : coeff * env x = -(e.offset) := by
              calc coeff * env x = 0 - e.offset := by rw [← this]; ring
              _ = -e.offset := by ring
            exact this
          rw [show env x = coeff⁻¹ * (coeff * env x) from by
            rw [← mul_assoc, inv_mul_cancel₀ hci, one_mul]]
          rw [h1]; ring
        rw [← ha]; simp [key]
    | _ :: _ :: _ => simp [h_list] at h_solve
