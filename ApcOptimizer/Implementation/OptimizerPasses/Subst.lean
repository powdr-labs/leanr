import ApcOptimizer.Implementation.OptimizerPasses.Measure

set_option autoImplicit false

/-! # Dense substitution

Single-variable substitution over `DenseExpr`/`DenseConstraintSystem` (the variable-elimination
core Gauss and the domain passes build on), with its variable-bound and coverage lemmas. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Substitution on dense expressions -/

def DenseExpr.subst (e : DenseExpr p) (i : VarId) (t : DenseExpr p) : DenseExpr p :=
  match e with
  | .const n => .const n
  | .var j => if j = i then t else .var j
  | .add a b => .add (a.subst i t) (b.subst i t)
  | .mul a b => .mul (a.subst i t) (b.subst i t)

theorem DenseExpr.subst_vars (e : DenseExpr p) (i : VarId) (t : DenseExpr p) :
    ∀ k ∈ (e.subst i t).vars, k ∈ e.vars ∨ k ∈ t.vars := by
  induction e with
  | const n => intro k hk; simp [DenseExpr.subst, DenseExpr.vars] at hk
  | var j =>
      intro k hk
      simp only [DenseExpr.subst] at hk
      by_cases h : j = i
      · rw [if_pos h] at hk; exact Or.inr hk
      · rw [if_neg h] at hk; exact Or.inl hk
  | add a b iha ihb =>
      intro k hk
      simp only [DenseExpr.subst, DenseExpr.vars, List.mem_append] at hk
      rcases hk with hk | hk
      · exact (iha k hk).imp (List.mem_append.2 <| Or.inl ·) id
      · exact (ihb k hk).imp (List.mem_append.2 <| Or.inr ·) id
  | mul a b iha ihb =>
      intro k hk
      simp only [DenseExpr.subst, DenseExpr.vars, List.mem_append] at hk
      rcases hk with hk | hk
      · exact (iha k hk).imp (List.mem_append.2 <| Or.inl ·) id
      · exact (ihb k hk).imp (List.mem_append.2 <| Or.inr ·) id

end ApcOptimizer.Dense
