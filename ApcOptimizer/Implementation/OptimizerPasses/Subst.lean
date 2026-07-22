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

theorem DenseExpr.subst_covered {reg : VarRegistry} {e t : DenseExpr p} {i : VarId}
    (he : e.CoveredBy reg) (ht : t.CoveredBy reg) : (e.subst i t).CoveredBy reg := by
  intro k hk
  rcases DenseExpr.subst_vars e i t k hk with h | h
  · exact he k h
  · exact ht k h

/-! ## Substitution on dense constraint systems -/

def denseBIsubst (bi : BusInteraction (DenseExpr p)) (i : VarId) (t : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.subst i t,
    payload := bi.payload.map (·.subst i t) }

def DenseConstraintSystem.subst (d : DenseConstraintSystem p) (i : VarId) (t : DenseExpr p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map (·.subst i t),
    busInteractions := d.busInteractions.map (denseBIsubst · i t) }

theorem DenseConstraintSystem.subst_covered {reg : VarRegistry} {d : DenseConstraintSystem p}
    {t : DenseExpr p} {i : VarId} (hd : d.CoveredBy reg) (ht : t.CoveredBy reg) :
    (d.subst i t).CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hd
  refine ⟨fun e he => ?_, fun bi hbimem => ?_⟩
  · simp only [DenseConstraintSystem.subst, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact DenseExpr.subst_covered (hac e0 he0) ht
  · simp only [DenseConstraintSystem.subst, List.mem_map] at hbimem
    obtain ⟨bi0, hbi0, rfl⟩ := hbimem
    obtain ⟨hm, hp⟩ := hbi bi0 hbi0
    refine ⟨DenseExpr.subst_covered hm ht, fun e he => ?_⟩
    simp only [denseBIsubst, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact DenseExpr.subst_covered (hp e0 he0) ht

end ApcOptimizer.Dense
