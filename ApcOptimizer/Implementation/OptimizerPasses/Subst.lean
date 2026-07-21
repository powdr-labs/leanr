import ApcOptimizer.Implementation.OptimizerPasses.Measure

set_option autoImplicit false

/-! # Dense substitution (Task 3, WP-E)

The dense mirror of `Expression.subst`/`ConstraintSystem.subst` — the core variable-elimination
machinery Gauss and the domain passes build on. The runtime cores (`DenseExpr.subst`,
`denseBIsubst`, `DenseConstraintSystem.subst`) and their variable-bound / coverage-preservation
lemmas (`subst_vars`, `subst_covered`) are `VarId`-native; the decode-commutation lemmas the
commutation-era ports used have been removed (their consumers converted to native proofs). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Substitution on dense expressions -/

/-- Substitute `VarId` `i` by dense expression `t` throughout a dense expression. -/
def DenseExpr.subst (e : DenseExpr p) (i : VarId) (t : DenseExpr p) : DenseExpr p :=
  match e with
  | .const n => .const n
  | .var j => if j = i then t else .var j
  | .add a b => .add (a.subst i t) (b.subst i t)
  | .mul a b => .mul (a.subst i t) (b.subst i t)

/-- Substitution introduces no variable outside `e` and `t`. -/
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

/-- Substitution preserves coverage when the substituted expression is covered. -/
theorem DenseExpr.subst_covered {reg : VarRegistry} {e t : DenseExpr p} {i : VarId}
    (he : e.CoveredBy reg) (ht : t.CoveredBy reg) : (e.subst i t).CoveredBy reg := by
  intro k hk
  rcases DenseExpr.subst_vars e i t k hk with h | h
  · exact he k h
  · exact ht k h

/-! ## Substitution on dense constraint systems -/

/-- Substitute `i := t` in a dense bus interaction. -/
def denseBIsubst (bi : BusInteraction (DenseExpr p)) (i : VarId) (t : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.subst i t,
    payload := bi.payload.map (·.subst i t) }

/-- Substitute `i := t` everywhere in a dense constraint system. -/
def DenseConstraintSystem.subst (d : DenseConstraintSystem p) (i : VarId) (t : DenseExpr p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map (·.subst i t),
    busInteractions := d.busInteractions.map (denseBIsubst · i t) }

/-- Substitution preserves system coverage when `t` is covered. -/
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
