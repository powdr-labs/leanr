import ApcOptimizer.Implementation.OptimizerPasses.Measure
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Subst

set_option autoImplicit false

/-! # Dense substitution (Task 3, WP-E)

The dense mirror of `Expression.subst`/`ConstraintSystem.subst` — the core variable-elimination
machinery Gauss and the domain passes build on. Unlike the eval-preserving maps (constant folding),
substitution *compares variables* (`if j = i`), so its decode-commutation needs validity: `resolve`
is injective only on valid IDs, so `j = i ↔ resolve j = resolve i` requires `i` and `j` valid. The
commutation lemma `decodeCS_subst` therefore carries coverage/validity hypotheses, and downstream
passes discharge them from the threaded coverage invariant. -/

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

/-- **Substitution commutes with decode** (given `i` valid and `e` covered): decoding a dense
    substitution is the spec substitution of the decoded pieces. -/
theorem VarRegistry.decodeExpr_subst (reg : VarRegistry) {i : VarId} (hi : reg.Valid i)
    (t : DenseExpr p) (e : DenseExpr p) : e.CoveredBy reg →
    reg.decodeExpr (e.subst i t)
      = (reg.decodeExpr e).subst (reg.resolve i) (reg.decodeExpr t) := by
  induction e with
  | const n => intro _; rfl
  | var j =>
      intro hc
      have hjv : reg.Valid j := hc j (by simp [DenseExpr.vars])
      by_cases h : j = i
      · subst h; simp [DenseExpr.subst, VarRegistry.decodeExpr, Expression.subst]
      · simp only [DenseExpr.subst, if_neg h, VarRegistry.decodeExpr, Expression.subst]
        rw [if_neg (fun he => h (reg.resolve_inj hjv hi he))]
  | add a b iha ihb =>
      intro hc
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      simp only [DenseExpr.subst, VarRegistry.decodeExpr, Expression.subst, iha ha, ihb hb]
  | mul a b iha ihb =>
      intro hc
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      simp only [DenseExpr.subst, VarRegistry.decodeExpr, Expression.subst, iha ha, ihb hb]

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

/-- Bus-interaction substitution commutes with decode. -/
theorem VarRegistry.decodeBI_subst (reg : VarRegistry) {i : VarId} (hi : reg.Valid i)
    (t : DenseExpr p) (bi : BusInteraction (DenseExpr p)) (hc : denseBICovered reg bi) :
    reg.decodeBI (denseBIsubst bi i t)
      = (reg.decodeBI bi).subst (reg.resolve i) (reg.decodeExpr t) := by
  obtain ⟨hm, hp⟩ := hc
  simp only [denseBIsubst, VarRegistry.decodeBI, BusInteraction.subst, List.map_map,
    reg.decodeExpr_subst hi t _ hm]
  congr 1
  refine List.map_congr_left (fun e he => ?_)
  simp only [Function.comp_apply, reg.decodeExpr_subst hi t e (hp e he)]

/-- **System substitution commutes with decode** (given `i` valid and the system covered). -/
theorem VarRegistry.decodeCS_subst (reg : VarRegistry) {i : VarId} (hi : reg.Valid i)
    (t : DenseExpr p) (d : DenseConstraintSystem p) (hc : d.CoveredBy reg) :
    reg.decodeCS (d.subst i t)
      = (reg.decodeCS d).subst (reg.resolve i) (reg.decodeExpr t) := by
  obtain ⟨hac, hbi⟩ := hc
  simp only [DenseConstraintSystem.subst, VarRegistry.decodeCS, ConstraintSystem.subst,
    List.map_map]
  congr 1
  · refine List.map_congr_left (fun e he => ?_)
    simp only [Function.comp_apply, reg.decodeExpr_subst hi t e (hac e he)]
  · refine List.map_congr_left (fun bi hbimem => ?_)
    simp only [Function.comp_apply, reg.decodeBI_subst hi t bi (hbi bi hbimem)]

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
