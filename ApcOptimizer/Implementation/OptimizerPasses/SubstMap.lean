import ApcOptimizer.Implementation.OptimizerPasses.Measure

set_option autoImplicit false

/-! # Dense simultaneous substitution + `mentions`

Batch substitution `DenseExpr.substF` / `DenseConstraintSystem.substF` (with its variable-bound and
coverage lemmas) and the syntactic occurrence test `DenseExpr.mentions`, consumed by the Gauss /
domain / flag / rootPair passes. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Simultaneous substitution on dense expressions -/

/-- Substitute every `VarId` `i` with `df i = some t` by `t` (one traversal; inserted solutions are
    not re-visited). -/
def DenseExpr.substF (df : VarId → Option (DenseExpr p)) : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var j => match df j with | some t => t | none => .var j
  | .add a b => .add (a.substF df) (b.substF df)
  | .mul a b => .mul (a.substF df) (b.substF df)

/-- Every new variable of `e.substF df` comes from a solution `df i = some t` for an `i` occurring
    in `e` — which is what lets coverage gate `df` only on valid ids (see `substF_covered`). -/
theorem DenseExpr.substF_vars (df : VarId → Option (DenseExpr p)) (e : DenseExpr p) :
    ∀ k ∈ (e.substF df).vars,
      k ∈ e.vars ∨ ∃ i ∈ e.vars, ∃ t, df i = some t ∧ k ∈ t.vars := by
  induction e with
  | const n => intro k hk; simp [DenseExpr.substF, DenseExpr.vars] at hk
  | var j =>
      intro k hk
      cases hdf : df j with
      | none =>
          simp only [DenseExpr.substF, hdf] at hk
          exact Or.inl hk
      | some t =>
          simp only [DenseExpr.substF, hdf] at hk
          exact Or.inr ⟨j, by simp [DenseExpr.vars], t, hdf, hk⟩
  | add a b iha ihb =>
      intro k hk
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hk
      rcases hk with hk | hk
      · rcases iha k hk with h | ⟨i, hi, t, hft, hkt⟩
        · exact Or.inl (List.mem_append.2 (Or.inl h))
        · exact Or.inr ⟨i, List.mem_append.2 (Or.inl hi), t, hft, hkt⟩
      · rcases ihb k hk with h | ⟨i, hi, t, hft, hkt⟩
        · exact Or.inl (List.mem_append.2 (Or.inr h))
        · exact Or.inr ⟨i, List.mem_append.2 (Or.inr hi), t, hft, hkt⟩
  | mul a b iha ihb =>
      intro k hk
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hk
      rcases hk with hk | hk
      · rcases iha k hk with h | ⟨i, hi, t, hft, hkt⟩
        · exact Or.inl (List.mem_append.2 (Or.inl h))
        · exact Or.inr ⟨i, List.mem_append.2 (Or.inl hi), t, hft, hkt⟩
      · rcases ihb k hk with h | ⟨i, hi, t, hft, hkt⟩
        · exact Or.inl (List.mem_append.2 (Or.inr h))
        · exact Or.inr ⟨i, List.mem_append.2 (Or.inr hi), t, hft, hkt⟩

/-- Coverage is preserved when every solution `df` produces for a *valid* id is covered (only valid
    ids are looked up when `e` is covered — see `substF_vars`). -/
theorem DenseExpr.substF_covered {reg : VarRegistry} {e : DenseExpr p}
    {df : VarId → Option (DenseExpr p)} (he : e.CoveredBy reg)
    (hdf : ∀ i, reg.Valid i → ∀ t, df i = some t → t.CoveredBy reg) :
    (e.substF df).CoveredBy reg := by
  intro k hk
  rcases DenseExpr.substF_vars df e k hk with h | ⟨i, hi, t, hft, hkt⟩
  · exact he k h
  · exact hdf i (he i hi) t hft k hkt

/-! ## Simultaneous substitution on dense bus interactions and systems -/

def denseBIsubstF (bi : BusInteraction (DenseExpr p)) (df : VarId → Option (DenseExpr p)) :
    BusInteraction (DenseExpr p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.substF df,
    payload := bi.payload.map (·.substF df) }

def DenseConstraintSystem.substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map (·.substF df),
    busInteractions := d.busInteractions.map (denseBIsubstF · df) }

theorem denseBIsubstF_covered {reg : VarRegistry} {bi : BusInteraction (DenseExpr p)}
    {df : VarId → Option (DenseExpr p)} (hbi : denseBICovered reg bi)
    (hdf : ∀ i, reg.Valid i → ∀ t, df i = some t → t.CoveredBy reg) :
    denseBICovered reg (denseBIsubstF bi df) := by
  obtain ⟨hm, hp⟩ := hbi
  refine ⟨DenseExpr.substF_covered hm hdf, fun e he => ?_⟩
  simp only [denseBIsubstF, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  exact DenseExpr.substF_covered (hp e0 he0) hdf

theorem DenseConstraintSystem.substF_covered {reg : VarRegistry} {d : DenseConstraintSystem p}
    {df : VarId → Option (DenseExpr p)} (hd : d.CoveredBy reg)
    (hdf : ∀ i, reg.Valid i → ∀ t, df i = some t → t.CoveredBy reg) :
    (d.substF df).CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hd
  refine ⟨fun e he => ?_, fun bi hbimem => ?_⟩
  · simp only [DenseConstraintSystem.substF, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact DenseExpr.substF_covered (hac e0 he0) hdf
  · simp only [DenseConstraintSystem.substF, List.mem_map] at hbimem
    obtain ⟨bi0, hbi0, rfl⟩ := hbimem
    exact denseBIsubstF_covered (hbi bi0 hbi0) hdf

/-! ## The syntactic occurrence test -/

def DenseExpr.mentions (i : VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var j => j == i
  | .add a b => a.mentions i || b.mentions i
  | .mul a b => a.mentions i || b.mentions i

end ApcOptimizer.Dense
