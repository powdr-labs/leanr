import ApcOptimizer.Implementation.OptimizerPasses.Measure

set_option autoImplicit false

/-! # Dense simultaneous substitution + `mentions` (Task 3, Gauss foundation, part 4a)

The dense mirror of the *batch* substitution machinery `Expression.substF` /
`ConstraintSystem.substF` (`OptimizerPasses/SubstMap.lean`) and of the syntactic occurrence test
`Expression.mentions` (`OptimizerPasses/Gauss.lean`). These are the dense substitution primitives
the Gauss / domain / flag / rootPair passes consume: `DenseExpr.substF` / `denseBIsubstF` /
`DenseConstraintSystem.substF`, their variable-bound and coverage-preservation lemmas
(`substF_vars` / `substF_covered`), and `DenseExpr.mentions`. All pure/equational and `VarId`-native.

The decode-commutation lemmas that the commutation-era Gauss proof consumed have been removed; the
native Gauss proof (`GaussProof.lean`) needs only these dense cores. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Simultaneous substitution on dense expressions -/

/-- Substitute every `VarId` `i` with `df i = some t` by `t` (one traversal; inserted solutions are
    not re-visited). The dense mirror of `Expression.substF`. -/
def DenseExpr.substF (df : VarId → Option (DenseExpr p)) : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var j => match df j with | some t => t | none => .var j
  | .add a b => .add (a.substF df) (b.substF df)
  | .mul a b => .mul (a.substF df) (b.substF df)

/-- Simultaneous substitution introduces no variable outside `e` and the mapped solutions; each new
    variable comes from a solution `df i = some t` for some `i` *occurring in* `e`. The occurrence of
    `i` in `e` (stronger than the spec `substF_vars`) is what makes coverage preservation gate `df`
    only on valid ids. -/
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

/-- Substitution preserves coverage when every solution `df` produces for a *valid* id is covered.
    (Only valid ids are ever looked up, since `e` is covered — see `substF_vars`.) -/
theorem DenseExpr.substF_covered {reg : VarRegistry} {e : DenseExpr p}
    {df : VarId → Option (DenseExpr p)} (he : e.CoveredBy reg)
    (hdf : ∀ i, reg.Valid i → ∀ t, df i = some t → t.CoveredBy reg) :
    (e.substF df).CoveredBy reg := by
  intro k hk
  rcases DenseExpr.substF_vars df e k hk with h | ⟨i, hi, t, hft, hkt⟩
  · exact he k h
  · exact hdf i (he i hi) t hft k hkt

/-! ## Simultaneous substitution on dense bus interactions and systems -/

/-- Substitute the map `df` in every expression of a dense bus interaction. -/
def denseBIsubstF (bi : BusInteraction (DenseExpr p)) (df : VarId → Option (DenseExpr p)) :
    BusInteraction (DenseExpr p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.substF df,
    payload := bi.payload.map (·.substF df) }

/-- Substitute the map `df` everywhere in a dense constraint system. -/
def DenseConstraintSystem.substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map (·.substF df),
    busInteractions := d.busInteractions.map (denseBIsubstF · df) }

/-- Bus-interaction coverage is preserved by substitution when every `df`-value (for valid ids) is
    covered. -/
theorem denseBIsubstF_covered {reg : VarRegistry} {bi : BusInteraction (DenseExpr p)}
    {df : VarId → Option (DenseExpr p)} (hbi : denseBICovered reg bi)
    (hdf : ∀ i, reg.Valid i → ∀ t, df i = some t → t.CoveredBy reg) :
    denseBICovered reg (denseBIsubstF bi df) := by
  obtain ⟨hm, hp⟩ := hbi
  refine ⟨DenseExpr.substF_covered hm hdf, fun e he => ?_⟩
  simp only [denseBIsubstF, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  exact DenseExpr.substF_covered (hp e0 he0) hdf

/-- Substitution preserves system coverage when every `df`-value (for valid ids) is covered. -/
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

/-- Does the dense expression mention `VarId` `i`? Mirrors `Expression.mentions`. -/
def DenseExpr.mentions (i : VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var j => j == i
  | .add a b => a.mentions i || b.mentions i
  | .mul a b => a.mentions i || b.mentions i

end ApcOptimizer.Dense
