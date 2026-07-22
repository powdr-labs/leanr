import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Shared dense expression operations + the dense constant-fold pass

`DenseConstraintSystem.mapExpr g` maps every expression; when `g` is eval-preserving and adds no
variables it preserves the dense semantics (`mapExpr_satisfies` etc.), which is what an
eval-preserving pass discharges its `DensePassCorrect` with. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense expression maps -/

/-- Apply `g` to every expression of a dense constraint system. -/
def DenseConstraintSystem.mapExpr (d : DenseConstraintSystem p) (g : DenseExpr p → DenseExpr p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map g,
    busInteractions := d.busInteractions.map
      (fun bi => { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g }) }

/-- If `g` introduces no new dense variables per expression, `mapExpr g` preserves coverage. -/
theorem DenseConstraintSystem.mapExpr_covered {reg : VarRegistry} {g : DenseExpr p → DenseExpr p}
    (hgv : ∀ (e : DenseExpr p) (i : VarId), i ∈ (g e).vars → i ∈ e.vars)
    {d : DenseConstraintSystem p} (hc : d.CoveredBy reg) : (d.mapExpr g).CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hc
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [DenseConstraintSystem.mapExpr, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact fun i hi => hac e0 he0 i (hgv e0 i hi)
  · intro bi hbimem
    simp only [DenseConstraintSystem.mapExpr, List.mem_map] at hbimem
    obtain ⟨bi0, hbi0, rfl⟩ := hbimem
    obtain ⟨hm, hp⟩ := hbi bi0 hbi0
    refine ⟨fun i hi => hm i (hgv bi0.multiplicity i hi), fun e he => ?_⟩
    simp only [List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact fun i hi => hp e0 he0 i (hgv e0 i hi)

/-! ## Dense constant folding -/

/-- Smart addition on dense expressions. -/
def DenseExpr.foldAdd (a b : DenseExpr p) : DenseExpr p :=
  match a, b with
  | .const m, .const n => .const (m + n)
  | .const m, b => if m = 0 then b else .add (.const m) b
  | a, .const n => if n = 0 then a else .add a (.const n)
  | a, b => .add a b

/-- Smart multiplication on dense expressions. -/
def DenseExpr.foldMul (a b : DenseExpr p) : DenseExpr p :=
  match a, b with
  | .const m, .const n => .const (m * n)
  | .const m, b => if m = 0 then .const 0 else if m = 1 then b else .mul (.const m) b
  | a, .const n => if n = 0 then .const 0 else if n = 1 then a else .mul a (.const n)
  | a, b => .mul a b

/-- Bottom-up constant folding: evaluates constant subexpressions and drops `+0`, `*1`, `*0`.
    E.g. `2 * 3 + x` folds to `6 + x`, and `1 * x + 0` to `x`. -/
def DenseExpr.fold : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var i => .var i
  | .add a b => a.fold.foldAdd b.fold
  | .mul a b => a.fold.foldMul b.fold

theorem DenseExpr.foldAdd_vars (a b : DenseExpr p) :
    ∀ i ∈ (a.foldAdd b).vars, i ∈ a.vars ++ b.vars := by
  intro i hi
  unfold DenseExpr.foldAdd at hi
  split at hi <;> (try split_ifs at hi) <;> simp_all [DenseExpr.vars]

theorem DenseExpr.foldMul_vars (a b : DenseExpr p) :
    ∀ i ∈ (a.foldMul b).vars, i ∈ a.vars ++ b.vars := by
  intro i hi
  unfold DenseExpr.foldMul at hi
  split at hi <;> (try split_ifs at hi) <;> simp_all [DenseExpr.vars]

theorem DenseExpr.fold_vars (e : DenseExpr p) : ∀ i ∈ e.fold.vars, i ∈ e.vars := by
  induction e with
  | const n => intro i hi; simp [DenseExpr.fold, DenseExpr.vars] at hi
  | var j => intro i hi; simpa [DenseExpr.fold] using hi
  | add a b iha ihb =>
      intro i hi
      rw [DenseExpr.fold] at hi
      rcases List.mem_append.1 (DenseExpr.foldAdd_vars _ _ i hi) with h | h
      · exact List.mem_append.2 (Or.inl (iha i h))
      · exact List.mem_append.2 (Or.inr (ihb i h))
  | mul a b iha ihb =>
      intro i hi
      rw [DenseExpr.fold] at hi
      rcases List.mem_append.1 (DenseExpr.foldMul_vars _ _ i hi) with h | h
      · exact List.mem_append.2 (Or.inl (iha i h))
      · exact List.mem_append.2 (Or.inr (ihb i h))

/-! ## Eval-preservation of the dense fold -/

theorem DenseExpr.foldAdd_eval (a b : DenseExpr p) (denv : VarId → ZMod p) :
    (a.foldAdd b).eval denv = a.eval denv + b.eval denv := by
  unfold DenseExpr.foldAdd
  split <;> (try split_ifs) <;> simp_all [DenseExpr.eval]

theorem DenseExpr.foldMul_eval (a b : DenseExpr p) (denv : VarId → ZMod p) :
    (a.foldMul b).eval denv = a.eval denv * b.eval denv := by
  unfold DenseExpr.foldMul
  split <;> (try split_ifs) <;> simp_all [DenseExpr.eval]

theorem DenseExpr.fold_eval (e : DenseExpr p) (denv : VarId → ZMod p) :
    e.fold.eval denv = e.eval denv := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => rw [DenseExpr.fold, DenseExpr.foldAdd_eval, iha, ihb]; rfl
  | mul a b iha ihb => rw [DenseExpr.fold, DenseExpr.foldMul_eval, iha, ihb]; rfl

/-! ## `mapExpr` with an eval-preserving map preserves the dense semantics

`hg` = value-preservation of `g`; `hgv` = introduces no new variables. -/

variable {g : DenseExpr p → DenseExpr p}

theorem denseBIEval_mapExpr (hg : ∀ (e : DenseExpr p) (denv : VarId → ZMod p),
    (g e).eval denv = e.eval denv) (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p) :
    denseBIEval { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g } denv
      = denseBIEval bi denv := by
  simp only [denseBIEval, hg, List.map_map, Function.comp_def]

theorem DenseConstraintSystem.mapExpr_satisfies (hg : ∀ (e : DenseExpr p) (denv : VarId → ZMod p),
    (g e).eval denv = e.eval denv) (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (denv : VarId → ZMod p) : (d.mapExpr g).satisfies bs denv ↔ d.satisfies bs denv := by
  unfold DenseConstraintSystem.satisfies DenseConstraintSystem.mapExpr
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · have := h1 (g c) c hc rfl; rwa [hg] at this
    · have := h2 _ bi hbi rfl; rwa [denseBIEval_mapExpr hg] at this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro c c0 hc0 rfl; rw [hg]; exact h1 c0 hc0
    · rintro bi bi0 hbi0 rfl; rw [denseBIEval_mapExpr hg]; exact h2 bi0 hbi0

theorem DenseConstraintSystem.mapExpr_busInteractions (d : DenseConstraintSystem p)
    (g : DenseExpr p → DenseExpr p) :
    (d.mapExpr g).busInteractions = d.busInteractions.map
      (fun bi => { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g }) := rfl

theorem DenseConstraintSystem.mapExpr_admissible (hg : ∀ (e : DenseExpr p) (denv : VarId → ZMod p),
    (g e).eval denv = e.eval denv) (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (denv : VarId → ZMod p) : (d.mapExpr g).admissible bs denv ↔ d.admissible bs denv := by
  have hmap : (d.mapExpr g).busInteractions.map (fun bi => denseBIEval bi denv)
      = d.busInteractions.map (fun bi => denseBIEval bi denv) := by
    rw [DenseConstraintSystem.mapExpr_busInteractions, List.map_map]
    refine List.map_congr_left (fun bi _ => ?_)
    simp only [Function.comp_apply]; exact denseBIEval_mapExpr hg bi denv
  have heq : (d.mapExpr g).admissible bs denv = d.admissible bs denv := by
    unfold DenseConstraintSystem.admissible; rw [hmap]
  exact iff_of_eq heq

theorem DenseConstraintSystem.mapExpr_sideEffects (hg : ∀ (e : DenseExpr p) (denv : VarId → ZMod p),
    (g e).eval denv = e.eval denv) (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (denv : VarId → ZMod p) : (d.mapExpr g).sideEffects bs denv = d.sideEffects bs denv := by
  unfold DenseConstraintSystem.sideEffects
  rw [DenseConstraintSystem.mapExpr_busInteractions,
    filter_map_busId_comm d.busInteractions
      (fun bi => { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g }) bs
      (fun _ => rfl),
    List.map_map]
  refine List.map_congr_left (fun bi _ => ?_)
  simp only [Function.comp_apply, denseBIEval_mapExpr hg]

theorem DenseConstraintSystem.mapExpr_guaranteesInvariants
    (hg : ∀ (e : DenseExpr p) (denv : VarId → ZMod p), (g e).eval denv = e.eval denv)
    {d : DenseConstraintSystem p} {bs : BusSemantics p} (h : d.guaranteesInvariants bs) :
    (d.mapExpr g).guaranteesInvariants bs := by
  intro denv hsat bi' hbi'
  have hsatd : d.satisfies bs denv := (DenseConstraintSystem.mapExpr_satisfies hg d bs denv).mp hsat
  rw [DenseConstraintSystem.mapExpr_busInteractions, List.mem_map] at hbi'
  obtain ⟨bi0, hbi0, rfl⟩ := hbi'
  rw [denseBIEval_mapExpr hg]
  exact h denv hsatd bi0 hbi0

theorem DenseConstraintSystem.mapExpr_occ_subset
    (hgv : ∀ (e : DenseExpr p) (i : VarId), i ∈ (g e).vars → i ∈ e.vars)
    (d : DenseConstraintSystem p) : ∀ i ∈ (d.mapExpr g).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.mapExpr, List.mem_append,
    List.mem_flatMap, List.mem_map] at hi
  rcases hi with ⟨c, ⟨c0, hc0, rfl⟩, hic⟩ | ⟨bi, ⟨bi0, hbi0, rfl⟩, hib⟩
  · exact DenseConstraintSystem.mem_occ_of_constraint hc0 (hgv c0 i hic)
  · refine DenseConstraintSystem.mem_occ_of_bi hbi0 ?_
    simp only [denseBIVars, List.mem_append, List.mem_flatMap, List.mem_map] at hib ⊢
    rcases hib with hm | ⟨e, ⟨e0, he0, rfl⟩, hie⟩
    · exact Or.inl (hgv bi0.multiplicity i hm)
    · exact Or.inr ⟨e0, he0, hgv e0 i hie⟩

/-! ## The dense constant-fold pass -/

/-- The dense constant-folding pass (see `DenseExpr.fold`). -/
def denseConstantFoldPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => d.mapExpr DenseExpr.fold)
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov => DenseConstraintSystem.mapExpr_covered DenseExpr.fold_vars hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => by
      have hfe : ∀ (e : DenseExpr p) (denv : VarId → ZMod p),
          (DenseExpr.fold e).eval denv = e.eval denv := fun e denv => DenseExpr.fold_eval e denv
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- soundness: `(mapExpr fold).implies d`
        intro denv hsat
        refine ⟨denv, (DenseConstraintSystem.mapExpr_satisfies hfe d bs denv).mp hsat, ?_⟩
        rw [DenseConstraintSystem.mapExpr_sideEffects hfe]
        exact BusState.equiv_refl _
      · -- invariants
        exact fun h => DenseConstraintSystem.mapExpr_guaranteesInvariants hfe h
      · -- no new powdr column
        exact fun i hi _ => DenseConstraintSystem.mapExpr_occ_subset DenseExpr.fold_vars d i hi
      · -- completeness (witness = input env; no derivations)
        intro denv hadm hsat
        refine ⟨denv, (DenseConstraintSystem.mapExpr_satisfies hfe d bs denv).mpr hsat,
          (DenseConstraintSystem.mapExpr_admissible hfe d bs denv).mpr hadm, ?_, fun _ _ => rfl, ?_⟩
        · rw [DenseConstraintSystem.mapExpr_sideEffects hfe]
          exact BusState.equiv_refl _
        · intro _ _ i hi _
          exact ⟨DenseConstraintSystem.mapExpr_occ_subset DenseExpr.fold_vars d i hi, rfl⟩)

end ApcOptimizer.Dense
