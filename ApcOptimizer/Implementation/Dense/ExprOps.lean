import ApcOptimizer.Implementation.Dense.Pass
import ApcOptimizer.Implementation.OptimizerPasses.ConstantFold

set_option autoImplicit false

/-! # Shared dense expression operations (Task 3, WP-E) + the dense constant-fold pass

The reusable machinery for building dense passes as *eval-preserving expression maps*, and the first
concrete pass (constant folding) built on it.

`DenseConstraintSystem.mapExpr g` applies a dense expression transform to every expression. Its key
property, `decodeCS_mapExpr`, is a **commutation lemma**: if `g` commutes with `decode` against a
spec transform `g'` (`decode (g e) = g' (decode e)`), then `decode (d.mapExpr g) = (decode d).mapExpr
g'`. That is the bridge that lets a dense pass reuse the *existing* spec pass's `PassCorrect`: the
dense output decodes to exactly the spec pass's output, so no correctness is re-proved. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense expression maps -/

/-- Apply `g` to every expression of a dense constraint system. -/
def DenseConstraintSystem.mapExpr (d : DenseConstraintSystem p) (g : DenseExpr p → DenseExpr p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map g,
    busInteractions := d.busInteractions.map
      (fun bi => { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g }) }

/-- **Commutation of `mapExpr` with `decode`.** If the dense transform `g` decodes to the spec
    transform `g'`, then decoding after `g` equals `g'` after decoding — the identity a dense
    eval-preserving pass uses to inherit its spec counterpart's `PassCorrect`. -/
theorem VarRegistry.decodeCS_mapExpr (reg : VarRegistry) {g : DenseExpr p → DenseExpr p}
    {g' : Expression p → Expression p} (hg : ∀ e, reg.decodeExpr (g e) = g' (reg.decodeExpr e))
    (d : DenseConstraintSystem p) :
    reg.decodeCS (d.mapExpr g) = (reg.decodeCS d).mapExpr g' := by
  simp only [DenseConstraintSystem.mapExpr, VarRegistry.decodeCS, ConstraintSystem.mapExpr,
    BusInteraction.mapExpr, VarRegistry.decodeBI, List.map_map, Function.comp_def, hg]

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

/-! ## Dense constant folding (mirrors `Expression.foldAdd`/`foldMul`/`fold`) -/

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

/-- One bottom-up constant-fold over a dense expression. -/
def DenseExpr.fold : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var i => .var i
  | .add a b => a.fold.foldAdd b.fold
  | .mul a b => a.fold.foldMul b.fold

/-- Dense `foldAdd` decodes to spec `foldAdd`. -/
theorem VarRegistry.decodeExpr_foldAdd (reg : VarRegistry) (a b : DenseExpr p) :
    reg.decodeExpr (a.foldAdd b) = (reg.decodeExpr a).foldAdd (reg.decodeExpr b) := by
  cases a <;> cases b <;>
    simp only [DenseExpr.foldAdd, Expression.foldAdd, VarRegistry.decodeExpr] <;>
    split_ifs <;> simp [VarRegistry.decodeExpr]

/-- Dense `foldMul` decodes to spec `foldMul`. -/
theorem VarRegistry.decodeExpr_foldMul (reg : VarRegistry) (a b : DenseExpr p) :
    reg.decodeExpr (a.foldMul b) = (reg.decodeExpr a).foldMul (reg.decodeExpr b) := by
  cases a <;> cases b <;>
    simp only [DenseExpr.foldMul, Expression.foldMul, VarRegistry.decodeExpr] <;>
    split_ifs <;> simp [VarRegistry.decodeExpr]

/-- **Dense `fold` decodes to spec `fold`.** -/
theorem VarRegistry.decodeExpr_fold (reg : VarRegistry) (e : DenseExpr p) :
    reg.decodeExpr e.fold = (reg.decodeExpr e).fold := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb =>
      rw [DenseExpr.fold, reg.decodeExpr_foldAdd, iha, ihb, VarRegistry.decodeExpr, Expression.fold]
  | mul a b iha ihb =>
      rw [DenseExpr.fold, reg.decodeExpr_foldMul, iha, ihb, VarRegistry.decodeExpr, Expression.fold]

/-- Dense `foldAdd` introduces no new variables. -/
theorem DenseExpr.foldAdd_vars (a b : DenseExpr p) :
    ∀ i ∈ (a.foldAdd b).vars, i ∈ a.vars ++ b.vars := by
  intro i hi
  unfold DenseExpr.foldAdd at hi
  split at hi <;> (try split_ifs at hi) <;> simp_all [DenseExpr.vars]

/-- Dense `foldMul` introduces no new variables. -/
theorem DenseExpr.foldMul_vars (a b : DenseExpr p) :
    ∀ i ∈ (a.foldMul b).vars, i ∈ a.vars ++ b.vars := by
  intro i hi
  unfold DenseExpr.foldMul at hi
  split at hi <;> (try split_ifs at hi) <;> simp_all [DenseExpr.vars]

/-- Dense `fold` introduces no new variables. -/
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

/-! ## The dense constant-fold pass -/

/-- The dense constant-folding pass: normalize every dense expression. Its `PassCorrect` is inherited
    from the spec `constantFoldPass` — the dense output decodes to exactly `(decode d).mapExpr fold`,
    which is the spec pass's output. -/
def denseConstantFoldPass : DenseVerifiedPassW p := fun reg d hcov bs _ =>
  { reg' := reg
    out := d.mapExpr DenseExpr.fold
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := DenseConstraintSystem.mapExpr_covered DenseExpr.fold_vars hcov
    dcovered := by intro x hx; simp at hx
    correct := by
      rw [reg.decodeCS_mapExpr (fun e => reg.decodeExpr_fold e) d]
      exact ConstraintSystem.mapExpr_correct (g := Expression.fold)
        (fun e env => Expression.fold_eval e env) (reg.decodeCS d) bs Expression.fold_vars }

end ApcOptimizer.Dense
