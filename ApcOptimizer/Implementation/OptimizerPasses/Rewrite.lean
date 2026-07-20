import ApcOptimizer.Implementation.OptimizerPasses.ExprOps
import ApcOptimizer.Implementation.OptimizerPasses.TrivialConstraint

set_option autoImplicit false

/-! # Dense constraint/bus filtering + small predicates (Task 3, WP-E)

Dense mirrors of `ConstraintSystem.filterConstraints`/`filterBus` (`OptimizerPasses/Rewrite.lean`),
plus the small expression predicates the drop passes key on. Each carries the commutation lemma a
dense drop pass needs: if the dense keep-predicate corresponds to the spec keep-predicate under
decode, the dense filter decodes to the spec filter. Filtering only drops, so it preserves coverage
trivially. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `filter` then `map` equals `map` then `filter`, when the predicates correspond pointwise. -/
theorem filter_map_comm {α β : Type*} (g : α → β) (dk : α → Bool) (sk : β → Bool) :
    ∀ (l : List α), (∀ x ∈ l, dk x = sk (g x)) → (l.filter dk).map g = (l.map g).filter sk := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro h
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, List.filter_cons, hc]
      by_cases hs : sk (g c) = true
      · rw [if_pos hs, if_pos hs, List.map_cons,
          ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      · rw [if_neg hs, if_neg hs, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-! ## Dense filtering -/

/-- Keep only the algebraic constraints satisfying `keep`; bus interactions untouched. -/
def DenseConstraintSystem.filterConstraints (d : DenseConstraintSystem p)
    (keep : DenseExpr p → Bool) : DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.filter keep }

/-- Keep only the bus interactions satisfying `keep`; algebraic constraints untouched. -/
def DenseConstraintSystem.filterBus (d : DenseConstraintSystem p)
    (keep : BusInteraction (DenseExpr p) → Bool) : DenseConstraintSystem p :=
  { d with busInteractions := d.busInteractions.filter keep }

theorem VarRegistry.decodeCS_filterConstraints (reg : VarRegistry) {dk : DenseExpr p → Bool}
    {sk : Expression p → Bool} (d : DenseConstraintSystem p)
    (h : ∀ c ∈ d.algebraicConstraints, dk c = sk (reg.decodeExpr c)) :
    reg.decodeCS (d.filterConstraints dk) = (reg.decodeCS d).filterConstraints sk := by
  simp only [DenseConstraintSystem.filterConstraints, VarRegistry.decodeCS,
    ConstraintSystem.filterConstraints]
  rw [filter_map_comm reg.decodeExpr dk sk d.algebraicConstraints h]

theorem VarRegistry.decodeCS_filterBus (reg : VarRegistry)
    {dk : BusInteraction (DenseExpr p) → Bool} {sk : BusInteraction (Expression p) → Bool}
    (d : DenseConstraintSystem p)
    (h : ∀ bi ∈ d.busInteractions, dk bi = sk (reg.decodeBI bi)) :
    reg.decodeCS (d.filterBus dk) = (reg.decodeCS d).filterBus sk := by
  simp only [DenseConstraintSystem.filterBus, VarRegistry.decodeCS, ConstraintSystem.filterBus]
  rw [filter_map_comm reg.decodeBI dk sk d.busInteractions h]

theorem DenseConstraintSystem.filterConstraints_covered {reg : VarRegistry}
    {d : DenseConstraintSystem p} {keep : DenseExpr p → Bool} (hc : d.CoveredBy reg) :
    (d.filterConstraints keep).CoveredBy reg :=
  ⟨fun e he => hc.1 e (List.mem_of_mem_filter he), fun bi hbi => hc.2 bi hbi⟩

theorem DenseConstraintSystem.filterBus_covered {reg : VarRegistry}
    {d : DenseConstraintSystem p} {keep : BusInteraction (DenseExpr p) → Bool} (hc : d.CoveredBy reg) :
    (d.filterBus keep).CoveredBy reg :=
  ⟨fun e he => hc.1 e he, fun bi hbi => hc.2 bi (List.mem_of_mem_filter hbi)⟩

/-! ## Small dense expression predicates -/

/-- Is the dense expression the literal constant `0`? -/
def DenseExpr.isConstZero : DenseExpr p → Bool
  | .const n => decide (n = 0)
  | _ => false

theorem VarRegistry.decodeExpr_isConstZero (reg : VarRegistry) (e : DenseExpr p) :
    (reg.decodeExpr e).isConstZero = e.isConstZero := by
  cases e <;> rfl

end ApcOptimizer.Dense
