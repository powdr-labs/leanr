import ApcOptimizer.Implementation.OptimizerPasses.ExprOps

set_option autoImplicit false

/-! # Dense constraint/bus filtering + small predicates (Task 3, WP-E)

Dense mirrors of `ConstraintSystem.filterConstraints`/`filterBus` (`OptimizerPasses/Rewrite.lean`),
plus the small expression predicates the drop passes key on. Filtering only drops, so it preserves
coverage trivially. The native `DensePassCorrect` proofs for the drop passes built on these live in
`DropPassesProof.lean`; the former decode-commutation lemmas were removed with the commutation-era
scaffolding. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense filtering -/

/-- Keep only the algebraic constraints satisfying `keep`; bus interactions untouched. -/
def DenseConstraintSystem.filterConstraints (d : DenseConstraintSystem p)
    (keep : DenseExpr p → Bool) : DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.filter keep }

/-- Keep only the bus interactions satisfying `keep`; algebraic constraints untouched. -/
def DenseConstraintSystem.filterBus (d : DenseConstraintSystem p)
    (keep : BusInteraction (DenseExpr p) → Bool) : DenseConstraintSystem p :=
  { d with busInteractions := d.busInteractions.filter keep }

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

end ApcOptimizer.Dense
