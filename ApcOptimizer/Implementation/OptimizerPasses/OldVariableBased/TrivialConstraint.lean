import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Rewrite
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ConstantFold

set_option autoImplicit false

/-! # Trivial-constraint removal

Drops algebraic constraints that fold to the literal constant `0` — e.g. `1 - 1`, `0 - 0`, and the
`selector * (…)` constraints left behind once a selector is substituted to `0`. Such constraints
are vacuously satisfied, so removing them is equivalence-preserving via the proven
`filterConstraints_correct`.

It removes no variable on its own, but it is a load-bearing cleanup: after a selector like
`rs2_as_0` is substituted to `0`, its guarded constraints fold to `0` and are dropped here, leaving
the freed auxiliary variables living *only* inside now-zero-multiplicity bus interactions — which is
exactly what lets the zero-multiplicity bus-removal pass eliminate them. Field-free. -/

variable {p : ℕ}

/-- Decides (soundly, not completely) whether an expression is identically zero: `true` only for the
    literal constant `0`. Combined with folding this catches all constraints that normalize to `0`. -/
def Expression.isConstZero : Expression p → Bool
  | .const n => decide (n = 0)
  | _ => false

theorem Expression.isConstZero_sound (e : Expression p) (h : e.isConstZero = true)
    (env : Variable → ZMod p) : e.eval env = 0 := by
  cases e <;> simp_all [Expression.isConstZero, Expression.eval]

/-- The trivial-constraint removal pass: drop every algebraic constraint whose fold is the literal
    `0`. Correct via `filterConstraints_correct`, discharging the dropped-constraints-are-zero
    obligation through `fold_eval` and `isConstZero_sound`. -/
def trivialConstraintDropPass : VerifiedPass p := fun cs bs =>
  ⟨cs.filterConstraints (fun c => !c.fold.isConstZero), [],
   cs.filterConstraints_correct bs (fun c => !c.fold.isConstZero) (by
     intro c _ hkf env
     have hz : c.fold.isConstZero = true := by simpa using hkf
     rw [← c.fold_eval env]
     exact c.fold.isConstZero_sound hz env)⟩
