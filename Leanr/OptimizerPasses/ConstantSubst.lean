import Leanr.OptimizerPasses.Subst
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Constant substitution (variable elimination)

Eliminates a variable pinned to a constant. After constant folding, a constraint that fixes a
variable has one of two normal forms:

* `x` (i.e. `var x`), forcing `x = 0`; or
* `x + const d`, forcing `x = -d`.

`solveConst` recognizes exactly these, and `solveConst_sound` proves the entailment. Feeding them to
the generic `substFromConstraint` gives `constantFixPass`, which substitutes the pinned variable
everywhere — removing it from the circuit. Purely equational (works over any commutative ring); no
field/primality needed. This is the first pass that actually reduces the variable count. -/

variable {p : ℕ}

/-- Recognize a constraint that pins a variable to a constant, returning `(x, t)` with `t` the
    constant it is forced to equal:
    * `var x ↦ (x, 0)`;
    * `x + const d ↦ (x, -d)`. -/
def solveConst : Expression p → Option (String × Expression p)
  | .var x => some (x, .const 0)
  | .add (.var x) (.const d) => some (x, .const (-d))
  | _ => none

/-- Soundness of `solveConst`: if it returns `(x, t)` for a constraint `c`, then `c.eval env = 0`
    forces `env x = t.eval env`. -/
theorem solveConst_sound (c : Expression p) (x : String) (t : Expression p)
    (h : solveConst c = some (x, t)) (env : String → ZMod p) (hc : c.eval env = 0) :
    env x = t.eval env := by
  unfold solveConst at h
  split at h <;>
    first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       simp only [Expression.eval] at hc ⊢
       linear_combination hc)
    | exact absurd h (by simp)

/-- The constant-substitution pass: eliminate one variable pinned to a constant. Iterate (with
    folding) to eliminate all of them. -/
def constantFixPass : VerifiedPass p := substFromConstraint solveConst solveConst_sound
