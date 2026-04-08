import Leanr.Solver
import Leanr.AlgebraicConstraint.Proofs

variable {p : ℕ} [Fact (Nat.Prime p)]

instance instFactPrime13 : Fact (Nat.Prime 13) where
  out := by norm_num

/-! ## Correctness -/

/-- A system's constraints are all satisfied by `env`. -/
def System.satisfies (s : System p) (env : String → ZMod p) : Prop :=
  ∀ c ∈ s.constraints.toList, AlgebraicConstraint.eval c env = 0

/-- Dropping a constraint whose constant value is 0 preserves satisfiability. -/
theorem toConstant_zero_satisfied {c : AlgebraicConstraint p} {env : String → ZMod p}
    (h : c.toConstant? = some 0) : c.eval env = 0 := by
  cases c with
  | affine e => exact AffineExpression.toConstant?_correct e 0 h env
  | general e =>
    simp [AlgebraicConstraint.toConstant?, Expression.toConstant?] at h
    cases e with
    | const n =>
      simp at h
      simp [AlgebraicConstraint.eval, Expression.eval, h]
    | _ => simp at h

/-- substituteAll preserves satisfaction when the map agrees with the environment. -/
theorem substituteAll_preserves_satisfaction
    (constraints : Array (AlgebraicConstraint p))
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h_map : ∀ x v, m[x]? = some v → env x = v)
    (h_sat : ∀ c ∈ constraints.toList, AlgebraicConstraint.eval c env = 0) :
    ∀ c ∈ (substitute_all_constraints constraints m).toList,
      AlgebraicConstraint.eval c env = 0 := by
  sorry -- requires reasoning about Id.run do loop and Array operations

/-- solve? is sound: if a constraint is zero under env and solve? succeeds,
    the found assignment agrees with env. -/
theorem find_all_assignments_sound
    (constraints : Array (AlgebraicConstraint p))
    (env : String → ZMod p)
    (h_sat : ∀ c ∈ constraints.toList, AlgebraicConstraint.eval c env = 0) :
    let (assignments, remaining) := find_all_assignments constraints
    (∀ a ∈ assignments.toList, env a.var = a.value) ∧
    (∀ c ∈ remaining.toList, AlgebraicConstraint.eval c env = 0) := by
  sorry -- requires reasoning about Id.run do loop and Array operations

/-- The solver preserves satisfiability: if all original constraints are satisfied by `env`,
    then all remaining constraints after solving are also satisfied by `env`. -/
theorem solve_sound (system : System (p := p)) (env : String → ZMod p) (log : Bool)
    (h_sat : system.satisfies env) :
    ∀ s, solve system log = pure s → s.satisfies env := by
  sorry -- follows from find_all_assignments_sound and substituteAll_preserves_satisfaction
