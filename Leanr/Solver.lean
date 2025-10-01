import Leanr.AlgebraicConstraint

structure Assignment {p : ℕ} where
  var : String
  value : ZMod p

--- Try to solve an affine constraint with at most one variable.
def solve_constraint? {p : ℕ}
  (constraint : AlgebraicConstraint p) : Option (Assignment (p := p)) :=
  -- After simplification, we know that constants are always on the left.
  -- So we solve expressions of the form
  --  x
  --  k + x
  --  c * x
  --  k + c * x
  match constraint.expression with
  | .var x => some { var := x, value := 0 }
  | .add (.const k) (.var x) => some { var := x, value := -k }
  | .mul (.const c) (.var x) =>
    if c = 0 then none else some { var := x, value := c⁻¹ * 0 }
  | .add (.const k) (.mul (.const c) (.var x)) =>
    if c = 0 then none else some { var := x, value := c⁻¹ * -k }
  | _ => none

-- TODO theorem: solve plus substitute yields trivial constraint.

theorem solve_constraint?_correct {p : ℕ}
  (constraint : AlgebraicConstraint p)
  (assignment : Assignment (p := p))
  (h : solve_constraint? constraint = some assignment)
  (env : String → ZMod p)
  (satisfying : constraint.is_satisfied_by env) :
  env assignment.var = assignment.value := by
  sorry

def find_assignments {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : List (Assignment (p := p)) :=
  constraints.filterMap solve_constraint?

def find_and_apply_assignments {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) :
  List (AlgebraicConstraint p) :=
  let assignments := find_assignments constraints
  let new_constraints := constraints.map (fun c =>
    assignments.foldl (fun acc a => acc.substitute a.var a.value) c)
  new_constraints.filterMap fun c =>
    if c.trivial? then none else some c
