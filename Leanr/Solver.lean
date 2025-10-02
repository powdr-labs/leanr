import Leanr.AlgebraicConstraint
import Leanr.Parser

structure Assignment {p : ℕ} where
  var : String
  value : ZMod p

--- Try to solve an affine constraint with at most one variable.
def solve_constraint? {p : ℕ}
  (constraint : AlgebraicConstraint p) : Option (Assignment (p := p)) :=
  let e := constraint.expression
  if !e.quadratic.isEmpty then
    none
  else match e.affine.toList with
    | [] => none
    | [(x, c)] =>
      if c = 0 then
        -- actually unreachable
        none
      else
        some { var := x, value := -c⁻¹ * e.offset }
    | _ :: _ :: _ => none -- more than one variable

-- TODO theorem: solve plus substitute yields trivial constraint.

theorem solve_constraint?_correct {p : ℕ}
  (constraint : AlgebraicConstraint p)
  (assignment : Assignment (p := p))
  (h : solve_constraint? constraint = some assignment)
  (env : String → ZMod p)
  (satisfying : constraint.is_satisfied_by env) :
  env assignment.var = assignment.value := by
  sorry

def find_assignment {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : Option (Assignment (p := p)) × List (AlgebraicConstraint p) :=
  match constraints with
  | [] => (none, [])
  | c :: cs =>
    match solve_constraint? c with
    | some assignment => (some assignment, cs)
    | none =>
      let (a, rest) := find_assignment cs
      (a, c :: rest)

def solve_step {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : List (AlgebraicConstraint p) :=
  match find_assignment constraints with
  | (none, _) => constraints
  | (some assignment, constraints) =>
    constraints.map (fun c => c.substitute assignment.var assignment.value)

def solve {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : List (AlgebraicConstraint p) :=
  let new_constraints := solve_step constraints
  if new_constraints.length < constraints.length then
    solve new_constraints
  else
    new_constraints
  termination_by constraints.length
  decreasing_by
    simpa [solve, new_constraints]

/-- info: 9 + 3 * k + 3 * z -/
#guard_msgs in
#eval (solve [ { expression := .ofExpression expr { 2 * x + 3 * (y + z + k) + 4 } },
                 { expression := .ofExpression expr { x + 1 } },
                 { expression := .ofExpression expr { y + 2 } } ] : List (AlgebraicConstraint 13))
