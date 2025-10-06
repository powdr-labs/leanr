import Leanr.AlgebraicConstraint
import Leanr.Parser

def find_assignment {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : Option (Assignment (p := p)) × List (AlgebraicConstraint p) :=
  match constraints with
  | [] => (none, [])
  | c :: cs =>
    match c.solve? with
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

/-- info: 8 + 10 * k + 10 * z -/
#guard_msgs in
#eval (solve [ .assertZero expr { 2 * x + 3 * (y + z + k) * x + 4 },
                 .assertZero expr { x + 1 },
                .assertZero expr { y + 2 } ] : List (AlgebraicConstraint 13))
