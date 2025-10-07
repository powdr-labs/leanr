import Leanr.AlgebraicConstraint
import Leanr.BusInteraction
import Leanr.Parser

structure System {p : ℕ} where
  constraints: List (AlgebraicConstraint p)
  bus_interactions: List (BusInteraction p)
  assignments: List (Assignment (p := p))

instance {p : ℕ} : ToString (System (p := p)) where
  toString s :=
    "Assignments:\n" ++
    String.intercalate "\n" (s.assignments.map toString) ++
    "\nConstraints:\n" ++
    String.intercalate "\n" (s.constraints.map toString) ++
    "\nBus Interactions:\n" ++
    String.intercalate "\n" (s.bus_interactions.map toString)


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

def solve_step {p : ℕ} (system : System (p := p)) : System (p := p) :=
  match find_assignment system.constraints with
  | (none, _) => system
  | (some assignment, constraints) =>
    {
      constraints := constraints.map (fun c => c.substitute assignment.var assignment.value),
      bus_interactions := system.bus_interactions.map (fun bi => bi.substitute assignment.var assignment.value),
      assignments := assignment :: system.assignments
    }

def solve {p : ℕ} (system : System (p := p)) : System (p := p) :=
  let new_system := solve_step system
  if new_system.constraints.length < system.constraints.length then
    solve new_system
  else
    new_system
  termination_by system.constraints.length
  decreasing_by
    simpa [solve]

def System.fromConstraints {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : System (p := p) :=
  { constraints := constraints, bus_interactions := [], assignments := [] }

/-- info: Assignments:
y = 11
x = 12
Constraints:
8 + 10 * k + 10 * z
Bus Interactions:
-/
#guard_msgs in
#eval (solve (System.fromConstraints (p := 13) [ .assertZero expr { 2 * x + 3 * (y + z + k) * x + 4 },
                 .assertZero expr { x + 1 },
                .assertZero expr { y + 2 } ]))
