import Leanr.AlgebraicConstraint
import Leanr.BusInteraction
import Leanr.Parser

variable {p : ℕ} [Fact (Nat.Prime p)]

structure System (p : ℕ) where
  constraints: List (AlgebraicConstraint p)
  bus_interactions: List (BusInteraction (Expression p))
  assignments: List (Assignment (p := p))

instance : ToString (System (p := p)) where
  toString s :=
    "Assignments:\n" ++
    String.intercalate "\n" (s.assignments.map toString) ++
    "\nConstraints:\n" ++
    String.intercalate "\n" (s.constraints.map toString) ++
    "\nBus Interactions:\n" ++
    String.intercalate "\n" (s.bus_interactions.map toString)


def find_assignment
  (constraints : List (AlgebraicConstraint p)) : Option (Assignment (p := p)) × List (AlgebraicConstraint p) :=
  match constraints with
  | [] => (none, [])
  | c :: cs =>
    match c.solve? with
    | some assignment => (some assignment, cs)
    | none =>
      let (a, rest) := find_assignment cs
      (a, c :: rest)

def solve_step (system : System (p := p)) : System (p := p) :=
  match find_assignment system.constraints with
  | (none, _) => system
  | (some assignment, constraints) =>
    {
      constraints := constraints.map (fun c => c.substitute assignment.var assignment.value),
      bus_interactions := system.bus_interactions.map (fun bi => bi.substitute assignment.var assignment.value),
      assignments := assignment :: system.assignments
    }

def solve (system : System (p := p)) (log : Bool := false) : IO (System (p := p)) := do
  if log then
    IO.eprintln s!"[solve] {system.constraints.length} constraints, {system.assignments.length} assignments"
  let new_system := solve_step system
  if new_system.constraints.length < system.constraints.length then
    if log then
      match new_system.assignments with
      | a :: _ => IO.eprintln s!"[solve] solved: {a}"
      | [] => pure ()
    solve new_system log
  else
    if log then
      IO.eprintln s!"[solve] no more solvable constraints"
    return new_system
  termination_by system.constraints.length
  decreasing_by
    omega

def System.fromConstraints {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : System (p := p) :=
  { constraints := constraints, bus_interactions := [], assignments := [] }

instance : Fact (Nat.Prime 13) where
  out := by norm_num

-- #eval! do
--   let r ← solve (System.fromConstraints (p := 13) [ .assertZero expr { 2 * x + 3 * (y + z + k) * x + 4 },
--                  .assertZero expr { x + 1 },
--                 .assertZero expr { y + 2 } ])
--   IO.println s!"{r}"
