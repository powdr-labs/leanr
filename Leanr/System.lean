import Leanr.AlgebraicConstraint
import Leanr.BusInteraction

variable {p : ℕ} [Fact (Nat.Prime p)]

structure System (p : ℕ) where
  constraints: Array (AlgebraicConstraint p)
  bus_interactions: Array (BusInteraction (Expression p))
  assignments: Array (Assignment (p := p))

instance : ToString (System (p := p)) where
  toString s :=
    "Assignments:\n" ++
    String.intercalate "\n" (s.assignments.toList.map toString) ++
    "\nConstraints:\n" ++
    String.intercalate "\n" (s.constraints.toList.map toString) ++
    "\nBus Interactions:\n" ++
    String.intercalate "\n" (s.bus_interactions.toList.map toString)

def System.fromConstraints {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : System (p := p) :=
  { constraints := constraints.toArray, bus_interactions := #[], assignments := #[] }
