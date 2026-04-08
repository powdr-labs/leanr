import Leanr.AlgebraicConstraint
import Leanr.BusInteraction

variable {p : ℕ} [Fact (Nat.Prime p)]

structure System (p : ℕ) where
  constraints: Array (AlgebraicConstraint p)
  bus_interactions: Array (BusInteraction (Expression p))
  assignments: Array (Assignment (p := p))
  range_constraints: Std.HashMap String (RangeConstraint p) := ∅

instance : ToString (System (p := p)) where
  toString s :=
    "Assignments:\n" ++
    String.intercalate "\n" (s.assignments.toList.map toString) ++
    "\nConstraints:\n" ++
    String.intercalate "\n" (s.constraints.toList.map toString) ++
    "\nBus Interactions:\n" ++
    String.intercalate "\n" (s.bus_interactions.toList.map toString) ++
    "\nRange Constraints:\n" ++
    String.intercalate "\n" (s.range_constraints.toList.map fun (k, v) =>
      s!"  {k}: mask=0x{Nat.toDigits 16 v.mask |>.asString}, min={v.min.val}, max={v.max.val}")

def System.fromConstraints {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : System (p := p) :=
  { constraints := constraints.toArray, bus_interactions := #[], assignments := #[] }
