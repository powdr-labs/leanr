import Leanr.System
import Leanr.Parser
import Std.Data.HashMap

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Find all solvable single-variable assignments in one pass. -/
def find_all_assignments
    (constraints : Array (AlgebraicConstraint p)) :
    Array (Assignment (p := p)) × Array (AlgebraicConstraint p) := Id.run do
  let mut assignments : Array (Assignment (p := p)) := #[]
  let mut remaining : Array (AlgebraicConstraint p) := #[]
  for c in constraints do
    match c.solve? with
    | some a => assignments := assignments.push a
    | none => remaining := remaining.push c
  (assignments, remaining)

/-- Apply all substitutions to constraints in one pass per constraint, dropping trivial ones. -/
def substitute_all_constraints
    (constraints : Array (AlgebraicConstraint p))
    (env : Std.HashMap String (ZMod p)) : Array (AlgebraicConstraint p) := Id.run do
  let mut result : Array (AlgebraicConstraint p) := Array.mkEmpty constraints.size
  for c in constraints do
    let c' := c.substituteAll env
    unless c'.toConstant? == some 0 do
      result := result.push c'
  result

/-- Apply all substitutions to bus interactions, dropping those with zero multiplicity. -/
def substitute_all_bus
    (bis : Array (BusInteraction (Expression p)))
    (env : Std.HashMap String (ZMod p)) : Array (BusInteraction (Expression p)) := Id.run do
  let mut result : Array (BusInteraction (Expression p)) := Array.mkEmpty bis.size
  for bi in bis do
    let bi' := bi.substituteAll env
    unless bi'.multiplicity.toConstant? == some 0 do
      result := result.push bi'
  result

/-- Update range constraints with newly solved assignments (single-value constraints). -/
def update_range_constraints_from_assignments
    (rc : Std.HashMap String (RangeConstraint p))
    (assignments : Array (Assignment (p := p))) : Std.HashMap String (RangeConstraint p) :=
  assignments.foldl (init := rc) fun m a =>
    let newRc : RangeConstraint p := ↑a.value
    match m[a.var]? with
    | some existing => m.insert a.var (existing.conjunction newRc)
    | none => m.insert a.var newRc

/-- One round: find all solvable assignments, then apply them all at once. -/
def solve_round (system : System (p := p))
    (rc : Std.HashMap String (RangeConstraint p))
    (log : Bool) : IO (System (p := p) × Std.HashMap String (RangeConstraint p)) := do
  let (newAssignments, remaining) := find_all_assignments system.constraints
  if newAssignments.isEmpty then
    return (system, rc)
  if log then
    IO.eprintln s!"[solve] found {newAssignments.size} assignments in this round"
  -- Build a HashMap for O(1) lookup during substitution
  let env : Std.HashMap String (ZMod p) :=
    newAssignments.foldl (init := (∅ : Std.HashMap String (ZMod p))) fun m a => m.insert a.var a.value
  let constraints := substitute_all_constraints remaining env
  let bus := substitute_all_bus system.bus_interactions env
  let rc := update_range_constraints_from_assignments rc newAssignments
  return ({
    constraints := constraints,
    bus_interactions := bus,
    assignments := system.assignments ++ newAssignments,
  }, rc)

/-- Pure version of solve_round (no IO logging). -/
def solve_round_pure (system : System (p := p)) : System (p := p) :=
  let (newAssignments, remaining) := find_all_assignments system.constraints
  if newAssignments.isEmpty then
    system
  else
    let env : Std.HashMap String (ZMod p) :=
      newAssignments.foldl (init := (∅ : Std.HashMap String (ZMod p))) fun m a => m.insert a.var a.value
    let constraints := substitute_all_constraints remaining env
    let bus := substitute_all_bus system.bus_interactions env
    {
      constraints := constraints,
      bus_interactions := bus,
      assignments := system.assignments ++ newAssignments,
    }

/-- Pure version of solve (no IO logging). Iterates until no more assignments can be found. -/
def solve_pure (system : System (p := p)) : System (p := p) :=
  let new_system := solve_round_pure system
  if h : new_system.constraints.size < system.constraints.size then
    solve_pure new_system
  else
    new_system
  termination_by system.constraints.size
  decreasing_by omega

def solve (system : System (p := p)) (log : Bool := false) : IO (System (p := p)) := do
  if log then
    IO.eprintln s!"[solve] {system.constraints.size} constraints, {system.bus_interactions.size} bus, {system.assignments.size} assignments"
  let (new_system, _rc) ← solve_round system ∅ log
  if new_system.constraints.size < system.constraints.size then
    solve new_system log
  else
    if log then
      IO.eprintln s!"[solve] no more solvable constraints"
    return new_system
  termination_by system.constraints.size
  decreasing_by
    omega
