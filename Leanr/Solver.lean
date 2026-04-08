import Leanr.AlgebraicConstraint
import Leanr.BusInteraction
import Leanr.Parser
import Std.Data.HashMap

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

/-- One round: find all solvable assignments, then apply them all at once. -/
def solve_round (system : System (p := p)) (log : Bool) : IO (System (p := p)) := do
  let (newAssignments, remaining) := find_all_assignments system.constraints
  if newAssignments.isEmpty then
    return system
  if log then
    IO.eprintln s!"[solve] found {newAssignments.size} assignments in this round"
  -- Build a HashMap for O(1) lookup during substitution
  let env : Std.HashMap String (ZMod p) :=
    newAssignments.foldl (init := (∅ : Std.HashMap String (ZMod p))) fun m a => m.insert a.var a.value
  let constraints := substitute_all_constraints remaining env
  let bus := substitute_all_bus system.bus_interactions env
  return {
    constraints := constraints,
    bus_interactions := bus,
    assignments := system.assignments ++ newAssignments
  }

def solve (system : System (p := p)) (log : Bool := false) : IO (System (p := p)) := do
  if log then
    IO.eprintln s!"[solve] {system.constraints.size} constraints, {system.bus_interactions.size} bus, {system.assignments.size} assignments"
  let new_system ← solve_round system log
  if new_system.constraints.size < system.constraints.size then
    solve new_system log
  else
    if log then
      IO.eprintln s!"[solve] no more solvable constraints"
    return new_system
  termination_by system.constraints.size
  decreasing_by
    omega

def System.fromConstraints {p : ℕ}
  (constraints : List (AlgebraicConstraint p)) : System (p := p) :=
  { constraints := constraints.toArray, bus_interactions := #[], assignments := #[] }

instance : Fact (Nat.Prime 13) where
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
