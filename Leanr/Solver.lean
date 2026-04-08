import Leanr.System
import Leanr.Parser
import Std.Data.HashMap

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Solver state: the system being solved and current range constraints for variables. -/
structure SolverState (p : ℕ) where
  system : System p
  range_constraints : Std.HashMap String (RangeConstraint p)

/-- Look up the range constraint for a variable, defaulting to unconstrained. -/
def SolverState.getRangeConstraint (state : SolverState p) (x : String) : RangeConstraint p :=
  state.range_constraints[x]?.getD .unconstrained

/-- Update a variable's range constraint by conjunction with a new constraint.
    Returns the updated state and whether progress was made. -/
def SolverState.updateRangeConstraint (state : SolverState p) (x : String)
    (rc : RangeConstraint p) : SolverState p × Bool :=
  let existing := state.getRangeConstraint x
  let new_rc := existing.conjunction rc
  if new_rc.mask == existing.mask && new_rc.min == existing.min && new_rc.max == existing.max then
    (state, false)
  else
    ({ state with range_constraints := state.range_constraints.insert x new_rc }, true)

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

/-- For a single affine expression field with handler-refined range constraint `field_rc`,
    deduce tighter range constraints for each variable in the expression.

    If the expression is `k * X + rest`, then `X ∈ field_rc / k + RC(-rest/k)`.
    This is the key formula from the Rust solver's `BusInteraction::solve`. -/
def deduce_variable_range_constraints_from_field
    (ae : AffineExpression p)
    (field_rc : RangeConstraint p)
    (rc_env : String → RangeConstraint p) : List (String × RangeConstraint p) :=
  ae.affine.toList.filterMap fun (var, coeff) =>
    if coeff = 0 then none
    else
      let inv_k := coeff⁻¹
      -- RC(var) ⊆ field_rc / k + RC(-rest/k)
      let rc_field_scaled := field_rc.multiple inv_k
      match ae.solvedRangeConstraint var rc_env with
      | none => none
      | some rc_solved =>
        let var_rc := rc_field_scaled + rc_solved
        some (var, var_rc)

/-- Process a single bus interaction: convert fields to range constraints, call the handler,
    then deduce tighter variable range constraints from each affine field. -/
def process_bus_interaction
    (bi : BusInteraction (Expression p))
    (handler : BusInteractionHandler p)
    (rc_env : String → RangeConstraint p)
    : List (String × RangeConstraint p) :=
  let rc_bi := bi.toRangeConstraints rc_env
  let refined := handler.handleBusInteraction rc_bi
  -- Zip original fields with refined range constraints and deduce variable constraints
  let field_pairs := bi.fields.zip refined.fields
  field_pairs.flatMap fun pair =>
    match AffineExpression.ofExpression? pair.1 with
    | none => []
    | some ae => deduce_variable_range_constraints_from_field ae pair.2 rc_env

/-- Process all bus interactions to refine range constraints.
    Returns the updated state and whether any progress was made. -/
def process_all_bus_interactions
    (state : SolverState p)
    (handler : BusInteractionHandler p) : SolverState p × Bool :=
  let rc_env := state.getRangeConstraint
  let updates := state.system.bus_interactions.toList.flatMap fun bi =>
    process_bus_interaction bi handler rc_env
  updates.foldl (init := (state, false)) fun (st, progress) (var, rc) =>
    let (st', changed) := st.updateRangeConstraint var rc
    (st', progress || changed)

/-- One round: find all solvable assignments, apply them, then process bus interactions. -/
def solve_round_pure (state : SolverState p)
    (handler : BusInteractionHandler p) : SolverState p :=
  let system := state.system
  let (newAssignments, remaining) := find_all_assignments system.constraints
  if newAssignments.isEmpty then
    -- No algebraic progress; try bus interactions for range constraint refinement
    let (state', _) := process_all_bus_interactions state handler
    state'
  else
    let env : Std.HashMap String (ZMod p) :=
      newAssignments.foldl (init := (∅ : Std.HashMap String (ZMod p))) fun m a => m.insert a.var a.value
    let constraints := substitute_all_constraints remaining env
    let bus := substitute_all_bus system.bus_interactions env
    let rc := update_range_constraints_from_assignments state.range_constraints newAssignments
    let new_system : System p := {
      constraints := constraints,
      bus_interactions := bus,
      assignments := system.assignments ++ newAssignments,
    }
    -- Process bus interactions after substitution
    let state' : SolverState p := { system := new_system, range_constraints := rc }
    let (state'', _) := process_all_bus_interactions state' handler
    state''

/-- Iterates solve_round_pure until no more assignments can be found. -/
def solve_pure (state : SolverState p)
    (handler : BusInteractionHandler p) : SolverState p :=
  let new_state := solve_round_pure state handler
  if h : new_state.system.constraints.size < state.system.constraints.size then
    solve_pure new_state handler
  else
    new_state
  termination_by state.system.constraints.size
  decreasing_by omega

/-- Solve with optional logging. Delegates to solve_round_pure for the actual computation. -/
def solve (system : System (p := p))
    (handler : BusInteractionHandler p := { isBusStateful := fun _ => false, handleBusInteraction := id })
    (log : Bool := false) : IO (System (p := p)) := do
  if log then
    IO.eprintln s!"[solve] {system.constraints.size} constraints, {system.bus_interactions.size} bus, {system.assignments.size} assignments"
  let state : SolverState p := { system, range_constraints := ∅ }
  let new_state := solve_round_pure state handler
  if new_state.system.constraints.size < system.constraints.size then
    if log then
      IO.eprintln s!"[solve] solved {system.constraints.size - new_state.system.constraints.size} constraints in this round"
    solve new_state.system handler log
  else
    if log then
      IO.eprintln s!"[solve] no more solvable constraints"
    return new_state.system
  termination_by system.constraints.size
  decreasing_by omega
