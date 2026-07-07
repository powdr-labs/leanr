import Lean.Data.Json
import Leanr.Spec
import Leanr.OpenVmSemantics

/-!
# JSON parser for powdr `SymbolicMachine` exports

Parses the `ApcWithBusMap` JSON that powdr's APC export writes (see
`autoprecompiles/src/export.rs` in powdr): the `machine` key holds constraints (expression
trees, asserted zero) and bus interactions (`{id, mult, args}`), the `bus_map.bus_ids` key
maps bus ids to bus types. Adapted from the `main`-branch parser to target the `Spec.lean`
types (`ConstraintSystem`, `Nat` bus ids) and the structured `OpenVmBusType`.

Parsing needs no primality: everything lands in `ZMod p` verbatim.
-/

set_option autoImplicit false

open Leanr.OpenVM (OpenVmBusType BusMapList)

variable {p : ℕ}

private def parseBusType (j : Lean.Json) : Except String OpenVmBusType :=
  match j with
  | Lean.Json.str "ExecutionBridge" => .ok .executionBridge
  | Lean.Json.str "Memory" => .ok .memory
  | Lean.Json.str "PcLookup" => .ok .pcLookup
  | Lean.Json.obj obj =>
    match obj.toList.head? with
    | some ("Other", Lean.Json.str "VariableRangeChecker") => .ok .variableRangeChecker
    | some ("Other", Lean.Json.str "BitwiseLookup") => .ok .bitwiseLookup
    | some ("Other", Lean.Json.obj inner) =>
      match inner.toList.head? with
      | some ("TupleRangeChecker", Lean.Json.arr sizes) =>
        if h : sizes.size = 2 then do
          let s1 ← sizes[0].getNat?
          let s2 ← sizes[1].getNat?
          .ok (.tupleRangeChecker s1 s2)
        else .error s!"TupleRangeChecker expects 2 sizes, got {sizes.size}"
      | some (name, _) => .error s!"unknown bus type: Other.{name}"
      | none => .error "empty Other object in bus_map"
    -- An unknown bus type would be modeled as a no-op bus (never stateful, never
    -- violating), silently licensing unsound drops — so fail loudly instead.
    | some ("Other", Lean.Json.str name) => .error s!"unknown bus type: Other.{name}"
    | some (k, _) => .error s!"unknown bus type: {k}"
    | none => .error "empty object in bus_map"
  | _ => .error s!"unexpected bus type: {j}"

private def parseBusMap (j : Lean.Json) : Except String BusMapList := do
  let obj ← j.getObjVal? "bus_ids"
  let entries ← match obj with
    | Lean.Json.obj kvs => pure kvs.toList
    | _ => .error "bus_ids is not an object"
  entries.mapM fun (k, v) => do
    let id ← match k.toNat? with
      | some n => pure n
      | none => .error s!"non-numeric bus id: {k}"
    let ty ← parseBusType v
    pure (id, ty)

/-- Parse a JSON expression tree into an `Expression p`. -/
partial def parseJsonExpr (j : Lean.Json) : Except String (Expression p) :=
  match j with
  | Lean.Json.num n =>
    -- All constants in powdr exports are integers (exponent 0).
    let z := n.mantissa * (10 ^ n.exponent)
    .ok (.const (z : ZMod p))
  | Lean.Json.str s => .ok (.var (Variable.ofPowdrName s))
  | Lean.Json.arr items =>
    if h3 : items.size = 3 then
      let lhs := items[0]
      let op := items[1]
      let rhs := items[2]
      match op with
      | Lean.Json.str "+" => do
        let e1 ← parseJsonExpr lhs
        let e2 ← parseJsonExpr rhs
        .ok (.add e1 e2)
      | Lean.Json.str "-" => do
        let e1 ← parseJsonExpr lhs
        let e2 ← parseJsonExpr rhs
        .ok (.add e1 (.mul (.const (-1)) e2))
      | Lean.Json.str "*" => do
        let e1 ← parseJsonExpr lhs
        let e2 ← parseJsonExpr rhs
        .ok (.mul e1 e2)
      | _ => .error s!"unknown operator: {op}"
    else if h2 : items.size = 2 then
      -- unary minus: ["-", expr]
      let op := items[0]
      let operand := items[1]
      match op with
      | Lean.Json.str "-" => do
        let e ← parseJsonExpr operand
        .ok (.mul (.const (-1)) e)
      | _ => .error s!"unknown unary operator: {op}"
    else
      .error s!"expected 2 or 3-element array, got {items.size}"
  | _ => .error s!"unexpected JSON in expression: {j}"

private def parseConstraint (j : Lean.Json) : Except String (Expression p) :=
  parseJsonExpr j

private def parseBusInteraction (j : Lean.Json) :
    Except String (BusInteraction (Expression p)) := do
  let id ← j.getObjVal? "id"
  let busId ← id.getNat?
  let mult ← j.getObjVal? "mult"
  let multiplicity ← parseJsonExpr mult
  let argsJson ← j.getObjVal? "args"
  let argsArr ← match argsJson with
    | Lean.Json.arr a => pure a
    | _ => .error "args is not an array"
  let payload ← argsArr.toList.mapM fun a => parseJsonExpr a
  pure {
    busId := busId,
    multiplicity := multiplicity,
    payload := payload
  }

/-- Parse a JSON string into a `ConstraintSystem` and `BusMap`, starting at the `machine`
    key. Constraints are assert-zero expressions. -/
def parseJsonSystem (jsonStr : String) : Except String (ConstraintSystem p × BusMapList) := do
  let json ← Lean.Json.parse jsonStr
  let machine ← json.getObjVal? "machine"

  -- Parse constraints
  let constraintsJson ← machine.getObjVal? "constraints"
  let constraintArr ← match constraintsJson with
    | Lean.Json.arr a => pure a
    | _ => .error "constraints is not an array"
  let constraints : List (Expression p) ←
    constraintArr.toList.mapM fun c => parseConstraint (p := p) c

  -- Parse bus interactions
  let busJson ← machine.getObjVal? "bus_interactions"
  let busArr ← match busJson with
    | Lean.Json.arr a => pure a
    | _ => .error "bus_interactions is not an array"
  let busInteractions : List (BusInteraction (Expression p)) ←
    busArr.toList.mapM (parseBusInteraction (p := p))

  -- Parse bus_map
  let busMapJson ← json.getObjVal? "bus_map"
  let busMap ← parseBusMap busMapJson

  let system : ConstraintSystem p := {
    algebraicConstraints := constraints,
    busInteractions := busInteractions
  }
  pure (system, busMap)

/-- info: Parsed 9168 constraints, 3117 bus interactions, 6 bus types -/
#guard_msgs in
#eval! do
  let contents ← IO.FS.readFile "apc_reth_op_bug.json"
  match parseJsonSystem (p := 2013265921) contents with
  | .ok (system, busMap) =>
    IO.println s!"Parsed {system.algebraicConstraints.length} constraints, {system.busInteractions.length} bus interactions, {busMap.length} bus types"
  | .error e =>
    IO.println s!"Error: {e}"
