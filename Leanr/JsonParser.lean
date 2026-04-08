import Lean.Data.Json
import Leanr.Solver
import Leanr.Expression

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- A bus map entry describing the type of a bus. -/
inductive BusType where
  | executionBridge
  | memory
  | pcLookup
  | other (name : String)
  deriving Repr, BEq

instance : ToString BusType where
  toString
    | .executionBridge => "ExecutionBridge"
    | .memory => "Memory"
    | .pcLookup => "PcLookup"
    | .other name => name

/-- Mapping from bus IDs to their types. -/
def BusMap := List (Nat × BusType)

instance : ToString BusMap where
  toString bm :=
    let entries := bm.map fun (id, ty) => s!"  {id}: {ty}"
    "BusMap:\n" ++ String.intercalate "\n" entries

private def parseBusType (j : Lean.Json) : Except String BusType :=
  match j with
  | Lean.Json.str "ExecutionBridge" => .ok .executionBridge
  | Lean.Json.str "Memory" => .ok .memory
  | Lean.Json.str "PcLookup" => .ok .pcLookup
  | Lean.Json.str s => .ok (.other s)
  | Lean.Json.obj obj =>
    match obj.toList.head? with
    | some ("Other", Lean.Json.str name) => .ok (.other name)
    | some ("Other", Lean.Json.obj inner) =>
      match inner.toList.head? with
      | some (name, _) => .ok (.other name)
      | none => .error "empty Other object in bus_map"
    | some (k, _) => .ok (.other k)
    | none => .error "empty object in bus_map"
  | _ => .error s!"unexpected bus type: {j}"

private def parseBusMap (j : Lean.Json) : Except String BusMap := do
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
    let z := n.mantissa * (10 ^ n.exponent)
    .ok (.const (z : ZMod p))
  | Lean.Json.str s => .ok (.var s)
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

private def parseBusInteraction (j : Lean.Json) : Except String (BusInteraction (Expression p)) := do
  let id ← j.getObjVal? "id"
  let busId ← parseJsonExpr (p := p) id
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

/-- Parse a JSON string into a `System` and `BusMap`, starting at the `machine` key. -/
def parseJsonSystem (jsonStr : String) : Except String (System p × BusMap) := do
  let json ← Lean.Json.parse jsonStr
  let machine ← json.getObjVal? "machine"

  -- Parse constraints
  let constraintsJson ← machine.getObjVal? "constraints"
  let constraintArr ← match constraintsJson with
    | Lean.Json.arr a => pure a
    | _ => .error "constraints is not an array"
  let constraints : List (AlgebraicConstraint p) ←
    constraintArr.toList.mapM fun c =>
      (parseConstraint (p := p) c).map AlgebraicConstraint.assertZero

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

  let system : System p := {
    constraints := constraints.toArray,
    bus_interactions := busInteractions.toArray,
    assignments := #[]
  }
  pure (system, busMap)

-- BabyBear prime
instance instFactPrimeBabyBear : Fact (Nat.Prime 2013265921) where
  out := by native_decide

/-- info: Parsed 9168 constraints, 3117 bus interactions, 6 bus types -/
#guard_msgs in
#eval! do
  let contents ← IO.FS.readFile "apc_reth_op_bug.json"
  match parseJsonSystem (p := 2013265921) contents with
  | .ok (system, busMap) =>
    IO.println s!"Parsed {system.constraints.size} constraints, {system.bus_interactions.size} bus interactions, {busMap.length} bus types"
  | .error e =>
    IO.println s!"Error: {e}"
