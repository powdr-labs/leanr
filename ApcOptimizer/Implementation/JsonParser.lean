import Lean.Data.Json
import ApcOptimizer.Spec
import ApcOptimizer.Implementation.Variable
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Sp1Semantics

/-!
# JSON parser for powdr `SymbolicMachine` exports

Parses the `ApcWithBusMap` JSON that powdr's APC export writes (see `autoprecompiles/src/export.rs`
in powdr): the `machine` key holds constraints (assert-zero expression trees) and bus interactions
(`{id, mult, args}`), and `bus_map.bus_ids` maps bus ids to bus types. Parsing needs no primality:
everything lands in `ZMod p` verbatim.
-/

set_option autoImplicit false

open ApcOptimizer.OpenVM (OpenVmBusType BusMapList)

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

/-- Parse one SP1 bus type from a `bus_map.bus_ids` value, mirroring powdr's `sp1_bus_map`.
    Unknown bus types fail loudly: an unmapped bus would be modeled as a no-op (never stateful,
    never violating), silently licensing unsound drops. -/
private def parseBusTypeSp1 (j : Lean.Json) : Except String ApcOptimizer.SP1.Sp1BusType :=
  match j with
  | Lean.Json.str "ExecutionBridge" => .ok .executionBridge
  | Lean.Json.str "Memory" => .ok .memory
  | Lean.Json.str "PcLookup" => .ok .pcLookup
  | Lean.Json.obj obj =>
    match obj.toList.head? with
    | some ("Other", Lean.Json.str "Byte") => .ok .byteLookup
    | some ("Other", Lean.Json.str "UntrustedInstruction") => .ok .instructionFetch
    | some ("Other", Lean.Json.str "PageProt") => .ok .pageProt
    | some ("Other", Lean.Json.str name) => .error s!"unknown bus type: Other.{name}"
    | some (k, _) => .error s!"unknown bus type: {k}"
    | none => .error "empty object in bus_map"
  | _ => .error s!"unexpected bus type: {j}"

private def parseBusMapSp1 (j : Lean.Json) :
    Except String ApcOptimizer.SP1.BusMapList := do
  let obj ← j.getObjVal? "bus_ids"
  let entries ← match obj with
    | Lean.Json.obj kvs => pure kvs.toList
    | _ => .error "bus_ids is not an object"
  entries.mapM fun (k, v) => do
    let id ← match k.toNat? with
      | some n => pure n
      | none => .error s!"non-numeric bus id: {k}"
    let ty ← parseBusTypeSp1 v
    pure (id, ty)

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

/-! ### Variable interning

The parser mints a fresh `String`/`Variable` per occurrence; interning rebuilds the system with one
shared `Variable` per distinct value, so the runtime's pointer fast-path in `String` equality
short-circuits the many later equality tests. The interned system is the same value (`Variable`s
compare equal), so nothing downstream observes the difference except time. -/

/-- Collect one canonical `Variable` object per distinct value. -/
private def collectVars (m : Std.HashMap Variable Variable) : Expression p →
    Std.HashMap Variable Variable
  | .const _ => m
  | .var v => if m.contains v then m else m.insert v v
  | .add a b => collectVars (collectVars m a) b
  | .mul a b => collectVars (collectVars m a) b

/-- Rebuild an expression with every variable replaced by its canonical (equal, shared) object. -/
private def internExpr (m : Std.HashMap Variable Variable) : Expression p → Expression p
  | .const c => .const c
  | .var v => .var (m.getD v v)
  | .add a b => .add (internExpr m a) (internExpr m b)
  | .mul a b => .mul (internExpr m a) (internExpr m b)

/-- Intern all variables of a freshly-parsed system (see the section comment). -/
private def internSystem (cs : ConstraintSystem p) : ConstraintSystem p :=
  let m := cs.busInteractions.foldl
    (fun m bi => bi.payload.foldl collectVars (collectVars m bi.multiplicity))
    (cs.algebraicConstraints.foldl collectVars ∅)
  { algebraicConstraints := cs.algebraicConstraints.map (internExpr m),
    busInteractions := cs.busInteractions.map (fun bi =>
      { bi with multiplicity := internExpr m bi.multiplicity,
                payload := bi.payload.map (internExpr m) }) }

/-- Parse the bus-map-agnostic part of a powdr export: the top-level JSON (so callers pull
    `bus_map` with the right per-VM parser), the constraint system under `machine`, and the
    `next_free_id` cursor if present. -/
private def parseMachinePart (jsonStr : String) :
    Except String (Lean.Json × ConstraintSystem p × Option Nat) := do
  let json ← Lean.Json.parse jsonStr
  let machine ← json.getObjVal? "machine"

  let constraintsJson ← machine.getObjVal? "constraints"
  let constraintArr ← match constraintsJson with
    | Lean.Json.arr a => pure a
    | _ => .error "constraints is not an array"
  let constraints : List (Expression p) ←
    constraintArr.toList.mapM fun c => parseConstraint (p := p) c

  let busJson ← machine.getObjVal? "bus_interactions"
  let busArr ← match busJson with
    | Lean.Json.arr a => pure a
    | _ => .error "bus_interactions is not an array"
  let busInteractions : List (BusInteraction (Expression p)) ←
    busArr.toList.mapM (parseBusInteraction (p := p))

  -- powdr's `ColumnAllocator` cursor; absent or non-numeric parses as `none`.
  let nextFreeId? := (json.getObjVal? "next_free_id").toOption.bind (·.getNat?.toOption)

  let system : ConstraintSystem p := internSystem {
    algebraicConstraints := constraints,
    busInteractions := busInteractions
  }
  pure (json, system, nextFreeId?)

/-- Parse a powdr export into a `ConstraintSystem`, its OpenVM `BusMap`, and the `next_free_id`
    cursor. -/
def parseJsonSystem (jsonStr : String) :
    Except String (ConstraintSystem p × BusMapList × Option Nat) := do
  let (json, system, nextFreeId?) ← parseMachinePart (p := p) jsonStr
  let busMap ← parseBusMap (← json.getObjVal? "bus_map")
  pure (system, busMap, nextFreeId?)

/-- The SP1 counterpart of `parseJsonSystem`: same machine parsing, but the `bus_map` is read as SP1
    bus types. SP1 exports are over KoalaBear, so instantiate `p := koalaBear`. -/
def parseJsonSystemSp1 (jsonStr : String) :
    Except String (ConstraintSystem p × ApcOptimizer.SP1.BusMapList × Option Nat) := do
  let (json, system, nextFreeId?) ← parseMachinePart (p := p) jsonStr
  let busMap ← parseBusMapSp1 (← json.getObjVal? "bus_map")
  pure (system, busMap, nextFreeId?)

/- A real powdr export exercising every parser path; gzipped like the CLI inputs, so
   decompress with `gunzip -c`. -/
/-- info: Parsed 117 constraints, 71 bus interactions, 6 bus types -/
#guard_msgs in
#eval! do
  let result ← IO.Process.output
    { cmd := "gunzip",
      args := #["-c", "Benchmarks/OpenVM/openvm-eth/apc_001_pc0x4ecc54.json.gz"] }
  match parseJsonSystem (p := 2013265921) result.stdout with
  | .ok (system, busMap, _) =>
    IO.println s!"Parsed {system.algebraicConstraints.length} constraints, {system.busInteractions.length} bus interactions, {busMap.length} bus types"
  | .error e =>
    IO.println s!"Error: {e}"
