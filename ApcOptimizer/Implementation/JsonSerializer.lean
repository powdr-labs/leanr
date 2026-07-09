import Lean.Data.Json
import ApcOptimizer.Spec
import ApcOptimizer.Utils.Size
import ApcOptimizer.Implementation.Variable

/-!
# JSON serializer for powdr `SymbolicMachine` exports

Turns a `ConstraintSystem p` back into the JSON that powdr's serde deserializes into
`SymbolicMachine<T>` (see `autoprecompiles/src/symbolic_machine.rs` and
`expression/src/lib.rs`). This is the inverse of `ApcOptimizer/Implementation/JsonParser.lean`.

Output schema (matched empirically against powdr's serde):
- top level: `{"constraints":[expr...], "bus_interactions":[{"id","mult","args"}...],
  "derived_columns":[[is_new, "name@id", method]...]}` — a `SymbolicMachine` (`derived_columns`
  has no serde default, so it must be present; each entry is a `DerivedVariable` 3-tuple and
  `method` is an externally-tagged `ComputationMethod`).
- an expression is:
  - a constant  → a JSON integer (powdr's `BabyBearField` serializes as a canonical `u32`);
  - a variable  → the string `"name@id"` (powdr's `AlgebraicReference` manual serde);
  - `a + b`     → `[a, "+", b]`;
  - `a * b`     → `[a, "*", b]`.
  `Expression` has only `const/var/add/mul`, so subtraction / unary-minus never appear;
  negative constants are emitted as their positive representative in `[0, p)`, which powdr
  deserializes back as a `Number`.

## Fresh variables

Some passes (e.g. `Reencode`) introduce brand-new variables that carry no `powdrId?` (the
exporter's `AlgebraicReference` requires an `@<id>`). Before serializing we assign every such
variable a **fresh, unique** id strictly greater than any id already present, memoized so that
equal variables get equal ids and distinct variables get distinct ids. The Rust side then reseeds
its `ColumnAllocator` from the returned machine, so these ids never collide with later passes.

This file is in the (unaudited) implementation layer: a wrong serialization can only make the
round-trip fail, never affect the proven optimizer.
-/

set_option autoImplicit false

open Lean (Json JsonNumber)

variable {p : ℕ}

namespace ApcOptimizer.Serialize

/-- Distinct variables occurring anywhere in the system and (optionally) its derivations. The
    derived columns are introduced witness variables plus whatever variables their computation
    methods read; including them ensures each gets a stable fresh id, shared between its
    constraint occurrences and its derived-column entry. -/
def distinctVars (cs : ConstraintSystem p) (ds : Derivations p := []) : List Variable :=
  let occ := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars ++
    ds.flatMap (fun (v, cm) => v :: cm.vars)
  (occ.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList

/-- A renaming that assigns every fresh (id-less) variable a fresh id, taken strictly above the
    maximum id already present. Variables that already carry an id are absent from the map. -/
def freshRenaming (cs : ConstraintSystem p) (ds : Derivations p := []) : Std.HashMap Variable Nat :=
  let vars := distinctVars cs ds
  let maxId := vars.foldl (fun m x => match x.powdrId? with
    | some i => Nat.max m i
    | none => m) 0
  let fresh := vars.filter (fun x => x.powdrId?.isNone)
  (fresh.foldl (init := ((∅ : Std.HashMap Variable Nat), maxId + 1))
    (fun (acc, i) x => (acc.insert x i, i + 1))).1

/-- The reference string `name@id` emitted for a variable, drawing the id from the variable's own
    `powdrId?` when present, otherwise from the fresh renaming. -/
def refString (m : Std.HashMap Variable Nat) (x : Variable) : String :=
  let id := x.powdrId?.getD (m.getD x 0)
  x.name ++ "@" ++ toString id

/-- A field constant as a JSON integer, using its canonical representative in `[0, p)`. -/
def constJson (n : ZMod p) : Json :=
  Json.num (JsonNumber.fromNat n.val)

/-- Serialize an expression to `Lean.Json`. -/
def serializeExpr (m : Std.HashMap Variable Nat) : Expression p → Json
  | .const n => constJson n
  | .var x => Json.str (refString m x)
  | .add a b => Json.arr #[serializeExpr m a, Json.str "+", serializeExpr m b]
  | .mul a b => Json.arr #[serializeExpr m a, Json.str "*", serializeExpr m b]

/-- Serialize a computation method to powdr's externally-tagged `ComputationMethod` enum JSON
    (derived `serde` on `enum ComputationMethod<T, E>` in
    `constraint-solver/src/constraint_system.rs`):
    `const c → {"Constant": c}`, `quotientOrZero num den → {"QuotientOrZero": [num, den]}`,
    `ifEqZero cond thenM elseM → {"IfEqZero": [cond, thenM, elseM]}`. -/
def serializeComputationMethod (m : Std.HashMap Variable Nat) :
    ComputationMethod p → Json
  | .const c => Json.mkObj [("Constant", constJson c)]
  | .quotientOrZero num den =>
      Json.mkObj [("QuotientOrZero", Json.arr #[serializeExpr m num, serializeExpr m den])]
  | .ifEqZero cond thenM elseM =>
      Json.mkObj [("IfEqZero", Json.arr #[
        serializeExpr m cond,
        serializeComputationMethod m thenM,
        serializeComputationMethod m elseM])]

/-- Serialize the optimizer's derivations to powdr's `derived_columns` JSON: a list of
    `DerivedVariable` 3-tuples `[is_new, variable, computation_method]` (manual `serde` in
    `constraint-solver/src/constraint_system.rs`). Every entry is an optimizer-introduced column,
    so `is_new` is always `true`. -/
def serializeDerivations (m : Std.HashMap Variable Nat) (ds : Derivations p) : Json :=
  Json.arr (ds.map (fun (v, cm) =>
    Json.arr #[Json.bool true, Json.str (refString m v), serializeComputationMethod m cm])).toArray

/-- Serialize a bus interaction to a `{id, mult, args}` object. -/
def serializeBus (m : Std.HashMap Variable Nat) (bi : BusInteraction (Expression p)) : Json :=
  Json.mkObj [
    ("id", Json.num (JsonNumber.fromNat bi.busId)),
    ("mult", serializeExpr m bi.multiplicity),
    ("args", Json.arr (bi.payload.map (serializeExpr m)).toArray)
  ]

/-- Serialize a whole constraint system, together with the optimizer's derivations, as a powdr
    `SymbolicMachine` JSON string. Introduced (id-less) columns get a fresh id via `freshRenaming`
    that is shared between their constraint occurrences and their `derived_columns` entry. -/
def serializeSystem (cs : ConstraintSystem p) (ds : Derivations p := []) : String :=
  let m := freshRenaming cs ds
  let machine := Json.mkObj [
    ("constraints", Json.arr (cs.algebraicConstraints.map (serializeExpr m)).toArray),
    ("bus_interactions", Json.arr (cs.busInteractions.map (serializeBus m)).toArray),
    ("derived_columns", serializeDerivations m ds)
  ]
  machine.compress

end ApcOptimizer.Serialize
