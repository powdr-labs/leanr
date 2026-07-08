import Lean.Data.Json
import Leanr.Spec
import Leanr.Utils.Size
import Leanr.Implementation.Variable

/-!
# JSON serializer for powdr `SymbolicMachine` exports

Turns a `ConstraintSystem p` back into the JSON that powdr's serde deserializes into
`SymbolicMachine<T>` (see `autoprecompiles/src/symbolic_machine.rs` and
`expression/src/lib.rs`). This is the inverse of `Leanr/Implementation/JsonParser.lean`.

Output schema (matched empirically against powdr's serde):
- top level: `{"constraints":[expr...], "bus_interactions":[{"id","mult","args"}...],
  "derived_columns":[]}` — a bare `SymbolicMachine` (`derived_columns` has no serde default,
  so it must be present).
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

namespace Leanr.Serialize

/-- Distinct variables occurring anywhere in the system. -/
def distinctVars (cs : ConstraintSystem p) : List Variable :=
  let occ := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars
  (occ.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList

/-- A renaming that assigns every fresh (id-less) variable a fresh id, taken strictly above the
    maximum id already present. Variables that already carry an id are absent from the map. -/
def freshRenaming (cs : ConstraintSystem p) : Std.HashMap Variable Nat :=
  let vars := distinctVars cs
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

/-- Serialize a bus interaction to a `{id, mult, args}` object. -/
def serializeBus (m : Std.HashMap Variable Nat) (bi : BusInteraction (Expression p)) : Json :=
  Json.mkObj [
    ("id", Json.num (JsonNumber.fromNat bi.busId)),
    ("mult", serializeExpr m bi.multiplicity),
    ("args", Json.arr (bi.payload.map (serializeExpr m)).toArray)
  ]

/-- Serialize a whole constraint system as a powdr `SymbolicMachine` JSON string. -/
def serializeSystem (cs : ConstraintSystem p) : String :=
  let m := freshRenaming cs
  let machine := Json.mkObj [
    ("constraints", Json.arr (cs.algebraicConstraints.map (serializeExpr m)).toArray),
    ("bus_interactions", Json.arr (cs.busInteractions.map (serializeBus m)).toArray),
    ("derived_columns", Json.arr #[])
  ]
  machine.compress

end Leanr.Serialize
