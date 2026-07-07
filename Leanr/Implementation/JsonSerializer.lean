import Lean.Data.Json
import Leanr.Spec
import Leanr.Implementation.JsonParser
import Leanr.Utils.Size

/-!
# JSON serializer for powdr `SymbolicMachine` exports

Turns a `ConstraintSystem p` back into the JSON that powdr's serde deserializes into
`SymbolicMachine<T>` (see `autoprecompiles/src/symbolic_machine.rs` and
`expression/src/lib.rs`). This is the inverse of `Leanr/Implementation/JsonParser.lean`.

Output schema (matched empirically against powdr's serde):
- top level: `{"constraints":[expr...], "bus_interactions":[{"id","mult","args"}...],
  "derived_columns":[dv...]}` — a bare `SymbolicMachine` (`derived_columns` has no serde default,
  so it must be present).
- an expression is:
  - a constant  → a JSON integer (powdr's `BabyBearField` serializes as a canonical `u32`);
  - a variable  → the string `"name@id"` (powdr's `AlgebraicReference` manual serde);
  - `a + b`     → `[a, "+", b]`;
  - `a * b`     → `[a, "*", b]`.
  `Expression` has only `const/var/add/mul`, so subtraction / unary-minus never appear;
  negative constants are emitted as their positive representative in `[0, p)`, which powdr
  deserializes back as a `Number`.
- a `ComputationMethod` is an externally-tagged enum — `{"Constant": <field>}`,
  `{"QuotientOrZero": [num, den]}`, `{"IfEqZero": [cond, then, else]}`.
- a `DerivedVariable` is the 3-tuple `[is_new, "name@id", computation_method]`.

## Fresh variables

Some passes (e.g. `Reencode`) introduce brand-new variables whose names carry no `@<id>`
suffix (the exporter's `AlgebraicReference` requires an `@`). Before serializing we assign every
such name a **fresh, unique** id strictly greater than any id already present, memoized so that
equal names get equal ids and distinct names get distinct ids. Derived-column names and the
expressions inside their computation methods are renamed with the *same* map so a fresh column and
the hint that computes it agree on the id. The Rust side then reseeds its `ColumnAllocator` from
the returned machine, so these ids never collide with later passes.

This file is in the (unaudited) implementation layer: a wrong serialization can only make the
round-trip fail, never affect the proven optimizer.
-/

set_option autoImplicit false

open Lean (Json JsonNumber)

variable {p : ℕ}

namespace Leanr.Serialize

/-- The id encoded in a variable name `name@id` (after the *last* `@`, matching powdr's
    `rfind('@')`), or `none` if the name carries no numeric `@`-suffix. -/
def parseVarId (x : String) : Option Nat :=
  match (x.splitOn "@").reverse with
  | idStr :: _ :: _ => idStr.toNat?
  | _ => none

/-- Variable names referenced by a computation method (in its constituent expressions). -/
def computationVars : ComputationMethod p → List String
  | .constant _ => []
  | .quotientOrZero num den => Expression.vars num ++ Expression.vars den
  | .ifEqZero cond thenM elseM =>
      Expression.vars cond ++ computationVars thenM ++ computationVars elseM

/-- Distinct variable names occurring anywhere in the system, including derived-column names and
    the variables referenced by their computation methods. -/
def distinctVars (cs : ConstraintSystem p) : List String :=
  let occ := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars ++
    cs.derivedColumns.flatMap (fun dc => dc.name :: computationVars dc.computation)
  (occ.foldl (init := (∅ : Std.HashSet String)) (·.insert ·)).toList

/-- A renaming that maps every fresh (suffix-less) variable name to `name@<fresh id>`, with fresh
    ids taken strictly above the maximum id already present. Names that already carry an id map to
    themselves (absent from the map). -/
def freshRenaming (cs : ConstraintSystem p) : Std.HashMap String String :=
  let vars := distinctVars cs
  let maxId := vars.foldl (fun m x => match parseVarId x with
    | some i => Nat.max m i
    | none => m) 0
  let fresh := vars.filter (fun x => (parseVarId x).isNone)
  (fresh.foldl (init := ((∅ : Std.HashMap String String), maxId + 1))
    (fun (acc, i) x => (acc.insert x (x ++ "@" ++ toString i), i + 1))).1

/-- The reference string emitted for a variable, applying the fresh renaming. -/
def refString (m : Std.HashMap String String) (x : String) : String :=
  m.getD x x

/-- A field constant as a JSON integer, using its canonical representative in `[0, p)`. -/
def constJson (n : ZMod p) : Json :=
  Json.num (JsonNumber.fromNat n.val)

/-- Serialize an expression to `Lean.Json`. -/
def serializeExpr (m : Std.HashMap String String) : Expression p → Json
  | .const n => constJson n
  | .var x => Json.str (refString m x)
  | .add a b => Json.arr #[serializeExpr m a, Json.str "+", serializeExpr m b]
  | .mul a b => Json.arr #[serializeExpr m a, Json.str "*", serializeExpr m b]

/-- Serialize a bus interaction to a `{id, mult, args}` object. -/
def serializeBus (m : Std.HashMap String String) (bi : BusInteraction (Expression p)) : Json :=
  Json.mkObj [
    ("id", Json.num (JsonNumber.fromNat bi.busId)),
    ("mult", serializeExpr m bi.multiplicity),
    ("args", Json.arr (bi.payload.map (serializeExpr m)).toArray)
  ]

/-- Serialize a `ComputationMethod` as powdr's externally-tagged enum, applying the fresh
    renaming `m` to every variable reference inside it. -/
def serializeComputationMethod (m : Std.HashMap String String) :
    ComputationMethod p → Json
  | .constant n => Json.mkObj [("Constant", constJson n)]
  | .quotientOrZero num den =>
      Json.mkObj [("QuotientOrZero", Json.arr #[serializeExpr m num, serializeExpr m den])]
  | .ifEqZero cond thenM elseM =>
      Json.mkObj [("IfEqZero",
        Json.arr #[serializeExpr m cond,
          serializeComputationMethod m thenM, serializeComputationMethod m elseM])]

/-- Serialize a `DerivedVariable` as powdr's 3-tuple `[is_new, variable, computation_method]`,
    applying the fresh renaming to the variable name and to the computation method. -/
def serializeDerivedVariable (m : Std.HashMap String String) (dc : DerivedVariable p) : Json :=
  Json.arr #[Json.bool dc.isNew, Json.str (refString m dc.name),
    serializeComputationMethod m dc.computation]

/-- Serialize a whole constraint system as a powdr `SymbolicMachine` JSON string. -/
def serializeSystem (cs : ConstraintSystem p) : String :=
  let m := freshRenaming cs
  let machine := Json.mkObj [
    ("constraints", Json.arr (cs.algebraicConstraints.map (serializeExpr m)).toArray),
    ("bus_interactions", Json.arr (cs.busInteractions.map (serializeBus m)).toArray),
    ("derived_columns", Json.arr (cs.derivedColumns.map (serializeDerivedVariable m)).toArray)
  ]
  machine.compress

-- Round-trip check: serializing derived columns, parsing them back, and re-serializing yields
-- the identical JSON (so `serialize`/`parse` agree and match powdr's shape). All names already
-- carry an id, so the (empty) renaming is the identity on them.
#guard
  (let dcs : List (DerivedVariable 2013265921) :=
    [ { isNew := true, name := "a@1", computation := .constant 7 },
      { isNew := false, name := "b@2",
        computation := .quotientOrZero (.var "a@1") (.add (.var "c@3") (.const 1)) },
      { isNew := true, name := "d@4",
        computation := .ifEqZero (.var "e@5")
          (.constant 0) (.quotientOrZero (.const 1) (.var "e@5")) } ]
   let m : Std.HashMap String String := ∅
   let json := Json.arr (dcs.map (serializeDerivedVariable m)).toArray
   match json with
   | Json.arr items =>
     match items.toList.mapM (parseDerivedVariable (p := 2013265921)) with
     | .ok parsed =>
         (Json.arr (parsed.map (serializeDerivedVariable m)).toArray).compress = json.compress
     | .error _ => false
   | _ => false)

end Leanr.Serialize
