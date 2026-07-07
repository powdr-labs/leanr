import Lean.Data.Json
import Leanr.Spec
import Leanr.Implementation.JsonParser

/-!
# JSON serializer for derived columns

Serializes `DerivedVariable`/`ComputationMethod` (and the `Expression`s they contain) to the exact
JSON shape powdr's serde emits, so that Leanr's derived-column representation round-trips against
powdr (`autoprecompiles`/`constraint-solver`):

- an `Expression` is a JSON tree — `Number` → a bare number, `Reference` → the `"name@id"` string,
  a binary op → `[lhs, "+"/"-"/"*", rhs]` (Leanr only produces `+`/`*`);
- a `ComputationMethod` is an externally-tagged enum — `{"Constant": <field>}`,
  `{"QuotientOrZero": [num, den]}`, `{"IfEqZero": [cond, then, else]}`;
- a `DerivedVariable` is the 3-tuple `[is_new, "name@id", computation_method]`.

This mirrors `parseComputationMethod` / `parseDerivedVariable` in `JsonParser.lean`; the two are
tested to round-trip below. Leanr has no full circuit serializer yet (a separate task); this file
covers the derived-column portion required to emit hints.

Serialization needs no primality: field elements are written as their canonical `ZMod.val`.
-/

set_option autoImplicit false

variable {p : ℕ}

/-- Serialize a field element as its canonical natural-number representative. -/
private def serializeField (n : ZMod p) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat n.val)

/-- Serialize an `Expression` to powdr's JSON expression tree. -/
def serializeExpr : Expression p → Lean.Json
  | .const n => serializeField n
  | .var x => Lean.Json.str x
  | .add e1 e2 => Lean.Json.arr #[serializeExpr e1, Lean.Json.str "+", serializeExpr e2]
  | .mul e1 e2 => Lean.Json.arr #[serializeExpr e1, Lean.Json.str "*", serializeExpr e2]

/-- Serialize a `ComputationMethod` as powdr's externally-tagged enum. -/
def serializeComputationMethod : ComputationMethod p → Lean.Json
  | .constant n => Lean.Json.mkObj [("Constant", serializeField n)]
  | .quotientOrZero num den =>
      Lean.Json.mkObj [("QuotientOrZero", Lean.Json.arr #[serializeExpr num, serializeExpr den])]
  | .ifEqZero cond thenM elseM =>
      Lean.Json.mkObj [("IfEqZero",
        Lean.Json.arr #[serializeExpr cond,
          serializeComputationMethod thenM, serializeComputationMethod elseM])]

/-- Serialize a `DerivedVariable` as powdr's 3-tuple `[is_new, variable, computation_method]`. -/
def serializeDerivedVariable (dc : DerivedVariable p) : Lean.Json :=
  Lean.Json.arr #[Lean.Json.bool dc.isNew, Lean.Json.str dc.name,
    serializeComputationMethod dc.computation]

/-- Serialize a list of derived columns as a JSON array (powdr's `derived_columns`). -/
def serializeDerivedColumns (dcs : List (DerivedVariable p)) : Lean.Json :=
  Lean.Json.arr (dcs.map serializeDerivedVariable).toArray

-- Round-trip check: serializing derived columns, parsing them back, and re-serializing yields
-- the identical JSON (so `serialize`/`parse` agree and match powdr's shape).
#guard
  (let dcs : List (DerivedVariable 2013265921) :=
    [ { isNew := true, name := "a@1", computation := .constant 7 },
      { isNew := false, name := "b@2",
        computation := .quotientOrZero (.var "a@1") (.add (.var "c@3") (.const 1)) },
      { isNew := true, name := "d@4",
        computation := .ifEqZero (.var "e@5")
          (.constant 0) (.quotientOrZero (.const 1) (.var "e@5")) } ]
   let json := serializeDerivedColumns dcs
   match json with
   | Lean.Json.arr items =>
     match items.toList.mapM (parseDerivedVariable (p := 2013265921)) with
     | .ok parsed => (serializeDerivedColumns parsed).compress = json.compress
     | .error _ => false
   | _ => false)
