import Lean.Data.Json
import ApcOptimizer.Spec
import ApcOptimizer.Utils.Size
import ApcOptimizer.Implementation.Variable

/-!
# JSON serializer for powdr `SymbolicMachine` exports

Inverse of `ApcOptimizer/Implementation/JsonParser.lean`: turns a `ConstraintSystem p` back into the
JSON powdr's serde deserializes into `SymbolicMachine<T>`.

Output schema:
- `SymbolicMachine`: `{"constraints":[expr...], "bus_interactions":[{"id","mult","args"}...],
  "derived_columns":[[is_new, "name@id", method]...]}` (`derived_columns` must be present; `method`
  is an externally-tagged `ComputationMethod`). `serializeResult` wraps it as
  `{"machine": …, "next_free_id": N}`.
- an expression: constant → JSON integer; variable → `"name@id"`; `a + b` → `[a, "+", b]`;
  `a * b` → `[a, "*", b]`. Negative constants are emitted as their representative in `[0, p)`.

Fresh (id-less) variables introduced by passes get a unique id from powdr's incoming `next_free_id`
cursor (or, absent one, above the largest id present). A wrong serialization can only fail the
round-trip, never affect the proven optimizer.
-/

set_option autoImplicit false

open Lean (Json JsonNumber)

variable {p : ℕ}

namespace ApcOptimizer.Serialize

/-- Distinct variables occurring anywhere in the system and (optionally) its derivations, so each
    gets a stable fresh id shared across its occurrences and derived-column entry. -/
def distinctVars (cs : ConstraintSystem p) (ds : Derivations p := []) : List Variable :=
  let occ := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars ++
    ds.flatMap (fun (v, cm) => v :: cm.vars)
  (occ.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList

/-- Assign each fresh (id-less) variable a unique id starting at `base`, returning the map plus the
    advanced cursor. Variables that already carry an id are absent from the map. -/
def freshRenaming (cs : ConstraintSystem p) (ds : Derivations p := []) (base : Nat) :
    Std.HashMap Variable Nat × Nat :=
  let fresh := (distinctVars cs ds).filter (fun x => x.powdrId?.isNone)
  fresh.foldl (init := ((∅ : Std.HashMap Variable Nat), base))
    (fun (acc, i) x => (acc.insert x i, i + 1))

/-- The reference string `name@id` for a variable (id from `powdrId?` or the fresh renaming). -/
def refString (m : Std.HashMap Variable Nat) (x : Variable) : String :=
  let id := x.powdrId?.getD (m.getD x 0)
  x.name ++ "@" ++ toString id

/-- A field constant as a JSON integer, using its canonical representative in `[0, p)`. -/
def constJson (n : ZMod p) : Json :=
  Json.num (JsonNumber.fromNat n.val)

def serializeExpr (m : Std.HashMap Variable Nat) : Expression p → Json
  | .const n => constJson n
  | .var x => Json.str (refString m x)
  | .add a b => Json.arr #[serializeExpr m a, Json.str "+", serializeExpr m b]
  | .mul a b => Json.arr #[serializeExpr m a, Json.str "*", serializeExpr m b]

/-- Serialize a computation method to powdr's externally-tagged `ComputationMethod` JSON:
    `const c → {"Constant": c}`, `quotientOrZero → {"QuotientOrZero": [num, den]}`,
    `ifEqZero → {"IfEqZero": [cond, thenM, elseM]}`. -/
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

/-- Serialize derivations to powdr's `derived_columns` JSON: `DerivedVariable` 3-tuples
    `[is_new, variable, computation_method]`. Every entry is optimizer-introduced, so `is_new` is
    always `true`. -/
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

/-- The `SymbolicMachine` object `{constraints, bus_interactions, derived_columns}` under a
    variable→id renaming. -/
def serializeMachine (m : Std.HashMap Variable Nat) (cs : ConstraintSystem p)
    (ds : Derivations p) : Json :=
  Json.mkObj [
    ("constraints", Json.arr (cs.algebraicConstraints.map (serializeExpr m)).toArray),
    ("bus_interactions", Json.arr (cs.busInteractions.map (serializeBus m)).toArray),
    ("derived_columns", serializeDerivations m ds)
  ]

/-- Serialize the system as a bare `SymbolicMachine` JSON string (fresh ids start above the largest
    id present). -/
def serializeSystem (cs : ConstraintSystem p) (ds : Derivations p := []) : String :=
  let base := (distinctVars cs ds).foldl (fun m x => match x.powdrId? with
    | some i => Nat.max m (i + 1)
    | none => m) 0
  (serializeMachine (freshRenaming cs ds base).1 cs ds).compress

/-- Serialize the machine plus the advanced `next_free_id` as `{"machine": …, "next_free_id": N}`
    (the FFI reply; `base` is powdr's incoming cursor). -/
def serializeResult (cs : ConstraintSystem p) (ds : Derivations p := []) (base : Nat := 0) :
    String :=
  let (m, nextFreeId) := freshRenaming cs ds base
  (Json.mkObj [
    ("machine", serializeMachine m cs ds),
    ("next_free_id", Json.num (JsonNumber.fromNat nextFreeId))
  ]).compress

end ApcOptimizer.Serialize
