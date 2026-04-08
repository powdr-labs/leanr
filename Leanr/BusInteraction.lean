import Leanr.Expression
import Leanr.RangeConstraint

structure BusInteraction (e : Type) where
  busId : e
  multiplicity : e
  payload : Array e

instance {p : ℕ} : ToString (BusInteraction (Expression p)) where
  toString bi :=
    "BusInteraction { bus_id: " ++ toString bi.busId ++
    ", multiplicity: " ++ toString bi.multiplicity ++
    ", payload: [" ++ String.intercalate ", " (bi.payload.toList.map toString) ++ "] }"

def BusInteraction.substitute {p : ℕ}
  (bi : BusInteraction (Expression p))
  (x : String)
  (v : ZMod p) : BusInteraction (Expression p) :=
  {
    busId := bi.busId.substitute x v,
    multiplicity := bi.multiplicity.substitute x v,
    payload := bi.payload.map (fun e => e.substitute x v)
  }

/-- Substitute all variables in the map at once. -/
def BusInteraction.substituteAll {p : ℕ}
  (bi : BusInteraction (Expression p))
  (env : Std.HashMap String (ZMod p)) : BusInteraction (Expression p) :=
  {
    busId := bi.busId.substituteAll env,
    multiplicity := bi.multiplicity.substituteAll env,
    payload := bi.payload.map (fun e => e.substituteAll env)
  }

structure BusInteractionHandler (p : ℕ) where
  isBusStateful : ZMod p → Bool
  handleBusInteraction : BusInteraction (RangeConstraint p) → BusInteraction (RangeConstraint p)

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
