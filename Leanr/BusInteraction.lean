import Leanr.Expression
import Leanr

structure BusInteraction (e : Type) where
  busId : e
  multiplicity : e
  payload : List e

instance {p : ℕ} : ToString (BusInteraction (Expression p)) where
  toString bi :=
    "BusInteraction { bus_id: " ++ toString bi.busId ++
    ", multiplicity: " ++ toString bi.multiplicity ++
    ", payload: [" ++ String.intercalate ", " (bi.payload.map toString) ++ "] }"

def BusInteraction.substitute {p : ℕ}
  (bi : BusInteraction (Expression p))
  (x : String)
  (v : ZMod p) : BusInteraction (Expression p) :=
  {
    busId := bi.busId.substitute x v,
    multiplicity := bi.multiplicity.substitute x v,
    payload := bi.payload.map (fun e => e.substitute x v)
  }

structure BusInteractionHandler (p : ℕ) where
  isBusStateful : ZMod p → Bool
  handleBusInteraction : BusInteraction (RangeConstraint p) → BusInteraction (RangeConstraint p)
