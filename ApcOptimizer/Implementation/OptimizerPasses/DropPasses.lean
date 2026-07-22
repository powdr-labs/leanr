import ApcOptimizer.Implementation.OptimizerPasses.Rewrite
import ApcOptimizer.Implementation.OptimizerPasses.Adapter

set_option autoImplicit false

/-! # Dense drop-pass runtime recognizers (passes and proofs in `Proofs/DropPasses.lean`) -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Tautology-lookup removal (dense) -/

/-- Constant value of a dense expression (fold then require a literal). -/
def DenseExpr.constValue? (e : DenseExpr p) : Option (ZMod p) :=
  match e.fold with
  | .const c => some c
  | _ => none

/-- Constant values of a dense payload list. -/
def denseConstValues? : List (DenseExpr p) → Option (List (ZMod p))
  | [] => some []
  | e :: rest =>
    match e.constValue?, denseConstValues? rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Constant message of a dense bus interaction, if fully constant. -/
def denseConstMessage? (bi : BusInteraction (DenseExpr p)) : Option (BusInteraction (ZMod p)) :=
  match bi.multiplicity.constValue?, denseConstValues? bi.payload with
  | some m, some vs => some { busId := bi.busId, multiplicity := m, payload := vs }
  | _, _ => none

/-- Recognizes a tautological lookup: a stateless interaction whose message is fully constant and
    already accepted by the bus — e.g. a range check `[5]` against `[0..255]` — hence droppable. -/
def denseIsTautoLookup (bs : BusSemantics p) (bi : BusInteraction (DenseExpr p)) : Bool :=
  !bs.isStateful bi.busId &&
    (match denseConstMessage? bi with
     | some msg => !bs.violatesConstraint msg
     | none => false)

end ApcOptimizer.Dense
