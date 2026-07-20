import ApcOptimizer.Implementation.OptimizerPasses.Rewrite
import ApcOptimizer.Implementation.OptimizerPasses.Adapter
import ApcOptimizer.Implementation.OptimizerPasses.ZeroMultBus
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus

set_option autoImplicit false

/-! # Dense drop-pass runtime transforms (Task 3): trivial-constraint, zero-multiplicity-bus, and
    tautology-lookup removal

The three drop passes' *runtime* recognizers and predicates. The passes themselves (with their native
`DensePassCorrect` proofs) live in `DropPassesProof.lean`. -/

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

/-- Is this dense interaction a tautology: stateless, with a constant message the bus accepts? -/
def denseIsTautoLookup (bs : BusSemantics p) (bi : BusInteraction (DenseExpr p)) : Bool :=
  !bs.isStateful bi.busId &&
    (match denseConstMessage? bi with
     | some msg => !bs.violatesConstraint msg
     | none => false)

theorem VarRegistry.decodeExpr_constValue? (reg : VarRegistry) (e : DenseExpr p) :
    (reg.decodeExpr e).constValue? = e.constValue? := by
  have h := reg.decodeExpr_fold e
  simp only [Expression.constValue?, DenseExpr.constValue?, ← h]
  cases e.fold <;> rfl

@[simp] theorem VarRegistry.decodeBI_busId (reg : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    (reg.decodeBI bi).busId = bi.busId := rfl

end ApcOptimizer.Dense
