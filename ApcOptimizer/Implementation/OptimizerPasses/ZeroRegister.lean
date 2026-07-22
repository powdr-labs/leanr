import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense fixed-zero-register pinning

Impl-only recognisers: fixed-zero data-limb recogniser `denseCellZeroExprs` and filter predicate
`denseZeroPred`. Candidate collection, transform, proof, and wiring in `Proofs/ZeroRegister.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- For a memory message pinned to a fixed-zero cell (declared `zeroCell` shape, nonzero-constant
    multiplicity, and every fixed-address field matching), returns its data-slot expressions — each
    forced to `0`. Empty otherwise. -/
def denseCellZeroExprs (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  match facts.zeroCell bi.busId with
  | none => []
  | some (addrReq, dataSlots) =>
    match bi.multiplicity.constValue? with
    | none => []
    | some c =>
      if decide (c ≠ 0) &&
          addrReq.all (fun ar => decide (bi.payload[ar.1]? = some (DenseExpr.const ar.2))) then
        dataSlots.map (fun slot => (bi.payload[slot]?).getD (DenseExpr.const 0))
      else []

/-- Keep a candidate iff it is non-trivial, not already present, and all its variables occur in the
    system. `dVars` is the occurrence list, passed in by the caller (not recomputed here). -/
def denseZeroPred (d : DenseConstraintSystem p) (dVars : List VarId) (c : DenseExpr p) : Bool :=
  !c.normalize.fold.isConstZero && !d.algebraicConstraints.contains c
    && c.vars.all (fun z => decide (z ∈ dVars))

end ApcOptimizer.Dense
