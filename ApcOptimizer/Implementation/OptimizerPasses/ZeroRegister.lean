import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense fixed-zero-register pinning (impl-only)

Runtime recognisers for `zeroRegister`: the per-interaction fixed-zero data-limb recogniser
`denseCellZeroExprs` and the filter predicate `denseZeroPred`. The proof-carrying candidate
collection (`denseCollectZeroCells`), the transform (`denseZeroRegisterF`), the `DensePassCorrect`
proof, and the pass wiring live in `ZeroRegisterProof.lean` (the collection is the
candidate-collection shape and the entailment proof in one object).

`denseZeroPred` takes the occurrence list `dVars` as an explicit argument so the caller can hoist
`d.occ` ONCE rather than recomputing the full-system occurrence flatMap per candidate/variable. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense per-interaction fixed-zero data limbs -/

/-- The fixed-zero data limbs of one interaction: empty unless the bus has a declared zero-cell
    shape, the multiplicity is a nonzero constant, and every fixed-address field matches — in which
    case the data slots' payload expressions (each defaulting to the constant `0` if missing) are
    returned. -/
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

/-! ## The dense filter predicate -/

/-- Keep a candidate constraint iff it is non-trivial, not already present, and every one of its
    variables occurs somewhere in the system. The occurrence list `dVars` is hoisted and captured
    by the caller (`denseZeroRegisterF`); it is NOT recomputed per candidate. -/
def denseZeroPred (d : DenseConstraintSystem p) (dVars : List VarId) (c : DenseExpr p) : Bool :=
  !c.normalize.fold.isConstZero && !d.algebraicConstraints.contains c
    && c.vars.all (fun z => decide (z ∈ dVars))

end ApcOptimizer.Dense
