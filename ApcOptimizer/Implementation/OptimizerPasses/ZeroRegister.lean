import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense fixed-zero-register pinning (Task 3, impl-only)

Dense, `VarId`-native transliteration of the *runtime* recognisers of
the reference `ZeroRegister` pass: the per-interaction fixed-zero data-limb recogniser
`cellZeroExprs` (`:30`) and the filter predicate inside `zeroRegisterPass` (`:113`). The
proof-carrying candidate collection (`denseCollectZeroCells`), the transform (`denseZeroRegisterF`),
the native `DensePassCorrect` proof, and the pass wiring live in `ZeroRegisterProof.lean` (the
collection is the `collectZeroCells` shape fix and the entailment proof in one object).

`denseZeroPred` takes the occurrence list `dVars` as an explicit argument so the caller can hoist
`d.occ` ONCE (mirroring the spec's `let csVars := cs.vars` closure capture) rather than recomputing
the full-system occurrence flatMap per candidate/variable. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense per-interaction fixed-zero data limbs -/

/-- Dense `cellZeroExprs` (see `cellZeroExprs`). -/
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

/-- Dense fixed-zero filter predicate (see the filter inside `zeroRegisterPass`). The occurrence
    list `dVars` is hoisted and captured by the caller (`denseZeroRegisterF`), mirroring the spec's
    `let csVars := cs.vars`; it is NOT recomputed per candidate. -/
def denseZeroPred (d : DenseConstraintSystem p) (dVars : List VarId) (c : DenseExpr p) : Bool :=
  !c.normalize.fold.isConstZero && !d.algebraicConstraints.contains c
    && c.vars.all (fun z => decide (z ∈ dVars))

end ApcOptimizer.Dense
