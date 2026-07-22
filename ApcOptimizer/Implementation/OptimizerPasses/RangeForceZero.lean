import ApcOptimizer.Implementation.OptimizerPasses.DropPasses

set_option autoImplicit false

/-! # Dense width-0 range check → equality

Impl-only: recognizer `denseForceZeroAt`, seed collection `denseForceZeroSeeds`, transform
`denseRangeForceZeroF`; correctness and wiring in `RangeForceZeroProof.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The value-slot expression of a mult-1 width-0 (`bound = 1`) range check, forced to `0`. -/
def denseForceZeroAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = DenseExpr.const 1 ∧ bound = 1 then
      -- skip an already-constant slot: it would seed a trivial `0` every cycle until `tautoBus`
      -- drops the now-constant check.
      match bi.payload[valSlot]? with
      | some e => if e.constValue?.isNone then some e else none
      | none => none
    else none
  | none => none

/-- The seeds: the forced-zero expression of every recognised width-0 check. -/
def denseForceZeroSeeds {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  d.busInteractions.filterMap (denseForceZeroAt facts)

/-- For a width-0 range check (`bound = 1`, so its value slot must satisfy `x < 1`, i.e. `x = 0`),
    seeds the constraint `slotExpr = 0`. Gated on `(1 : ZMod p) ≠ 0`. -/
def denseRangeForceZeroF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := (denseForceZeroSeeds facts d).filter (fun e => e.vars.all (fun z => d.occ.contains z))
    { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
