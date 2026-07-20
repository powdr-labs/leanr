import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.RangeForceZero
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses

set_option autoImplicit false

/-! # Dense width-0 range check → equality (Task 3, impl-only)

Dense, `VarId`-native transliteration of `OldVariableBased/RangeForceZero.lean`'s *runtime*
definitions: `forceZeroAt` (`:24`), `forceZeroSeeds` (`:93`), and the pass `rangeForceZeroPass`
(`:99`). This is a **single-shot add-seeds** transform (`ConstraintSystem.addConstraints_correct`
at `:99`), so its dense mirror `denseRangeForceZeroF` is one `if`-gated append, exactly the shape
`DenseVerifiedPassW.ofNative`/the DigitFold-style direct construction expects
(`bs → facts → d → d'`). **Impl-only**: `forceZeroAt_spec`/`forceZeroAt_sound`/`forceZeroSeeds_sound`
are proof-side and left for the prover; nothing here is wired into the `denseImpl` selector (the
`OldVariableBased.RangeForceZero` import is kept, so `"rangeForceZero"` still runs the spec pass via
`ofSpec` until the prover flips the selector branch).

`facts.rangeCheckAt` is representation-independent (`(busId : Nat) → (pattern : List (Option (ZMod
p))) → …`) and is consulted unqualified, exactly as the spec does — no dense twin needed.
`Expression.constValue?` → `DenseExpr.constValue?` (`DropPasses.lean:64`). The membership filter
`e.vars.all (fun z => cs.vars.contains z)` mirrors onto `d.occ` (`Measure.lean`), the dense analogue
of `ConstraintSystem.vars` (established in `HintCollapse.lean`'s `denseIsFresh`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The forced-zero expression of `bi`: its value-slot expression, when `bi` is a mult-1 range
    check whose `rangeCheckAt` bound is `1` (`= 2⁰`, so the slot is `< 1`, i.e. `0`). Mirrors
    `RangeForceZero.forceZeroAt` (`OldVariableBased/RangeForceZero.lean:24`). -/
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

/-- The seeds: the forced-zero expression of every recognised width-0 check. Mirrors
    `RangeForceZero.forceZeroSeeds` (`:93`). -/
def denseForceZeroSeeds {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  d.busInteractions.filterMap (denseForceZeroAt facts)

/-- The dense transform: seed `expr = 0` for every width-0 (`bound = 1`) range check. Mirrors
    `RangeForceZero.rangeForceZeroPass` (`:99`), gated identically on `(1 : ZMod p) ≠ 0`. -/
def denseRangeForceZeroF (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := (denseForceZeroSeeds facts d).filter (fun e => e.vars.all (fun z => d.occ.contains z))
    { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
