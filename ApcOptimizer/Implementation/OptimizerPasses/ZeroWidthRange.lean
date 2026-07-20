import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Rewrite
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroWidthRange

set_option autoImplicit false

/-! # Dense width-0 / width-1 range-check conversion (Task 3)

Dense, `VarId`-native port of `ZeroWidthRange.zeroWidthRangePass`. Gated on `(1 : ZMod p) ≠ 0`, it
appends the equivalent algebraic constraint for every degenerate range check (`value = 0` for
width-0, its booleanity `value·(value−1) = 0` for width-1 when `p` is prime) and then drops the
now-entailed interactions.

It is **fact-consuming** (`zeroRangeEq`/`varRangeBus`), so it is built with the DigitFold
direct-`DensePassResult` construction (threading the unchanged `BusFacts`). The recognizer `rangeEq?`
is mirrored on `DenseExpr` (payload/multiplicity/constant/degree comparisons, all decode-stable);
the transform is an **append then `filterBus`**, so its output commutation chains
`decodeCS_append_constraints` with `decodeCS_filterBus` (the keep predicate corresponds under decode
because `Option.map` preserves `isNone`). -/

namespace ApcOptimizer.Dense

open ZeroWidthRange

variable {p : ℕ}

/-! ## Dense booleanity constraint -/

/-- `v·(v − 1)` as a dense expression (mirrors `ZeroWidthRange.boolC`). -/
def denseBoolC (v : DenseExpr p) : DenseExpr p := .mul v (.add v (.const (-1)))

theorem denseBoolC_decode (reg : VarRegistry) (v : DenseExpr p) :
    reg.decodeExpr (denseBoolC v) = boolC (reg.decodeExpr v) := rfl

theorem denseBoolC_covered {reg : VarRegistry} {v : DenseExpr p} (hv : v.CoveredBy reg) :
    (denseBoolC v).CoveredBy reg :=
  DenseExpr.coveredBy_mul.mpr
    ⟨hv, DenseExpr.coveredBy_add.mpr ⟨hv, DenseExpr.coveredBy_const reg _⟩⟩

/-! ## Dense recognizer -/

/-- Dense `rangeEq?` (see `ZeroWidthRange.rangeEq?`). -/
def denseRangeEq? (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match bi.payload with
  | [v, c] =>
    if bi.multiplicity = DenseExpr.const 1 then
      if facts.zeroRangeEq bi.busId = true ∧ c = DenseExpr.const 0 then some v
      else if one = true ∧ facts.varRangeBus bi.busId = true ∧ c = DenseExpr.const 1
          ∧ v.degree ≤ 1 then some (denseBoolC v)
      else none
    else none
  | _ => none

theorem denseRangeEq?_decode (reg : VarRegistry) (one : Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p)) :
    rangeEq? one bs facts (reg.decodeBI bi) = (denseRangeEq? one bs facts bi).map reg.decodeExpr := by
  unfold rangeEq? denseRangeEq?
  rw [show (reg.decodeBI bi).payload = bi.payload.map reg.decodeExpr from rfl]
  cases hpl : bi.payload with
  | nil => rfl
  | cons v rest =>
      cases rest with
      | nil => rfl
      | cons c rest2 =>
          cases rest2 with
          | cons _ _ => rfl
          | nil =>
              simp only [List.map_cons, List.map_nil]
              rw [show (reg.decodeBI bi).multiplicity = reg.decodeExpr bi.multiplicity from rfl]
              by_cases hm : bi.multiplicity = DenseExpr.const 1
              · rw [if_pos ((reg.decodeExpr_eq_const bi.multiplicity 1).mpr hm), if_pos hm,
                  show (reg.decodeBI bi).busId = bi.busId from rfl]
                by_cases hA : facts.zeroRangeEq bi.busId = true ∧ c = DenseExpr.const 0
                · rw [if_pos ⟨hA.1, (reg.decodeExpr_eq_const c 0).mpr hA.2⟩, if_pos hA]; rfl
                · rw [if_neg (fun hh => hA ⟨hh.1, (reg.decodeExpr_eq_const c 0).mp hh.2⟩), if_neg hA]
                  by_cases hB : one = true ∧ facts.varRangeBus bi.busId = true ∧ c = DenseExpr.const 1
                      ∧ v.degree ≤ 1
                  · rw [if_pos ⟨hB.1, hB.2.1, (reg.decodeExpr_eq_const c 1).mpr hB.2.2.1,
                        by rw [reg.decodeExpr_degree]; exact hB.2.2.2⟩, if_pos hB]; rfl
                  · rw [if_neg (fun hh => hB ⟨hh.1, hh.2.1, (reg.decodeExpr_eq_const c 1).mp hh.2.2.1,
                        by rw [← reg.decodeExpr_degree v]; exact hh.2.2.2⟩), if_neg hB]; rfl
              · rw [if_neg (fun hh => hm ((reg.decodeExpr_eq_const bi.multiplicity 1).mp hh)),
                  if_neg hm]; rfl

theorem denseRangeEq?_covered (reg : VarRegistry) (one : Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) {bi : BusInteraction (DenseExpr p)} (hc : denseBICovered reg bi)
    {e : DenseExpr p} (h : denseRangeEq? one bs facts bi = some e) : e.CoveredBy reg := by
  unfold denseRangeEq? at h
  cases hpl : bi.payload with
  | nil => rw [hpl] at h; simp at h
  | cons v rest =>
      cases rest with
      | nil => rw [hpl] at h; simp at h
      | cons c rest2 =>
          cases rest2 with
          | cons _ _ => rw [hpl] at h; simp at h
          | nil =>
              rw [hpl] at h
              have hvc : v.CoveredBy reg := hc.2 v (by rw [hpl]; simp)
              dsimp only at h
              split_ifs at h with hm hA hB
              · obtain rfl := Option.some.inj h; exact hvc
              · obtain rfl := Option.some.inj h; exact denseBoolC_covered hvc

/-- The keep predicate corresponds under decode: `Option.map` preserves `isNone`. -/
theorem denseKeep_decode (reg : VarRegistry) (one : Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p)) :
    (denseRangeEq? one bs facts bi).isNone = (rangeEq? one bs facts (reg.decodeBI bi)).isNone := by
  rw [denseRangeEq?_decode reg one bs facts bi]
  cases denseRangeEq? one bs facts bi <;> rfl

/-! ## The dense transform and pass -/

/-- The dense width-0/width-1 conversion transform: append the entailed constraints, then drop the
    now-entailed interactions (identity off a prime field). -/
def denseZeroWidthRangeF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    ({ d with algebraicConstraints :=
        d.algebraicConstraints ++ d.busInteractions.filterMap (denseRangeEq? pw.isPrime bs facts) }
      : DenseConstraintSystem p).filterBus
      (fun bi => (denseRangeEq? pw.isPrime bs facts bi).isNone)
  else d

/-- The spec pass output, exposing the field gate. -/
theorem zeroWidthRangePass_out (pw : PrimeWitness p) (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    (zeroWidthRangePass pw cs bs facts).out
      = if (1 : ZMod p) ≠ 0 then
          ({ cs with algebraicConstraints :=
              cs.algebraicConstraints ++ cs.busInteractions.filterMap (rangeEq? pw.isPrime bs facts) }
            : ConstraintSystem p).filterBus (fun bi => (rangeEq? pw.isPrime bs facts bi).isNone)
        else cs := by
  unfold zeroWidthRangePass
  by_cases h : (1 : ZMod p) ≠ 0
  · simp only [dif_pos h, if_pos h]
  · simp only [dif_neg h, if_neg h]

theorem denseZeroWidthRangeF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseZeroWidthRangeF pw bs facts d).CoveredBy reg := by
  unfold denseZeroWidthRangeF
  by_cases h : (1 : ZMod p) ≠ 0
  · rw [if_pos h]
    refine DenseConstraintSystem.filterBus_covered ?_
    refine ⟨fun e he => ?_, fun bi hbi => hcov.2 bi hbi⟩
    rcases List.mem_append.1 he with h1 | h1
    · exact hcov.1 e h1
    · obtain ⟨bi, hbi, hval⟩ := List.mem_filterMap.1 h1
      exact denseRangeEq?_covered reg pw.isPrime bs facts (hcov.2 bi hbi) hval
  · rw [if_neg h]; exact hcov

/-- The dense width-0/width-1 range-check-conversion pass. Fact-consuming; inherits
    `zeroWidthRangePass`'s `PassCorrect` through the decode-commutation of its transform. -/
def denseZeroWidthRangePass (pw : PrimeWitness p) : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := denseZeroWidthRangeF pw bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := denseZeroWidthRangeF_covered pw reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := by
      show PassCorrect (reg.decodeCS d) (reg.decodeCS (denseZeroWidthRangeF pw bs facts d))
        (reg.decodeDerivs ([] : DenseDerivations p)) bs
      have hnewC : (d.busInteractions.filterMap (denseRangeEq? pw.isPrime bs facts)).map reg.decodeExpr
          = (reg.decodeCS d).busInteractions.filterMap (rangeEq? pw.isPrime bs facts) := by
        rw [List.map_filterMap,
          show (reg.decodeCS d).busInteractions = d.busInteractions.map reg.decodeBI from rfl,
          List.filterMap_map]
        exact List.filterMap_congr (fun bi _ => (denseRangeEq?_decode reg pw.isPrime bs facts bi).symm)
      have hout : reg.decodeCS (denseZeroWidthRangeF pw bs facts d)
          = (zeroWidthRangePass pw (reg.decodeCS d) bs facts).out := by
        rw [zeroWidthRangePass_out]
        unfold denseZeroWidthRangeF
        by_cases h : (1 : ZMod p) ≠ 0
        · rw [if_pos h, if_pos h,
            reg.decodeCS_filterBus
              (dk := fun bi => (denseRangeEq? pw.isPrime bs facts bi).isNone)
              (sk := fun bi => (rangeEq? pw.isPrime bs facts bi).isNone)
              _ (fun bi _ => denseKeep_decode reg pw.isPrime bs facts bi),
            reg.decodeCS_append_constraints d, hnewC]
        · rw [if_neg h, if_neg h]
      rw [show reg.decodeDerivs ([] : DenseDerivations p) = [] from rfl, hout]
      have hderiv : (zeroWidthRangePass pw (reg.decodeCS d) bs facts).derivs = [] := by
        unfold zeroWidthRangePass
        by_cases h : (1 : ZMod p) ≠ 0
        · rw [dif_pos h]
        · rw [dif_neg h]
      have hc := (zeroWidthRangePass pw (reg.decodeCS d) bs facts).correct
      rw [hderiv] at hc
      exact hc }

end ApcOptimizer.Dense
