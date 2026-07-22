import ApcOptimizer.Implementation.OptimizerPasses.ZeroWidthRange
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.RangeBool

set_option autoImplicit false

/-! # Dense width-0 / width-1 range-check conversion: correctness proof and wiring

`DensePassCorrect` proof for `ZeroWidthRange.lean`, lifted via `DenseVerifiedPassW.of`: add the
entailed constraints (`denseAddConstraints`), then drop the now-entailed checks
(`denseFilterBusEntailed`), composed by `DensePassCorrect.trans`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Structure of a recognised degenerate range check. -/
theorem denseRangeEq?_spec (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (h : denseRangeEq? one bs facts bi = some e) :
    bi.multiplicity = DenseExpr.const 1 ∧
      ∃ v, ((facts.zeroRangeEq bi.busId = true ∧ bi.payload = [v, DenseExpr.const 0] ∧ e = v)
        ∨ (one = true ∧ facts.varRangeBus bi.busId = true
            ∧ bi.payload = [v, DenseExpr.const 1] ∧ e = denseBoolC v)) := by
  grind [denseRangeEq?]

/-- A recognised degenerate range check lives on a stateless bus. -/
theorem denseRangeEq?_stateless (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (h : denseRangeEq? one bs facts bi = some e) : bs.isStateful bi.busId = false := by
  obtain ⟨_, v, hcase⟩ := denseRangeEq?_spec one bs facts bi e h
  rcases hcase with ⟨hz, _, _⟩ | ⟨_, hv, _, _⟩
  · exact (facts.zeroRangeEq_sound bi.busId hz).1
  · exact (facts.varRangeBus_sound bi.busId hv).1

/-- For a recognised check, acceptance is exactly the vanishing of its returned constraint. -/
theorem denseRangeEq?_violates_iff (one : Bool) (hone : one = true → Nat.Prime p)
    (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (e : DenseExpr p) (denv : VarId → ZMod p) (h : denseRangeEq? one bs facts bi = some e) :
    bs.violatesConstraint (denseBIEval bi denv) = false ↔ e.eval denv = 0 := by
  obtain ⟨hm, v, hcase⟩ := denseRangeEq?_spec one bs facts bi e h
  rcases hcase with ⟨hz, hp', rfl⟩ | ⟨hone', hv, hp', rfl⟩
  · have hev : denseBIEval bi denv
        = { busId := bi.busId, multiplicity := 1, payload := [e.eval denv, 0] } := by
      unfold denseBIEval; rw [hm, hp']; simp [DenseExpr.eval]
    rw [hev]
    exact (facts.zeroRangeEq_sound bi.busId hz).2 (e.eval denv)
  · have hev : denseBIEval bi denv
        = { busId := bi.busId, multiplicity := 1, payload := [v.eval denv, 1] } := by
      unfold denseBIEval; rw [hm, hp']; simp [DenseExpr.eval]
    have hprime := hone hone'
    rw [hev, denseBoolC_eval, ← ZeroWidthRange.val_lt_two_iff hprime]
    have h1val : (1 : ZMod p).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hprime.one_lt]
    rw [(facts.varRangeBus_sound bi.busId hv).2 (v.eval denv) 1 1, h1val]
    constructor
    · exact fun ⟨_, hlt⟩ => by rwa [pow_one] at hlt
    · exact fun hlt => ⟨by omega, by rwa [pow_one]⟩

/-- The variables of a recognised check's constraint occur in `d`. -/
theorem denseRangeEq?_vars (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (h : denseRangeEq? one bs facts bi = some e) (hbi : bi ∈ d.busInteractions) :
    ∀ z ∈ e.vars, z ∈ d.occ := by
  grind [denseRangeEq?, DenseConstraintSystem.mem_occ_of_bi, denseBIVars, denseBoolC,
    DenseExpr.vars]

/-- A recognised check's constraint holds on every satisfying dense assignment. -/
theorem denseRangeEq?_eval (one : Bool) (hone : one = true → Nat.Prime p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (bi : BusInteraction (DenseExpr p))
    (e : DenseExpr p) (h1ne : (1 : ZMod p) ≠ 0) (h : denseRangeEq? one bs facts bi = some e)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) (hbi : bi ∈ d.busInteractions) :
    e.eval denv = 0 := by
  have hmult : (denseBIEval bi denv).multiplicity = 1 := by
    obtain ⟨hm, _⟩ := denseRangeEq?_spec one bs facts bi e h
    show bi.multiplicity.eval denv = 1; rw [hm]; rfl
  have hviol : bs.violatesConstraint (denseBIEval bi denv) = false :=
    hsat.2 bi hbi (by rw [hmult]; exact h1ne)
  exact (denseRangeEq?_violates_iff one hone bs facts bi e denv h).mp hviol

/-- Every variable of an added constraint occurs in `d`. -/
theorem denseRangeEqNew_vars (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ e ∈ d.busInteractions.filterMap (denseRangeEq? one bs facts), ∀ z ∈ e.vars, z ∈ d.occ := by
  intro e he z hz
  obtain ⟨bi, hbi, hf⟩ := List.mem_filterMap.1 he
  exact denseRangeEq?_vars one bs facts d bi e hf hbi z hz

theorem denseZeroWidthRangeF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseZeroWidthRangeF pw bs facts d).CoveredBy reg := by
  unfold denseZeroWidthRangeF
  by_cases h : (1 : ZMod p) ≠ 0
  · rw [if_pos h]
    refine DenseConstraintSystem.filterBus_covered ?_
    refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h1 | h1
    · exact hcov.1 e h1
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i
        (denseRangeEqNew_vars pw.isPrime bs facts d e h1 i hi)
  · rw [if_neg h]; exact hcov

theorem denseZeroWidthRangeF_correct (pw : PrimeWitness p) (reg : VarRegistry) {bs : BusSemantics p}
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseZeroWidthRangeF pw bs facts d) [] bs := by
  unfold denseZeroWidthRangeF
  by_cases h1 : (1 : ZMod p) ≠ 0
  · rw [if_pos h1]
    have hone : pw.isPrime = true → Nat.Prime p := pw.correct
    have hadd : DensePassCorrect reg.isInput d
        { d with algebraicConstraints :=
          d.algebraicConstraints ++ d.busInteractions.filterMap (denseRangeEq? pw.isPrime bs facts) }
        [] bs :=
      DensePassCorrect.denseAddConstraints d bs
        (d.busInteractions.filterMap (denseRangeEq? pw.isPrime bs facts))
        (denseRangeEqNew_vars pw.isPrime bs facts d)
        (fun denv _ hsat c hc => by
          obtain ⟨bi, hbi, hf⟩ := List.mem_filterMap.1 hc
          exact denseRangeEq?_eval pw.isPrime hone bs facts d bi c h1 hf denv hsat hbi)
    refine DensePassCorrect.trans hadd ?_
    refine DensePassCorrect.denseFilterBusEntailed _ bs reg.isInput
      (fun bi => (denseRangeEq? pw.isPrime bs facts bi).isNone) ?_ ?_
    · intro bi hbimem hkf
      obtain ⟨e, he⟩ : ∃ e, denseRangeEq? pw.isPrime bs facts bi = some e := by
        have hkf' : (denseRangeEq? pw.isPrime bs facts bi).isNone = false := hkf
        cases hopt : denseRangeEq? pw.isPrime bs facts bi with
        | none => rw [hopt] at hkf'; simp at hkf'
        | some e => exact ⟨e, rfl⟩
      exact denseRangeEq?_stateless pw.isPrime bs facts bi e he
    · intro bi hbimem hkf denv hsatf _hm
      obtain ⟨e, he⟩ : ∃ e, denseRangeEq? pw.isPrime bs facts bi = some e := by
        have hkf' : (denseRangeEq? pw.isPrime bs facts bi).isNone = false := hkf
        cases hopt : denseRangeEq? pw.isPrime bs facts bi with
        | none => rw [hopt] at hkf'; simp at hkf'
        | some e => exact ⟨e, rfl⟩
      have hbi : bi ∈ d.busInteractions := hbimem
      have hemem : e ∈ d.algebraicConstraints
          ++ d.busInteractions.filterMap (denseRangeEq? pw.isPrime bs facts) :=
        List.mem_append_right _ (List.mem_filterMap.2 ⟨bi, hbi, he⟩)
      rw [denseRangeEq?_violates_iff pw.isPrime hone bs facts bi e denv he]
      exact hsatf.1 e hemem
  · rw [if_neg h1]; exact DensePassCorrect.refl reg.isInput d bs

/-- The dense `zeroWidthRange` pass. -/
def denseZeroWidthRangePass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (denseZeroWidthRangeF pw) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseZeroWidthRangeF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseZeroWidthRangeF_correct pw reg facts d)

end ApcOptimizer.Dense
