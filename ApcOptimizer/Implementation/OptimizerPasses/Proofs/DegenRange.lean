import ApcOptimizer.Implementation.OptimizerPasses.DegenRange
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch

set_option autoImplicit false

/-! # Dense degenerate range checks → algebraic constraints: rules and wiring

`DenseCheckRule`s for the two recognizers in `DegenRange.lean`, assembled into the `degenRange`
pass by `DenseVerifiedPassW.ofCheckRules`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

theorem denseBoolC_eval (v : DenseExpr p) (denv : VarId → ZMod p) :
    (denseBoolC v).eval denv = v.eval denv * (v.eval denv - 1) := by
  simp only [denseBoolC, DenseExpr.eval]; ring

theorem denseBoolC_vars (v : DenseExpr p) : ∀ x ∈ (denseBoolC v).vars, x ∈ v.vars := by
  intro x hx
  simp only [denseBoolC, DenseExpr.vars, List.mem_append, List.not_mem_nil, or_false] at hx
  tauto

/-! ## The width-0 / width-1 recognizer (`denseRangeEq?`) -/

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
    rw [hev, denseBoolC_eval, ← DegenRange.val_lt_two_iff hprime]
    have h1val : (1 : ZMod p).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hprime.one_lt]
    rw [(facts.varRangeBus_sound bi.busId hv).2 (v.eval denv) 1 1, h1val]
    constructor
    · exact fun ⟨_, hlt⟩ => by rwa [pow_one] at hlt
    · exact fun hlt => ⟨by omega, by rwa [pow_one]⟩

/-- A recognised check's constraint reads only the check's own variables. -/
theorem denseRangeEq?_vars (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (h : denseRangeEq? one bs facts bi = some e) : ∀ z ∈ e.vars, z ∈ denseBIVars bi := by
  grind [denseRangeEq?, denseBIVars, denseBoolC, DenseExpr.vars]

/-- The width-0 / width-1 degenerate-range rule. -/
def denseZeroWidthRule (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    DenseCheckRule p bs where
  recognize := denseRangeEq? pw.isPrime bs facts
  multOne bi e h := (denseRangeEq?_spec pw.isPrime bs facts bi e h).1
  stateless bi e h := denseRangeEq?_stateless pw.isPrime bs facts bi e h
  vars bi e h := denseRangeEq?_vars pw.isPrime bs facts bi e h
  violates_iff bi e h denv :=
    denseRangeEq?_violates_iff pw.isPrime pw.correct bs facts bi e denv h

/-! ## The bare-variable width-1 recognizer (`denseBoolCheck?`) -/

/-- Structure of a recognised width-1 check. -/
theorem denseBoolCheck?_spec {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseBoolCheck? facts bi = some c) :
    ∃ valSlot x, facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?)
        = some (valSlot, 2) ∧ bi.multiplicity = DenseExpr.const 1 ∧
        bi.payload[valSlot]? = some (DenseExpr.var x) ∧ c = denseBoolC (DenseExpr.var x) := by
  grind [denseBoolCheck?]

/-- For a recognised width-1 check, acceptance is exactly the booleanity of its value variable. -/
theorem denseBoolCheck?_violates_iff {bs : BusSemantics p} (hp : Nat.Prime p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseBoolCheck? facts bi = some c)
    (denv : VarId → ZMod p) :
    bs.violatesConstraint (denseBIEval bi denv) = false ↔ c.eval denv = 0 := by
  obtain ⟨valSlot, x, hrc, hmc, hxp, rfl⟩ := denseBoolCheck?_spec facts bi c h
  obtain ⟨_, hm⟩ := facts.rangeCheckAt_sound bi.busId (bi.payload.map DenseExpr.constValue?)
    valSlot 2 hrc
  have hmult : (denseBIEval bi denv).multiplicity = 1 := by
    show bi.multiplicity.eval denv = 1; rw [hmc]; rfl
  obtain ⟨_, hiff⟩ := hm (denseBIEval bi denv) rfl hmult (denseMatches_evalPattern bi.payload denv)
  have hget : (denseBIEval bi denv).payload[valSlot]? = some (denv x) := by
    show (bi.payload.map (fun e => e.eval denv))[valSlot]? = some (denv x)
    rw [List.getElem?_map, hxp]; rfl
  rw [hiff (denv x) hget, denseBoolC_eval]
  simpa only [DenseExpr.eval] using DegenRange.val_lt_two_iff hp (denv x)

/-- The bare-variable width-1 booleanity rule (prime fields only). -/
def denseRangeBoolRule (hp : Nat.Prime p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    DenseCheckRule p bs where
  recognize := denseBoolCheck? facts
  multOne bi c h := by
    obtain ⟨_, _, _, hmc, _, _⟩ := denseBoolCheck?_spec facts bi c h
    exact hmc
  stateless bi c h := by
    obtain ⟨valSlot, x, hrc, _, _, _⟩ := denseBoolCheck?_spec facts bi c h
    exact (facts.rangeCheckAt_sound bi.busId (bi.payload.map DenseExpr.constValue?) valSlot 2 hrc).1
  vars bi c h := by
    obtain ⟨valSlot, x, hrc, hmc, hxp, rfl⟩ := denseBoolCheck?_spec facts bi c h
    intro z hz
    have hzx : z ∈ (DenseExpr.var x : DenseExpr p).vars := denseBoolC_vars (DenseExpr.var x) z hz
    simp only [denseBIVars, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨DenseExpr.var x, List.mem_of_getElem? hxp, hzx⟩
  violates_iff bi c h denv := denseBoolCheck?_violates_iff hp facts bi c h denv

/-! ## The pass -/

/-- Rule list: the width-0 / width-1 recognizer always (its booleanity arm self-gates on
    `pw.isPrime`); the bare-variable booleanity rule only on a proven-prime field. -/
def denseDegenRangeRules (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (DenseCheckRule p bs) :=
  denseZeroWidthRule pw bs facts ::
    (if h : pw.isPrime = true then [denseRangeBoolRule (pw.correct h) bs facts] else [])

/-- Degenerate range checks become algebraic constraints: a width-0 check pins its value slot to
    `0` (`[v, 0]` gives `v = 0`) and a width-1 check becomes booleanity (`[x, 1]` gives
    `x·(x−1) = 0`); the recognized checks are dropped. -/
def denseDegenRangePass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofCheckRules (denseDegenRangeRules pw)

end ApcOptimizer.Dense
