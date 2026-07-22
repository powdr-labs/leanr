import ApcOptimizer.Implementation.OptimizerPasses.RangeBool
import ApcOptimizer.Implementation.OptimizerPasses.BusUnifyProof
import ApcOptimizer.Implementation.OptimizerPasses.FlagFoldDropsProof
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Dense width-1 range check → booleanity: correctness proof and wiring

`DensePassCorrect` proof for the dense `rangeBool` transform (`RangeBool.lean`), lifted to the
audited spec via `DenseVerifiedPassW.of`. The pass is exactly **two** steps composed by
`DensePassCorrect.trans`:

1. **add** every recognised booleanity (`x·(x−1)`) as an algebraic constraint — entailed by the
   width-1 check's acceptance on a prime field — via `DensePassCorrect.denseAddConstraints`
   (`BusUnifyProof.lean`);
2. **drop** the now-entailed checks via `DensePassCorrect.denseFilterBusEntailed`
   (`FlagFoldDropsProof.lean`); the added booleanity survives the bus filter (it touches only
   interactions), so the dropped check's acceptance is re-derived from the still-present
   constraint.

The recogniser soundness applies the representation-independent `facts.rangeCheckAt` field
**value-level** over `denseBIEval bi denv` (no decode), with `denseMatches_evalPattern`
(`DomainBatchProof.lean`) and the pure-`ZMod` `ZeroWidthRange.val_lt_two_iff`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense booleanity eval / vars -/

theorem denseBoolC_eval (v : DenseExpr p) (denv : VarId → ZMod p) :
    (denseBoolC v).eval denv = v.eval denv * (v.eval denv - 1) := by
  simp only [denseBoolC, DenseExpr.eval]; ring

theorem denseBoolC_vars (v : DenseExpr p) : ∀ x ∈ (denseBoolC v).vars, x ∈ v.vars := by
  intro x hx
  simp only [denseBoolC, DenseExpr.vars, List.mem_append, List.not_mem_nil, or_false] at hx
  tauto

/-! ## The recogniser: structure, statelessness, acceptance ⟺ booleanity, variables -/

/-- Structure of a recognised width-1 check. -/
theorem denseBoolCheck?_spec {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseBoolCheck? facts bi = some c) :
    ∃ valSlot x, facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?)
        = some (valSlot, 2) ∧ bi.multiplicity = DenseExpr.const 1 ∧
        bi.payload[valSlot]? = some (DenseExpr.var x) ∧ c = denseBoolC (DenseExpr.var x) := by
  unfold denseBoolCheck? at h
  split at h
  · rename_i vs bd hrc
    split_ifs at h with hcond
    obtain ⟨hmc, rfl⟩ := hcond
    cases hp : bi.payload[vs]? with
    | none => simp only [hp] at h; simp at h
    | some ex =>
      cases ex with
      | var x =>
        simp only [hp] at h; simp only [Option.some.injEq] at h
        exact ⟨vs, x, hrc, hmc, hp, h.symm⟩
      | const _ => simp only [hp] at h; simp at h
      | add _ _ => simp only [hp] at h; simp at h
      | mul _ _ => simp only [hp] at h; simp at h
  · exact absurd h (by simp)

/-- A recognised width-1 check lives on a stateless bus. -/
theorem denseBoolCheck?_stateless {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseBoolCheck? facts bi = some c) :
    bs.isStateful bi.busId = false := by
  obtain ⟨valSlot, x, hrc, _, _, _⟩ := denseBoolCheck?_spec facts bi c h
  exact (facts.rangeCheckAt_sound bi.busId (bi.payload.map DenseExpr.constValue?) valSlot 2 hrc).1

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
  simpa only [DenseExpr.eval] using ZeroWidthRange.val_lt_two_iff hp (denv x)

/-- The variables of a recognised booleanity occur in `d`. -/
theorem denseBoolCheck?_vars {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p)
    (h : denseBoolCheck? facts bi = some c) (hbi : bi ∈ d.busInteractions) :
    ∀ z ∈ c.vars, z ∈ d.occ := by
  obtain ⟨valSlot, x, hrc, hmc, hxp, rfl⟩ := denseBoolCheck?_spec facts bi c h
  intro z hz
  have hzx : z ∈ (DenseExpr.var x).vars := denseBoolC_vars (DenseExpr.var x) z hz
  have hxpay : (DenseExpr.var x) ∈ bi.payload := List.mem_of_getElem? hxp
  refine DenseConstraintSystem.mem_occ_of_bi hbi ?_
  simp only [denseBIVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨DenseExpr.var x, hxpay, hzx⟩

/-- The forward entailment consumed by the add step: a recognised booleanity holds on every
    satisfying dense assignment (acceptance ⟹ booleanity). -/
theorem denseBoolCheck?_eval {bs : BusSemantics p} (hp : Nat.Prime p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p)
    (h1ne : (1 : ZMod p) ≠ 0) (h : denseBoolCheck? facts bi = some c) (denv : VarId → ZMod p)
    (hsat : d.satisfies bs denv) (hbi : bi ∈ d.busInteractions) : c.eval denv = 0 := by
  have hmult : (denseBIEval bi denv).multiplicity = 1 := by
    obtain ⟨_, _, _, hmc, _, _⟩ := denseBoolCheck?_spec facts bi c h
    show bi.multiplicity.eval denv = 1; rw [hmc]; rfl
  have hviol : bs.violatesConstraint (denseBIEval bi denv) = false :=
    hsat.2 bi hbi (by rw [hmult]; exact h1ne)
  exact (denseBoolCheck?_violates_iff hp facts bi c h denv).mp hviol

/-! ## Coverage and the two-step correctness -/

/-- Every variable of an added booleanity occurs in `d`. -/
theorem denseRangeBoolNew_vars {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ d.busInteractions.filterMap (denseBoolCheck? facts), ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  obtain ⟨bi, hbi, hf⟩ := List.mem_filterMap.1 hc
  exact denseBoolCheck?_vars facts d bi c hf hbi z hz

theorem denseRangeBoolAddF_covered (reg : VarRegistry) {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseRangeBoolAddF facts d).CoveredBy reg := by
  unfold denseRangeBoolAddF
  refine ⟨fun e he => ?_, hcov.2⟩
  rcases List.mem_append.1 he with h' | h'
  · exact hcov.1 e h'
  · intro i hi
    exact DenseConstraintSystem.occ_valid hcov i (denseRangeBoolNew_vars facts d e h' i hi)

theorem denseRangeBoolF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseRangeBoolF pw bs facts d).CoveredBy reg := by
  unfold denseRangeBoolF
  by_cases h1 : (1 : ZMod p) ≠ 0
  · rw [if_pos h1]
    by_cases hpr : pw.isPrime = true
    · rw [if_pos hpr]
      unfold denseRangeBoolDropF
      exact DenseConstraintSystem.filterBus_covered (denseRangeBoolAddF_covered reg facts d hcov)
    · rw [if_neg hpr]; exact hcov
  · rw [if_neg h1]; exact hcov

/-- Step 1: adding the recognised booleanities is `DensePassCorrect`. -/
theorem denseRangeBoolAddF_correct (hp : Nat.Prime p) (isInput : VarId → Bool) {bs : BusSemantics p}
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (h1ne : (1 : ZMod p) ≠ 0) :
    DensePassCorrect isInput d (denseRangeBoolAddF facts d) [] bs := by
  unfold denseRangeBoolAddF
  exact DensePassCorrect.denseAddConstraints d bs (d.busInteractions.filterMap (denseBoolCheck? facts))
    (denseRangeBoolNew_vars facts d)
    (fun denv _ hsat c hc => by
      obtain ⟨bi, hbi, hf⟩ := List.mem_filterMap.1 hc
      exact denseBoolCheck?_eval hp facts d bi c h1ne hf denv hsat hbi)

/-- Step 2: dropping the now-entailed checks is `DensePassCorrect`. -/
theorem denseRangeBoolDropF_correct (hp : Nat.Prime p) (isInput : VarId → Bool) {bs : BusSemantics p}
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect isInput (denseRangeBoolAddF facts d)
      (denseRangeBoolDropF facts (denseRangeBoolAddF facts d)) [] bs := by
  set mid := denseRangeBoolAddF facts d with hmid
  unfold denseRangeBoolDropF
  refine DensePassCorrect.denseFilterBusEntailed mid bs isInput
    (fun bi => (denseBoolCheck? facts bi).isNone) ?_ ?_
  · intro bi hbimem hkf
    obtain ⟨e, he⟩ : ∃ e, denseBoolCheck? facts bi = some e := by
      have hkf' : (denseBoolCheck? facts bi).isNone = false := hkf
      cases hopt : denseBoolCheck? facts bi with
      | none => rw [hopt] at hkf'; simp at hkf'
      | some e => exact ⟨e, rfl⟩
    exact denseBoolCheck?_stateless facts bi e he
  · intro bi hbimem hkf denv hsatf _hm
    obtain ⟨e, he⟩ : ∃ e, denseBoolCheck? facts bi = some e := by
      have hkf' : (denseBoolCheck? facts bi).isNone = false := hkf
      cases hopt : denseBoolCheck? facts bi with
      | none => rw [hopt] at hkf'; simp at hkf'
      | some e => exact ⟨e, rfl⟩
    have hbi : bi ∈ d.busInteractions := hbimem
    have hemem : e ∈ (mid.filterBus (fun bi => (denseBoolCheck? facts bi).isNone)).algebraicConstraints := by
      show e ∈ d.algebraicConstraints ++ d.busInteractions.filterMap (denseBoolCheck? facts)
      exact List.mem_append_right _ (List.mem_filterMap.2 ⟨bi, hbi, he⟩)
    rw [denseBoolCheck?_violates_iff hp facts bi e he denv]
    exact hsatf.1 e hemem

theorem denseRangeBoolF_correct (pw : PrimeWitness p) (reg : VarRegistry) {bs : BusSemantics p}
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseRangeBoolF pw bs facts d) [] bs := by
  unfold denseRangeBoolF
  by_cases h1 : (1 : ZMod p) ≠ 0
  · rw [if_pos h1]
    by_cases hpr : pw.isPrime = true
    · rw [if_pos hpr]
      have hp : Nat.Prime p := pw.correct hpr
      exact DensePassCorrect.trans (denseRangeBoolAddF_correct hp reg.isInput facts d h1)
        (denseRangeBoolDropF_correct hp reg.isInput facts d)
    · rw [if_neg hpr]; exact DensePassCorrect.refl reg.isInput d bs
  · rw [if_neg h1]; exact DensePassCorrect.refl reg.isInput d bs

/-- **The dense `rangeBool` pass.** Prime-gated; threads the original `facts` unchanged,
    connected to the audited spec via `DensePassCorrect.lift` (through `of`). -/
def denseRangeBoolPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (denseRangeBoolF pw) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseRangeBoolF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseRangeBoolF_correct pw reg facts d)

end ApcOptimizer.Dense
