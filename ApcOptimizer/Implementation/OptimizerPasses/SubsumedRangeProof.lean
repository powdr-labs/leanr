import ApcOptimizer.Implementation.OptimizerPasses.SubsumedRange
import ApcOptimizer.Implementation.OptimizerPasses.FlagFoldDropsProof
import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnifyProof
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Soundness for the dense subsumed range-check drop

`DensePassCorrect` — over `VarId → ZMod p` — for the subsumed variable-range-check dropper
(`SubsumedRange.lean`). Every dropped range check has its variable bounded `< 2^w.val` by the
non-circular base, hence accepted under every assignment satisfying the filtered system. Built via
`denseFilterBusEntailed` (`FlagFoldDropsProof.lean`) and `denseFindVarBound_sound`
(`RootPairUnifyProof.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Structure of a recognised check: it lives on a `varRangeBus`, has multiplicity `1`, a satisfiable
    width, and payload `[x, c]` with `c` the constant `cv`. -/
theorem denseSubsumedRangeCheck?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (cv : ZMod p)
    (h : denseSubsumedRangeCheck? bs facts bi = some (x, cv)) :
    facts.varRangeBus bi.busId = true ∧ bi.multiplicity = DenseExpr.const 1 ∧ cv.val ≤ 17 ∧
      ∃ c, bi.payload = [DenseExpr.var x, c] ∧ c.constValue? = some cv := by
  unfold denseSubsumedRangeCheck? at h
  split at h
  case h_2 => exact absurd h (by simp)
  case h_1 v c hpay =>
    split at h
    case h_2 => exact absurd h (by simp)
    case h_1 x' hv =>
      split at h
      case h_2 => exact absurd h (by simp)
      case h_1 cv' hcv =>
        split_ifs at h with hcond
        obtain ⟨hvr, hm, hle⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hvr, hm, hle, c, hpay, hcv⟩

/-- A recognised range check lives on a stateless bus. -/
theorem denseSubsumedRangeCheck?_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (cv : ZMod p)
    (h : denseSubsumedRangeCheck? bs facts bi = some (x, cv)) :
    bs.isStateful bi.busId = false :=
  (facts.varRangeBus_sound bi.busId (denseSubsumedRangeCheck?_spec bs facts bi x cv h).1).1

/-- If the checked variable is in range (`< 2^width`), the recognised message is accepted. -/
theorem denseSubsumedRangeCheck?_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (cv : ZMod p)
    (h : denseSubsumedRangeCheck? bs facts bi = some (x, cv)) (denv : VarId → ZMod p)
    (hlt : (denv x).val < 2 ^ cv.val) : bs.violatesConstraint (denseBIEval bi denv) = false := by
  obtain ⟨hvr, hm, hle, c, hpay, hcv⟩ := denseSubsumedRangeCheck?_spec bs facts bi x cv h
  have hev : denseBIEval bi denv
      = { busId := bi.busId, multiplicity := 1, payload := [denv x, cv] } := by
    unfold denseBIEval
    rw [hm, hpay]
    simp only [List.map_cons, List.map_nil, DenseExpr.eval,
      DenseExpr.constValue?_sound c cv hcv denv]
  rw [hev]
  exact ((facts.varRangeBus_sound bi.busId hvr).2 (denv x) cv 1).2 ⟨hle, hlt⟩

/-- Every dropped interaction is a recognised range check whose variable is already bounded
    `< 2^w.val` by the retained base, so it is accepted under every assignment satisfying the
    filtered system. -/
theorem denseSubsumedRangeDropF_correct (bs : BusSemantics p) (facts : BusFacts p bs)
    (isInput : VarId → Bool) (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d (denseSubsumedRangeDropF bs facts d) [] bs := by
  unfold denseSubsumedRangeDropF
  refine DensePassCorrect.denseFilterBusEntailed d bs isInput
    (denseSubsumedRangeDropKeep bs facts (denseSubsumedRangeDropBase bs facts d)) ?_ ?_
  · intro bi _ hkf
    cases hr : denseSubsumedRangeCheck? bs facts bi with
    | none => exact absurd hkf (by simp [denseSubsumedRangeDropKeep, hr])
    | some xcv =>
      obtain ⟨x, cv⟩ := xcv
      exact denseSubsumedRangeCheck?_stateless bs facts bi x cv hr
  · intro bi _ hkf denv hsat hm
    cases hr : denseSubsumedRangeCheck? bs facts bi with
    | none => exact absurd hkf (by simp [denseSubsumedRangeDropKeep, hr])
    | some xcv =>
      obtain ⟨x, cv⟩ := xcv
      cases hb : denseFindVarBound bs facts (denseSubsumedRangeDropBase bs facts d) x with
      | none => exact absurd hkf (by simp [denseSubsumedRangeDropKeep, hr, hb])
      | some b' =>
        have hble : b' ≤ 2 ^ cv.val := by
          simp only [denseSubsumedRangeDropKeep, hr, hb, Bool.not_eq_false',
            decide_eq_true_eq] at hkf
          exact hkf
        have hbase : (denv x).val < b' := by
          refine denseFindVarBound_sound bs facts (denseSubsumedRangeDropBase bs facts d) x b' hb
            denv (fun bi' hbi' hmult => ?_)
          have hbimem' : bi' ∈ d.busInteractions := (List.mem_filter.1 hbi').1
          have hnone : denseSubsumedRangeCheck? bs facts bi' = none := by
            have := (List.mem_filter.1 hbi').2
            simpa using this
          have hkeep : denseSubsumedRangeDropKeep bs facts
              (denseSubsumedRangeDropBase bs facts d) bi' = true := by
            simp only [denseSubsumedRangeDropKeep, hnone]
          exact hsat.2 bi' (List.mem_filter.2 ⟨hbimem', hkeep⟩) hmult
        exact denseSubsumedRangeCheck?_accepted bs facts bi x cv hr denv
          (lt_of_lt_of_le hbase hble)

/-- The dense subsumed range-check drop pass; transform `denseSubsumedRangeDropF`
    (`SubsumedRange.lean`). -/
def denseSubsumedRangeDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d => denseSubsumedRangeDropF bs facts d)
    (fun _ _ _ => [])
    (fun _ bs facts d hcov => by
      unfold denseSubsumedRangeDropF
      exact DenseConstraintSystem.filterBus_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseSubsumedRangeDropF_correct bs facts reg.isInput d)

end ApcOptimizer.Dense
