import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagFoldDrops
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch

set_option autoImplicit false

/-! # Soundness for the dense subsumed bound-check drops

`DensePassCorrect` — over `VarId → ZMod p` — for the generic subsumed-check dropper
(`SubsumedCheck.lean`): every dropped check has its variable bounded `< B` by the non-circular
base, hence is accepted under every assignment satisfying the filtered system.
`denseSubsumedDropF_correct` consumes the recognizer's one semantic obligation
(`SubsumedRecognizerSound`); the `rangeCheckAt` and `varRangeBus` recognizers discharge it, giving
the two wired passes. Built via `denseFilterBusEntailed` (`Proofs/FlagFoldDrops.lean`) and
`denseFindVarBound_sound` (`Proofs/RootPairUnify.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A recognizer is *sound* when every check it recognises is stateless and accepted whenever the
    checked variable's value is under the returned bound. -/
def SubsumedRecognizerSound (bs : BusSemantics p)
    (f : BusInteraction (DenseExpr p) → Option (VarId × Nat)) : Prop :=
  ∀ bi x B, f bi = some (x, B) →
    bs.isStateful bi.busId = false ∧
    ∀ denv : VarId → ZMod p, (denv x).val < B →
      bs.violatesConstraint (denseBIEval bi denv) = false

/-- Every dropped interaction is a recognised check whose variable is already bounded `< B` by the
    retained base, so it is accepted under every assignment satisfying the filtered system. -/
theorem denseSubsumedDropF_correct (bs : BusSemantics p) (facts : BusFacts p bs)
    (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    {f : BusInteraction (DenseExpr p) → Option (VarId × Nat)}
    (hf : SubsumedRecognizerSound bs f) :
    DensePassCorrect isInput d (denseSubsumedDropF bs facts f d) [] bs := by
  unfold denseSubsumedDropF
  refine DensePassCorrect.denseFilterBusEntailed d bs isInput
    (denseSubsumedDropKeep bs facts f (denseSubsumedDropBase f d)) ?_ ?_
  · intro bi _ hkf
    cases hr : f bi with
    | none => exact absurd hkf (by simp [denseSubsumedDropKeep, hr])
    | some xB => exact (hf bi xB.1 xB.2 hr).1
  · intro bi _ hkf denv hsat hm
    cases hr : f bi with
    | none => exact absurd hkf (by simp [denseSubsumedDropKeep, hr])
    | some xB =>
      obtain ⟨x, B⟩ := xB
      cases hb : denseFindVarBound bs facts (denseSubsumedDropBase f d) x with
      | none => exact absurd hkf (by simp [denseSubsumedDropKeep, hr, hb])
      | some b' =>
        have hble : b' ≤ B := by
          simp only [denseSubsumedDropKeep, hr, hb, Bool.not_eq_false',
            decide_eq_true_eq] at hkf
          exact hkf
        have hbase : (denv x).val < b' := by
          refine denseFindVarBound_sound bs facts (denseSubsumedDropBase f d) x b' hb
            denv (fun bi' hbi' hmult => ?_)
          have hbimem' : bi' ∈ d.busInteractions := (List.mem_filter.1 hbi').1
          have hnone : f bi' = none := by
            have := (List.mem_filter.1 hbi').2
            simpa using this
          have hkeep : denseSubsumedDropKeep bs facts f
              (denseSubsumedDropBase f d) bi' = true := by
            simp only [denseSubsumedDropKeep, hnone]
          exact hsat.2 bi' (List.mem_filter.2 ⟨hbimem', hkeep⟩) hmult
        exact (hf bi x B hr).2 denv (lt_of_lt_of_le hbase hble)

/-! ## The two recognizers' soundness -/

/-- Recognition by `denseSubsumedCheckOf` unfolds to its three facts: a matching `rangeCheckAt`,
    unit multiplicity, and a bare variable in the value slot. -/
theorem denseSubsumedCheckOf_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (bound : Nat)
    (h : denseSubsumedCheckOf bs facts bi = some (x, bound)) :
    ∃ valSlot,
      facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) = some (valSlot, bound) ∧
        bi.multiplicity = DenseExpr.const 1 ∧ bi.payload[valSlot]? = some (DenseExpr.var x) := by
  unfold denseSubsumedCheckOf at h
  split at h
  · rename_i vs bd hrc
    split_ifs at h with hmc
    split at h
    · rename_i x' hxp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨vs, hrc, hmc, hxp⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem denseSubsumedCheckOf_sound (bs : BusSemantics p) (facts : BusFacts p bs) :
    SubsumedRecognizerSound bs (denseSubsumedCheckOf bs facts) := by
  intro bi x bound h
  obtain ⟨valSlot, hrc, hmc, hxp⟩ := denseSubsumedCheckOf_spec bs facts bi x bound h
  obtain ⟨hstateless, hm⟩ :=
    facts.rangeCheckAt_sound bi.busId (bi.payload.map DenseExpr.constValue?) valSlot bound hrc
  refine ⟨hstateless, fun denv hlt => ?_⟩
  have hmult : (denseBIEval bi denv).multiplicity = 1 := by
    show bi.multiplicity.eval denv = 1
    rw [hmc]; rfl
  obtain ⟨_, hiff⟩ := hm (denseBIEval bi denv) rfl hmult (denseMatches_evalPattern bi.payload denv)
  have hget : (denseBIEval bi denv).payload[valSlot]? = some (denv x) := by
    show (bi.payload.map (fun e => e.eval denv))[valSlot]? = some (denv x)
    rw [List.getElem?_map, hxp]; rfl
  exact (hiff (denv x) hget).mpr hlt

/-- Recognition by `denseSubsumedRangeCheck?` unfolds to its structure: a `varRangeBus`, unit
    multiplicity, a satisfiable constant width, and payload `[x, c]`. -/
theorem denseSubsumedRangeCheck?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (B : Nat)
    (h : denseSubsumedRangeCheck? bs facts bi = some (x, B)) :
    facts.varRangeBus bi.busId = true ∧ bi.multiplicity = DenseExpr.const 1 ∧
      ∃ c cv, bi.payload = [DenseExpr.var x, c] ∧ c.constValue? = some cv ∧ cv.val ≤ 17 ∧
        B = 2 ^ cv.val := by
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
        exact ⟨hvr, hm, c, cv', hpay, hcv, hle, rfl⟩

theorem denseSubsumedRangeCheck?_sound (bs : BusSemantics p) (facts : BusFacts p bs) :
    SubsumedRecognizerSound bs (denseSubsumedRangeCheck? bs facts) := by
  intro bi x B h
  obtain ⟨hvr, hm, c, cv, hpay, hcv, hle, rfl⟩ := denseSubsumedRangeCheck?_spec bs facts bi x B h
  refine ⟨(facts.varRangeBus_sound bi.busId hvr).1, fun denv hlt => ?_⟩
  have hev : denseBIEval bi denv
      = { busId := bi.busId, multiplicity := 1, payload := [denv x, cv] } := by
    unfold denseBIEval
    rw [hm, hpay]
    simp only [List.map_cons, List.map_nil, DenseExpr.eval,
      DenseExpr.constValue?_sound c cv hcv denv]
  rw [hev]
  exact ((facts.varRangeBus_sound bi.busId hvr).2 (denv x) cv 1).2 ⟨hle, hlt⟩

/-! ## The two wired passes -/

/-- Wire `denseSubsumedDropF f` into a pass, given the recognizer's soundness. -/
def denseSubsumedDropPassOf
    (f : (bs : BusSemantics p) → BusFacts p bs → BusInteraction (DenseExpr p) →
      Option (VarId × Nat))
    (hf : ∀ (bs : BusSemantics p) (facts : BusFacts p bs),
      SubsumedRecognizerSound bs (f bs facts)) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d => denseSubsumedDropF bs facts (f bs facts) d)
    (fun _ _ _ => [])
    (fun _ bs facts d hcov => by
      unfold denseSubsumedDropF
      exact DenseConstraintSystem.filterBus_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseSubsumedDropF_correct bs facts reg.isInput d (hf bs facts))

/-- Drops a pure single-value range check (`facts.rangeCheckAt`) on `x` when a retained check
    already bounds `x` at least as tightly. -/
def denseSubsumedCheckDropPass : DenseVerifiedPassW p :=
  denseSubsumedDropPassOf denseSubsumedCheckOf denseSubsumedCheckOf_sound

/-- Drops a variable range check `[x, w]` (`facts.varRangeBus`) when a retained check already
    bounds `x` below `2^w`. -/
def denseSubsumedRangeDropPass : DenseVerifiedPassW p :=
  denseSubsumedDropPassOf denseSubsumedRangeCheck? denseSubsumedRangeCheck?_sound

end ApcOptimizer.Dense
