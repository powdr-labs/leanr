import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.FlagFoldDropsProof
import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnifyProof
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Soundness for the dense subsumed pure-range-check drop

`DensePassCorrect` — over `VarId → ZMod p` — for the subsumed pure-range-check dropper
(`SubsumedCheck.lean`). Every dropped check has its variable bounded `< bound` by the non-circular
base, hence accepted under every assignment satisfying the filtered system. Built via
`denseFilterBusEntailed` (`FlagFoldDropsProof.lean`) and `denseFindVarBound_sound`
(`RootPairUnifyProof.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognition unfolds to its three facts: a matching `rangeCheckAt`, unit multiplicity, and a bare
    variable in the value slot. -/
theorem denseSubsumedCheckOf_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (valSlot bound : Nat)
    (h : denseSubsumedCheckOf bs facts bi = some (x, valSlot, bound)) :
    facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) = some (valSlot, bound) ∧
      bi.multiplicity = DenseExpr.const 1 ∧ bi.payload[valSlot]? = some (DenseExpr.var x) := by
  unfold denseSubsumedCheckOf at h
  split at h
  · rename_i vs bd hrc
    split_ifs at h with hmc
    split at h
    · rename_i x' hxp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hrc, hmc, hxp⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A recognised check lives on a stateless bus. -/
theorem denseSubsumedCheckOf_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (valSlot bound : Nat)
    (h : denseSubsumedCheckOf bs facts bi = some (x, valSlot, bound)) :
    bs.isStateful bi.busId = false :=
  (facts.rangeCheckAt_sound bi.busId (bi.payload.map DenseExpr.constValue?) valSlot bound
    (denseSubsumedCheckOf_spec bs facts bi x valSlot bound h).1).1

/-- If the checked variable is in range (`< bound`), the recognised message is accepted. -/
theorem denseSubsumedCheckOf_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x : VarId) (valSlot bound : Nat)
    (h : denseSubsumedCheckOf bs facts bi = some (x, valSlot, bound)) (denv : VarId → ZMod p)
    (hlt : (denv x).val < bound) : bs.violatesConstraint (denseBIEval bi denv) = false := by
  obtain ⟨hrc, hmc, hxp⟩ := denseSubsumedCheckOf_spec bs facts bi x valSlot bound h
  obtain ⟨_, hm⟩ := facts.rangeCheckAt_sound bi.busId (bi.payload.map DenseExpr.constValue?)
    valSlot bound hrc
  have hmult : (denseBIEval bi denv).multiplicity = 1 := by
    show bi.multiplicity.eval denv = 1
    rw [hmc]; rfl
  obtain ⟨_, hiff⟩ := hm (denseBIEval bi denv) rfl hmult (denseMatches_evalPattern bi.payload denv)
  have hget : (denseBIEval bi denv).payload[valSlot]? = some (denv x) := by
    show (bi.payload.map (fun e => e.eval denv))[valSlot]? = some (denv x)
    rw [List.getElem?_map, hxp]; rfl
  exact (hiff (denv x) hget).mpr hlt

/-- Every dropped interaction is a recognised pure check whose variable is already bounded
    `< bound` by the retained base, so it is accepted under every assignment satisfying the
    filtered system. -/
theorem denseSubsumedCheckDropF_correct (bs : BusSemantics p) (facts : BusFacts p bs)
    (isInput : VarId → Bool) (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d (denseSubsumedCheckDropF bs facts d) [] bs := by
  unfold denseSubsumedCheckDropF
  refine DensePassCorrect.denseFilterBusEntailed d bs isInput
    (denseSubsumedCheckDropKeep bs facts (denseSubsumedCheckDropBase bs facts d)) ?_ ?_
  · intro bi _ hkf
    cases hr : denseSubsumedCheckOf bs facts bi with
    | none => exact absurd hkf (by simp [denseSubsumedCheckDropKeep, hr])
    | some xvb =>
      obtain ⟨x, valSlot, bound⟩ := xvb
      exact denseSubsumedCheckOf_stateless bs facts bi x valSlot bound hr
  · intro bi _ hkf denv hsat hm
    cases hr : denseSubsumedCheckOf bs facts bi with
    | none => exact absurd hkf (by simp [denseSubsumedCheckDropKeep, hr])
    | some xvb =>
      obtain ⟨x, valSlot, bound⟩ := xvb
      cases hb : denseFindVarBound bs facts (denseSubsumedCheckDropBase bs facts d) x with
      | none => exact absurd hkf (by simp [denseSubsumedCheckDropKeep, hr, hb])
      | some b' =>
        have hble : b' ≤ bound := by
          simp only [denseSubsumedCheckDropKeep, hr, hb, Bool.not_eq_false',
            decide_eq_true_eq] at hkf
          exact hkf
        have hbase : (denv x).val < b' := by
          refine denseFindVarBound_sound bs facts (denseSubsumedCheckDropBase bs facts d) x b' hb
            denv (fun bi' hbi' hmult => ?_)
          have hbimem' : bi' ∈ d.busInteractions := (List.mem_filter.1 hbi').1
          have hnone : denseSubsumedCheckOf bs facts bi' = none := by
            have := (List.mem_filter.1 hbi').2
            simpa using this
          have hkeep : denseSubsumedCheckDropKeep bs facts
              (denseSubsumedCheckDropBase bs facts d) bi' = true := by
            simp only [denseSubsumedCheckDropKeep, hnone]
          exact hsat.2 bi' (List.mem_filter.2 ⟨hbimem', hkeep⟩) hmult
        exact denseSubsumedCheckOf_accepted bs facts bi x valSlot bound hr denv
          (lt_of_lt_of_le hbase hble)

/-- The dense subsumed pure-range-check drop pass; transform `denseSubsumedCheckDropF`
    (`SubsumedCheck.lean`). -/
def denseSubsumedCheckDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d => denseSubsumedCheckDropF bs facts d)
    (fun _ _ _ => [])
    (fun _ bs facts d hcov => by
      unfold denseSubsumedCheckDropF
      exact DenseConstraintSystem.filterBus_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseSubsumedCheckDropF_correct bs facts reg.isInput d)

end ApcOptimizer.Dense
