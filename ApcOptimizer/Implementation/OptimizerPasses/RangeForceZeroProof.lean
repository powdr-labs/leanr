import ApcOptimizer.Implementation.OptimizerPasses.RangeForceZero
import ApcOptimizer.Implementation.OptimizerPasses.BusUnifyProof
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Dense width-0 range check → equality: proof and wiring

`DensePassCorrect` proof for `RangeForceZero.lean` via `DensePassCorrect.denseAddConstraints`,
lifted through `DenseVerifiedPassW.of`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Structure of a recognised width-0 check. -/
theorem denseForceZeroAt_spec {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p) (h : denseForceZeroAt facts bi = some e) :
    ∃ valSlot, facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?)
        = some (valSlot, 1) ∧ bi.multiplicity = DenseExpr.const 1
        ∧ bi.payload[valSlot]? = some e := by
  unfold denseForceZeroAt at h
  split at h
  · rename_i vs bd hrc
    split_ifs at h with hcond
    obtain ⟨hmc, rfl⟩ := hcond
    cases hp : bi.payload[vs]? with
    | none => simp only [hp] at h; simp at h
    | some e' =>
      simp only [hp] at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨vs, hrc, hmc, hp⟩
  · exact absurd h (by simp)

/-- Every accepted-and-active width-0 check forces its slot expression to `0`. -/
theorem denseForceZeroAt_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (h1ne : (1 : ZMod p) ≠ 0) (h : denseForceZeroAt facts bi = some e) (denv : VarId → ZMod p)
    (hsat : d.satisfies bs denv) (hbi : bi ∈ d.busInteractions) : e.eval denv = 0 := by
  obtain ⟨valSlot, hrc, hmc, hget⟩ := denseForceZeroAt_spec facts bi e h
  obtain ⟨_, hm⟩ := facts.rangeCheckAt_sound bi.busId (bi.payload.map DenseExpr.constValue?)
    valSlot 1 hrc
  have hmult : (denseBIEval bi denv).multiplicity = 1 := by
    show bi.multiplicity.eval denv = 1; rw [hmc]; rfl
  obtain ⟨_, hiff⟩ := hm (denseBIEval bi denv) rfl hmult (denseMatches_evalPattern bi.payload denv)
  have hviol : bs.violatesConstraint (denseBIEval bi denv) = false := by
    refine hsat.2 bi hbi ?_; rw [hmult]; exact h1ne
  have hgetEv : (denseBIEval bi denv).payload[valSlot]? = some (e.eval denv) := by
    show (bi.payload.map (fun t => t.eval denv))[valSlot]? = some (e.eval denv)
    rw [List.getElem?_map, hget]; rfl
  have hlt : (e.eval denv).val < 1 := (hiff (e.eval denv) hgetEv).mp hviol
  exact (ZMod.val_eq_zero _).mp (by omega)

/-- Every appended seed evaluates to zero on satisfying dense assignments. -/
theorem denseRangeForceZeroNew_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (h1ne : (1 : ZMod p) ≠ 0) (denv : VarId → ZMod p)
    (hsat : d.satisfies bs denv) :
    ∀ c ∈ (denseForceZeroSeeds facts d).filter (fun e => e.vars.all (fun z => d.occ.contains z)),
      c.eval denv = 0 := by
  intro c hc
  obtain ⟨bi, hbi, hf⟩ := List.mem_filterMap.1 (List.mem_of_mem_filter hc)
  exact denseForceZeroAt_sound facts d bi c h1ne hf denv hsat hbi

/-- Every variable of an appended seed occurs in `d`. -/
theorem denseRangeForceZeroNew_vars {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ (denseForceZeroSeeds facts d).filter (fun e => e.vars.all (fun z => d.occ.contains z)),
      ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  have hp := (List.mem_filter.1 hc).2
  simp only [List.all_eq_true] at hp
  exact List.contains_iff_mem.mp (hp z hz)

theorem denseRangeForceZeroF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseRangeForceZeroF bs facts d).CoveredBy reg := by
  unfold denseRangeForceZeroF
  by_cases h : (1 : ZMod p) ≠ 0
  · rw [if_pos h]
    refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h1 | h1
    · exact hcov.1 e h1
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i (denseRangeForceZeroNew_vars facts d e h1 i hi)
  · rw [if_neg h]; exact hcov

theorem denseRangeForceZeroF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseRangeForceZeroF bs facts d) [] bs := by
  unfold denseRangeForceZeroF
  by_cases h : (1 : ZMod p) ≠ 0
  · rw [if_pos h]
    exact DensePassCorrect.denseAddConstraints d bs _
      (denseRangeForceZeroNew_vars facts d)
      (fun denv _ hsat => denseRangeForceZeroNew_sound facts d h denv hsat)
  · rw [if_neg h]; exact DensePassCorrect.refl reg.isInput d bs

/-- The dense `rangeForceZero` pass. -/
def denseRangeForceZeroPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseRangeForceZeroF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseRangeForceZeroF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseRangeForceZeroF_correct reg bs facts d)

end ApcOptimizer.Dense
