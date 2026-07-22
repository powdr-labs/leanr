import ApcOptimizer.Implementation.OptimizerPasses.ZeroRegister
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch

set_option autoImplicit false

/-! # Dense fixed-zero-register pinning: correctness proof and wiring

`DensePassCorrect` proof for `ZeroRegister.lean` via `DensePassCorrect.denseAddConstraints`
(appending `data_i = 0` for every active fixed-zero memory message), lifted through
`DenseVerifiedPassW.of`. The entailment needs only admissibility (`facts.zeroCell_sound`); the
candidate collection `denseCollectZeroCells` carries its entailment proof alongside the data. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Every expression `denseCellZeroExprs` returns evaluates to `0` on an admissible assignment
    (`zeroCell_sound`). Needs only admissibility. -/
theorem denseCellZeroExprs_eval_zero (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ d.busInteractions)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (c : DenseExpr p)
    (hc : c ∈ denseCellZeroExprs bs facts bi) : c.eval denv = 0 := by
  unfold denseCellZeroExprs at hc
  split at hc
  · exact absurd hc (by simp)
  · rename_i addrReq dataSlots hzc
    split at hc
    · exact absurd hc (by simp)
    · rename_i cval hconst
      split at hc
      · rename_i hcond
        rw [Bool.and_eq_true] at hcond
        obtain ⟨hcne, haddrall⟩ := hcond
        have hcne' : cval ≠ 0 := of_decide_eq_true hcne
        rw [List.mem_map] at hc
        obtain ⟨slot, hslot, rfl⟩ := hc
        have hmem : denseBIEval bi denv ∈ d.busInteractions.map (fun b => denseBIEval b denv) :=
          List.mem_map.2 ⟨bi, hbi, rfl⟩
        have hadm' : bs.admissible ((d.busInteractions.map (fun b => denseBIEval b denv)).filter
            (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
        have hbusId : (denseBIEval bi denv).busId = bi.busId := rfl
        have hmult : (denseBIEval bi denv).multiplicity = cval :=
          bi.multiplicity.constValue?_sound cval hconst denv
        have hmne : (denseBIEval bi denv).multiplicity ≠ 0 := by rw [hmult]; exact hcne'
        have haddr : ∀ ar ∈ addrReq, (denseBIEval bi denv).payload[ar.1]? = some ar.2 := by
          intro ar har
          have hpay : bi.payload[ar.1]? = some (DenseExpr.const ar.2) :=
            of_decide_eq_true (List.all_eq_true.1 haddrall ar har)
          show (bi.payload.map (fun e => e.eval denv))[ar.1]? = some ar.2
          rw [List.getElem?_map, hpay]; rfl
        cases hpsl : bi.payload[slot]? with
        | none => simp [DenseExpr.eval]
        | some e =>
          rw [Option.getD_some]
          have hget : (denseBIEval bi denv).payload[slot]? = some (e.eval denv) := by
            show (bi.payload.map (fun e => e.eval denv))[slot]? = some (e.eval denv)
            rw [List.getElem?_map, hpsl]; rfl
          exact facts.zeroCell_sound (d.busInteractions.map (fun b => denseBIEval b denv)) hadm'
            bi.busId addrReq dataSlots hzc (denseBIEval bi denv) hmem hbusId hmne haddr slot hslot
            (e.eval denv) hget
      · exact absurd hc (by simp)

/-- Collect every interaction's fixed-zero data-limb expressions, carrying the proof that each
    evaluates to `0` on an admissible assignment. -/
def denseCollectZeroCells (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    (pending : List (BusInteraction (DenseExpr p))) →
    (∀ bi ∈ pending, bi ∈ d.busInteractions) →
    { out : List (DenseExpr p) //
        ∀ denv, d.admissible bs denv → ∀ c ∈ out, c.eval denv = 0 }
  | [], _ => ⟨[], fun _ _ _ h => absurd h (by simp)⟩
  | bi :: rest, hmem =>
    let ⟨acc, hacc⟩ := denseCollectZeroCells d bs facts rest
      (fun b hb => hmem b (List.mem_cons_of_mem _ hb))
    ⟨denseCellZeroExprs bs facts bi ++ acc, by
      intro denv hadm c hc
      rcases List.mem_append.1 hc with h | h
      · exact denseCellZeroExprs_eval_zero d bs facts bi (hmem bi (List.mem_cons_self ..))
          denv hadm c h
      · exact hacc denv hadm c h⟩

/-- The filtered fixed-zero data-limb equalities the pass appends (`d.occ` bound once). -/
def denseZeroRegisterNew (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let exprs := (denseCollectZeroCells d bs facts d.busInteractions (fun _ h => h)).1
  let dVars := d.occ
  exprs.filter (denseZeroPred d dVars)

/-- The dense fixed-zero pinning transform: append the filtered fixed-zero data limbs (identity
    when there are none). -/
def denseZeroRegisterF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  let exprs := (denseCollectZeroCells d bs facts d.busInteractions (fun _ h => h)).1
  let dVars := d.occ
  let new := exprs.filter (denseZeroPred d dVars)
  if new.isEmpty then d
  else { d with algebraicConstraints := d.algebraicConstraints ++ new }

theorem denseZeroRegisterF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseZeroRegisterF bs facts d =
      if (denseZeroRegisterNew bs facts d).isEmpty then d
      else { d with algebraicConstraints := d.algebraicConstraints ++ denseZeroRegisterNew bs facts d } :=
  rfl

/-- Every variable of a surviving candidate occurs in `d` (the filter's third conjunct). -/
theorem denseZeroRegisterNew_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseZeroRegisterNew bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  have hp : denseZeroPred d d.occ c = true := (List.mem_filter.1 hc).2
  unfold denseZeroPred at hp
  simp only [Bool.and_eq_true, List.all_eq_true] at hp
  exact of_decide_eq_true (hp.2 z hz)

/-- Every surviving candidate evaluates to `0` on an admissible assignment. -/
theorem denseZeroRegisterNew_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p) (hadm : d.admissible bs denv) :
    ∀ c ∈ denseZeroRegisterNew bs facts d, c.eval denv = 0 := by
  intro c hc
  exact (denseCollectZeroCells d bs facts d.busInteractions (fun _ h => h)).2 denv hadm c
    (List.mem_of_mem_filter hc)

theorem denseZeroRegisterF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseZeroRegisterF bs facts d).CoveredBy reg := by
  rw [denseZeroRegisterF_eq]
  split
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h' | h'
    · exact hcov.1 e h'
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i (denseZeroRegisterNew_vars bs facts d e h' i hi)

theorem denseZeroRegisterF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseZeroRegisterF bs facts d) [] bs := by
  rw [denseZeroRegisterF_eq]
  split
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseZeroRegisterNew bs facts d)
      (denseZeroRegisterNew_vars bs facts d)
      (fun denv hadm _hsat => denseZeroRegisterNew_sound bs facts d denv hadm)

/-- The dense fixed-zero-register pass. -/
def denseZeroRegisterPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseZeroRegisterF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseZeroRegisterF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseZeroRegisterF_correct reg bs facts d)

end ApcOptimizer.Dense
