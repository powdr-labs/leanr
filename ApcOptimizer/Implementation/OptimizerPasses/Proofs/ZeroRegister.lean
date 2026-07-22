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

/-- The dense fixed-zero-register pass: appends `data_i = 0` for every data slot of a memory
    message pinned to a declared fixed-zero cell. -/
def denseZeroRegisterPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofAddConstraints denseZeroRegisterNew denseZeroRegisterNew_vars
    (fun bs facts d denv hadm _ => denseZeroRegisterNew_sound bs facts d denv hadm)

end ApcOptimizer.Dense
