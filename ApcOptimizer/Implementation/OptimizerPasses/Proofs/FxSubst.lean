import ApcOptimizer.Implementation.OptimizerPasses.FxSubst
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagUnify

set_option autoImplicit false

/-! # Soundness for the dense `fxSubst` pass (`FxSubst.lean`, part A of `flagFold`).
Substitution-shaped like `flagUnify`: correctness rides on `substF_denseCorrect`, fed the
solution map's entailment (`denseFxCheck_sound`) and occurrence closure (`denseFxCheck_vars`),
both threaded through the scan by `denseFxLoop_sound`. The pair-level machinery and scan lemmas
are reused from `flagUnify`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The certificate is sound -/

/-- **`denseFxCheck` exposes payload membership of the built expression**: a passed certificate
    forces every variable of `E` into `biX`'s payload variables (needed for occurrence closure of
    the adopted `vy := E`). -/
theorem denseFxCheck_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (biX biY : BusInteraction (DenseExpr p))
    (x : VarId) (E : DenseExpr p) (vy : VarId)
    (h : denseFxCheck bs facts domCs biX biY x E vy = true) :
    ∀ v ∈ E.vars, v ∈ biX.payload.flatMap DenseExpr.vars := by
  intro v hv
  unfold denseFxCheck at h
  cases hd : denseFuPairData? bs facts domCs biX biY x with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    have hpay : d.payXVars = biX.payload.flatMap DenseExpr.vars := by
      unfold denseFuPairData? at hd
      cases hmx : biX.multiplicity.constValue? with
      | none => rw [hmx] at hd; simp at hd
      | some mx =>
        cases hmy : biY.multiplicity.constValue? with
        | none => rw [hmx, hmy] at hd; simp at hd
        | some my =>
          simp only [hmx, hmy] at hd
          split_ifs at hd
          cases hOX : biX.payload[0]? with
          | none => simp [hOX] at hd
          | some OX =>
            cases hOY : biY.payload[0]? with
            | none => simp [hOX, hOY] at hd
            | some OY =>
              simp only [hOX, hOY] at hd
              cases hbX : facts.slotBound biX.busId mx
                  (biX.payload.map DenseExpr.constValue?) 0 with
              | none => simp [hbX] at hd
              | some bX =>
                cases hbY : facts.slotBound biY.busId my
                    (biY.payload.map DenseExpr.constValue?) 0 with
                | none => simp [hbX, hbY] at hd
                | some bY =>
                  simp only [hbX, hbY] at hd
                  cases hsX : OX.splitAt x with
                  | none => simp [hsX] at hd
                  | some kRX =>
                    obtain ⟨k, RX⟩ := kRX
                    cases hsY : OY.splitAt x with
                    | none => simp [hsX, hsY] at hd
                    | some kRY =>
                      obtain ⟨k2, RY⟩ := kRY
                      simp only [hsX, hsY] at hd
                      split_ifs at hd
                      simp only [Option.some.injEq] at hd
                      rw [← hd]
    unfold denseFxCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact hpay ▸ of_decide_eq_true (List.all_eq_true.mp h.1.2 v hv)

/-- **`denseFxCheck` entails the interpolation**: on satisfying assignments `denv vy = E.eval denv`.
    Same pair-level residue argument as `flagUnify`'s `denseFuCheck_sound`, with the interpolation
    `E` as the certificate's target in place of the twin flag. -/
theorem denseFxCheck_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (biX biY : BusInteraction (DenseExpr p))
    (x : VarId) (E : DenseExpr p) (vy : VarId)
    (h : denseFxCheck bs facts domCs biX biY x E vy = true)
    (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval denv = 0)
    (hobX : (denseBIEval biX denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval biX denv) = false)
    (hobY : (denseBIEval biY denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval biY denv) = false) :
    denv vy = E.eval denv := by
  unfold denseFxCheck at h
  cases hd : denseFuPairData? bs facts domCs biX biY x with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    unfold denseFxCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hvyR', _hEm⟩, hEjoint⟩, _hEpay⟩, hcw⟩ := h
    unfold denseFuPairData? at hd
    cases hmx : biX.multiplicity.constValue? with
    | none => rw [hmx] at hd; simp at hd
    | some mx =>
      cases hmy : biY.multiplicity.constValue? with
      | none => rw [hmx, hmy] at hd; simp at hd
      | some my =>
        simp only [hmx, hmy] at hd
        split_ifs at hd with hmx0 hmy0
        cases hOX : biX.payload[0]? with
        | none => simp [hOX] at hd
        | some OX =>
          cases hOY : biY.payload[0]? with
          | none => simp [hOX, hOY] at hd
          | some OY =>
            simp only [hOX, hOY] at hd
            cases hbX : facts.slotBound biX.busId mx
                (biX.payload.map DenseExpr.constValue?) 0 with
            | none => simp [hbX] at hd
            | some bX =>
              cases hbY : facts.slotBound biY.busId my
                  (biY.payload.map DenseExpr.constValue?) 0 with
              | none => simp [hbX, hbY] at hd
              | some bY =>
                simp only [hbX, hbY] at hd
                cases hsX : OX.splitAt x with
                | none => simp [hsX] at hd
                | some kRX =>
                  obtain ⟨k, RX⟩ := kRX
                  cases hsY : OY.splitAt x with
                  | none => simp [hsX, hsY] at hd
                  | some kRY =>
                    obtain ⟨k2, RY⟩ := kRY
                    simp only [hsX, hsY] at hd
                    split_ifs at hd with hconds hcov hall
                    obtain ⟨hk2, hunit, hwrapX, hwrapY⟩ := hconds
                    obtain ⟨hcover, _hcap⟩ := hcov
                    simp only [Option.some.injEq] at hd
                    subst hd
                    simp only at hvyR' hEjoint hcw
                    -- acceptance and slot-value bounds
                    have hmXe : (denseBIEval biX denv).multiplicity = mx :=
                      biX.multiplicity.constValue?_sound mx hmx denv
                    have hmYe : (denseBIEval biY denv).multiplicity = my :=
                      biY.multiplicity.constValue?_sound my hmy denv
                    have hviolX : bs.violatesConstraint (denseBIEval biX denv) = false :=
                      hobX (by rw [hmXe]; exact hmx0)
                    have hviolY : bs.violatesConstraint (denseBIEval biY denv) = false :=
                      hobY (by rw [hmYe]; exact hmy0)
                    have hgetX : (denseBIEval biX denv).payload[0]? = some (OX.eval denv) := by
                      show (biX.payload.map (fun e => e.eval denv))[0]? = _
                      rw [List.getElem?_map, hOX]; rfl
                    have hgetY : (denseBIEval biY denv).payload[0]? = some (OY.eval denv) := by
                      show (biY.payload.map (fun e => e.eval denv))[0]? = _
                      rw [List.getElem?_map, hOY]; rfl
                    have hbXv : (OX.eval denv).val < bX :=
                      facts.slotBound_sound (denseBIEval biX denv)
                        (biX.payload.map DenseExpr.constValue?) 0 bX (OX.eval denv)
                        (by rw [(rfl : (denseBIEval biX denv).busId = biX.busId), hmXe]; exact hbX)
                        (denseMatches_evalPattern biX.payload denv) hviolX hgetX
                    have hbYv : (OY.eval denv).val < bY :=
                      facts.slotBound_sound (denseBIEval biY denv)
                        (biY.payload.map DenseExpr.constValue?) 0 bY (OY.eval denv)
                        (by rw [(rfl : (denseBIEval biY denv).busId = biY.busId), hmYe]; exact hbY)
                        (denseMatches_evalPattern biY.payload denv) hviolY hgetY
                    -- field decomposition `x = m·u + W`, both sides
                    set m := k⁻¹ with hm
                    have hOXe : OX.eval denv = k * denv x + RX.eval denv :=
                      DenseExpr.splitAt_eval x OX k RX hsX denv
                    have hOYe : OY.eval denv = k * denv x + RY.eval denv := by
                      have h0 := DenseExpr.splitAt_eval x OY k2 RY hsY denv
                      rw [hk2] at h0; exact h0
                    have hxX : denv x = m * OX.eval denv + (-m) * RX.eval denv := by
                      have h1 : m * OX.eval denv = m * k * denv x + m * RX.eval denv := by
                        rw [hOXe]; ring
                      rw [mul_comm m k, hunit, one_mul] at h1
                      linear_combination -h1
                    have hxY : denv x = m * OY.eval denv + (-m) * RY.eval denv := by
                      have h1 : m * OY.eval denv = m * k * denv x + m * RY.eval denv := by
                        rw [hOYe]; ring
                      rw [mul_comm m k, hunit, one_mul] at h1
                      linear_combination -h1
                    -- the environment restricted to the joint flag box is an enumerated point
                    have hmemdoms : ∀ vd ∈ (RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                        (denseFindDomainAlg domCs v).map (fun d => (v, d))), denv vd.1 ∈ vd.2 := by
                      intro vd hvd
                      obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
                      cases hfd : denseFindDomainAlg domCs v with
                      | none => rw [hfd] at hvd'; simp at hvd'
                      | some dm =>
                        rw [hfd] at hvd'
                        simp only [Option.map_some, Option.some.injEq] at hvd'
                        obtain rfl := hvd'.symm
                        exact denseFindDomainAlg_sound denv domCs v dm hfd hdom
                    have hpt := mem_denseAssignments ((RX.vars ++ RY.vars).eraseDups.filterMap
                      (fun v => (denseFindDomainAlg domCs v).map (fun d => (v, d)))) denv hmemdoms
                    have hagree : ∀ v, v ∈ (RX.vars ++ RY.vars).eraseDups →
                        denseEnvOfFast (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, denv vd.1))) v = denv v := by
                      intro v hv
                      refine denseEnvOfFast_map _ denv v ?_
                      rw [show (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                        (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map Prod.fst)
                        = (RX.vars ++ RY.vars).eraseDups from hcover]
                      exact hv
                    have hRXagree : RX.eval (denseEnvOfFast (((RX.vars ++ RY.vars).eraseDups.filterMap
                        (fun v => (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                          (fun vd => (vd.1, denv vd.1)))) = RX.eval denv :=
                      DenseExpr.eval_congr RX _ denv (fun v hv =>
                        hagree v (List.mem_eraseDups.2 (List.mem_append_left _ hv)))
                    have hRYagree : RY.eval (denseEnvOfFast (((RX.vars ++ RY.vars).eraseDups.filterMap
                        (fun v => (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                          (fun vd => (vd.1, denv vd.1)))) = RY.eval denv :=
                      DenseExpr.eval_congr RY _ denv (fun v hv =>
                        hagree v (List.mem_eraseDups.2 (List.mem_append_right _ hv)))
                    -- pair-level point bounds, at the environment's own point
                    have hpair := List.all_eq_true.mp hall _ hpt
                    rw [Bool.and_eq_true] at hpair
                    have hWXlt : ((-m) * RX.eval denv).val < m.val := by
                      rw [← hRXagree]; exact of_decide_eq_true hpair.1
                    have hWYlt : ((-m) * RY.eval denv).val < m.val := by
                      rw [← hRYagree]; exact of_decide_eq_true hpair.2
                    -- integer decomposition of `x.val` through both checks
                    have hbX1 : (OX.eval denv).val ≤ bX - 1 := by omega
                    have hbY1 : (OY.eval denv).val ≤ bY - 1 := by omega
                    have hle1 : m.val * (OX.eval denv).val ≤ m.val * (bX - 1) :=
                      Nat.mul_le_mul_left _ hbX1
                    have hle2 : m.val * (OY.eval denv).val ≤ m.val * (bY - 1) :=
                      Nat.mul_le_mul_left _ hbY1
                    have hMuX : (m * OX.eval denv).val = m.val * (OX.eval denv).val :=
                      ZMod.val_mul_of_lt (by omega)
                    have hMuY : (m * OY.eval denv).val = m.val * (OY.eval denv).val :=
                      ZMod.val_mul_of_lt (by omega)
                    have hsumX : (m * OX.eval denv).val + ((-m) * RX.eval denv).val < p := by
                      rw [hMuX]; omega
                    have hsumY : (m * OY.eval denv).val + ((-m) * RY.eval denv).val < p := by
                      rw [hMuY]; omega
                    have hvalX : (denv x).val
                        = m.val * (OX.eval denv).val + ((-m) * RX.eval denv).val := by
                      rw [hxX, ZMod.val_add_of_lt hsumX, hMuX]
                    have hvalY : (denv x).val
                        = m.val * (OY.eval denv).val + ((-m) * RY.eval denv).val := by
                      rw [hxY, ZMod.val_add_of_lt hsumY, hMuY]
                    have hres : ((-m) * RX.eval denv).val = ((-m) * RY.eval denv).val :=
                      residue_uniq m.val (OX.eval denv).val (OY.eval denv).val _ _
                        (hvalX.symm.trans hvalY) hWXlt hWYlt
                    -- the target condition at the environment's point
                    have hmempts : (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, denv vd.1)),
                        decide (((-m) * RX.eval (denseEnvOfFast
                            (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, denv vd.1))))).val
                          = ((-m) * RY.eval (denseEnvOfFast
                            (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, denv vd.1))))).val))
                        ∈ ((denseAssignments ((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (denseFindDomainAlg domCs v).map (fun d => (v, d))))).map
                            (fun pt => (pt, decide (((-m) * RX.eval (denseEnvOfFast pt)).val
                              = ((-m) * RY.eval (denseEnvOfFast pt)).val)))) :=
                      List.mem_map.2 ⟨_, hpt, rfl⟩
                    have horb := List.all_eq_true.mp hcw _ hmempts
                    have hb : decide (((-m) * RX.eval (denseEnvOfFast (((RX.vars
                        ++ RY.vars).eraseDups.filterMap (fun v =>
                          (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, denv vd.1))))).val
                        = ((-m) * RY.eval (denseEnvOfFast
                            (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, denv vd.1))))).val) = true :=
                      decide_eq_true (by rw [hRXagree, hRYagree]; exact hres)
                    simp only [hb, Bool.not_true, Bool.false_or, decide_eq_true_eq] at horb
                    -- the built expression agrees on the box point (all its vars are joint flags)
                    have hEagree : E.eval (denseEnvOfFast (((RX.vars ++ RY.vars).eraseDups.filterMap
                        (fun v => (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                          (fun vd => (vd.1, denv vd.1)))) = E.eval denv := by
                      refine DenseExpr.eval_congr E _ denv (fun v hv => ?_)
                      refine hagree v (List.mem_eraseDups.2 ?_)
                      rcases of_decide_eq_true (List.all_eq_true.mp hEjoint v hv) with h1 | h1
                      · exact List.mem_append_left _ h1
                      · exact List.mem_append_right _ h1
                    rw [← hagree vy (List.mem_eraseDups.2 (List.mem_append_right _ hvyR')),
                        ← hEagree]
                    exact horb

/-- **The fxSubst scan loop is sound**: the final solution map is entailed and occurrence-closed.
    Per matched pair a list of certified interpolations `vy := E` is adopted; `denseFxCheck_sound`
    forces each on satisfying assignments and `denseFxCheck_vars` closes their variables into the
    interaction's payload. -/
theorem denseFxLoop_sound [Fact p.Prime] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    ∀ (pending : List (BusInteraction (DenseExpr p)))
      (seen : Std.HashMap UInt64 (List (DenseFUSeen p))) (σ : DenseSolved p),
      (∀ bi ∈ pending, bi ∈ d.busInteractions) →
      (∀ hsh e, e ∈ seen.getD hsh [] → e.bi ∈ d.busInteractions) →
      (∀ denv, d.satisfies bs denv → ∀ i t, σ.fn i = some t → denv i = t.eval denv) →
      (∀ i t, σ.fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
          (denseFxLoop bs facts d.algebraicConstraints pending seen σ).fn i
            = some t → denv i = t.eval denv) ∧
      (∀ i t, (denseFxLoop bs facts d.algebraicConstraints pending seen σ).fn i
          = some t → ∀ z ∈ t.vars, z ∈ d.occ) := by
  intro pending
  induction pending with
  | nil =>
      intro seen σ _ _ hσs hσv
      exact ⟨hσs, hσv⟩
  | cons c rest ih =>
      intro seen σ hpend hseen hσs hσv
      have hcmem : c ∈ d.busInteractions := hpend c (List.mem_cons_self ..)
      have hrest : ∀ bi ∈ rest, bi ∈ d.busInteractions :=
        fun bi h => hpend bi (List.mem_cons_of_mem _ h)
      have hseen' : ∀ hsh e, e ∈ (denseFuInsertAll seen
          ((denseFuCandidates c).map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseFUSeen p)))).getD hsh [] →
          e.bi ∈ d.busInteractions := by
        refine denseFuInsertAll_seen _ seen hseen ?_
        intro e' he'
        obtain ⟨xk', _hxk', rfl⟩ := List.mem_map.1 he'
        exact hcmem
      rw [denseFxLoop]
      cases hf : (denseFuCandidates c).findSome? (fun xk =>
          (seen.getD (denseFuKeyHash xk.2) []).findSome? (fun e =>
            if e.key == xk.2 then some (e, xk.1) else none)) with
      | none =>
          simp only []
          exact ih _ σ hrest hseen' hσs hσv
      | some ex =>
          simp only []
          cases hd0 : denseFuPairData? bs facts d.algebraicConstraints ex.1.bi c ex.2 with
          | none =>
              simp only []
              exact ih _ σ hrest hseen' hσs hσv
          | some d0 =>
              simp only []
              -- the matched seen-entry's interaction is one of `d`'s interactions
              obtain ⟨xk, _hxkmem, hinner⟩ := List.exists_of_findSome?_eq_some hf
              obtain ⟨e, hemem, hif⟩ := List.exists_of_findSome?_eq_some hinner
              by_cases hk : (e.key == xk.2) = true
              · rw [if_pos hk] at hif
                simp only [Option.some.injEq] at hif
                have hexbi : ex.1.bi ∈ d.busInteractions := by
                  rw [← hif]; exact hseen (denseFuKeyHash xk.2) e hemem
                refine ih _ (σ.insertAll _) hrest hseen' ?_ ?_
                · -- (a) entailment of the updated map
                  intro denv hsat i t hti
                  refine DenseSolved.insertAll_preserves _ σ
                    (fun i' t' h' => hσs denv hsat i' t' h') ?_ i t hti
                  intro pr hpr
                  obtain ⟨vy, _hvy, hpif⟩ := List.mem_filterMap.1 hpr
                  by_cases hck : denseFxCheckWith d0 (denseBuildE d0 vy) vy = true
                  · rw [if_pos hck] at hpif
                    simp only [Option.some.injEq] at hpif
                    rw [← hpif]
                    show denv vy = (denseBuildE d0 vy).eval denv
                    have hfc : denseFxCheck bs facts d.algebraicConstraints
                        ex.1.bi c ex.2 (denseBuildE d0 vy) vy = true := by
                      unfold denseFxCheck; rw [hd0]; exact hck
                    exact denseFxCheck_sound bs facts d.algebraicConstraints ex.1.bi c ex.2
                      (denseBuildE d0 vy) vy hfc denv hsat.1 (hsat.2 ex.1.bi hexbi) (hsat.2 c hcmem)
                  · rw [if_neg hck] at hpif
                    exact absurd hpif (by simp)
                · -- (b) occurrence closure of the updated map
                  intro i t hti
                  refine DenseSolved.insertAll_preserves
                    (Q := fun i t => ∀ z ∈ t.vars, z ∈ d.occ) _ σ hσv ?_ i t hti
                  intro pr hpr
                  obtain ⟨vy, _hvy, hpif⟩ := List.mem_filterMap.1 hpr
                  by_cases hck : denseFxCheckWith d0 (denseBuildE d0 vy) vy = true
                  · rw [if_pos hck] at hpif
                    simp only [Option.some.injEq] at hpif
                    rw [← hpif]
                    intro z hz
                    have hfc : denseFxCheck bs facts d.algebraicConstraints
                        ex.1.bi c ex.2 (denseBuildE d0 vy) vy = true := by
                      unfold denseFxCheck; rw [hd0]; exact hck
                    exact DenseConstraintSystem.mem_occ_of_bi hexbi (by
                      simp only [denseBIVars, List.mem_append]
                      exact Or.inr (denseFxCheck_vars bs facts d.algebraicConstraints
                        ex.1.bi c ex.2 (denseBuildE d0 vy) vy hfc z hz))
                  · rw [if_neg hck] at hpif
                    exact absurd hpif (by simp)
              · rw [if_neg hk] at hif
                exact absurd hif (by simp)

/-! ## The dense `fxSubst` pass -/

/-- The dense `fxSubst` transform re-expressed with the loop's solution map named, for the
    correctness/coverage proofs. -/
theorem denseFxSubstF_eq (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseFxSubstF pw bs facts d
      = (if pw.isPrime = true then
          (if (denseFxLoop bs facts d.algebraicConstraints d.busInteractions ∅
                DenseSolved.empty).map.isEmpty then d
           else d.substF (denseFxLoop bs facts d.algebraicConstraints d.busInteractions ∅
                DenseSolved.empty).fn)
         else d) := rfl

/-- The final loop solution map is entailed and occurrence-closed (specialising `denseFxLoop_sound`
    to the pass's initial `∅`/`empty` accumulators). -/
theorem denseFxSubst_loop_invariant [Fact p.Prime] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseFxLoop bs facts d.algebraicConstraints d.busInteractions ∅
          DenseSolved.empty).fn i = some t → denv i = t.eval denv) ∧
    (∀ i t, (denseFxLoop bs facts d.algebraicConstraints d.busInteractions ∅
        DenseSolved.empty).fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) := by
  refine denseFxLoop_sound bs facts d d.busInteractions ∅ DenseSolved.empty
    (fun _ h => h) ?_ ?_ ?_
  · intro hsh e hmem
    rw [Std.HashMap.getD_empty] at hmem
    exact absurd hmem (by simp)
  · intro denv _ i t hti
    exact absurd hti (by simp [DenseSolved.fn, DenseSolved.empty])
  · intro i t hti
    exact absurd hti (by simp [DenseSolved.fn, DenseSolved.empty])

theorem denseFxSubstF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseFxSubstF pw bs facts d).CoveredBy reg := by
  rw [denseFxSubstF_eq]
  split_ifs with hp hempty
  · exact hcov
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    refine DenseConstraintSystem.substF_covered hcov ?_
    intro i _ t hti z hz
    exact DenseConstraintSystem.occ_valid hcov z
      ((denseFxSubst_loop_invariant bs facts d).2 i t hti z hz)
  · exact hcov

theorem denseFxSubstF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (_hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseFxSubstF pw bs facts d) [] bs := by
  rw [denseFxSubstF_eq]
  split_ifs with hp hempty
  · exact dpcRefl reg.isInput d bs
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    have hinv := denseFxSubst_loop_invariant bs facts d
    exact DenseConstraintSystem.substF_denseCorrect d _ bs reg.isInput
      (fun denv hsat i t hti => hinv.1 denv hsat i t hti)
      (fun i t hti z hz => hinv.2 i t hti z hz)
  · exact dpcRefl reg.isInput d bs

/-- The wired dense `fxSubst` pass (`denseFxSubstF`, `FxSubst.lean`); part A of `flagFold`. -/
def denseFxSubstPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (denseFxSubstF pw) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseFxSubstF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseFxSubstF_correct pw reg bs facts d hcov)

end ApcOptimizer.Dense
