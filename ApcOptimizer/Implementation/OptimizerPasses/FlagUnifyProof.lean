import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify
import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnifyProof

set_option autoImplicit false

/-! # Soundness for the dense `flagUnify` pass

`DensePassCorrect` for `denseFlagUnifyF` (`FlagUnify.lean`): a substitution-shaped pass parallel to
`denseRootPairUnifyF`, riding on `DenseConstraintSystem.substF_denseCorrect`. The new content is the
certificate soundness `denseFuCheck_sound` (via `facts.slotBound_sound` + `residue_uniq`) and the
scan-loop invariant. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The certificate is sound -/

/-- A passed `denseFuCheck` forces `vx` into `biX`'s payload variables (for occurrence closure). -/
theorem denseFuCheck_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (biX biY : BusInteraction (DenseExpr p))
    (x vx vy : VarId) (h : denseFuCheck bs facts domCs biX biY x vx vy = true) :
    vx ∈ biX.payload.flatMap DenseExpr.vars := by
  unfold denseFuCheck at h
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
    unfold denseFuCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact hpay ▸ h.1.2

/-- `denseFuCheck` entails `vy = vx` on satisfying assignments: two scaled range checks of the same
    carrier `x` whose offsets agree pointwise on their finite flag box pin the flags equal. -/
theorem denseFuCheck_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (biX biY : BusInteraction (DenseExpr p))
    (x vx vy : VarId) (h : denseFuCheck bs facts domCs biX biY x vx vy = true)
    (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval denv = 0)
    (hobX : (denseBIEval biX denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval biX denv) = false)
    (hobY : (denseBIEval biY denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval biY denv) = false) :
    denv vy = denv vx := by
  unfold denseFuCheck at h
  cases hd : denseFuPairData? bs facts domCs biX biY x with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    unfold denseFuCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hvxR', hvyR'⟩, _hne⟩, _hpay'⟩, hcw⟩ := h
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
                    simp only at hvxR' hvyR' hcw
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
                    have hpair := List.all_eq_true.mp hall _ hpt
                    rw [Bool.and_eq_true] at hpair
                    have hWXlt : ((-m) * RX.eval denv).val < m.val := by
                      rw [← hRXagree]; exact of_decide_eq_true hpair.1
                    have hWYlt : ((-m) * RY.eval denv).val < m.val := by
                      rw [← hRYagree]; exact of_decide_eq_true hpair.2
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
                    rw [← hagree vy (List.mem_eraseDups.2 (List.mem_append_right _ hvyR')),
                        ← hagree vx (List.mem_eraseDups.2 (List.mem_append_left _ hvxR'))]
                    exact horb

/-! ## Solution-map list update -/

/-- A left fold of `HashMap` inserts preserves any per-entry property `Q` holding of the base map
    and every inserted pair. -/
theorem foldl_insert_getElem {Q : VarId → DenseExpr p → Prop} :
    ∀ (pairs : List (VarId × DenseExpr p)) (m : Std.HashMap VarId (DenseExpr p)),
      (∀ i t, m[i]? = some t → Q i t) → (∀ pr ∈ pairs, Q pr.1 pr.2) →
      ∀ i t, (pairs.foldl (fun m pr => m.insert pr.1 pr.2) m)[i]? = some t → Q i t := by
  intro pairs
  induction pairs with
  | nil => intro m hm _ i t ht; exact hm i t ht
  | cons hd rest ih =>
      intro m hm hpairs i t ht
      obtain ⟨x, t0⟩ := hd
      simp only [List.foldl_cons] at ht
      refine ih (m.insert x t0) ?_ (fun pr hpr => hpairs pr (List.mem_cons_of_mem _ hpr)) i t ht
      intro j s hjs
      rw [Std.HashMap.getElem?_insert] at hjs
      split_ifs at hjs with hjx
      · simp only [Option.some.injEq] at hjs
        have hj : x = j := by simpa using hjx
        rw [← hjs, ← hj]
        exact hpairs (x, t0) (List.mem_cons_self ..)
      · exact hm j s hjs

/-- Insertions preserve any per-entry property of the `DenseSolved` solution map. -/
theorem DenseSolved.insertAll_preserves {Q : VarId → DenseExpr p → Prop}
    (pairs : List (VarId × DenseExpr p)) (σ : DenseSolved p)
    (hσ : ∀ i t, σ.fn i = some t → Q i t) (hpairs : ∀ pr ∈ pairs, Q pr.1 pr.2) :
    ∀ i t, (σ.insertAll pairs).fn i = some t → Q i t := by
  intro i t ht
  simp only [DenseSolved.fn, DenseSolved.insertAll_map] at ht
  exact foldl_insert_getElem pairs σ.map (fun i t h => hσ i t h) hpairs i t ht

/-! ## The scan-loop invariant (parallels `RootPairUnifyProof.lean`) -/

/-- `denseFuInsertAll` preserves the `seen`-bucket invariant (every entry's `bi` is in `S`). -/
theorem denseFuInsertAll_seen {S : List (BusInteraction (DenseExpr p))} :
    ∀ (es : List (DenseFUSeen p)) (seen : Std.HashMap UInt64 (List (DenseFUSeen p))),
      (∀ hsh e, e ∈ seen.getD hsh [] → e.bi ∈ S) → (∀ e ∈ es, e.bi ∈ S) →
      ∀ hsh e, e ∈ (denseFuInsertAll seen es).getD hsh [] → e.bi ∈ S := by
  intro es
  induction es with
  | nil => intro seen hseen _ hsh e hmem; exact hseen hsh e hmem
  | cons e0 rest ih =>
      intro seen hseen hes hsh e hmem
      have hacc : ∀ hsh' e', e' ∈ (denseFuInsertAll seen rest).getD hsh' [] → e'.bi ∈ S :=
        ih seen hseen (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
      have hstep : denseFuInsertAll seen (e0 :: rest)
          = (denseFuInsertAll seen rest).insert (denseFuKeyHash e0.key)
              (e0 :: (denseFuInsertAll seen rest).getD (denseFuKeyHash e0.key) []) := by
        simp only [denseFuInsertAll, List.foldr_cons]
      rw [hstep, Std.HashMap.getD_insert] at hmem
      split_ifs at hmem with hk
      · rcases List.mem_cons.1 hmem with rfl | hmem'
        · exact hes e (List.mem_cons_self ..)
        · exact hacc (denseFuKeyHash e0.key) e hmem'
      · exact hacc hsh e hmem

/-- The flagUnify scan loop is sound: the final solution map is entailed (a) and occurrence-closed
    (b), each adopted `vy = vx` justified by `denseFuCheck_sound`. -/
theorem denseFuLoop_sound [Fact p.Prime] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    ∀ (pending : List (BusInteraction (DenseExpr p)))
      (seen : Std.HashMap UInt64 (List (DenseFUSeen p))) (σ : DenseSolved p),
      (∀ bi ∈ pending, bi ∈ d.busInteractions) →
      (∀ hsh e, e ∈ seen.getD hsh [] → e.bi ∈ d.busInteractions) →
      (∀ denv, d.satisfies bs denv → ∀ i t, σ.fn i = some t → denv i = t.eval denv) →
      (∀ i t, σ.fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
          (denseFuLoop bs facts d.algebraicConstraints pending seen σ).fn i
            = some t → denv i = t.eval denv) ∧
      (∀ i t, (denseFuLoop bs facts d.algebraicConstraints pending seen σ).fn i
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
      rw [denseFuLoop]
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
              obtain ⟨xk, _hxkmem, hinner⟩ := List.exists_of_findSome?_eq_some hf
              obtain ⟨e, hemem, hif⟩ := List.exists_of_findSome?_eq_some hinner
              by_cases hk : (e.key == xk.2) = true
              · rw [if_pos hk] at hif
                simp only [Option.some.injEq] at hif
                have hexbi : ex.1.bi ∈ d.busInteractions := by
                  rw [← hif]; exact hseen (denseFuKeyHash xk.2) e hemem
                refine ih _ (σ.insertAll _) hrest hseen' ?_ ?_
                ·
                  intro denv hsat i t hti
                  refine DenseSolved.insertAll_preserves _ σ
                    (fun i' t' h' => hσs denv hsat i' t' h') ?_ i t hti
                  intro pr hpr
                  obtain ⟨tt, _htt, hpif⟩ := List.mem_filterMap.1 hpr
                  by_cases hck : denseFuCheckWith d0 tt.2 tt.1 = true
                  · rw [if_pos hck] at hpif
                    simp only [Option.some.injEq] at hpif
                    rw [← hpif]
                    show denv tt.1 = denv tt.2
                    have hfc : denseFuCheck bs facts d.algebraicConstraints
                        ex.1.bi c ex.2 tt.2 tt.1 = true := by
                      unfold denseFuCheck; rw [hd0]; exact hck
                    exact denseFuCheck_sound bs facts d.algebraicConstraints ex.1.bi c ex.2
                      tt.2 tt.1 hfc denv hsat.1 (hsat.2 ex.1.bi hexbi) (hsat.2 c hcmem)
                  · rw [if_neg hck] at hpif
                    exact absurd hpif (by simp)
                ·
                  intro i t hti
                  refine DenseSolved.insertAll_preserves
                    (Q := fun i t => ∀ z ∈ t.vars, z ∈ d.occ) _ σ hσv ?_ i t hti
                  intro pr hpr
                  obtain ⟨tt, _htt, hpif⟩ := List.mem_filterMap.1 hpr
                  by_cases hck : denseFuCheckWith d0 tt.2 tt.1 = true
                  · rw [if_pos hck] at hpif
                    simp only [Option.some.injEq] at hpif
                    rw [← hpif]
                    intro z hz
                    simp only [DenseExpr.vars, List.mem_singleton] at hz
                    subst hz
                    have hfc : denseFuCheck bs facts d.algebraicConstraints
                        ex.1.bi c ex.2 tt.2 tt.1 = true := by
                      unfold denseFuCheck; rw [hd0]; exact hck
                    exact DenseConstraintSystem.mem_occ_of_bi hexbi (by
                      simp only [denseBIVars, List.mem_append]
                      exact Or.inr (denseFuCheck_vars bs facts d.algebraicConstraints
                        ex.1.bi c ex.2 tt.2 tt.1 hfc))
                  · rw [if_neg hck] at hpif
                    exact absurd hpif (by simp)
              · rw [if_neg hk] at hif
                exact absurd hif (by simp)

/-! ## The dense `flagUnify` pass -/

/-- `denseFlagUnifyF` re-expressed with the loop's solution map named, for the proofs below. -/
theorem denseFlagUnifyF_eq (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseFlagUnifyF pw bs facts d
      = (if pw.isPrime = true then
          (if (denseFuLoop bs facts d.algebraicConstraints d.busInteractions ∅
                DenseSolved.empty).map.isEmpty then d
           else d.substF (denseFuLoop bs facts d.algebraicConstraints d.busInteractions ∅
                DenseSolved.empty).fn)
         else d) := rfl

/-- The final loop solution map is entailed and occurrence-closed (`denseFuLoop_sound` at `∅`). -/
theorem denseFlagUnify_loop_invariant [Fact p.Prime] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseFuLoop bs facts d.algebraicConstraints d.busInteractions ∅
          DenseSolved.empty).fn i = some t → denv i = t.eval denv) ∧
    (∀ i t, (denseFuLoop bs facts d.algebraicConstraints d.busInteractions ∅
        DenseSolved.empty).fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) := by
  refine denseFuLoop_sound bs facts d d.busInteractions ∅ DenseSolved.empty
    (fun _ h => h) ?_ ?_ ?_
  · intro hsh e hmem
    rw [Std.HashMap.getD_empty] at hmem
    exact absurd hmem (by simp)
  · intro denv _ i t hti
    exact absurd hti (by simp [DenseSolved.fn, DenseSolved.empty])
  · intro i t hti
    exact absurd hti (by simp [DenseSolved.fn, DenseSolved.empty])

theorem denseFlagUnifyF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseFlagUnifyF pw bs facts d).CoveredBy reg := by
  rw [denseFlagUnifyF_eq]
  split_ifs with hp hempty
  · exact hcov
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    refine DenseConstraintSystem.substF_covered hcov ?_
    intro i _ t hti z hz
    exact DenseConstraintSystem.occ_valid hcov z
      ((denseFlagUnify_loop_invariant bs facts d).2 i t hti z hz)
  · exact hcov

theorem denseFlagUnifyF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (_hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseFlagUnifyF pw bs facts d) [] bs := by
  rw [denseFlagUnifyF_eq]
  split_ifs with hp hempty
  · exact dpcRefl reg.isInput d bs
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    have hinv := denseFlagUnify_loop_invariant bs facts d
    exact DenseConstraintSystem.substF_denseCorrect d _ bs reg.isInput
      (fun denv hsat i t hti => hinv.1 denv hsat i t hti)
      (fun i t hti z hz => hinv.2 i t hti z hz)
  · exact dpcRefl reg.isInput d bs

/-- The dense `flagUnify` pass (transform `denseFlagUnifyF`). -/
def denseFlagUnifyPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (denseFlagUnifyF pw) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseFlagUnifyF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseFlagUnifyF_correct pw reg bs facts d hcov)

end ApcOptimizer.Dense
