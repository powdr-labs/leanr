import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.ListSplit
import ApcOptimizer.Implementation.OptimizerPasses.RootPairCore

set_option autoImplicit false

/-! # Soundness for the dense `rootPairUnify` pass

`DensePassCorrect` for `denseRootPairUnifyF` (`RootPairUnify.lean`), lifted through
`DenseVerifiedPassW.of`. A substitution-shaped pass: it eliminates variables via a `DenseSolved` map
and one `DenseConstraintSystem.substF`, so (through `substF_denseCorrect`, `Proofs/DomainBatch.lean`)
it only has to discharge entailment and occurrence-closure of the map — both from the scan-loop
invariant `denseRpLoop_sound`. The per-adoption entailment is the pair certificate
`denseRpCheckPair_sound`, combining `denseTwoRootOf?_sound` (`Proofs/AddrDiseq.lean`) with the field
core `rootPair_eq` (`RootPairCore.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `DenseExpr.splitAt` is exact -/

/-- The constant-coefficient decomposition is exact: `e` evaluates as `k · x + r`. -/
theorem DenseExpr.splitAt_eval (x : VarId) (e : DenseExpr p) (k : ZMod p) (r : DenseExpr p)
    (h : e.splitAt x = some (k, r)) (denv : VarId → ZMod p) :
    e.eval denv = k * denv x + r.eval denv := by
  induction e generalizing k r with
  | const n =>
      simp only [DenseExpr.splitAt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [DenseExpr.eval]
  | var y =>
      simp only [DenseExpr.splitAt] at h
      split_ifs at h with hyx
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hyx
        simp [DenseExpr.eval]
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [DenseExpr.eval]
  | add a b iha ihb =>
      cases ha : a.splitAt x with
      | none => simp [DenseExpr.splitAt, ha] at h
      | some pa =>
          cases hb : b.splitAt x with
          | none => simp [DenseExpr.splitAt, ha, hb] at h
          | some pb =>
              obtain ⟨ca, ra⟩ := pa
              obtain ⟨cb, rb⟩ := pb
              simp only [DenseExpr.splitAt, ha, hb, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [DenseExpr.eval, iha ca ra ha, ihb cb rb hb]
              ring
  | mul a b iha ihb =>
      simp only [DenseExpr.splitAt] at h
      split_ifs at h with hm
      · cases hka : a.constValue? with
        | some ka =>
            cases hb : b.splitAt x with
            | none => simp [hka, hb] at h
            | some pb =>
                obtain ⟨cb, rb⟩ := pb
                simp only [hka, hb, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hae : a.eval denv = ka := a.constValue?_sound ka hka denv
                simp only [DenseExpr.eval, hae, ihb cb rb hb]
                ring
        | none =>
            cases hkb : b.constValue? with
            | none => simp [hka, hkb] at h
            | some kb =>
                cases ha : a.splitAt x with
                | none => simp [hka, hkb, ha] at h
                | some pa =>
                    obtain ⟨ca, ra⟩ := pa
                    simp only [hka, hkb, ha, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hbe : b.eval denv = kb := b.constValue?_sound kb hkb denv
                    simp only [DenseExpr.eval, hbe, iha ca ra ha]
                    ring
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [DenseExpr.eval]

/-! ## Enumeration soundness -/

/-- The pointwise-in-domain restriction of `f` is one of the enumerated dense assignments. -/
theorem mem_denseAssignments (doms : List (VarId × List (ZMod p))) (f : VarId → ZMod p)
    (h : ∀ yd ∈ doms, f yd.1 ∈ yd.2) :
    doms.map (fun yd => (yd.1, f yd.1)) ∈ denseAssignments doms := by
  induction doms with
  | nil => simp [denseAssignments]
  | cons yd rest ih =>
      obtain ⟨x, d⟩ := yd
      simp only [List.map_cons, denseAssignments, List.mem_flatMap]
      refine ⟨rest.map (fun yd => (yd.1, f yd.1)),
              ih (fun yd hyd => h yd (List.mem_cons_of_mem _ hyd)), ?_⟩
      exact List.mem_map.2 ⟨f x, h (x, d) (List.mem_cons_self ..), rfl⟩

/-- On its own variables, the dense restriction environment agrees with `f`. -/
theorem denseEnvOfFast_map (doms : List (VarId × List (ZMod p))) (f : VarId → ZMod p) (y : VarId)
    (hy : y ∈ doms.map Prod.fst) :
    denseEnvOfFast (doms.map (fun yd => (yd.1, f yd.1))) y = f y := by
  induction doms with
  | nil => simp at hy
  | cons yd rest ih =>
      simp only [List.map_cons, denseEnvOfFast]
      by_cases hyx : y = yd.1
      · rw [if_pos (by simp [hyx]), hyx]
      · rw [if_neg (by simpa using hyx)]
        refine ih ?_
        simp only [List.map_cons] at hy
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h hyx
        · exact h

/-! ## Bounds through scaled range checks -/

/-- **`denseScaledSlotBound` is sound.** A slot's affine (unit-coefficient) decomposition plus its
    bus-fact value bound (`facts.slotBound_sound`, applied at the value level) and the enumeration
    of the offset part's finite domains bound `x`. -/
theorem denseScaledSlotBound_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (bi : BusInteraction (DenseExpr p)) (x : VarId)
    (B : Nat) (h : denseScaledSlotBound bs facts domCs bi x = some B) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval denv = 0)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (denv x).val < B := by
  unfold denseScaledSlotBound at h
  cases hmv : bi.multiplicity.constValue? with
  | none => rw [hmv] at h; simp at h
  | some mval =>
    simp only [hmv] at h
    split_ifs at h with hmz
    obtain ⟨slot, _hslot, hs⟩ := List.exists_of_findSome?_eq_some h
    cases hO : bi.payload[slot]? with
    | none => simp [hO] at hs
    | some O =>
      simp only [hO] at hs
      cases hfact : facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot with
      | none => simp [hfact] at hs
      | some bound =>
        simp only [hfact] at hs
        cases hlin : O.splitAt x with
        | none => simp [hlin] at hs
        | some kR =>
          obtain ⟨k, R⟩ := kR
          simp only [hlin] at hs
          split_ifs at hs with hcond hwrap
          simp only [Option.some.injEq] at hs
          obtain ⟨hunit, hcover, _hcap⟩ := hcond
          have hmeval : (denseBIEval bi denv).multiplicity = mval :=
            bi.multiplicity.constValue?_sound mval hmv denv
          have hviol : bs.violatesConstraint (denseBIEval bi denv) = false :=
            hob (by rw [hmeval]; exact hmz)
          have hget : (denseBIEval bi denv).payload[slot]? = some (O.eval denv) := by
            show (bi.payload.map (fun e => e.eval denv))[slot]? = _
            rw [List.getElem?_map, hO]; rfl
          have hOb : (O.eval denv).val < bound := by
            have hfact' : facts.slotBound (denseBIEval bi denv).busId
                (denseBIEval bi denv).multiplicity (bi.payload.map DenseExpr.constValue?) slot
                = some bound := by
              rw [(rfl : (denseBIEval bi denv).busId = bi.busId), hmeval]; exact hfact
            exact facts.slotBound_sound (denseBIEval bi denv)
              (bi.payload.map DenseExpr.constValue?) slot bound (O.eval denv) hfact'
              (denseMatches_evalPattern bi.payload denv) hviol hget
          set m := k⁻¹ with hm
          have hOx : O.eval denv = k * denv x + R.eval denv :=
            DenseExpr.splitAt_eval x O k R hlin denv
          have hxid : denv x = m * O.eval denv + (-m) * R.eval denv := by
            have hh : m * O.eval denv = m * k * denv x + m * R.eval denv := by rw [hOx]; ring
            rw [mul_comm m k] at hh
            rw [hunit, one_mul] at hh
            linear_combination -hh
          have hmemdoms : ∀ vd ∈ R.vars.eraseDups.filterMap (fun v =>
              (denseFindDomainAlg domCs v).map (fun d => (v, d))), denv vd.1 ∈ vd.2 := by
            intro vd hvd
            obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
            cases hfd : denseFindDomainAlg domCs v with
            | none => rw [hfd] at hvd'; simp at hvd'
            | some d =>
              rw [hfd] at hvd'
              simp only [Option.map_some, Option.some.injEq] at hvd'
              obtain rfl := hvd'.symm
              exact denseFindDomainAlg_sound denv domCs v d hfd hdom
          have hpt := mem_denseAssignments (R.vars.eraseDups.filterMap (fun v =>
            (denseFindDomainAlg domCs v).map (fun d => (v, d)))) denv hmemdoms
          have hWagree : R.eval (denseEnvOfFast ((R.vars.eraseDups.filterMap (fun v =>
              (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map
                (fun vd => (vd.1, denv vd.1)))) = R.eval denv := by
            refine DenseExpr.eval_congr R _ denv (fun v hv => ?_)
            refine denseEnvOfFast_map _ denv v ?_
            rw [show ((R.vars.eraseDups.filterMap (fun v =>
              (denseFindDomainAlg domCs v).map (fun d => (v, d)))).map Prod.fst)
              = R.vars.eraseDups from hcover]
            exact List.mem_eraseDups.2 hv
          have hWle : ((-m) * R.eval denv).val
              ≤ ((denseAssignments (R.vars.eraseDups.filterMap (fun v =>
                (denseFindDomainAlg domCs v).map (fun d => (v, d))))).map
                  (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 := by
            refine le_foldl_max _ 0 _ ?_
            refine List.mem_map.2 ⟨_, hpt, ?_⟩
            rw [hWagree]
          have hu : (m * O.eval denv).val = m.val * (O.eval denv).val := by
            refine ZMod.val_mul_of_lt ?_
            calc m.val * (O.eval denv).val ≤ m.val * (bound - 1) := by
                  exact Nat.mul_le_mul_left _ (by omega)
              _ < p := by omega
          have hsum : (m * O.eval denv).val + ((-m) * R.eval denv).val < p := by
            rw [hu]
            have h1 : m.val * (O.eval denv).val ≤ m.val * (bound - 1) :=
              Nat.mul_le_mul_left _ (by omega)
            omega
          rw [hxid, ZMod.val_add_of_lt hsum, hu]
          have h1 : m.val * (O.eval denv).val ≤ m.val * (bound - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega

/-! ## `findVarBound` / `anyVarBound` soundness -/

/-- **`denseFindVarBound` is sound**, folding `denseInteractionBound_sound` over the interaction
    list. -/
theorem denseFindVarBound_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (x : VarId) (bound : Nat)
    (h : denseFindVarBound bs facts bis x = some bound) (denv : VarId → ZMod p)
    (hbus : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) : (denv x).val < bound := by
  induction bis with
  | nil => exact absurd h (by simp [denseFindVarBound])
  | cons bi rest ih =>
    rw [denseFindVarBound] at h
    cases hr : denseInteractionBound bs facts bi x with
    | some bound' =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        exact h ▸ denseInteractionBound_sound bs facts bi x bound' hr denv
          (hbus bi (List.mem_cons_self ..))
    | none =>
        rw [hr] at h
        exact ih h (fun bi' hbi' => hbus bi' (List.mem_cons_of_mem _ hbi'))

/-- **`denseAnyVarBound` is sound.** -/
theorem denseAnyVarBound_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (x : VarId) (B : Nat) (h : denseAnyVarBound bs facts bis domCs x = some B)
    (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval denv = 0)
    (hbus : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) : (denv x).val < B := by
  unfold denseAnyVarBound at h
  cases hfb : denseFindVarBound bs facts bis x with
  | some B' =>
    simp only [hfb, Option.some.injEq] at h
    exact h ▸ denseFindVarBound_sound bs facts bis x B' hfb denv hbus
  | none =>
    simp only [hfb] at h
    obtain ⟨bi, hbi, hsb⟩ := List.exists_of_findSome?_eq_some h
    exact denseScaledSlotBound_sound bs facts domCs bi x B hsb denv hdom (hbus bi hbi)

/-! ## The pair certificate is sound -/

/-- **`denseRpCheckPair` entails variable equality.** Two-root twins with both variables
    range-bounded below the root gap are provably equal on satisfying assignments: the value-level
    two-root soundness `denseTwoRootOf?_sound` places each variable at one of the two roots, and the
    bounded-integer field core `rootPair_eq` forces the shared choice. -/
theorem denseRpCheckPair_sound [Fact p.Prime] (bs : BusSemantics p)
    (facts : BusFacts p bs) (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (cX cY : DenseExpr p) (x y : VarId)
    (h : denseRpCheckPair bs facts bis domCs cX cY x y = true) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval denv = 0)
    (hcXe : cX.eval denv = 0) (hcYe : cY.eval denv = 0)
    (hbus : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    denv x = denv y := by
  unfold denseRpCheckPair at h
  cases hxt : denseTwoRootOf? cX x with
  | none => rw [hxt] at h; simp at h
  | some t =>
    obtain ⟨k, A, δ⟩ := t
    cases hyt : denseTwoRootOf? cY y with
    | none => rw [hxt, hyt] at h; simp at h
    | some t' =>
      obtain ⟨k', A', δ'⟩ := t'
      rw [hxt, hyt] at h
      cases hbx : denseAnyVarBound bs facts bis domCs x with
      | none => rw [hbx] at h; simp at h
      | some Bx =>
        cases hby : denseAnyVarBound bs facts bis domCs y with
        | none => rw [hbx, hby] at h; simp at h
        | some By =>
          rw [hbx, hby] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨⟨⟨⟨hk', hAt⟩, hAc⟩, hδ'⟩, hunit⟩, _hxv⟩, _hyv⟩, hB1, hB2⟩ := h
          have hxr := denseTwoRootOf?_sound cX x k A δ hxt hunit denv hcXe
          have hyr := denseTwoRootOf?_sound cY y k' A' δ' hyt (by rw [hk']; exact hunit)
            denv hcYe
          have hAeq : A'.eval denv = A.eval denv := by
            rw [DenseLinExpr.eval_of_terms_eq A A' hAt denv, hAc]; ring
          rw [hk', hAeq, hδ'] at hyr
          exact rootPair_eq (-(k⁻¹ * A.eval denv)) (k⁻¹ * δ) (denv x) (denv y) hxr hyr
            (max Bx By)
            (lt_of_lt_of_le (denseAnyVarBound_sound bs facts bis domCs x Bx hbx denv hdom hbus)
              (le_max_left _ _))
            (lt_of_lt_of_le (denseAnyVarBound_sound bs facts bis domCs y By hby denv hdom hbus)
              (le_max_right _ _))
            hB1 hB2

/-- Extract the variable memberships from a passed certificate. -/
theorem denseRpCheckPair_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (cX cY : DenseExpr p) (x y : VarId)
    (h : denseRpCheckPair bs facts bis domCs cX cY x y = true) : x ∈ cX.vars ∧ y ∈ cY.vars := by
  unfold denseRpCheckPair at h
  cases hxt : denseTwoRootOf? cX x with
  | none => rw [hxt] at h; simp at h
  | some t =>
    obtain ⟨k, A, δ⟩ := t
    cases hyt : denseTwoRootOf? cY y with
    | none => rw [hxt, hyt] at h; simp at h
    | some t' =>
      obtain ⟨k', A', δ'⟩ := t'
      rw [hxt, hyt] at h
      cases hbx : denseAnyVarBound bs facts bis domCs x with
      | none => rw [hbx] at h; simp at h
      | some Bx =>
        cases hby : denseAnyVarBound bs facts bis domCs y with
        | none => rw [hbx, hby] at h; simp at h
        | some By =>
          rw [hbx, hby] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨h.1.1.2, h.1.2⟩

/-! ## The scan-loop invariant

Structural induction over the pending constraints threading `DenseSolved`. Maintained: (a) every
stored solution is entailed by satisfaction, (b) every stored solution is occurrence-closed, and
every `seen` constraint is one of `d`'s (recovering the membership `DenseRPSeen` omits). -/

/-- The `seen`-bucket invariant is preserved by `denseRpInsertAll`: if every bucketed and every
    inserted entry's constraint is in `S`, then so is every entry of any bucket afterwards. -/
theorem denseRpInsertAll_seen {S : List (DenseExpr p)} :
    ∀ (es : List (DenseRPSeen p)) (seen : Std.HashMap UInt64 (List (DenseRPSeen p))),
      (∀ hsh e, e ∈ seen.getD hsh [] → e.c ∈ S) → (∀ e ∈ es, e.c ∈ S) →
      ∀ hsh e, e ∈ (denseRpInsertAll seen es).getD hsh [] → e.c ∈ S := by
  intro es
  induction es with
  | nil => intro seen hseen _ hsh e hmem; exact hseen hsh e hmem
  | cons e0 rest ih =>
      intro seen hseen hes hsh e hmem
      have hacc : ∀ hsh' e', e' ∈ (denseRpInsertAll seen rest).getD hsh' [] → e'.c ∈ S :=
        ih seen hseen (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
      have hstep : denseRpInsertAll seen (e0 :: rest)
          = (denseRpInsertAll seen rest).insert (denseRpKeyHash e0.key)
              (e0 :: (denseRpInsertAll seen rest).getD (denseRpKeyHash e0.key) []) := by
        simp only [denseRpInsertAll, List.foldr_cons]
      rw [hstep, Std.HashMap.getD_insert] at hmem
      split_ifs at hmem with hk
      · rcases List.mem_cons.1 hmem with rfl | hmem'
        · exact hes e (List.mem_cons_self ..)
        · exact hacc (denseRpKeyHash e0.key) e hmem'
      · exact hacc hsh e hmem

/-- **The scan loop is sound**: the final solution map is entailed (a) and occurrence-closed (b).
    The certificate (`denseRpCheckPair_sound`) forces each adopted `x = y` on satisfying
    assignments; the bucketed `seen` scan is proof-free, its membership recovered by
    `denseRpInsertAll_seen`. -/
theorem denseRpLoop_sound [Fact p.Prime] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    ∀ (pending : List (DenseExpr p)) (seen : Std.HashMap UInt64 (List (DenseRPSeen p)))
      (σ : DenseSolved p),
      (∀ c ∈ pending, c ∈ d.algebraicConstraints) →
      (∀ hsh e, e ∈ seen.getD hsh [] → e.c ∈ d.algebraicConstraints) →
      (∀ denv, d.satisfies bs denv → ∀ i t, σ.fn i = some t → denv i = t.eval denv) →
      (∀ i t, σ.fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
          (denseRpLoop bs facts d.busInteractions d.algebraicConstraints pending seen σ).fn i
            = some t → denv i = t.eval denv) ∧
      (∀ i t, (denseRpLoop bs facts d.busInteractions d.algebraicConstraints pending seen σ).fn i
          = some t → ∀ z ∈ t.vars, z ∈ d.occ) := by
  intro pending
  induction pending with
  | nil =>
      intro seen σ _ _ hσs hσv
      exact ⟨hσs, hσv⟩
  | cons c rest ih =>
      intro seen σ hpend hseen hσs hσv
      have hcmem : c ∈ d.algebraicConstraints := hpend c (List.mem_cons_self ..)
      have hrest : ∀ c' ∈ rest, c' ∈ d.algebraicConstraints :=
        fun c' h' => hpend c' (List.mem_cons_of_mem _ h')
      rw [denseRpLoop]
      cases hf : (denseRpCandidates c).findSome? (fun xk =>
          (seen.getD (denseRpKeyHash xk.2) []).findSome? (fun e =>
            if e.key == xk.2 && e.x != xk.1 &&
                denseRpCheckPair bs facts d.busInteractions d.algebraicConstraints e.c c e.x xk.1
            then some (e, xk.1) else none)) with
      | none =>
          simp only []
          refine ih _ σ hrest ?_ hσs hσv
          refine denseRpInsertAll_seen _ seen hseen ?_
          intro e he
          obtain ⟨xk, _hxk, rfl⟩ := List.mem_map.1 he
          exact hcmem
      | some ex =>
          simp only []
          obtain ⟨xk, _hxkmem, hinner⟩ := List.exists_of_findSome?_eq_some hf
          obtain ⟨e, hemem, hif⟩ := List.exists_of_findSome?_eq_some hinner
          by_cases hcnd : (e.key == xk.2 && e.x != xk.1 &&
              denseRpCheckPair bs facts d.busInteractions d.algebraicConstraints e.c c e.x xk.1)
              = true
          · rw [if_pos hcnd] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd
            have hcert : denseRpCheckPair bs facts d.busInteractions d.algebraicConstraints
                e.c c e.x xk.1 = true := hcnd.2
            have hecmem : e.c ∈ d.algebraicConstraints := hseen (denseRpKeyHash xk.2) e hemem
            obtain ⟨hexv, _hxkv⟩ := denseRpCheckPair_vars bs facts d.busInteractions
              d.algebraicConstraints e.c c e.x xk.1 hcert
            have hexocc : e.x ∈ d.occ := DenseConstraintSystem.mem_occ_of_constraint hecmem hexv
            have hfn : ∀ i, (σ.insertAll [((e, xk.1).2, DenseExpr.var (e, xk.1).1.x)]).fn i
                = (σ.map.insert xk.1 (DenseExpr.var e.x))[i]? := by
              intro i
              show (σ.insertAll [(xk.1, DenseExpr.var e.x)]).map[i]? = _
              rw [DenseSolved.insertAll_map]; rfl
            refine ih _ _ hrest ?_ ?_ ?_
            · -- `seen` invariant preservation
              refine denseRpInsertAll_seen _ seen hseen ?_
              intro e' he'
              obtain ⟨xk', _hxk', rfl⟩ := List.mem_map.1 he'
              exact hcmem
            · -- (a) entailment of the updated map
              intro denv hsat i t hti
              rw [hfn, Std.HashMap.getElem?_insert] at hti
              split_ifs at hti with hik
              · have hi : xk.1 = i := by simpa using hik
                simp only [Option.some.injEq] at hti
                subst hti
                subst hi
                have heq := denseRpCheckPair_sound bs facts d.busInteractions
                  d.algebraicConstraints e.c c e.x xk.1 hcert denv
                  hsat.1 (hsat.1 e.c hecmem) (hsat.1 c hcmem) hsat.2
                show denv xk.1 = denv e.x
                exact heq.symm
              · exact hσs denv hsat i t hti
            · -- (b) occurrence closure of the updated map
              intro i t hti z hz
              rw [hfn, Std.HashMap.getElem?_insert] at hti
              split_ifs at hti with hik
              · simp only [Option.some.injEq] at hti
                subst hti
                simp only [DenseExpr.vars, List.mem_singleton] at hz
                subst hz
                exact hexocc
              · exact hσv i t hti z hz
          · rw [if_neg hcnd] at hif
            exact absurd hif (by simp)

/-! ## The dense `rootPairUnify` pass -/

/-- The dense `rootPairUnify` transform re-expressed with the loop's solution map named, for the
    correctness/coverage proofs. -/
theorem denseRootPairUnifyF_eq (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseRootPairUnifyF pw bs facts d
      = (if pw.isPrime = true then
          (if (denseRpLoop bs facts d.busInteractions d.algebraicConstraints
                d.algebraicConstraints ∅ DenseSolved.empty).map.isEmpty then d
           else d.substF (denseRpLoop bs facts d.busInteractions d.algebraicConstraints
                d.algebraicConstraints ∅ DenseSolved.empty).fn)
         else d) := rfl

/-- The final loop solution map is entailed and occurrence-closed (specializing `denseRpLoop_sound`
    to the pass's initial `∅`/`empty` accumulators). -/
theorem denseRootPairUnify_loop_invariant [Fact p.Prime] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseRpLoop bs facts d.busInteractions d.algebraicConstraints d.algebraicConstraints ∅
          DenseSolved.empty).fn i = some t → denv i = t.eval denv) ∧
    (∀ i t, (denseRpLoop bs facts d.busInteractions d.algebraicConstraints d.algebraicConstraints ∅
        DenseSolved.empty).fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) := by
  refine denseRpLoop_sound bs facts d d.algebraicConstraints ∅ DenseSolved.empty
    (fun _ h => h) ?_ ?_ ?_
  · intro hsh e hmem
    rw [Std.HashMap.getD_empty] at hmem
    exact absurd hmem (by simp)
  · intro denv _ i t hti
    exact absurd hti (by simp [DenseSolved.fn, DenseSolved.empty])
  · intro i t hti
    exact absurd hti (by simp [DenseSolved.fn, DenseSolved.empty])

theorem denseRootPairUnifyF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseRootPairUnifyF pw bs facts d).CoveredBy reg := by
  rw [denseRootPairUnifyF_eq]
  split_ifs with hp hempty
  · exact hcov
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    refine DenseConstraintSystem.substF_covered hcov ?_
    intro i _ t hti z hz
    exact DenseConstraintSystem.occ_valid hcov z
      ((denseRootPairUnify_loop_invariant bs facts d).2 i t hti z hz)
  · exact hcov

theorem denseRootPairUnifyF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (_hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseRootPairUnifyF pw bs facts d) [] bs := by
  rw [denseRootPairUnifyF_eq]
  split_ifs with hp hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    have hinv := denseRootPairUnify_loop_invariant bs facts d
    exact DenseConstraintSystem.substF_denseCorrect d _ bs reg.isInput
      (fun denv hsat i t hti => hinv.1 denv hsat i t hti)
      (fun i t hti z hz => hinv.2 i t hti z hz)
  · exact DensePassCorrect.refl reg.isInput d bs

/-- The dense `rootPairUnify` pass (see `denseRootPairUnifyF`). -/
def denseRootPairUnifyPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (denseRootPairUnifyF pw) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseRootPairUnifyF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseRootPairUnifyF_correct pw reg bs facts d hcov)

end ApcOptimizer.Dense
