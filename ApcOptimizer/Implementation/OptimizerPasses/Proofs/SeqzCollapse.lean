import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapse
import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapseCore
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.HintCollapse

set_option autoImplicit false

/-! # Collapsing the `sltu x, 1` (seqz) gadget — correctness proof

`DensePassCorrect` for the dense `seqzCollapse` port (`SeqzCollapse.lean`), over `Bridge.lean`'s
dense semantics. The representation-independent value-level engines (`seqz_forward`,
`seqz_reconstruct`, and the byte/bus facts) come from `SeqzCollapseCore.lean`; freshness and
registry helpers from `Proofs/HintCollapse.lean`; byte bounds from `denseBuild_sound`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense expression evaluation congruence (file-local) -/

private theorem scEvalCongr (e : DenseExpr p) (d1 d2 : VarId → ZMod p)
    (h : ∀ i ∈ e.vars, d1 i = d2 i) : e.eval d1 = e.eval d2 := by
  induction e with
  | const n => rfl
  | var i => exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
      simp only [DenseExpr.eval]
      rw [iha (fun i hi => h i (by simp [DenseExpr.vars, hi])),
          ihb (fun i hi => h i (by simp [DenseExpr.vars, hi]))]
  | mul a b iha ihb =>
      simp only [DenseExpr.eval]
      rw [iha (fun i hi => h i (by simp [DenseExpr.vars, hi])),
          ihb (fun i hi => h i (by simp [DenseExpr.vars, hi]))]

private theorem scDCMEvalCongr (cm : DenseComputationMethod p) (e1 e2 : VarId → ZMod p)
    (h : ∀ i ∈ cm.vars, e1 i = e2 i) : cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => rfl
  | quotientOrZero num den =>
      have hn : num.eval e1 = num.eval e2 :=
        scEvalCongr num _ _ (fun i hi => h i (List.mem_append_left _ hi))
      have hd : den.eval e1 = den.eval e2 :=
        scEvalCongr den _ _ (fun i hi => h i (List.mem_append_right _ hi))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      have hc : cond.eval e1 = cond.eval e2 :=
        scEvalCongr cond _ _ (fun i hi => h i (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hi)))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, iht (fun i hi => h i (by
            simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hi))),
          ihe (fun i hi => h i (by
            simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inr hi))]

/-! ## Bridging the constraint templates and their value forms -/

/-- The 14 gadget constraints all hold at `g` iff the 14 value equations do. -/
theorem denseClusterEval_iff (m3 m2 m1 m0 dv R a3 a2 a1 a0 : VarId) (K : ZMod p)
    (g : VarId → ZMod p) :
    (∀ c ∈ denseSeqzClusterConstraints m3 m2 m1 m0 dv R a3 a2 a1 a0 K, c.eval g = 0) ↔
      (g m3 * (g m3 - 1) = 0 ∧
        (g m3 - 1) * (g a3 * (K + g R)) = 0 ∧
        g m3 * (g dv + g a3 * (2 * g R - 1)) = 0 ∧
        g m2 * (g m2 - 1) = 0 ∧
        (g m3 + g m2 - 1) * (g a2 * (K + g R)) = 0 ∧
        g m2 * (g dv + g a2 * (2 * g R - 1)) = 0 ∧
        g m1 * (g m1 - 1) = 0 ∧
        (g m3 + g m2 + g m1 - 1) * (g a1 * (K + g R)) = 0 ∧
        g m1 * (g dv + g a1 * (2 * g R - 1)) = 0 ∧
        g m0 * (g m0 - 1) = 0 ∧
        (g m3 + g m2 + g m1 + g m0 - 1) * ((g a0 - 1) * (K + g R)) = 0 ∧
        g m0 * (g dv + (g a0 - 1) * (2 * g R - 1)) = 0 ∧
        (g m3 + g m2 + g m1 + g m0) * (g m3 + g m2 + g m1 + g m0 - 1) = 0 ∧
        (g m3 + g m2 + g m1 + g m0 - 1) * g R = 0) := by
  simp only [denseSeqzClusterConstraints, List.forall_mem_cons,
    DenseExpr.eval, denseSeqzEM1, denseSeqzE1, denseSeqzE2, denseSeqzSExpr,
    denseSeqzMarkerSum, denseSeqzKrExpr, denseSeqzTwoRExpr, denseSeqzDiffInner, denseSeqzDiffInner0]
  constructor
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, -⟩
    exact ⟨by linear_combination c1, by linear_combination c2, by linear_combination c3,
      by linear_combination c4, by linear_combination c5, by linear_combination c6,
      by linear_combination c7, by linear_combination c8, by linear_combination c9,
      by linear_combination c10, by linear_combination c11, by linear_combination c12,
      by linear_combination c13, by linear_combination c14⟩
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩
    exact ⟨by linear_combination c1, by linear_combination c2, by linear_combination c3,
      by linear_combination c4, by linear_combination c5, by linear_combination c6,
      by linear_combination c7, by linear_combination c8, by linear_combination c9,
      by linear_combination c10, by linear_combination c11, by linear_combination c12,
      by linear_combination c13, by linear_combination c14, by simp⟩

/-! ## Reassigning the five private witnesses -/

/-- Reassign the five private witnesses to given values, leaving everything else at `env`. -/
def denseSetFive (m3 m2 m1 m0 dv : VarId) (v3 v2 v1 v0 vd : ZMod p) (env : VarId → ZMod p) :
    VarId → ZMod p :=
  fun x => if x = m3 then v3 else if x = m2 then v2 else if x = m1 then v1
    else if x = m0 then v0 else if x = dv then vd else env x

theorem denseSetFive_free {m3 m2 m1 m0 dv : VarId} {v3 v2 v1 v0 vd : ZMod p}
    {env : VarId → ZMod p} {x : VarId}
    (h3 : x ≠ m3) (h2 : x ≠ m2) (h1 : x ≠ m1) (h0 : x ≠ m0) (hd : x ≠ dv) :
    denseSetFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env x = env x := by
  simp only [denseSetFive, if_neg h3, if_neg h2, if_neg h1, if_neg h0, if_neg hd]

theorem denseSetFive_at3 {m3 m2 m1 m0 dv : VarId} {v3 v2 v1 v0 vd : ZMod p}
    {env : VarId → ZMod p} :
    denseSetFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m3 = v3 := by
  simp only [denseSetFive, if_true]

theorem denseSetFive_at2 {m3 m2 m1 m0 dv : VarId} {v3 v2 v1 v0 vd : ZMod p}
    {env : VarId → ZMod p} (h32 : m2 ≠ m3) :
    denseSetFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m2 = v2 := by
  simp only [denseSetFive, if_neg h32, if_true]

theorem denseSetFive_at1 {m3 m2 m1 m0 dv : VarId} {v3 v2 v1 v0 vd : ZMod p}
    {env : VarId → ZMod p} (h31 : m1 ≠ m3) (h21 : m1 ≠ m2) :
    denseSetFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m1 = v1 := by
  simp only [denseSetFive, if_neg h31, if_neg h21, if_true]

theorem denseSetFive_at0 {m3 m2 m1 m0 dv : VarId} {v3 v2 v1 v0 vd : ZMod p}
    {env : VarId → ZMod p} (h30 : m0 ≠ m3) (h20 : m0 ≠ m2) (h10 : m0 ≠ m1) :
    denseSetFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m0 = v0 := by
  simp only [denseSetFive, if_neg h30, if_neg h20, if_neg h10, if_true]

theorem denseSetFive_atd {m3 m2 m1 m0 dv : VarId} {v3 v2 v1 v0 vd : ZMod p}
    {env : VarId → ZMod p} (h3d : dv ≠ m3) (h2d : dv ≠ m2) (h1d : dv ≠ m1) (h0d : dv ≠ m0) :
    denseSetFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env dv = vd := by
  simp only [denseSetFive, if_neg h3d, if_neg h2d, if_neg h1d, if_neg h0d, if_true]

/-! ## Filter/drop list helpers (side effects & admissibility) -/

/-- Dropping list elements on which `keep` is false but which are already `sf`-false leaves the
    `sf`-filtered list unchanged. -/
private theorem filter_filter_drop {α : Type} (keep sf : α → Bool) (L : List α)
    (h : ∀ a ∈ L, keep a = false → sf a = false) :
    (L.filter keep).filter sf = L.filter sf := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      have hrest := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      by_cases hk : keep a = true
      · rw [List.filter_cons_of_pos hk]
        by_cases hs : sf a = true
        · rw [List.filter_cons_of_pos hs, List.filter_cons_of_pos hs, hrest]
        · rw [List.filter_cons_of_neg (by simpa using hs),
              List.filter_cons_of_neg (by simpa using hs), hrest]
      · have hs : sf a = false := h a (List.mem_cons_self ..) (by simpa using hk)
        rw [List.filter_cons_of_neg hk, List.filter_cons_of_neg (by simp [hs]), hrest]

/-- Same drop, through a `map` and a downstream `cond` filter: dropped elements are `cond`-false
    after `g`, so the map-then-filter is unchanged. -/
private theorem filter_map_filter_drop {α β : Type} (keep : α → Bool) (g : α → β) (cond : β → Bool)
    (L : List α) (h : ∀ a ∈ L, keep a = false → cond (g a) = false) :
    ((L.filter keep).map g).filter cond = (L.map g).filter cond := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      have hrest := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      by_cases hk : keep a = true
      · rw [List.filter_cons_of_pos hk, List.map_cons, List.map_cons]
        by_cases hc : cond (g a) = true
        · rw [List.filter_cons_of_pos hc, List.filter_cons_of_pos hc, hrest]
        · rw [List.filter_cons_of_neg (by simpa using hc),
              List.filter_cons_of_neg (by simpa using hc), hrest]
      · have hc : cond (g a) = false := h a (List.mem_cons_self ..) (by simpa using hk)
        rw [List.filter_cons_of_neg hk, List.map_cons, List.filter_cons_of_neg (by simp [hc]), hrest]

/-! ## Correctness of the collapse -/

set_option maxHeartbeats 1600000 in
/-- The collapse is `DensePassCorrect`: soundness reconstructs the marker witnesses via
    `seqz_reconstruct`; completeness derives the is-zero constraints via `seqz_forward`, computing
    `inv` by `QuotientOrZero`. Proved directly over `VarId → ZMod p`. -/
theorem dense_seqzCollapse_correct [Fact p.Prime] (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (r : DenseSeqzRoles p) (spec : ByteXorSpec p) (invId : VarId)
    (hspec : facts.byteXorSpec r.busId = some spec)
    (h1024 : 1024 ≤ p) (hK : 2 * r.K + 1 = 0) (hbound : spec.bound = 256)
    (hbusMem : denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec ∈ d.busInteractions)
    (hclMem : ∀ c ∈ denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K,
      c ∈ d.algebraicConstraints)
    (hboolMem : denseSeqzBoolConstraint r.R ∈ d.algebraicConstraints)
    (hboolNC : denseSeqzBoolConstraint r.R ∉
      denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K)
    (hpure : ∀ w ∈ r.witnesses, denseSeqzPureInCluster d
      (denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K)
      (denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec) w = true)
    (habyteAll : ∀ (denv : VarId → ZMod p),
      (∀ bi ∈ (denseSeqzCollapsedSystem d r invId spec).busInteractions,
        (denseBIEval bi denv).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi denv) = false) →
      ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List VarId), (denv a).val < 256)
    (hnodup : ([r.R, r.a0, r.a1, r.a2, r.a3, r.m3, r.m2, r.m1, r.m0, r.dv] : List VarId).Nodup)
    (hinv_fresh : invId ∉ d.occ) (hinv_id : isInput invId = false)
    (hpow5 : ∀ v ∈ ([r.R, r.a0, r.a1, r.a2, r.a3] : List VarId), isInput v = true) :
    DensePassCorrect isInput d (denseSeqzCollapsedSystem d r invId spec)
      [(invId, denseSeqzInvMethod r.R r.a0 r.a1 r.a2 r.a3)] bs := by
  haveI : NeZero p := ⟨by omega⟩
  have hpowR : isInput r.R = true := hpow5 r.R (by simp)
  have hpowa : ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List VarId), isInput a = true :=
    fun a ha => hpow5 a (List.mem_cons_of_mem r.R ha)
  set cl := denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K
    with hcldef
  set busE := denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec with hbusEdef
  set out := denseSeqzCollapsedSystem d r invId spec with houtdef
  set method : DenseComputationMethod p := denseSeqzInvMethod r.R r.a0 r.a1 r.a2 r.a3 with hmethoddef
  have hbusStateless : bs.isStateful r.busId = false := (facts.byteXorSpec_sound r.busId spec hspec).1
  have hdisj : ∀ x ∈ ([r.R, r.a0, r.a1, r.a2, r.a3] : List VarId), x ∉ r.witnesses := by
    have hnd : (([r.R, r.a0, r.a1, r.a2, r.a3] : List VarId) ++ r.witnesses).Nodup := hnodup
    have hpw := (List.nodup_append.mp hnd).2.2
    exact fun x hx hxw => hpw x hx x hxw rfl
  have hRw : ∀ w ∈ r.witnesses, r.R ≠ w := fun w hw h => hdisj r.R (by simp) (h ▸ hw)
  have ha0w : ∀ w ∈ r.witnesses, r.a0 ≠ w := fun w hw h => hdisj r.a0 (by simp) (h ▸ hw)
  have ha1w : ∀ w ∈ r.witnesses, r.a1 ≠ w := fun w hw h => hdisj r.a1 (by simp) (h ▸ hw)
  have ha2w : ∀ w ∈ r.witnesses, r.a2 ≠ w := fun w hw h => hdisj r.a2 (by simp) (h ▸ hw)
  have ha3w : ∀ w ∈ r.witnesses, r.a3 ≠ w := fun w hw h => hdisj r.a3 (by simp) (h ▸ hw)
  have hwmem : ∀ w ∈ ([r.m3, r.m2, r.m1, r.m0, r.dv] : List VarId), w ∈ r.witnesses := by
    intro w hw; simpa [DenseSeqzRoles.witnesses] using hw
  have hboolOut : denseSeqzBoolConstraint r.R ∈ out.algebraicConstraints := by
    rw [houtdef, denseSeqzCollapsedSystem]
    refine List.mem_append_left _ (List.mem_filter.2 ⟨hboolMem, ?_⟩)
    simpa using hboolNC
  have hncOut : ∀ c ∈ denseSeqzNewConstraints r.R r.a0 r.a1 r.a2 r.a3 invId,
      c ∈ out.algebraicConstraints := by
    intro c hc; rw [houtdef, denseSeqzCollapsedSystem]; exact List.mem_append_right _ hc
  have hpureC : ∀ w ∈ r.witnesses, ∀ c ∈ d.algebraicConstraints, c ∉ cl → w ∉ c.vars := by
    intro w hw c hc hccl
    have hp := hpure w hw
    simp only [denseSeqzPureInCluster, Bool.and_eq_true, List.all_eq_true] at hp
    have hcc := hp.1 c hc
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcc
    rcases hcc with h | h
    · exact absurd (by simpa using h) hccl
    · exact denseMentions_false_not_mem w c h
  have hpureB : ∀ w ∈ r.witnesses, ∀ bi ∈ d.busInteractions, bi ≠ busE →
      w ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, w ∉ e.vars := by
    intro w hw bi hbi hbne
    have hp := hpure w hw
    simp only [denseSeqzPureInCluster, Bool.and_eq_true, List.all_eq_true] at hp
    have hbb := hp.2 bi hbi
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true] at hbb
    rcases hbb with h | ⟨hm, hpay⟩
    · exact absurd h hbne
    · exact ⟨denseMentions_false_not_mem w bi.multiplicity hm,
        fun e he => denseMentions_false_not_mem w e (hpay e he)⟩
  have wm3 : r.m3 ∈ r.witnesses := hwmem r.m3 (by simp)
  have wm2 : r.m2 ∈ r.witnesses := hwmem r.m2 (by simp)
  have wm1 : r.m1 ∈ r.witnesses := hwmem r.m1 (by simp)
  have wm0 : r.m0 ∈ r.witnesses := hwmem r.m0 (by simp)
  have wdv : r.dv ∈ r.witnesses := hwmem r.dv (by simp)
  have hwnd : r.witnesses.Nodup :=
    (List.nodup_append.mp
      (show (([r.R, r.a0, r.a1, r.a2, r.a3] : List VarId) ++ r.witnesses).Nodup from hnodup)).2.1
  simp only [DenseSeqzRoles.witnesses, List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, List.nodup_nil, and_true, or_false] at hwnd
  obtain ⟨⟨d32, d31, d30, d3d⟩, ⟨d21, d20, d2d⟩, ⟨d10, d1d⟩, d0d, -⟩ := hwnd
  -- `R, a0..a3` are occurrences of `d` (anchors for `inv`-framing / output occurrences).
  have hRocc : r.R ∈ d.occ :=
    DenseConstraintSystem.mem_occ_of_constraint hboolMem
      (by simp [denseSeqzBoolConstraint, DenseExpr.vars, denseSeqzEM1])
  have ha3occ : r.a3 ∈ d.occ :=
    DenseConstraintSystem.mem_occ_of_constraint
      (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 3) (.mul (.var r.a3) (denseSeqzKrExpr r.K r.R)))
        (by rw [hcldef]; simp [denseSeqzClusterConstraints]))
      (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
  have ha2occ : r.a2 ∈ d.occ :=
    DenseConstraintSystem.mem_occ_of_constraint
      (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 2) (.mul (.var r.a2) (denseSeqzKrExpr r.K r.R)))
        (by rw [hcldef]; simp [denseSeqzClusterConstraints]))
      (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
  have ha1occ : r.a1 ∈ d.occ :=
    DenseConstraintSystem.mem_occ_of_constraint
      (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 1) (.mul (.var r.a1) (denseSeqzKrExpr r.K r.R)))
        (by rw [hcldef]; simp [denseSeqzClusterConstraints]))
      (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
  have ha0occ : r.a0 ∈ d.occ :=
    DenseConstraintSystem.mem_occ_of_constraint
      (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 0)
          (.mul (.add denseSeqzEM1 (.var r.a0)) (denseSeqzKrExpr r.K r.R)))
        (by rw [hcldef]; simp [denseSeqzClusterConstraints]))
      (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
  have hacs_mem : ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List VarId), a ∈ d.occ := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ha0occ
    · exact ha1occ
    · exact ha2occ
    · exact ha3occ
  have hstatefulNe : ∀ (bi : BusInteraction (DenseExpr p)),
      bs.isStateful bi.busId = true → bi ≠ busE := by
    intro bi hst h
    rw [h, show busE.busId = r.busId from rfl, hbusStateless] at hst
    exact absurd hst (by decide)
  have hbusEvalAt : ∀ (denv : VarId → ZMod p), denseBIEval busE denv =
      { busId := r.busId, multiplicity := denv r.m3 + denv r.m2 + denv r.m1 + denv r.m0,
        payload := spec.encode spec.pairOp (-1 + denv r.dv) 0 0 } := by
    intro denv
    simp only [hbusEdef, denseSeqzClusterBus, denseBIEval, spec.encode_map, denseSeqzMarkerSum,
      denseSeqzEM1, denseSeqzE0, DenseExpr.eval]
  have hside : ∀ (denv : VarId → ZMod p), out.sideEffects bs denv = d.sideEffects bs denv := by
    intro denv
    simp only [houtdef, denseSeqzCollapsedSystem, DenseConstraintSystem.sideEffects, ← hbusEdef]
    rw [filter_filter_drop (fun bi => decide (bi ≠ busE)) (fun bi => bs.isStateful bi.busId)
      d.busInteractions (fun bi _ hkf => by
        have hbe : bi = busE := by simpa using hkf
        simp only [hbe, hbusEdef, denseSeqzClusterBus]
        exact hbusStateless)]
  -- Soundness reconstruction: any `out`-satisfying assignment lifts to a `d`-satisfying one.
  have hReconstruct : ∀ env, out.satisfies bs env → ∃ g,
      d.satisfies bs g ∧
      (∀ bi ∈ d.busInteractions, bi ≠ busE → denseBIEval bi g = denseBIEval bi env) ∧
      d.sideEffects bs g = d.sideEffects bs env := by
    intro env hsatOut
    have hb0 := habyteAll env hsatOut.2 r.a0 (by simp)
    have hb1 := habyteAll env hsatOut.2 r.a1 (by simp)
    have hb2 := habyteAll env hsatOut.2 r.a2 (by simp)
    have hb3 := habyteAll env hsatOut.2 r.a3 (by simp)
    have hRbool : env r.R = 0 ∨ env r.R = 1 := by
      have h := hsatOut.1 (denseSeqzBoolConstraint r.R) hboolOut
      simp only [denseSeqzBoolConstraint, denseSeqzEM1, DenseExpr.eval] at h
      exact SeqzCollapse.zbool (by linear_combination h)
    have hRS : env r.R * (env r.a0 + env r.a1 + env r.a2 + env r.a3) = 0 := by
      have h := hsatOut.1 (DenseExpr.mul (.var r.R) (denseSeqzSumExpr4 r.a0 r.a1 r.a2 r.a3))
        (hncOut _ (by simp [denseSeqzNewConstraints]))
      simpa only [denseSeqzSumExpr4, DenseExpr.eval] using h
    have hSR : env r.a0 + env r.a1 + env r.a2 + env r.a3 = 0 → env r.R = 1 := by
      intro hS
      have h := hsatOut.1 (DenseExpr.add (.mul (.var invId) (denseSeqzSumExpr4 r.a0 r.a1 r.a2 r.a3))
        (.add (.var r.R) denseSeqzEM1)) (hncOut _ (by simp [denseSeqzNewConstraints]))
      simp only [denseSeqzSumExpr4, denseSeqzEM1, DenseExpr.eval] at h
      have hz : env r.R + -1 = 0 := by linear_combination h - env invId * hS
      linear_combination hz
    obtain ⟨v0, v1, v2, v3, vd, eB3, eB2, eB1, eB0, eBs, eNM, eP3, eP2, eP1, eP0,
        eD3, eD2, eD1, eD0, eBus⟩ :=
      SeqzCollapse.seqz_reconstruct h1024 r.K (env r.R) (env r.a0) (env r.a1) (env r.a2) (env r.a3)
        hK hb0 hb1 hb2 hb3 hRbool hRS hSR
    set g := denseSetFive r.m3 r.m2 r.m1 r.m0 r.dv v3 v2 v1 v0 vd env with hgdef
    have gm3 : g r.m3 = v3 := denseSetFive_at3
    have gm2 : g r.m2 = v2 := denseSetFive_at2 (Ne.symm d32)
    have gm1 : g r.m1 = v1 := denseSetFive_at1 (Ne.symm d31) (Ne.symm d21)
    have gm0 : g r.m0 = v0 := denseSetFive_at0 (Ne.symm d30) (Ne.symm d20) (Ne.symm d10)
    have gdv : g r.dv = vd := denseSetFive_atd (Ne.symm d3d) (Ne.symm d2d) (Ne.symm d1d) (Ne.symm d0d)
    have ga0 : g r.a0 = env r.a0 :=
      denseSetFive_free (ha0w _ wm3) (ha0w _ wm2) (ha0w _ wm1) (ha0w _ wm0) (ha0w _ wdv)
    have ga1 : g r.a1 = env r.a1 :=
      denseSetFive_free (ha1w _ wm3) (ha1w _ wm2) (ha1w _ wm1) (ha1w _ wm0) (ha1w _ wdv)
    have ga2 : g r.a2 = env r.a2 :=
      denseSetFive_free (ha2w _ wm3) (ha2w _ wm2) (ha2w _ wm1) (ha2w _ wm0) (ha2w _ wdv)
    have ga3 : g r.a3 = env r.a3 :=
      denseSetFive_free (ha3w _ wm3) (ha3w _ wm2) (ha3w _ wm1) (ha3w _ wm0) (ha3w _ wdv)
    have gR : g r.R = env r.R :=
      denseSetFive_free (hRw _ wm3) (hRw _ wm2) (hRw _ wm1) (hRw _ wm0) (hRw _ wdv)
    have hgframeE : ∀ (e : DenseExpr p), (∀ w ∈ r.witnesses, w ∉ e.vars) →
        e.eval g = e.eval env := by
      intro e he
      apply scEvalCongr
      intro x hx
      exact denseSetFive_free (fun h => he r.m3 wm3 (h ▸ hx)) (fun h => he r.m2 wm2 (h ▸ hx))
        (fun h => he r.m1 wm1 (h ▸ hx)) (fun h => he r.m0 wm0 (h ▸ hx))
        (fun h => he r.dv wdv (h ▸ hx))
    have hgframeBus : ∀ bi ∈ d.busInteractions, bi ≠ busE → denseBIEval bi g = denseBIEval bi env := by
      intro bi hbi hne
      have hmul : bi.multiplicity.eval g = bi.multiplicity.eval env :=
        hgframeE bi.multiplicity (fun w hw => (hpureB w hw bi hbi hne).1)
      have hpay : bi.payload.map (fun e => e.eval g) = bi.payload.map (fun e => e.eval env) :=
        List.map_congr_left (fun e he => hgframeE e (fun w hw => (hpureB w hw bi hbi hne).2 e he))
      simp only [denseBIEval, hmul, hpay]
    have hbusEval : denseBIEval busE g =
        { busId := r.busId, multiplicity := v3 + v2 + v1 + v0,
          payload := spec.encode spec.pairOp (-1 + vd) 0 0 } := by
      rw [hbusEvalAt g, gm3, gm2, gm1, gm0, gdv]
    have hclG : ∀ c ∈ cl, c.eval g = 0 := by
      rw [hcldef]
      refine (denseClusterEval_iff r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K g).mpr ?_
      simp only [gm3, gm2, gm1, gm0, gdv, ga0, ga1, ga2, ga3, gR]
      exact ⟨by linear_combination eB3, by linear_combination eP3, by linear_combination eD3,
        by linear_combination eB2, by linear_combination eP2, by linear_combination eD2,
        by linear_combination eB1, by linear_combination eP1, by linear_combination eD1,
        by linear_combination eB0, by linear_combination eP0, by linear_combination eD0,
        by linear_combination eBs, by linear_combination eNM⟩
    have hgcs : d.satisfies bs g := by
      refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
      · by_cases hccl : c ∈ cl
        · exact hclG c hccl
        · have hcout : c ∈ out.algebraicConstraints := by
            rw [houtdef, denseSeqzCollapsedSystem, ← hcldef]
            exact List.mem_append_left _ (List.mem_filter.2 ⟨hc, by simpa using hccl⟩)
          rw [hgframeE c (fun w hw => hpureC w hw c hc hccl)]
          exact hsatOut.1 c hcout
      · by_cases hbe : bi = busE
        · show (denseBIEval bi g).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi g) = false
          rw [hbe, hbusEval]
          intro hmult
          exact SeqzCollapse.bus_accepts_byte_zero facts r.busId spec hspec hbound (-1 + vd)
            (v3 + v2 + v1 + v0) (eBus hmult)
        · have hbout : bi ∈ out.busInteractions := by
            rw [houtdef, denseSeqzCollapsedSystem, ← hbusEdef]
            exact List.mem_filter.2 ⟨hbi, by simpa using hbe⟩
          show (denseBIEval bi g).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi g) = false
          rw [hgframeBus bi hbi hbe]
          exact hsatOut.2 bi hbout
    have hseSound : d.sideEffects bs g = d.sideEffects bs env := by
      simp only [DenseConstraintSystem.sideEffects]
      apply List.map_congr_left
      intro bi hbi
      have hbimem : bi ∈ d.busInteractions := List.mem_of_mem_filter hbi
      have hst : bs.isStateful bi.busId = true := by simpa using List.of_mem_filter hbi
      rw [hgframeBus bi hbimem (hstatefulNe bi hst)]
    exact ⟨g, hgcs, hgframeBus, hseSound⟩
  have hout_occ : ∀ i ∈ out.occ, i = invId ∨ i ∈ d.occ := by
    intro i hi
    rw [hcMemOcc] at hi
    rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
    · rw [houtdef, denseSeqzCollapsedSystem] at hc
      simp only at hc
      rw [List.mem_append] at hc
      rcases hc with hcf | hcnc
      · exact Or.inr (DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hcf) hic)
      · simp only [denseSeqzNewConstraints, List.mem_cons, List.not_mem_nil,
          or_false] at hcnc
        rcases hcnc with rfl | rfl
        · simp only [denseSeqzSumExpr4, DenseExpr.vars, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hic
          rcases hic with rfl | rfl | rfl | rfl | rfl
          · exact Or.inr hRocc
          · exact Or.inr ha0occ
          · exact Or.inr ha1occ
          · exact Or.inr ha2occ
          · exact Or.inr ha3occ
        · simp only [denseSeqzSumExpr4, denseSeqzEM1, DenseExpr.vars, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false,
            or_assoc] at hic
          rcases hic with rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ha0occ
          · exact Or.inr ha1occ
          · exact Or.inr ha2occ
          · exact Or.inr ha3occ
          · exact Or.inr hRocc
    · rw [houtdef, denseSeqzCollapsedSystem] at hbi
      simp only at hbi
      exact Or.inr (DenseConstraintSystem.mem_occ_of_bi (List.mem_of_mem_filter hbi) hib)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- soundness (`out.implies d`)
    intro env hsatOut
    obtain ⟨g, hgcs, _, hse⟩ := hReconstruct env hsatOut
    refine ⟨g, hgcs, ?_⟩
    rw [hse, ← hside env]
    exact BusState.equiv_refl _
  · -- invariant preservation
    intro hdInv env hsatOut bi hbiOut
    show (denseBIEval bi env).multiplicity ≠ 0 → bs.breaksInvariant (denseBIEval bi env) = false
    obtain ⟨g, hgcs, hgfr, _⟩ := hReconstruct env hsatOut
    have hbicsmem : bi ∈ d.busInteractions := by
      have := hbiOut; rw [houtdef, denseSeqzCollapsedSystem] at this
      exact List.mem_of_mem_filter this
    have hbne : bi ≠ busE := by
      have := hbiOut; rw [houtdef, denseSeqzCollapsedSystem, ← hbusEdef] at this
      simpa using (List.of_mem_filter this)
    rw [← hgfr bi hbicsmem hbne]
    exact hdInv g hgcs bi hbicsmem
  · -- no new input (powdr-ID) column
    intro i hiout hisT
    rcases hout_occ i hiout with rfl | hd
    · rw [hinv_id] at hisT; exact absurd hisT (by simp)
    · exact hd
  · -- completeness with derivations
    intro env hadm hsat
    set envC := Function.update env invId (method.eval env) with hCdef
    have hagreeOcc : ∀ i ∈ d.occ, envC i = env i := by
      intro i hi
      refine Function.update_of_ne (fun h => hinv_fresh ?_) _ _
      rw [← h]; exact hi
    have hbeC : ∀ bi ∈ d.busInteractions, denseBIEval bi envC = denseBIEval bi env := by
      intro bi hbi
      refine denseBIEval_congr bi _ _ (fun x hx => ?_)
      exact hagreeOcc x (DenseConstraintSystem.mem_occ_of_bi hbi hx)
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ :=
      (denseClusterEval_iff r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K env).mp
        (fun c hc => hsat.1 c (hclMem c hc))
    have hbusOutEnv : ∀ bi ∈ (denseSeqzCollapsedSystem d r invId spec).busInteractions,
        (denseBIEval bi env).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi env) = false := by
      intro bi hbi hm
      rw [denseSeqzCollapsedSystem] at hbi
      exact hsat.2 bi (List.mem_of_mem_filter hbi) hm
    have hb0 := habyteAll env hbusOutEnv r.a0 (by simp)
    have hb1 := habyteAll env hbusOutEnv r.a1 (by simp)
    have hb2 := habyteAll env hbusOutEnv r.a2 (by simp)
    have hb3 := habyteAll env hbusOutEnv r.a3 (by simp)
    have hRbool : env r.R = 0 ∨ env r.R = 1 := by
      have h := hsat.1 (denseSeqzBoolConstraint r.R) hboolMem
      simp only [denseSeqzBoolConstraint, denseSeqzEM1, DenseExpr.eval] at h
      exact SeqzCollapse.zbool (by linear_combination h)
    have hbusFwd : (env r.m3 + env r.m2 + env r.m1 + env r.m0) ≠ 0 → (-1 + env r.dv).val < 256 := by
      intro hmult
      have hbe := hsat.2 busE hbusMem
      rw [hbusEvalAt env] at hbe
      exact SeqzCollapse.bus_byte_of_accepts facts r.busId spec hspec hbound (-1 + env r.dv) _
        (hbe hmult)
    obtain ⟨hfRS, hfSR⟩ :=
      SeqzCollapse.seqz_forward h1024 r.K (env r.R) (env r.a0) (env r.a1) (env r.a2) (env r.a3)
        (env r.m0) (env r.m1) (env r.m2) (env r.m3) (env r.dv)
        hK hb0 hb1 hb2 hb3 f1 f4 f7 f10 f13 f14 f2 f5 f8 f11 f3 f6 f9 f12 hRbool hbusFwd
    refine ⟨envC, ⟨fun c hc => ?_, fun bi hbi => ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [houtdef, denseSeqzCollapsedSystem, List.mem_append] at hc
      rcases hc with hcf | hcnc
      · have hccs : c ∈ d.algebraicConstraints := List.mem_of_mem_filter hcf
        rw [scEvalCongr c envC env
          (fun x hx => hagreeOcc x (DenseConstraintSystem.mem_occ_of_constraint hccs hx))]
        exact hsat.1 c hccs
      · simp only [denseSeqzNewConstraints, List.mem_cons, List.not_mem_nil,
          or_false] at hcnc
        rcases hcnc with rfl | rfl
        · show DenseExpr.eval (.mul (.var r.R) (denseSeqzSumExpr4 r.a0 r.a1 r.a2 r.a3)) envC = 0
          simp only [denseSeqzSumExpr4, DenseExpr.eval]
          rw [hagreeOcc r.R hRocc, hagreeOcc r.a0 ha0occ, hagreeOcc r.a1 ha1occ,
            hagreeOcc r.a2 ha2occ, hagreeOcc r.a3 ha3occ]
          linear_combination hfRS
        · show DenseExpr.eval
            (.add (.mul (.var invId) (denseSeqzSumExpr4 r.a0 r.a1 r.a2 r.a3))
              (.add (.var r.R) denseSeqzEM1)) envC = 0
          simp only [denseSeqzSumExpr4, denseSeqzEM1, DenseExpr.eval]
          rw [hagreeOcc r.a0 ha0occ, hagreeOcc r.a1 ha1occ, hagreeOcc r.a2 ha2occ,
            hagreeOcc r.a3 ha3occ, hagreeOcc r.R hRocc, hCdef, Function.update_self, hmethoddef,
            denseSeqzInvMethod]
          by_cases hS0 : env r.a0 + env r.a1 + env r.a2 + env r.a3 = 0
          · simp only [DenseComputationMethod.eval, denseSeqzSumExpr4, denseSeqzE1, denseSeqzEM1,
              DenseExpr.eval, if_pos hS0]
            rw [hfSR hS0]; ring
          · simp only [DenseComputationMethod.eval, denseSeqzSumExpr4, denseSeqzE1, denseSeqzEM1,
              DenseExpr.eval, if_neg hS0]
            rw [mul_right_comm, inv_mul_cancel₀ hS0, one_mul]; ring
    · have hbics : bi ∈ d.busInteractions := by
        rw [houtdef, denseSeqzCollapsedSystem] at hbi; exact List.mem_of_mem_filter hbi
      show (denseBIEval bi envC).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi envC) = false
      rw [hbeC bi hbics]; exact hsat.2 bi hbics
    · -- admissibility preserved
      show bs.admissible ((out.busInteractions.map (fun bi => denseBIEval bi envC)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
      have hmapC : out.busInteractions.map (fun bi => denseBIEval bi envC)
          = out.busInteractions.map (fun bi => denseBIEval bi env) :=
        List.map_congr_left (fun bi hbi => by
          have : bi ∈ d.busInteractions := by
            rw [houtdef, denseSeqzCollapsedSystem] at hbi; exact List.mem_of_mem_filter hbi
          exact hbeC bi this)
      rw [hmapC, houtdef, denseSeqzCollapsedSystem, ← hbusEdef]
      simp only
      rw [filter_map_filter_drop (fun bi => decide (bi ≠ busE)) (fun bi => denseBIEval bi env)
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) d.busInteractions
        (fun bi _ hkf => by
          have hbe : bi = busE := by simpa using hkf
          simp only [hbe, hbusEvalAt, hbusStateless, Bool.and_false])]
      exact hadm
    · -- side effects match
      have hseC : out.sideEffects bs envC = d.sideEffects bs env := by
        rw [hside envC]
        simp only [DenseConstraintSystem.sideEffects]
        exact List.map_congr_left (fun bi hbi => by rw [hbeC bi (List.mem_of_mem_filter hbi)])
      rw [hseC]; exact BusState.equiv_refl _
    · -- input columns keep their values
      intro i hisT
      exact Function.update_of_ne (fun h => by rw [h, hinv_id] at hisT; exact absurd hisT (by simp))
        _ _
    · -- reconstruction of derived columns
      intro inputVarIds hpowIn i hiout hisF
      have hmvars : ∀ x ∈ method.vars, x = r.R ∨ x ∈ ([r.a0, r.a1, r.a2, r.a3] : List VarId) := by
        intro x hx
        rw [hmethoddef, denseSeqzInvMethod] at hx
        simp only [DenseComputationMethod.vars, denseSeqzSumExpr4, denseSeqzE1, denseSeqzEM1,
          DenseExpr.vars, List.mem_append, List.mem_cons, List.nil_append,
          List.not_mem_nil, or_false, or_assoc] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
      by_cases hveq : i = invId
      · subst hveq
        have hmf : DenseDerivations.methodFor [(i, method)] i = some method := by
          simp [DenseDerivations.methodFor]
        rw [hmf]
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases hmvars x hx with rfl | hxa
          · exact hpowR
          · exact hpowa x hxa
        · intro x hx
          rcases hmvars x hx with rfl | hxa
          · exact hpowIn r.R hRocc hpowR
          · exact hpowIn x (hacs_mem x hxa) (hpowa x hxa)
        · rw [hCdef, Function.update_self]
          refine scDCMEvalCongr method envC env (fun x hx => ?_)
          rcases hmvars x hx with rfl | hxa
          · exact hagreeOcc r.R hRocc
          · exact hagreeOcc x (hacs_mem x hxa)
      · have hmf : DenseDerivations.methodFor [(invId, method)] i = none := by
          simp [DenseDerivations.methodFor, Ne.symm hveq]
        rw [hmf]
        have hidocc : i ∈ d.occ := (hout_occ i hiout).resolve_left hveq
        exact ⟨hidocc, hagreeOcc i hidocc⟩

/-! ## The full collapse bundle (extends + coverage + correctness) at the minted registry -/

set_option maxHeartbeats 1600000 in
/-- The complete `ofExtending` obligation bundle for one accepted collapse: mint the fresh `inv`
    witness, extend the registry, and combine output/derivation coverage with
    `dense_seqzCollapse_correct`. Primality comes from the `denseSeqzRolesValid` flag. -/
theorem dense_seqzCollapse_bundle (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (facts : BusFacts p bs) (r : DenseSeqzRoles p) (spec : ByteXorSpec p)
    (hcov : d.CoveredBy reg) (hspec : facts.byteXorSpec r.busId = some spec)
    (hvalid : denseSeqzRolesValid reg d r spec
      (denseBuild bs facts (d.busInteractions.filter
        (fun bi => decide (bi ≠ denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec)))) = true) :
    reg.Extends (reg.register (denseSeqzInvVar reg r)).1 ∧
    (denseSeqzCollapsedSystem d r (reg.register (denseSeqzInvVar reg r)).2 spec).CoveredBy
      (reg.register (denseSeqzInvVar reg r)).1 ∧
    DenseDerivations.CoveredBy (reg.register (denseSeqzInvVar reg r)).1
      [((reg.register (denseSeqzInvVar reg r)).2, denseSeqzInvMethod (p := p) r.R r.a0 r.a1 r.a2 r.a3)] ∧
    DensePassCorrect (reg.register (denseSeqzInvVar reg r)).1.isInput d
      (denseSeqzCollapsedSystem d r (reg.register (denseSeqzInvVar reg r)).2 spec)
      [((reg.register (denseSeqzInvVar reg r)).2, denseSeqzInvMethod r.R r.a0 r.a1 r.a2 r.a3)] bs := by
  have hpv : (denseSeqzInvVar reg r).powdrId? = none := rfl
  simp only [denseSeqzRolesValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hvalid
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hprime, h1024⟩, hK⟩, hbound⟩, hbusMemB⟩, hclMemB⟩, hboolMemB⟩, hboolNCB⟩,
    hpure⟩, hboundsB⟩, hnodup⟩, hfreshFlag⟩, hpow5B⟩ := hvalid
  haveI : Fact p.Prime := ⟨hprime⟩
  have hext : reg.Extends (reg.register (denseSeqzInvVar reg r)).1 :=
    VarRegistry.register_extends reg (denseSeqzInvVar reg r)
  have hii : ∀ i, (reg.register (denseSeqzInvVar reg r)).1.isInput i = reg.isInput i :=
    hcRegisterIsInputEq reg (denseSeqzInvVar reg r) hpv
  have hbusMem : denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec ∈ d.busInteractions := by
    simpa using hbusMemB
  have hclMem : ∀ c ∈ denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K,
      c ∈ d.algebraicConstraints := fun c hc => by simpa using hclMemB c hc
  have hboolMem : denseSeqzBoolConstraint r.R ∈ d.algebraicConstraints := by simpa using hboolMemB
  have hboolNC : denseSeqzBoolConstraint r.R ∉
      denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K := by
    simpa using hboolNCB
  have hpow5 : ∀ v ∈ ([r.R, r.a0, r.a1, r.a2, r.a3] : List VarId),
      (reg.register (denseSeqzInvVar reg r)).1.isInput v = true :=
    fun v hv => by rw [hii]; exact hpow5B v hv
  have hinv_fresh : (reg.register (denseSeqzInvVar reg r)).2 ∉ d.occ :=
    denseIsFresh_notMem hcov hfreshFlag
  have hinv_id : (reg.register (denseSeqzInvVar reg r)).1.isInput
      (reg.register (denseSeqzInvVar reg r)).2 = false := by
    show ((reg.register (denseSeqzInvVar reg r)).1.resolve
      (reg.register (denseSeqzInvVar reg r)).2).powdrId?.isSome = false
    rw [VarRegistry.register_resolve reg (denseSeqzInvVar reg r), hpv]; rfl
  have hRocc : r.R ∈ d.occ :=
    DenseConstraintSystem.mem_occ_of_constraint hboolMem
      (by simp [denseSeqzBoolConstraint, DenseExpr.vars, denseSeqzEM1])
  have haocc : ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List VarId), a ∈ d.occ := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact DenseConstraintSystem.mem_occ_of_constraint
        (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 0)
            (.mul (.add denseSeqzEM1 (.var r.a0)) (denseSeqzKrExpr r.K r.R)))
          (by simp [denseSeqzClusterConstraints]))
        (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
    · exact DenseConstraintSystem.mem_occ_of_constraint
        (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 1) (.mul (.var r.a1) (denseSeqzKrExpr r.K r.R)))
          (by simp [denseSeqzClusterConstraints]))
        (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
    · exact DenseConstraintSystem.mem_occ_of_constraint
        (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 2) (.mul (.var r.a2) (denseSeqzKrExpr r.K r.R)))
          (by simp [denseSeqzClusterConstraints]))
        (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
    · exact DenseConstraintSystem.mem_occ_of_constraint
        (hclMem (.mul (denseSeqzSExpr r.m3 r.m2 r.m1 r.m0 3) (.mul (.var r.a3) (denseSeqzKrExpr r.K r.R)))
          (by simp [denseSeqzClusterConstraints]))
        (by simp [DenseExpr.vars, denseSeqzSExpr, denseSeqzKrExpr, denseSeqzEM1])
  -- byte bounds on the limbs for any output-satisfying assignment, via `denseBuild_sound`
  have habyteAll : ∀ (denv : VarId → ZMod p),
      (∀ bi ∈ (denseSeqzCollapsedSystem d r (reg.register (denseSeqzInvVar reg r)).2 spec).busInteractions,
        (denseBIEval bi denv).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi denv) = false) →
      ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List VarId), (denv a).val < 256 := by
    intro denv hnv a ha
    have hb := hboundsB a ha
    cases hlk : (denseBuild bs facts (d.busInteractions.filter
        (fun bi => decide (bi ≠ denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec))))[a]? with
    | none => rw [hlk] at hb; simp at hb
    | some b =>
        rw [hlk] at hb
        have hb256 : b ≤ 256 := of_decide_eq_true hb
        have hlt := denseBuild_sound bs facts (d.busInteractions.filter
            (fun bi => decide (bi ≠ denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec)))
          a b hlk denv (fun bi hbi hm => hnv bi (by
            show bi ∈ (denseSeqzCollapsedSystem d r (reg.register (denseSeqzInvVar reg r)).2 spec).busInteractions
            simpa [denseSeqzCollapsedSystem] using hbi) hm)
        omega
  have hcorrect := dense_seqzCollapse_correct (reg.register (denseSeqzInvVar reg r)).1.isInput d bs
    facts r spec (reg.register (denseSeqzInvVar reg r)).2 hspec h1024 hK hbound hbusMem hclMem
    hboolMem hboolNC hpure habyteAll hnodup hinv_fresh hinv_id hpow5
  have hout_occ : ∀ i ∈ (denseSeqzCollapsedSystem d r (reg.register (denseSeqzInvVar reg r)).2 spec).occ,
      i = (reg.register (denseSeqzInvVar reg r)).2 ∨ i ∈ d.occ := by
    intro i hi
    rw [hcMemOcc] at hi
    rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
    · rw [denseSeqzCollapsedSystem] at hc
      simp only at hc
      rw [List.mem_append] at hc
      rcases hc with hcf | hcnc
      · exact Or.inr (DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hcf) hic)
      · simp only [denseSeqzNewConstraints, List.mem_cons, List.not_mem_nil, or_false] at hcnc
        rcases hcnc with rfl | rfl
        · simp only [denseSeqzSumExpr4, DenseExpr.vars, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hic
          rcases hic with rfl | rfl | rfl | rfl | rfl
          · exact Or.inr hRocc
          · exact Or.inr (haocc r.a0 (by simp))
          · exact Or.inr (haocc r.a1 (by simp))
          · exact Or.inr (haocc r.a2 (by simp))
          · exact Or.inr (haocc r.a3 (by simp))
        · simp only [denseSeqzSumExpr4, denseSeqzEM1, DenseExpr.vars, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hic
          rcases hic with rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (haocc r.a0 (by simp))
          · exact Or.inr (haocc r.a1 (by simp))
          · exact Or.inr (haocc r.a2 (by simp))
          · exact Or.inr (haocc r.a3 (by simp))
          · exact Or.inr hRocc
    · rw [denseSeqzCollapsedSystem] at hbi
      simp only at hbi
      exact Or.inr (DenseConstraintSystem.mem_occ_of_bi (List.mem_of_mem_filter hbi) hib)
  refine ⟨hext, ?_, ?_, hcorrect⟩
  · refine hcCoveredByOfOcc (fun i hi => ?_)
    rcases hout_occ i hi with rfl | hd
    · exact VarRegistry.register_valid reg (denseSeqzInvVar reg r)
    · exact hext.valid (DenseConstraintSystem.occ_valid hcov i hd)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    refine ⟨VarRegistry.register_valid reg (denseSeqzInvVar reg r), ?_⟩
    show (denseSeqzInvMethod r.R r.a0 r.a1 r.a2 r.a3).CoveredBy (reg.register (denseSeqzInvVar reg r)).1
    rw [denseSeqzInvMethod]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hiR : i = r.R := by simpa [denseSeqzE1, denseSeqzEM1, DenseExpr.vars] using hi
      subst hiR
      exact hext.valid (DenseConstraintSystem.occ_valid hcov _ hRocc)
    · simp only [denseSeqzSumExpr4, DenseExpr.vars, List.mem_append, List.mem_singleton] at hi
      rcases hi with ((rfl | rfl) | rfl) | rfl
      · exact hext.valid (DenseConstraintSystem.occ_valid hcov _ (haocc r.a0 (by simp)))
      · exact hext.valid (DenseConstraintSystem.occ_valid hcov _ (haocc r.a1 (by simp)))
      · exact hext.valid (DenseConstraintSystem.occ_valid hcov _ (haocc r.a2 (by simp)))
      · exact hext.valid (DenseConstraintSystem.occ_valid hcov _ (haocc r.a3 (by simp)))

/-! ## The scanning driver -/

/-- First-hit scan correctness: whatever candidate is selected, it is a `DensePassCorrect`
    collapse at the extended registry. -/
theorem denseSeqzTryList_correct (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (facts : BusFacts p bs) (hcov : d.CoveredBy reg) :
    ∀ (L : List (BusInteraction (DenseExpr p)))
      (res : VarRegistry × DenseConstraintSystem p × DenseDerivations p),
      denseSeqzTryList reg d bs facts L = some res →
        reg.Extends res.1 ∧ res.2.1.CoveredBy res.1 ∧ DenseDerivations.CoveredBy res.1 res.2.2 ∧
          DensePassCorrect res.1.isInput d res.2.1 res.2.2 bs := by
  intro L
  induction L with
  | nil => intro res hr; simp [denseSeqzTryList] at hr
  | cons bi rest ih =>
      intro res hr
      simp only [denseSeqzTryList] at hr
      split at hr
      · exact ih res hr
      · rename_i rr _
        split at hr
        · rename_i spec hbx
          split at hr
          · rename_i hvalid
            obtain rfl := Option.some.inj hr
            exact dense_seqzCollapse_bundle reg d bs facts rr spec hcov hbx hvalid
          · exact ih res hr
        · exact ih res hr

/-! ## The pass, as a registry-extending transform -/

theorem denseSeqzCollapseF_props (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    reg.Extends (denseSeqzCollapseF reg bs facts d).1
    ∧ (denseSeqzCollapseF reg bs facts d).2.1.CoveredBy (denseSeqzCollapseF reg bs facts d).1
    ∧ DenseDerivations.CoveredBy (denseSeqzCollapseF reg bs facts d).1
        (denseSeqzCollapseF reg bs facts d).2.2
    ∧ DensePassCorrect (denseSeqzCollapseF reg bs facts d).1.isInput d
        (denseSeqzCollapseF reg bs facts d).2.1 (denseSeqzCollapseF reg bs facts d).2.2 bs := by
  unfold denseSeqzCollapseF
  cases hL : denseSeqzTryList reg d bs facts d.busInteractions with
  | none =>
      simp only [Option.getD_none]
      exact ⟨VarRegistry.Extends.refl reg, hcov, (by intro x hx; simp at hx),
        DensePassCorrect.refl reg.isInput d bs⟩
  | some res =>
      simp only [Option.getD_some]
      exact denseSeqzTryList_correct reg d bs facts hcov d.busInteractions res hL

/-- One scan-and-collapse step (see `denseSeqzCollapseF`), lifted to the audited spec via
    `ofExtending`. -/
def denseSeqzCollapseStep : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofExtending (fun reg bs facts d => denseSeqzCollapseF reg bs facts d)
    (fun reg bs facts d hcov => (denseSeqzCollapseF_props reg bs facts d hcov).1)
    (fun reg bs facts d hcov => (denseSeqzCollapseF_props reg bs facts d hcov).2.1)
    (fun reg bs facts d hcov => (denseSeqzCollapseF_props reg bs facts d hcov).2.2.1)
    (fun reg bs facts d hcov => (denseSeqzCollapseF_props reg bs facts d hcov).2.2.2)

/-- Run the dense seqz collapse to a fixpoint. -/
def denseSeqzCollapsePass : DenseVerifiedPassW p :=
  denseIterateToFixpoint denseSeqzCollapseStep

end ApcOptimizer.Dense
