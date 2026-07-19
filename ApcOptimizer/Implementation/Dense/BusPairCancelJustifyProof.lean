import ApcOptimizer.Implementation.Dense.BusPairCancelJustify
import ApcOptimizer.Implementation.Dense.RootPairUnifyNativeProof

set_option autoImplicit false

/-! # Native soundness of the dense deep-byte-justification tower (Task 3, chunk C1a — prover)

Native, `VarId`-native `_sound` lemmas for the byte-justification certificates defined in
`Dense/BusPairCancelJustify.lean` (`densePointByteOk`, the `denseDeep*` chain, `denseExprPointByte`,
`denseDomainByteJustified`). These mirror, without any decode dependency, the spec soundness chain
(`pointByteOk_sound`/`deepBoundOk_sound`/`deepByteJustified_sound`/`domainByteJustified_sound` in
`OptimizerPasses/BusPairCancel.lean`).

Every argument is finite-domain enumeration + linear arithmetic over dense environments
(`VarId → ZMod p`), discharged natively via the dense infrastructure already established for the
`busUnify` cluster: `denseFindVarBound_sound`, `denseFindDomainAlg_sound`, `mem_denseAssignments`,
`denseEnvOfFast_map` (`Dense/RootPairUnifyNativeProof.lean`/`Dense/DomainFoldNativeProof.lean`),
`denseLinearize_eval`, `DenseLinExpr.norm_eval`, `DenseExpr.eval_substF`, `denseEnvF_eq_self`,
`DenseExpr.fold_eval`, `DenseExpr.constValue?_sound` (`Dense/DomainBatchNativeProof.lean`/
`Dense/ExprOps.lean`). No spec `_sound` lemma is reused (no decode) — the tower is proven directly.

The statement shapes match the spec versions so the byte-justification tower top (chunk C1c,
`byteJustifiedW`) and `dropPair_correct` (chunk C2) can consume them exactly as the spec consumers
(`byteJustifiedW_sound`/`byteJustified_sound`/`recvSlotsJustified_sound`/`dropPair_correct`) consume
`deepByteJustified_sound`/`domainByteJustified_sound`: the witness-lookup obligation `hbus` is stated
over `denseBIEval` (dense interaction evaluation), and byte-boundedness of a dense slot is derived
from dense satisfaction of the remaining system plus the same `BusFacts`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `densePointByteOk` soundness (native mirror of `pointByteOk_sound`) -/

/-- **`densePointByteOk` is sound.** If the per-point certificate accepts, and the enumerated `keys`
    of `c` are pinned to `pt` under `denv`, `c` is satisfied, and the precomputed `byteVars` really
    are bytes, then `x` is a byte at this point. Native mirror of `pointByteOk_sound`. -/
theorem densePointByteOk_sound [Fact p.Prime] (x : VarId) (c : DenseExpr p)
    (byteVars : List VarId)
    (keys : List VarId) (pt : List (VarId × ZMod p))
    (h : densePointByteOk x c byteVars keys pt = true) (denv : VarId → ZMod p)
    (hpt : ∀ y, keys.contains y = true → denseEnvOfFast pt y = denv y)
    (hc0 : c.eval denv = 0)
    (hbyteVars : ∀ v ∈ byteVars, (denv v).val < 256) :
    (denv x).val < 256 := by
  unfold densePointByteOk at h
  -- the substitution is transparent under `denv`
  have hsub : ((c.substF (fun v =>
      if keys.contains v then some (.const (denseEnvOfFast pt v)) else none)).fold).eval denv = 0 := by
    rw [DenseExpr.fold_eval, DenseExpr.eval_substF, denseEnvF_eq_self]
    · exact hc0
    · intro y t hy
      split_ifs at hy with hk
      · simp only [Option.some.injEq] at hy
        subst hy
        exact (hpt y hk).symm
  cases hl : denseLinearize ((c.substF (fun v =>
      if keys.contains v then some (.const (denseEnvOfFast pt v)) else none)).fold) with
  | none => rw [hl] at h; simp at h
  | some l =>
    rw [hl] at h
    dsimp only at h
    have hleval : (DenseLinExpr.norm l).const
        + ((DenseLinExpr.norm l).terms.map (fun t => t.2 * denv t.1)).sum = 0 := by
      have h1 : (DenseLinExpr.norm l).eval denv = 0 := by
        rw [DenseLinExpr.norm_eval, ← denseLinearize_eval _ l hl]
        exact hsub
      simpa [DenseLinExpr.eval] using h1
    cases hterms : (DenseLinExpr.norm l).terms with
    | nil => rw [hterms] at h; simp at h
    | cons t1 tail =>
      cases t1 with
      | mk v a =>
        cases tail with
        | nil =>
          -- single pinned term: `x = r`, a byte
          rw [hterms] at h hleval
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hleval
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
          obtain ⟨⟨⟨hvx, ha⟩, hroot⟩, hbyte⟩ := h
          have hvx' := of_decide_eq_true hvx
          have ha' := of_decide_eq_true ha
          have hroot' := of_decide_eq_true hroot
          rw [← hvx']
          have hcancel : a * denv v = a * (-(a⁻¹ * (DenseLinExpr.norm l).const)) := by
            have h1 : a * denv v = -(DenseLinExpr.norm l).const := by linear_combination hleval
            have h2 : a * (-(a⁻¹ * (DenseLinExpr.norm l).const)) = -(DenseLinExpr.norm l).const := by
              linear_combination hroot'
            rw [h1, h2]
          rw [mul_left_cancel₀ ha' hcancel]
          exact of_decide_eq_true hbyte
        | cons t2 tail2 =>
          cases t2 with
          | mk v2 a2 =>
            cases tail2 with
            | nil =>
              -- `x = other`: opposite coefficients, no constant
              rw [hterms] at h hleval
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                add_zero] at hleval
              rw [Bool.and_eq_true] at h
              obtain ⟨hconst, hbr⟩ := h
              have hconst' := of_decide_eq_true hconst
              rw [hconst', zero_add] at hleval
              split_ifs at hbr with hv1 hv2
              · -- v = x, bound v2
                rw [← hv1]
                rw [Bool.and_eq_true, Bool.and_eq_true] at hbr
                obtain ⟨⟨hopp, hne⟩, hbound⟩ := hbr
                have hopp' := of_decide_eq_true hopp
                have hne' := of_decide_eq_true hne
                have heqv : denv v = denv v2 := by
                  have : a * (denv v - denv v2) = 0 := by
                    rw [hopp'] at hleval; linear_combination hleval
                  rcases mul_eq_zero.mp this with h' | h'
                  · exact absurd h' hne'
                  · exact sub_eq_zero.mp h'
                rw [heqv]
                exact hbyteVars v2 (List.contains_iff_mem.mp hbound)
              · -- v2 = x, bound v
                rw [← hv2]
                rw [Bool.and_eq_true, Bool.and_eq_true] at hbr
                obtain ⟨⟨hopp, hne⟩, hbound⟩ := hbr
                have hopp' := of_decide_eq_true hopp
                have hne' := of_decide_eq_true hne
                have heqv : denv v2 = denv v := by
                  have : a2 * (denv v2 - denv v) = 0 := by
                    rw [hopp'] at hleval; linear_combination hleval
                  rcases mul_eq_zero.mp this with h' | h'
                  · exact absurd h' hne'
                  · exact sub_eq_zero.mp h'
                rw [heqv]
                exact hbyteVars v (List.contains_iff_mem.mp hbound)
            | cons t3 tail3 =>
              rw [hterms] at h; simp at h

/-! ## `denseDeepBoundOk` soundness (native mirror of `deepBoundOk_sound`) -/

/-- **`denseDeepBoundOk` is sound.** If the deep bound certificate accepts for `x` from `c`, `c` and
    every domain constraint `domCs` hold, and each witness interaction never violates when active,
    then `x` is a byte. Native mirror of `deepBoundOk_sound`. -/
theorem denseDeepBoundOk_sound [Fact p.Prime] (domCs : List (DenseExpr p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) (c : DenseExpr p)
    (h : denseDeepBoundOk domCs bs facts wits x c = true) (denv : VarId → ZMod p)
    (hdom : ∀ c' ∈ domCs, c'.eval denv = 0) (hc0 : c.eval denv = 0)
    (hbus : ∀ v, ∀ bi ∈ wits v, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (denv x).val < 256 := by
  unfold denseDeepBoundOk at h
  simp only [] at h
  split_ifs at h with hcap
  -- every enumerated variable's value lies in its domain
  have hdomsound : ∀ vd ∈ denseDeepEnumDoms domCs x c, denv vd.1 ∈ vd.2 := by
    intro vd hvd
    unfold denseDeepEnumDoms at hvd
    obtain ⟨v, _, hfn⟩ := List.mem_filterMap.mp hvd
    cases hfd : denseFindDomainAlg domCs v with
    | none => rw [hfd] at hfn; exact absurd hfn (by simp)
    | some d =>
      rw [hfd] at hfn
      dsimp only at hfn
      split_ifs at hfn
      simp only [Option.some.injEq] at hfn
      subst hfn
      exact denseFindDomainAlg_sound denv domCs v d hfd hdom
  -- the precomputed byte-bounded variables really are bytes under `denv`
  have hbyteVars : ∀ v ∈ denseDeepByteVars bs facts wits x c, (denv v).val < 256 := by
    intro v hv
    unfold denseDeepByteVars at hv
    obtain ⟨hv1, hv2⟩ := List.mem_filter.mp hv
    cases hb : denseFindVarBound bs facts (wits v) v with
    | none => rw [hb] at hv2; simp at hv2
    | some b =>
      rw [hb] at hv2
      dsimp only at hv2
      exact lt_of_lt_of_le (denseFindVarBound_sound bs facts (wits v) v b hb denv (hbus v))
        (of_decide_eq_true hv2)
  -- `denv`'s restriction to the enumerated domains is one of the checked points
  have hmem : (denseDeepEnumDoms domCs x c).map (fun vd => (vd.1, denv vd.1))
      ∈ denseAssignments (denseDeepEnumDoms domCs x c) :=
    mem_denseAssignments _ denv hdomsound
  have hpoint := List.all_eq_true.mp h _ hmem
  refine densePointByteOk_sound x c (denseDeepByteVars bs facts wits x c)
    ((denseDeepEnumDoms domCs x c).map Prod.fst)
    ((denseDeepEnumDoms domCs x c).map (fun vd => (vd.1, denv vd.1))) hpoint denv ?_
    hc0 hbyteVars
  intro y hy
  exact denseEnvOfFast_map (denseDeepEnumDoms domCs x c) denv y (List.contains_iff_mem.mp hy)

/-! ## `denseDeepByteJustified` soundness (native mirror of `deepByteJustified_sound`) -/

/-- **`denseDeepByteJustified` is sound.** If one of the candidate constraints deep-justifies `x` as
    a byte, and every constraint in `all` (a superset of `domCs`/`cands`) holds while each witness
    interaction never violates, then `x` is a byte. Native mirror of `deepByteJustified_sound`. -/
theorem denseDeepByteJustified_sound [Fact p.Prime] [NeZero p]
    (all domCs cands : List (DenseExpr p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId)
    (hdomCs : ∀ c ∈ domCs, c ∈ all) (hcands : ∀ c ∈ cands, c ∈ all)
    (h : denseDeepByteJustified domCs cands bs facts wits x = true) (denv : VarId → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval denv = 0)
    (hbus : ∀ v, ∀ bi ∈ wits v, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (denv x).val < 256 := by
  obtain ⟨c, hc, hck⟩ := List.any_eq_true.1 h
  have hc' : c ∈ all := hcands c (List.mem_of_mem_take hc)
  exact denseDeepBoundOk_sound domCs bs facts wits x c hck denv
    (fun c' hc'' => hall c' (hdomCs c' hc'')) (hall c hc') hbus

/-! ## `denseExprPointByte`/`denseDomainByteJustified` soundness (native mirror of
    `domainByteJustified_sound`) -/

/-- **`denseExprPointByte` is sound at the variable's own value.** If the single-variable expression
    `e` evaluates (with its variable fixed to its actual value `denv x`) to a byte constant, then `e`
    is a byte under `denv`. Factored out of the spec's inline `domainByteJustified_sound` reasoning. -/
theorem denseExprPointByte_sound (e : DenseExpr p) (x : VarId) (denv : VarId → ZMod p)
    (h : denseExprPointByte e x (denv x) = true) : (e.eval denv).val < 256 := by
  unfold denseExprPointByte at h
  cases hcv : (e.substF (fun v => if v = x then some (.const (denv x)) else none)).fold.constValue?
    with
  | none => rw [hcv] at h; simp at h
  | some c =>
    rw [hcv] at h
    have hbyte : c.val < 256 := of_decide_eq_true h
    have hfoldeval :
        (e.substF (fun v => if v = x then some (.const (denv x)) else none)).fold.eval denv = c :=
      DenseExpr.constValue?_sound _ c hcv denv
    have hsubeval :
        (e.substF (fun v => if v = x then some (.const (denv x)) else none)).eval denv
          = e.eval denv := by
      rw [DenseExpr.eval_substF, denseEnvF_eq_self]
      intro y t hy
      by_cases hk : y = x
      · subst y
        simp only [] at hy
        injection hy with hy'
        subst hy'
        rfl
      · simp only [if_neg hk] at hy; exact absurd hy (by simp)
    rw [DenseExpr.fold_eval, hsubeval] at hfoldeval
    rw [hfoldeval]; exact hbyte

/-- **`denseDomainByteJustified` is sound.** If `e` is a single-variable expression whose variable's
    constraint-derived finite domain makes `e` a byte at every point, then `e` is a byte under any
    assignment zeroing the domain constraints. Native mirror of `domainByteJustified_sound`. -/
theorem denseDomainByteJustified_sound [Fact p.Prime] (domCs : List (DenseExpr p)) (e : DenseExpr p)
    (h : denseDomainByteJustified domCs e = true) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval denv = 0) :
    (e.eval denv).val < 256 := by
  unfold denseDomainByteJustified at h
  cases hsv : e.singleVarAux with
  | none => rw [hsv] at h; simp at h
  | some ov =>
    cases ov with
    | none => rw [hsv] at h; simp at h
    | some x =>
      rw [hsv] at h
      dsimp only at h
      cases hfd : denseFindDomainAlg domCs x with
      | none => rw [hfd] at h; simp at h
      | some d =>
        rw [hfd, Bool.and_eq_true] at h
        obtain ⟨_, hall⟩ := h
        have hmem : denv x ∈ d := denseFindDomainAlg_sound denv domCs x d hfd hdom
        have hpt : denseExprPointByte e x (denv x) = true := List.all_eq_true.mp hall _ hmem
        exact denseExprPointByte_sound e x denv hpt

end ApcOptimizer.Dense
