import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify
import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnifyProof

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

/-! # Native soundness of the affine + basis justification tier (Task 3, chunk C1b — prover)

Native, `VarId`-native `_sound` lemmas for the affine and basis justification certificates defined in
`Dense/BusPairCancelJustify.lean` (`denseLinTermsNatBound`/`DenseLinExpr.natBound`/
`denseAffineJustified`, `denseFormBoundAt`/`denseBasisReduceGo`/`denseBasisJustified`). These mirror,
without any decode dependency, the spec soundness chain (`terms_eval_eq_cast`/`linTermsNatBound_le`/
`LinExpr.eval_val_lt`/`affineJustified_sound`, `formBoundAt_sound`/`basisReduceGo_sound`/
`basisJustified_sound` in `OptimizerPasses/BusPairCancel.lean`).

Every argument is linear/natural arithmetic over dense environments (`VarId → ZMod p`). The affine
tier needs no primality at all (it is pure nat-level wraparound bookkeeping); the basis tier reuses
`denseFormBoundAt_sound` (value-level `facts.slotBound_sound` + `denseMatches_evalPattern` +
`DenseExpr.constValue?_sound`, the same value-level fact-application precedent as
`denseScaledSlotBound_sound`) and the exact `DenseLinExpr` algebra
(`DenseLinExpr.add_eval`/`scale_eval`/`norm_eval`, `denseLinearize_eval`). `IntervalForce.srep` only
selects the reduction multiplier `μ`; its numeric correctness is *never used* in soundness — the
subtraction `L = μ·Lf + L'` is exact `DenseLinExpr` algebra regardless of how `μ` is chosen — so no
`srep` fact is required. No spec `_sound` lemma is reused (no decode); the tier is proven directly.

The statement shapes match the spec versions exactly (`Variable → VarId`, `Expression → DenseExpr`,
`bi.eval env → denseBIEval bi denv`) so the byte-justification tower top (chunk C1c,
`byteJustifiedW`) consumes `denseAffineJustified_sound`/`denseBasisJustified_sound` exactly as the
spec `byteJustifiedW_sound` consumes `affineJustified_sound`/`basisJustified_sound`. -/

/-! ## `denseAffineJustified` soundness (native mirror of `affineJustified_sound`) -/

/-- Over `ZMod p` a dense term-list sum equals the cast of its natural (`.val`-wise) sum. Native
    mirror of `terms_eval_eq_cast`. -/
theorem denseTerms_eval_eq_cast [NeZero p] (terms : List (VarId × ZMod p))
    (denv : VarId → ZMod p) :
    (terms.map (fun t => t.2 * denv t.1)).sum
      = (((terms.map (fun t => t.2.val * (denv t.1).val)).sum : ℕ) : ZMod p) := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add, Nat.cast_mul]
    congr 1
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]

/-- The natural term-sum is bounded by `denseLinTermsNatBound` when every variable is bounded. Native
    mirror of `linTermsNatBound_le`. -/
theorem denseLinTermsNatBound_le (bnd : VarId → Option Nat) (denv : VarId → ZMod p)
    (terms : List (VarId × ZMod p)) (M : Nat) (h : denseLinTermsNatBound bnd terms = some M)
    (hbnd : ∀ v ∈ terms.map Prod.fst, ∀ b, bnd v = some b → (denv v).val < b) :
    (terms.map (fun t => t.2.val * (denv t.1).val)).sum ≤ M := by
  induction terms generalizing M with
  | nil => simp only [denseLinTermsNatBound, Option.some.injEq] at h; subst h; simp
  | cons t rest ih =>
    simp only [denseLinTermsNatBound] at h
    cases hb : bnd t.1 with
    | none => rw [hb] at h; simp at h
    | some b =>
      cases hr : denseLinTermsNatBound bnd rest with
      | none => rw [hb, hr] at h; simp at h
      | some Macc =>
        rw [hb, hr] at h; simp only [Option.some.injEq] at h; subst h
        have hvt : (denv t.1).val < b := hbnd t.1 (by simp) b hb
        have hacc : (rest.map (fun t => t.2.val * (denv t.1).val)).sum ≤ Macc :=
          ih Macc hr
            (fun v hv => hbnd v (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hv))
        simp only [List.map_cons, List.sum_cons]
        have hmul : t.2.val * (denv t.1).val ≤ t.2.val * (b - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega

/-- If `L`'s natural bound `M` is `< p`, then `L.eval` has value `≤ M` (`< bound` when `M < bound`):
    no wraparound, so the field value equals the natural value. Native mirror of
    `LinExpr.eval_val_lt`. -/
theorem DenseLinExpr.eval_val_lt (L : DenseLinExpr p) (denv : VarId → ZMod p)
    (bnd : VarId → Option Nat)
    (hbnd : ∀ v ∈ L.terms.map Prod.fst, ∀ b, bnd v = some b → (denv v).val < b)
    (M : Nat) (hM : L.natBound bnd = some M) (bound : Nat) (hMb : M < bound) (hMp : M < p) :
    (L.eval denv).val < bound := by
  have hNe : NeZero p := ⟨by omega⟩
  unfold DenseLinExpr.natBound at hM
  cases hs : denseLinTermsNatBound bnd L.terms with
  | none => rw [hs] at hM; simp at hM
  | some S =>
    rw [hs] at hM
    simp only [Option.map_some, Option.some.injEq] at hM
    subst hM
    have hsum := denseLinTermsNatBound_le bnd denv L.terms S hs hbnd
    have hcast : L.eval denv
        = (((L.const.val + (L.terms.map (fun t => t.2.val * (denv t.1).val)).sum : ℕ)) : ZMod p) := by
      rw [DenseLinExpr.eval, denseTerms_eval_eq_cast, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id]
    have hlt : L.const.val + (L.terms.map (fun t => t.2.val * (denv t.1).val)).sum < p := by omega
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    omega

/-- **`denseAffineJustified` is sound.** If `e` linearizes to a form whose per-variable-bounded
    natural value is `< bound` (and `< p`), then `e` is a byte/limb under any assignment respecting
    the bounds. Native mirror of `affineJustified_sound`. -/
theorem denseAffineJustified_sound (bound : Nat) (bnd : VarId → Option Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (denv v).val < b)
    (h : denseAffineJustified bound bnd e = true) : (e.eval denv).val < bound := by
  unfold denseAffineJustified at h
  cases hL : denseLinearize e with
  | none => simp [hL] at h
  | some L =>
    cases hM : L.natBound bnd with
    | none => simp [hL, hM] at h
    | some M =>
      simp only [hL, hM, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [denseLinearize_eval e L hL denv]
      exact DenseLinExpr.eval_val_lt L denv bnd (fun v _ b hb => hbnd v b hb) M hM bound h.1 h.2

/-! ## `denseFormBoundAt` soundness (native mirror of `formBoundAt_sound`) -/

/-- **`denseFormBoundAt` is sound.** If payload slot `i` of `bi` linearizes to `Lr` with slot bound
    `Br`, and the interaction never violates when active, then `Lr`'s value is `< Br`. Native mirror
    of `formBoundAt_sound`: the value-level `facts.slotBound_sound` is applied at `denseBIEval`, with
    `denseMatches_evalPattern` supplying the pattern match — no decode. -/
theorem denseFormBoundAt_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : Nat) (Lr : DenseLinExpr p) (Br : Nat)
    (h : denseFormBoundAt facts bi i = some (Lr, Br)) (denv : VarId → ZMod p)
    (hviol : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (Lr.eval denv).val < Br := by
  unfold denseFormBoundAt at h
  cases hmc : bi.multiplicity.constValue? with
  | none => simp only [hmc] at h; exact absurd h (by simp)
  | some mval =>
    simp only [hmc] at h
    split_ifs at h with hmz
    cases hpe : bi.payload[i]? with
    | none => simp only [hpe] at h; exact absurd h (by simp)
    | some e =>
      cases hsb : facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
      | none => simp only [hpe, hsb] at h; exact absurd h (by simp)
      | some B =>
        simp only [hpe, hsb] at h
        cases hL : denseLinearize e with
        | none => simp only [hL] at h; exact absurd h (by simp)
        | some L' =>
          simp only [hL, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hmeval : (denseBIEval bi denv).multiplicity = mval :=
            bi.multiplicity.constValue?_sound mval hmc denv
          have hv : bs.violatesConstraint (denseBIEval bi denv) = false := by
            apply hviol
            rw [hmeval]
            exact hmz
          have hget : (denseBIEval bi denv).payload[i]? = some (e.eval denv) := by
            show (bi.payload.map (fun e => e.eval denv))[i]? = some (e.eval denv)
            rw [List.getElem?_map, hpe]
            rfl
          have hsb' : facts.slotBound (denseBIEval bi denv).busId (denseBIEval bi denv).multiplicity
              (bi.payload.map DenseExpr.constValue?) i = some B := by
            show facts.slotBound bi.busId (denseBIEval bi denv).multiplicity _ i = some B
            rw [hmeval]
            exact hsb
          have hbound : (e.eval denv).val < B :=
            facts.slotBound_sound (denseBIEval bi denv) (bi.payload.map DenseExpr.constValue?) i B
              (e.eval denv) hsb' (denseMatches_evalPattern bi.payload denv) hv hget
          rwa [DenseLinExpr.norm_eval, ← denseLinearize_eval e L' hL denv]

/-! ## `denseBasisReduceGo`/`denseBasisJustified` soundness (native mirror of
    `basisReduceGo_sound`/`basisJustified_sound`) -/

/-- **`denseBasisReduceGo` is sound.** Fuel-bounded induction: at each step it either finishes on the
    plain per-variable natural bound, or subtracts an integer multiple `μ` of a range-checked slot
    form (`denseFormBoundAt`, value-bounded by `denseFormBoundAt_sound`) accounting `μ·(B_F − 1)`
    against the budget; the subtraction is exact `DenseLinExpr` algebra (`μ` is chosen by
    `IntervalForce.srep`, but its numeric correctness is unused). Native mirror of
    `basisReduceGo_sound`. -/
theorem denseBasisReduceGo_sound (bound : Nat) (bnd : VarId → Option Nat) {bs : BusSemantics p}
    (facts : BusFacts p bs) (fwits : VarId → List (BusInteraction (DenseExpr p)))
    (denv : VarId → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (denv v).val < b)
    (hfw : ∀ v, ∀ bi ∈ fwits v, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    ∀ (fuel used : Nat) (L : DenseLinExpr p),
      denseBasisReduceGo bound bnd facts fwits fuel used L = true →
      ∃ n : ℕ, L.eval denv = (n : ZMod p) ∧ n + used < bound ∧ n + used < p := by
  intro fuel
  induction fuel with
  | zero => intro used L h; exact absurd h (by simp [denseBasisReduceGo])
  | succ fuel ih =>
    intro used L h
    rw [denseBasisReduceGo, Bool.or_eq_true] at h
    rcases h with hfin | hstep
    · -- finish arm: the plain per-variable natural bound
      cases hM : L.natBound bnd with
      | none => rw [hM] at hfin; simp at hfin
      | some M =>
        rw [hM] at hfin
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hfin
        obtain ⟨hb, hp'⟩ := hfin
        haveI : NeZero p := ⟨by omega⟩
        unfold DenseLinExpr.natBound at hM
        cases hs : denseLinTermsNatBound bnd L.terms with
        | none => rw [hs] at hM; simp at hM
        | some SN =>
          rw [hs] at hM
          simp only [Option.map_some, Option.some.injEq] at hM
          subst hM
          refine ⟨L.const.val + (L.terms.map (fun t => t.2.val * (denv t.1).val)).sum, ?_, ?_, ?_⟩
          · rw [DenseLinExpr.eval, denseTerms_eval_eq_cast, Nat.cast_add, ZMod.natCast_val,
              ZMod.cast_id]
          · have := denseLinTermsNatBound_le bnd denv L.terms SN hs
              (fun v _ b hb' => hbnd v b hb')
            omega
          · have := denseLinTermsNatBound_le bnd denv L.terms SN hs
              (fun v _ b hb' => hbnd v b hb')
            omega
    · -- reduction arm: subtract μ·F for a range-checked slot form F
      rw [List.any_eq_true] at hstep
      obtain ⟨v, _, hstep⟩ := hstep
      rw [List.any_eq_true] at hstep
      obtain ⟨bi, hbi, hstep⟩ := hstep
      rw [List.any_eq_true] at hstep
      obtain ⟨i, _, hstep⟩ := hstep
      cases hfb : denseFormBoundAt facts bi i with
      | none => rw [hfb] at hstep; simp at hstep
      | some LfBf =>
        obtain ⟨Lf, Bf⟩ := LfBf
        rw [hfb] at hstep
        simp only at hstep
        split_ifs at hstep with hcond
        obtain ⟨n', heval', hb', hp'⟩ := ih _ _ hstep
        haveI : NeZero p := ⟨by omega⟩
        have hef : (Lf.eval denv).val < Bf :=
          denseFormBoundAt_sound facts bi i Lf Bf hfb denv (hfw v bi hbi)
        set μ := (IntervalForce.srep (L.coeff v) / IntervalForce.srep (Lf.coeff v)).toNat with hμ
        -- the exact algebraic decomposition L = μ·Lf + L'
        have hdecomp : L.eval denv
            = (μ : ZMod p) * Lf.eval denv + ((L.add (Lf.scale (-(μ : ZMod p)))).norm).eval denv := by
          rw [DenseLinExpr.norm_eval, DenseLinExpr.add_eval, DenseLinExpr.scale_eval]
          ring
        refine ⟨μ * (Lf.eval denv).val + n', ?_, ?_, ?_⟩
        · rw [hdecomp, heval']
          push_cast
          rw [ZMod.natCast_val, ZMod.cast_id]
        · have hmul : μ * (Lf.eval denv).val ≤ μ * (Bf - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        · have hmul : μ * (Lf.eval denv).val ≤ μ * (Bf - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega

/-- **`denseBasisJustified` is sound.** If `e` linearizes to a form the fuel-bounded reduction proves
    `< bound`, then `e` is a byte/limb under any assignment respecting the bounds and never violating
    the witness interactions. Native mirror of `basisJustified_sound`. -/
theorem denseBasisJustified_sound (bound : Nat) (bnd : VarId → Option Nat) {bs : BusSemantics p}
    (facts : BusFacts p bs) (fwits : VarId → List (BusInteraction (DenseExpr p)))
    (e : DenseExpr p) (denv : VarId → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (denv v).val < b)
    (hfw : ∀ v, ∀ bi ∈ fwits v, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false)
    (h : denseBasisJustified bound bnd facts fwits e = true) : (e.eval denv).val < bound := by
  unfold denseBasisJustified at h
  cases hL : denseLinearize e with
  | none => rw [hL] at h; simp at h
  | some L =>
    rw [hL] at h
    obtain ⟨n, heval, hb, hp'⟩ :=
      denseBasisReduceGo_sound bound bnd facts fwits denv hbnd hfw basisFuel 0 L.norm h
    haveI : NeZero p := ⟨by omega⟩
    rw [denseLinearize_eval e L hL denv, ← DenseLinExpr.norm_eval, heval, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-! # Native soundness of the byte-justification dispatcher (Task 3, chunk C1c — prover)

Native, `VarId`-native `_sound` lemmas for the dispatcher defined in
`Dense/BusPairCancelJustify.lean` (`denseByteJustifiedW`/`denseByteJustified`/
`denseRecvSlotsJustified`). These mirror, without any decode dependency, the spec soundness chain
(`byteJustifiedW_sound`/`byteJustified_sound`/`recvSlotsJustified_sound` in
`OptimizerPasses/BusPairCancel.lean`), composing the C1a/C1b leaf certificates
(`denseFindVarBound_sound`, `DenseExpr.constValue?_sound`, `denseDeepByteJustified_sound`,
`denseDomainByteJustified_sound`, `denseAffineJustified_sound`, `denseBasisJustified_sound`) exactly
as the spec versions compose theirs (`findVarBound_sound`/`constValue?_sound`/
`deepByteJustified_sound`/`domainByteJustified_sound`/`affineJustified_sound`/`basisJustified_sound`).

The statement shapes match the spec versions (`Variable → VarId`, `Expression → DenseExpr`,
`bi.eval env → denseBIEval bi denv`, `env : Variable → ZMod p → denv : VarId → ZMod p`). In
particular `denseRecvSlotsJustified_sound`'s conclusion,
`∀ slot ∈ slots, ∀ x, (denseBIEval R denv).payload[slot]? = some x → x.val < bound`, is exactly the
byte-boundedness fact the dense `dropPair_correct` (chunk C2) will require as its `hbyte` obligation
and that the dense `checkCancel_sound` (chunk C5) will discharge — with `all := d.algebraicConstraints`
and `rest := A ++ B ++ C ++ checks` — mirroring how spec's `checkCancel_sound` feeds `dropPair_correct`
via `recvSlotsJustified_sound`. No spec `_sound` lemma is reused (no decode). -/

/-! ## `denseByteJustifiedW` soundness (native mirror of `byteJustifiedW_sound`) -/

/-- **`denseByteJustifiedW` is sound.** If the dispatcher accepts, every constraint in the superset
    `all` (which includes `domCs`/`candsOf`) holds under `denv`, and every witnessed remaining
    interaction (`wits`/`fwits ⊆ rest`) never violates when active, then `e` is a byte/limb (`< bound`)
    under `denv`. Native mirror of `byteJustifiedW_sound`. -/
theorem denseByteJustifiedW_sound (bound : Nat) (deep : Bool) (all domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (DenseExpr p)))
    (wits fwits : VarId → List (BusInteraction (DenseExpr p))) (e : DenseExpr p)
    (hdeep : deep = true → p.Prime)
    (hdomCs : ∀ c ∈ domCs, c ∈ all) (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ all)
    (hwits : ∀ v, ∀ bi ∈ wits v, bi ∈ rest)
    (hfwits : ∀ v, ∀ bi ∈ fwits v, bi ∈ rest)
    (h : denseByteJustifiedW bound deep domCs candsOf bs facts wits fwits e = true)
    (denv : VarId → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval denv = 0)
    (hbus : ∀ bi ∈ rest, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (e.eval denv).val < bound := by
  have hbusW : ∀ v, ∀ bi ∈ wits v, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false :=
    fun v bi hbi => hbus bi (hwits v bi hbi)
  unfold denseByteJustifiedW at h
  cases hc : e.constValue? with
  | some c =>
    rw [hc] at h
    dsimp only at h
    rw [e.constValue?_sound c hc denv]
    exact of_decide_eq_true h
  | none =>
    rw [hc] at h
    dsimp only at h
    rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · -- variable path (bus-fact bound or deep selector-flag justification)
      cases e with
      | var x =>
        dsimp only at h
        show (denv x).val < bound
        rcases Bool.or_eq_true _ _ |>.mp h with h' | h'
        · cases hb : denseFindVarBound bs facts (wits x) x with
          | some b =>
            rw [hb] at h'
            dsimp only at h'
            exact lt_of_lt_of_le
              (denseFindVarBound_sound bs facts (wits x) x b hb denv (hbusW x))
              (of_decide_eq_true h')
          | none => rw [hb] at h'; simp at h'
        · rw [Bool.and_eq_true, Bool.and_eq_true] at h'
          haveI : Fact p.Prime := ⟨hdeep h'.1.1⟩
          haveI : NeZero p := ⟨(hdeep h'.1.1).ne_zero⟩
          exact lt_of_lt_of_le
            (denseDeepByteJustified_sound all domCs (candsOf x) bs facts wits x hdomCs (hcands x)
              h'.2 denv hall hbusW)
            (of_decide_eq_true h'.1.2)
      | const n => simp at h
      | add a b => simp at h
      | mul a b => simp at h
    · -- single-variable finite-domain expression path
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      haveI : Fact p.Prime := ⟨hdeep h.1.1⟩
      exact lt_of_lt_of_le
        (denseDomainByteJustified_sound domCs e h.2 denv (fun c' hc' => hall c' (hdomCs c' hc')))
        (of_decide_eq_true h.1.2)
    · -- affine recomposition path (`256·hi + lo`, …)
      exact denseAffineJustified_sound bound (fun x => denseFindVarBound bs facts (wits x) x) e denv
        (fun v b hb => denseFindVarBound_sound bs facts (wits v) v b hb denv (hbusW v)) h
    · -- basis reduction path (range-checked slot forms)
      exact denseBasisJustified_sound bound (fun x => denseFindVarBound bs facts (wits x) x) facts
        fwits e denv (fun v b hb => denseFindVarBound_sound bs facts (wits v) v b hb denv (hbusW v))
        (fun v bi hbi => hbus bi (hfwits v bi hbi)) h

/-! ## `denseByteJustified` soundness (native mirror of `byteJustified_sound`) -/

/-- **`denseByteJustified` is sound** (the plain full-scan form). Native mirror of
    `byteJustified_sound`: instantiate `denseByteJustifiedW_sound` at the naive per-query filters
    (`domCs = all.filter isSingleVar`, `candsOf x = all.filter (mentions x)`, `wits _ = rest`,
    `fwits _ = []`). -/
theorem denseByteJustified_sound (bound : Nat) (deep : Bool) (all : List (DenseExpr p))
    (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (DenseExpr p))) (e : DenseExpr p)
    (hdeep : deep = true → p.Prime)
    (h : denseByteJustified bound deep all bs facts rest e = true) (denv : VarId → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval denv = 0)
    (hbus : ∀ bi ∈ rest, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (e.eval denv).val < bound :=
  denseByteJustifiedW_sound bound deep all (all.filter DenseExpr.isSingleVar)
    (fun x => all.filter (DenseExpr.mentions x)) bs facts rest (fun _ => rest)
    (fun _ => []) e hdeep
    (fun _ hc => List.mem_of_mem_filter hc) (fun _ _ hc => List.mem_of_mem_filter hc)
    (fun _ _ hbi => hbi) (fun _ _ hbi => absurd hbi (by simp)) h denv hall hbus

/-! ## `denseRecvSlotsJustified` soundness (native mirror of `recvSlotsJustified_sound`)

This is the byte-justification tower **top** consumed by the dense `dropPair_correct` (C2) /
`checkCancel_sound` (C5): its conclusion is the per-slot byte bound on the *evaluated* dropped
receive `denseBIEval R denv`. -/

/-- **`denseRecvSlotsJustified` is sound.** If every declared byte slot of `R` is justified, then at
    every such slot the evaluated payload entry of `R` (under any `denv` zeroing `all` and never
    violating the remaining witnessed interactions) is a byte/limb (`< bound`). Native mirror of
    `recvSlotsJustified_sound`; the conclusion is stated over `denseBIEval R denv` to feed the dense
    `dropPair_correct`'s `hbyte` obligation directly. -/
theorem denseRecvSlotsJustified_sound (bound : Nat) (deep : Bool) (all domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (DenseExpr p)))
    (wits fwits : VarId → List (BusInteraction (DenseExpr p))) (slots : List Nat)
    (R : BusInteraction (DenseExpr p)) (hdeep : deep = true → p.Prime)
    (hdomCs : ∀ c ∈ domCs, c ∈ all) (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ all)
    (hwits : ∀ v, ∀ bi ∈ wits v, bi ∈ rest)
    (hfwits : ∀ v, ∀ bi ∈ fwits v, bi ∈ rest)
    (h : denseRecvSlotsJustified bound deep domCs candsOf bs facts wits fwits slots R = true)
    (denv : VarId → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval denv = 0)
    (hbus : ∀ bi ∈ rest, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    ∀ slot ∈ slots, ∀ x : ZMod p, (denseBIEval R denv).payload[slot]? = some x → x.val < bound := by
  intro slot hslot x hget
  have hcheck := List.all_eq_true.mp h slot hslot
  -- the evaluated payload entry is the evaluation of the syntactic entry
  have hget' : (R.payload[slot]?).map (fun e => e.eval denv) = some x := by
    rw [← List.getElem?_map]
    exact hget
  cases he : R.payload[slot]? with
  | none => rw [he] at hget'; exact absurd hget' (by simp)
  | some e =>
    rw [he] at hget' hcheck
    simp only [Option.map_some, Option.some.injEq] at hget'
    subst hget'
    exact denseByteJustifiedW_sound bound deep all domCs candsOf bs facts rest wits fwits e hdeep
      hdomCs hcands hwits hfwits hcheck denv hall hbus

end ApcOptimizer.Dense
