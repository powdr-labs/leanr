import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Bridge
import ApcOptimizer.Implementation.OptimizerPasses.RootPairCore

set_option autoImplicit false

/-! # Native soundness for the dense address-disequality certificate library (Task 3)

The proof layer for `Dense/AddrDiseq.lean`. This module is a **library**: it exposes no pass, only the
value-level soundness lemmas the dense `busUnify` / `busPairCancel` native proofs consume to discharge
their `DensePassCorrect` without re-proving representation correspondence per certificate.

## Proof strategy

Each dense certificate is proved sound **natively at the value level**, directly over dense
environments `VarId → ZMod p` (`DenseExpr.eval`/`DenseLinExpr.eval`/`denseBIEval`). Every argument is
the dense linear-arithmetic mirror of the reference `Variable`-level `AddrDiseq` proof: the same
`norm`/`add`/`scale`/`eval_split`/`linearize` algebra,
carried out over the dense forms with the dense eval lemmas (`DenseLinExpr.norm_eval`, `add_eval`,
`scale_eval`, `eval_split`, `denseLinearize_eval`). No `VarRegistry`, no `decode`, and no reference
*pass*'s `PassCorrect` is involved; the field-membership core (`twoRoot_mem`, `RootPairCore.lean`) is
representation-independent.

The proof-carrying spec wrappers (`TwoRootMap.sound`, `NonzeroWits.sound`) are replaced by native
soundness invariants over the dense data: `DenseTwoRootMap.Sound` (proved along
`build`/`addAll`/`addVars`/`insertEntry`) records that every map lookup is prime-gated,
unit-coefficient, and witnessed by an actual constraint's `denseTwoRootOf?` decomposition; the
reciprocal-nonzero certificate reads its witnesses straight off `DenseNonzeroWits.build`.

The value-level two-root soundness `denseTwoRootOf?_sound` (proved directly over dense evaluation via
`twoRoot_mem`) also lives here; the dense `rootPairUnify` proof consumes it directly. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Nonzero-constant differences (native) -/

/-- **`denseConstDiffNZ` is sound.** Two dense linear forms whose normalized difference is a nonzero
    constant evaluate differently. Native mirror of `constDiffNZ_sound`. -/
theorem denseConstDiffNZ_sound (a b : DenseLinExpr p) (h : denseConstDiffNZ a b = true)
    (denv : VarId → ZMod p) : a.eval denv ≠ b.eval denv := by
  unfold denseConstDiffNZ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hterms, hconst⟩ := h
  have hd : ((a.add (b.scale (-1))).norm).eval denv = a.eval denv - b.eval denv := by
    rw [DenseLinExpr.norm_eval, DenseLinExpr.add_eval, DenseLinExpr.scale_eval]; ring
  have hd2 : ((a.add (b.scale (-1))).norm).eval denv = ((a.add (b.scale (-1))).norm).const := by
    simp only [DenseLinExpr.eval, List.isEmpty_iff.1 hterms, List.map_nil, List.sum_nil, add_zero]
  intro heq
  have hz : ((a.add (b.scale (-1))).norm).const = 0 := by rw [← hd2, hd, heq, sub_self]
  exact (of_decide_eq_true hconst) hz

/-! ## Address-slot glue: a per-slot value (dis)equality forces an address (dis)equality (dense) -/

/-- If some declared address slot of `S` and `bi` evaluates differently under `denv`, the addresses
    differ. Dense mirror of the `addr_eq_slot` contrapositive. -/
theorem denseAddr_slot_neq (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p))
    (denv : VarId → ZMod p) {slot : Nat} (hslot : slot ∈ shape.addressFields)
    {e e' : DenseExpr p} (hSe : S.payload[slot]? = some e) (hbe : bi.payload[slot]? = some e')
    (hne : e.eval denv ≠ e'.eval denv) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  intro heq
  obtain ⟨j, hj⟩ : ∃ j, shape.addressFields[j]? = some slot := List.getElem?_of_mem hslot
  have e1 : (shape.address (denseBIEval S denv))[j]? = some ((denseBIEval S denv).payload[slot]?) := by
    simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
  have e2 : (shape.address (denseBIEval bi denv))[j]? = some ((denseBIEval bi denv).payload[slot]?) := by
    simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
  rw [heq, e2] at e1
  have key : (denseBIEval S denv).payload[slot]? = (denseBIEval bi denv).payload[slot]? :=
    (Option.some.inj e1).symm
  have keyS : (denseBIEval S denv).payload[slot]? = some (e.eval denv) := by
    show (S.payload.map (fun e => e.eval denv))[slot]? = some (e.eval denv)
    rw [List.getElem?_map, hSe]; rfl
  have keyB : (denseBIEval bi denv).payload[slot]? = some (e'.eval denv) := by
    show (bi.payload.map (fun e => e.eval denv))[slot]? = some (e'.eval denv)
    rw [List.getElem?_map, hbe]; rfl
  rw [keyS, keyB] at key
  exact hne (Option.some.inj key)

/-- Equal addresses agree at every declared address slot (the forward per-slot half). Dense mirror of
    `addr_eq_slot`. -/
theorem denseAddr_eq_slot (shape : MemoryBusShape) (S m : BusInteraction (DenseExpr p))
    (denv : VarId → ZMod p)
    (heq : shape.address (denseBIEval S denv) = shape.address (denseBIEval m denv))
    (f : Nat) (hf : f ∈ shape.addressFields) :
    (denseBIEval S denv).payload[f]? = (denseBIEval m denv).payload[f]? := by
  obtain ⟨j, hj⟩ : ∃ j, shape.addressFields[j]? = some f := List.getElem?_of_mem hf
  have e1 : (shape.address (denseBIEval S denv))[j]? = some ((denseBIEval S denv).payload[f]?) := by
    simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
  have e2 : (shape.address (denseBIEval m denv))[j]? = some ((denseBIEval m denv).payload[f]?) := by
    simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
  rw [heq, e2] at e1
  exact (Option.some.inj e1).symm

/-! ## The affine (same-base) certificate (native) -/

/-- **`denseAddrAffineNeq` is sound.** Some address slot linearizes to two affine forms differing by a
    nonzero constant, so the addresses differ. Native mirror of `addrAffineNeq_sound`. -/
theorem denseAddrAffineNeq_sound (reg : VarRegistry) (shape : MemoryBusShape)
    (S bi : BusInteraction (DenseExpr p)) (_hS : denseBICovered reg S) (_hbi : denseBICovered reg bi)
    (h : denseAddrAffineNeq shape S bi = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  unfold denseAddrAffineNeq at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : bi.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      simp only [hSp, hbp] at hcond
      cases hL : denseLinearize e with
      | none => simp [hL] at hcond
      | some L =>
        cases hL' : denseLinearize e' with
        | none => simp [hL, hL'] at hcond
        | some L' =>
          simp only [hL, hL'] at hcond
          refine denseAddr_slot_neq shape S bi denv hslot hSp hbp ?_
          rw [denseLinearize_eval e L hL denv, denseLinearize_eval e' L' hL' denv]
          exact denseConstDiffNZ_sound L L' hcond denv

/-! ## The two-root map: the lookup-wise soundness invariant -/

/-- The dense soundness invariant: every successful lookup is prime-gated, unit-coefficient, and
    witnessed by an actual constraint's `denseTwoRootOf?` decomposition. Purely dense (mentions no
    registry / decode). -/
def DenseTwoRootMap.Sound (dcs : List (DenseExpr p)) (T : DenseTwoRootMap p) : Prop :=
  ∀ v k A δ, T.map[v]? = some (k, A, δ) →
    Nat.Prime p ∧ k * k⁻¹ = 1 ∧ ∃ c ∈ dcs, denseTwoRootOf? c v = some (k, A, δ)

theorem DenseTwoRootMap.empty_sound (dcs : List (DenseExpr p)) :
    (DenseTwoRootMap.empty : DenseTwoRootMap p).Sound dcs := by
  intro v k A δ h
  simp only [DenseTwoRootMap.empty, Std.HashMap.getElem?_empty] at h
  exact absurd h (by simp)

theorem DenseTwoRootMap.Sound.insertEntry {dcs : List (DenseExpr p)} {T : DenseTwoRootMap p}
    (hT : T.Sound dcs) {v : VarId} {k : ZMod p} {A : DenseLinExpr p} {δ : ZMod p}
    (hnew : Nat.Prime p ∧ k * k⁻¹ = 1 ∧ ∃ c ∈ dcs, denseTwoRootOf? c v = some (k, A, δ)) :
    (T.insertEntry v k A δ).Sound dcs := by
  intro w k' A' δ' hw
  simp only [DenseTwoRootMap.insertEntry, Std.HashMap.getElem?_insert] at hw
  by_cases hvw : (v == w) = true
  · rw [if_pos hvw] at hw
    have heq : (k, A, δ) = (k', A', δ') := by simpa using hw
    have hvw' : v = w := by simpa using hvw
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    subst hvw'
    exact hnew
  · rw [if_neg hvw] at hw
    exact hT w k' A' δ' hw

theorem DenseTwoRootMap.Sound.addVars {dcs : List (DenseExpr p)} (hp : Nat.Prime p) {c : DenseExpr p}
    (hc : c ∈ dcs) : ∀ (T : DenseTwoRootMap p) (vs : List VarId), T.Sound dcs →
      (DenseTwoRootMap.addVars c T vs).Sound dcs := by
  intro T vs
  induction vs generalizing T with
  | nil => intro hT; exact hT
  | cons v rest ih =>
      intro hT
      rw [DenseTwoRootMap.addVars]
      cases htr : denseTwoRootOf? c v with
      | none => exact ih T hT
      | some kAδ =>
          obtain ⟨k, A, δ⟩ := kAδ
          dsimp only
          by_cases hu : k * k⁻¹ = 1
          · rw [if_pos hu]; exact ih _ (hT.insertEntry ⟨hp, hu, c, hc, htr⟩)
          · rw [if_neg hu]; exact ih T hT

theorem DenseTwoRootMap.Sound.addAll {dcs : List (DenseExpr p)} (hp : Nat.Prime p) :
    ∀ (T : DenseTwoRootMap p) (pending : List (DenseExpr p)), (∀ c ∈ pending, c ∈ dcs) →
      T.Sound dcs → (DenseTwoRootMap.addAll T pending).Sound dcs := by
  intro T pending
  induction pending generalizing T with
  | nil => intro _ hT; exact hT
  | cons c rest ih =>
      intro hmem hT
      rw [DenseTwoRootMap.addAll]
      exact ih _ (fun c' h => hmem c' (List.mem_cons_of_mem _ h))
        (DenseTwoRootMap.Sound.addVars hp (hmem c (List.mem_cons_self ..)) T _ hT)

/-- **The built two-root map is sound.** -/
theorem DenseTwoRootMap.build_sound (dcs : List (DenseExpr p)) :
    (DenseTwoRootMap.build dcs).Sound dcs := by
  rw [DenseTwoRootMap.build]
  by_cases hp : Nat.Prime p
  · rw [if_pos hp]
    exact DenseTwoRootMap.Sound.addAll hp DenseTwoRootMap.empty dcs (fun _ h => h)
      (DenseTwoRootMap.empty_sound dcs)
  · rw [if_neg hp]; exact DenseTwoRootMap.empty_sound dcs

/-! ## Two-root decomposition soundness (native, value-level)

The keystone the dense `rootPairUnify` (and `busPairCancel`) proofs consume: a recognized
`denseTwoRootOf?` puts `x` at one of the two roots on every satisfying dense assignment, proved
directly over `DenseExpr`/`DenseLinExpr` evaluation via the field core `twoRoot_mem`. No registry
or decode is involved — the statement and proof are entirely `VarId`-native. -/

/-- Two dense linear forms with equal term lists evaluate a constant apart. -/
theorem DenseLinExpr.eval_of_terms_eq (a b : DenseLinExpr p) (h : b.terms = a.terms)
    (denv : VarId → ZMod p) : b.eval denv = a.eval denv + (b.const - a.const) := by
  simp only [DenseLinExpr.eval, h]; ring

/-- **`denseTwoRootOf?` is sound.** A recognized two-root decomposition `(k, A, δ)` of a constraint
    `c` (a product of two affine factors, both linear in `x` with the same unit coefficient `k`,
    `x`-free parts a constant `δ` apart) places `x` at one of the two roots `-(k⁻¹·A)` and
    `-(k⁻¹·A) - k⁻¹·δ` on every satisfying assignment. Proved natively over dense evaluation. -/
theorem denseTwoRootOf?_sound [Fact p.Prime] (c : DenseExpr p) (x : VarId)
    (k : ZMod p) (A : DenseLinExpr p) (δ : ZMod p)
    (h : denseTwoRootOf? c x = some (k, A, δ)) (hk : k * k⁻¹ = 1)
    (denv : VarId → ZMod p) (hcz : c.eval denv = 0) :
    denv x = -(k⁻¹ * A.eval denv) ∨ denv x = -(k⁻¹ * A.eval denv) - k⁻¹ * δ := by
  cases c with
  | const n => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | var i => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | add a b => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | mul f1 f2 =>
      simp only [denseTwoRootOf?] at h
      cases hl1 : denseLinearize f1 with
      | none => simp only [hl1] at h; exact absurd h (by simp)
      | some l1 =>
        cases hl2 : denseLinearize f2 with
        | none => simp only [hl1, hl2] at h; exact absurd h (by simp)
        | some l2 =>
          simp only [hl1, hl2] at h
          split_ifs at h with hcond
          · obtain ⟨hk0, hcoeff, hterms⟩ := hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hf1 : f1.eval denv = ((l1.others x).norm).eval denv + l1.coeff x * denv x := by
              rw [denseLinearize_eval f1 l1 hl1 denv, l1.eval_split x]
              have := DenseLinExpr.norm_eval (l1.others x) denv
              rw [this]; ring
            have hf2 : f2.eval denv = ((l1.others x).norm).eval denv
                + ((l2.others x).norm.const - (l1.others x).norm.const) + l1.coeff x * denv x := by
              rw [denseLinearize_eval f2 l2 hl2 denv, l2.eval_split x, hcoeff]
              have h2 := DenseLinExpr.norm_eval (l2.others x) denv
              have h3 := DenseLinExpr.eval_of_terms_eq (l1.others x).norm (l2.others x).norm hterms
                denv
              rw [← h2, h3]; ring
            have hprod : (((l1.others x).norm).eval denv + l1.coeff x * denv x)
                * (((l1.others x).norm).eval denv
                  + ((l2.others x).norm.const - (l1.others x).norm.const)
                  + l1.coeff x * denv x) = 0 := by
              rw [← hf1, ← hf2]; exact hcz
            exact twoRoot_mem (l1.coeff x) (((l1.others x).norm).eval denv) _ (denv x) hk hprod

/-! ## Substituting a two-root branch into a linear form (native eval) -/

/-- The two branch forms of `densePtrBranchesOf` evaluate to `rest` plus the substituted root value.
    Native mirror of `ptrBranchesOf_eval`. -/
theorem densePtrBranchesOf_eval (k : ZMod p) (A : DenseLinExpr p) (δ cx : ZMod p)
    (rest : DenseLinExpr p) (denv : VarId → ZMod p) :
    ((densePtrBranchesOf k A δ cx rest).1).eval denv
        = rest.eval denv + cx * (-(k⁻¹) * A.eval denv) ∧
    ((densePtrBranchesOf k A δ cx rest).2).eval denv
        = rest.eval denv + cx * (-(k⁻¹) * A.eval denv - k⁻¹ * δ) := by
  have hc0 : (⟨-(k⁻¹ * δ), []⟩ : DenseLinExpr p).eval denv = -(k⁻¹ * δ) := by simp [DenseLinExpr.eval]
  refine ⟨?_, ?_⟩
  · simp only [densePtrBranchesOf, DenseLinExpr.norm_eval, DenseLinExpr.add_eval,
      DenseLinExpr.scale_eval]
  · simp only [densePtrBranchesOf, DenseLinExpr.norm_eval, DenseLinExpr.add_eval,
      DenseLinExpr.scale_eval, hc0]
    ring

/-! ## `densePtrReductions` soundness (native, via the two-root soundness) -/

/-- **`densePtrReductions` is sound** (native): every reduction pair of an expression brackets its
    value under any dense environment satisfying the constraints the map was built from. Mirrors
    `ptrReductions_sound`, using the native `denseTwoRootOf?_sound` and `densePtrBranchesOf_eval`. -/
theorem densePtrReductions_sound {dcs : List (DenseExpr p)}
    (T : DenseTwoRootMap p) (hT : T.Sound dcs)
    (E : DenseExpr p) (b1 b2 : DenseLinExpr p)
    (hmem : (b1, b2) ∈ densePtrReductions T E) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    E.eval denv = b1.eval denv ∨ E.eval denv = b2.eval denv := by
  unfold densePtrReductions at hmem
  cases hL : denseLinearize E with
  | none => rw [hL] at hmem; simp at hmem
  | some L =>
    rw [hL] at hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨v, _hv, hmatch⟩ := hmem
    cases htm : T.map[v]? with
    | none => rw [htm] at hmatch; simp at hmatch
    | some kAδ =>
      obtain ⟨k, A, δ⟩ := kAδ
      rw [htm] at hmatch
      dsimp only at hmatch
      simp only [Option.some.injEq] at hmatch
      obtain ⟨hp, hunit, c, hc, htr⟩ := hT v k A δ htm
      haveI : Fact p.Prime := ⟨hp⟩
      have hroot := denseTwoRootOf?_sound c v k A δ htr hunit denv (hcon c hc)
      have hEL : E.eval denv = L.eval denv := denseLinearize_eval E L hL denv
      have hsplit : L.eval denv = L.coeff v * denv v + (L.others v).eval denv := L.eval_split v denv
      obtain ⟨he1, he2⟩ := densePtrBranchesOf_eval k A δ (L.coeff v) (L.others v) denv
      have hb1 : b1 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).1 :=
        (congrArg Prod.fst hmatch).symm
      have hb2 : b2 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).2 :=
        (congrArg Prod.snd hmatch).symm
      rcases hroot with hr | hr
      · left; rw [hEL, hsplit, hr, hb1, he1]; ring
      · right; rw [hEL, hsplit, hr, hb2, he2]; ring

/-- **`denseExprTwoRootNeq` is sound** (native). Mirrors `exprTwoRootNeq_sound`. -/
theorem denseExprTwoRootNeq_sound {dcs : List (DenseExpr p)}
    (T : DenseTwoRootMap p) (hT : T.Sound dcs) (e e' : DenseExpr p)
    (h : denseExprTwoRootNeq T e e' = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) : e.eval denv ≠ e'.eval denv := by
  unfold denseExprTwoRootNeq at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨a1, a2⟩, hred, hinner⟩ := h
  rw [List.any_eq_true] at hinner
  obtain ⟨⟨b1, b2⟩, hred', hchk⟩ := hinner
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨h11, h12⟩, h21⟩, h22⟩ := hchk
  have hev := densePtrReductions_sound T hT e a1 a2 hred denv hcon
  have hev' := densePtrReductions_sound T hT e' b1 b2 hred' denv hcon
  rcases hev with ha | ha <;> rcases hev' with hb | hb <;> rw [ha, hb]
  · exact denseConstDiffNZ_sound a1 b1 h11 denv
  · exact denseConstDiffNZ_sound a1 b2 h12 denv
  · exact denseConstDiffNZ_sound a2 b1 h21 denv
  · exact denseConstDiffNZ_sound a2 b2 h22 denv

/-- **`denseAddrTwoRootNeq` is sound** (native). Some address slot's two interactions provably differ,
    so the addresses differ. Consumes the lookup-wise `DenseTwoRootMap.Sound` invariant. -/
theorem denseAddrTwoRootNeq_sound (reg : VarRegistry) (shape : MemoryBusShape)
    {dcs : List (DenseExpr p)} (T : DenseTwoRootMap p) (hT : T.Sound dcs)
    (_hdcov : ∀ c ∈ dcs, c.CoveredBy reg) (S bi : BusInteraction (DenseExpr p))
    (_hS : denseBICovered reg S) (_hbi : denseBICovered reg bi)
    (h : denseAddrTwoRootNeq shape T S bi = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  unfold denseAddrTwoRootNeq at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : bi.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at hcond
      have hne := denseExprTwoRootNeq_sound T hT e e' hcond denv hcon
      exact denseAddr_slot_neq shape S bi denv hslot hSp hbp hne

/-! ## The nonzero-witness (register-vs-RAM) certificate (native) -/

/-- **`denseIsZeroLin` is sound.** A form recognized as identically zero evaluates to `0`. Native
    mirror of `isZeroLin_sound`. -/
theorem denseIsZeroLin_sound (l : DenseLinExpr p) (h : denseIsZeroLin l = true)
    (denv : VarId → ZMod p) : l.eval denv = 0 := by
  unfold denseIsZeroLin at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hterms, hconst⟩ := h
  have hz : l.norm.eval denv = l.norm.const := by
    simp only [DenseLinExpr.eval, List.isEmpty_iff.1 hterms, List.map_nil, List.sum_nil, add_zero]
  rw [← DenseLinExpr.norm_eval, hz, hconst]

/-- **`denseReciprocalWitsProd` is sound.** Each recognized factor of a reciprocal product `a·b + r`
    (with `r` a nonzero constant) is nonzero. Native mirror of `reciprocalWitsProd_sound`. -/
theorem denseReciprocalWitsProd_sound (a b r : DenseExpr p) (g : DenseLinExpr p)
    (h : g ∈ denseReciprocalWitsProd a b r) (denv : VarId → ZMod p)
    (hc : a.eval denv * b.eval denv + r.eval denv = 0) : g.eval denv ≠ 0 := by
  unfold denseReciprocalWitsProd at h
  cases hr : denseLinearize r with
  | none => simp [hr] at h
  | some lr =>
    simp only [hr] at h
    split_ifs at h with hcond
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hterms, hne⟩ := hcond
      have hrconst : r.eval denv = lr.const := by
        rw [denseLinearize_eval r lr hr denv]
        simp only [DenseLinExpr.eval, List.isEmpty_iff.1 hterms, List.map_nil, List.sum_nil, add_zero]
      have hrne : r.eval denv ≠ 0 := by rw [hrconst]; exact hne
      have hprodne : a.eval denv * b.eval denv ≠ 0 := by
        intro hp0; rw [hp0] at hc; exact hrne (by linear_combination hc)
      have hane : a.eval denv ≠ 0 := fun ha => hprodne (by rw [ha, zero_mul])
      have hbne : b.eval denv ≠ 0 := fun hb => hprodne (by rw [hb, mul_zero])
      rw [List.mem_append] at h
      rcases h with hla | hlb
      · cases ha : denseLinearize a with
        | none => rw [ha] at hla; simp at hla
        | some la =>
          rw [ha] at hla; simp only [List.mem_singleton] at hla
          rw [hla, ← denseLinearize_eval a la ha denv]; exact hane
      · cases hb : denseLinearize b with
        | none => rw [hb] at hlb; simp at hlb
        | some lb =>
          rw [hb] at hlb; simp only [List.mem_singleton] at hlb
          rw [hlb, ← denseLinearize_eval b lb hb denv]; exact hbne
    · simp at h

/-- **`denseReciprocalWits?` is sound.** Native mirror of `reciprocalWits?_sound`. -/
theorem denseReciprocalWits?_sound (c : DenseExpr p) (g : DenseLinExpr p)
    (h : g ∈ denseReciprocalWits? c) (denv : VarId → ZMod p) (hc : c.eval denv = 0) :
    g.eval denv ≠ 0 := by
  unfold denseReciprocalWits? at h
  split at h
  · rename_i e1 e2
    split at h
    · rename_i a b
      exact denseReciprocalWitsProd_sound a b e2 g h denv (by rw [← hc]; simp [DenseExpr.eval])
    · split at h
      · rename_i a b
        exact denseReciprocalWitsProd_sound a b e1 g h denv
          (by rw [← hc]; simp only [DenseExpr.eval]; ring)
      · simp at h
  · simp at h

/-- If the two interactions agree at every listed slot (under `denv`), the difference sum is `0`.
    Native mirror of `diffSumOver_eval_zero`. -/
theorem denseDiffSumOver_eval_zero (S m : BusInteraction (DenseExpr p)) (fields : List Nat)
    (D : DenseLinExpr p) (h : denseDiffSumOver S m fields = some D) (denv : VarId → ZMod p)
    (hslots : ∀ f ∈ fields,
      (denseBIEval S denv).payload[f]? = (denseBIEval m denv).payload[f]?) :
    D.eval denv = 0 := by
  induction fields generalizing D with
  | nil =>
    simp only [denseDiffSumOver, Option.some.injEq] at h; subst h
    simp [DenseLinExpr.eval]
  | cons f fs ih =>
    simp only [denseDiffSumOver] at h
    cases hacc : denseDiffSumOver S m fs with
    | none => simp [hacc] at h
    | some acc =>
      cases hSp : S.payload[f]? with
      | none => simp [hacc, hSp] at h
      | some eS =>
        cases hmp : m.payload[f]? with
        | none => simp [hacc, hSp, hmp] at h
        | some eM =>
          cases hlS : denseLinearize eS with
          | none => simp [hacc, hSp, hmp, hlS] at h
          | some lS =>
            cases hlM : denseLinearize eM with
            | none => simp [hacc, hSp, hmp, hlS, hlM] at h
            | some lM =>
              simp only [hacc, hSp, hmp, hlS, hlM, Option.some.injEq] at h
              subst h
              have haccz : acc.eval denv = 0 :=
                ih acc hacc (fun f' hf' => hslots f' (List.mem_cons_of_mem _ hf'))
              have hkey : (denseBIEval S denv).payload[f]? = (denseBIEval m denv).payload[f]? :=
                hslots f (List.mem_cons_self ..)
              have hSev : (denseBIEval S denv).payload[f]? = some (eS.eval denv) := by
                show (S.payload.map (fun e => e.eval denv))[f]? = _
                rw [List.getElem?_map, hSp]; rfl
              have hMev : (denseBIEval m denv).payload[f]? = some (eM.eval denv) := by
                show (m.payload.map (fun e => e.eval denv))[f]? = _
                rw [List.getElem?_map, hmp]; rfl
              rw [hSev, hMev] at hkey
              have hval : eS.eval denv = eM.eval denv := (Option.some.inj hkey)
              have hlMe := denseLinearize_eval eM lM hlM denv
              have hlSe := denseLinearize_eval eS lS hlS denv
              rw [DenseLinExpr.add_eval, DenseLinExpr.add_eval, DenseLinExpr.scale_eval]
              linear_combination -hlMe + hlSe - hval + haccz

/-- **`denseAddrNonzeroNeq` is sound** (native). Some subset `T` of the address fields has
    limb-difference sum equal (up to sign) to a nonzero witness `g`; were the addresses equal that
    sum would vanish, contradicting `g ≠ 0`. Native mirror of `addrNonzeroNeq_sound`. -/
theorem denseAddrNonzeroNeq_sound (reg : VarRegistry) (shape : MemoryBusShape)
    (dcs : List (DenseExpr p)) (_hdcov : ∀ c ∈ dcs, c.CoveredBy reg)
    (S m : BusInteraction (DenseExpr p)) (_hS : denseBICovered reg S) (_hm : denseBICovered reg m)
    (h : denseAddrNonzeroNeq shape (DenseNonzeroWits.build dcs) S m = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval m denv) := by
  intro heq
  unfold denseAddrNonzeroNeq at h
  rw [List.any_eq_true] at h
  obtain ⟨T, hT, hcond⟩ := h
  have hTsub : List.Sublist T shape.addressFields := List.mem_sublists.mp hT
  cases hD : denseDiffSumOver S m T with
  | none => rw [hD] at hcond; simp at hcond
  | some D =>
    rw [hD] at hcond
    rw [List.any_eq_true] at hcond
    obtain ⟨g, hg, hzero⟩ := hcond
    have hDzero : D.eval denv = 0 :=
      denseDiffSumOver_eval_zero S m T D hD denv (fun f hf =>
        denseAddr_eq_slot shape S m denv heq f (hTsub.subset hf))
    have hgne : g.eval denv ≠ 0 := by
      have hgm : g ∈ dcs.flatMap denseReciprocalWits? := hg
      rw [List.mem_flatMap] at hgm
      obtain ⟨c, hc, hgc⟩ := hgm
      exact denseReciprocalWits?_sound c g hgc denv (hcon c hc)
    rcases (Bool.or_eq_true _ _).mp hzero with hz | hz
    · have hzz := denseIsZeroLin_sound _ hz denv
      rw [DenseLinExpr.add_eval, DenseLinExpr.scale_eval, hDzero] at hzz
      exact hgne (by linear_combination -hzz)
    · have hzz := denseIsZeroLin_sound _ hz denv
      rw [DenseLinExpr.add_eval, hDzero] at hzz
      exact hgne (by linear_combination hzz)

end ApcOptimizer.Dense
