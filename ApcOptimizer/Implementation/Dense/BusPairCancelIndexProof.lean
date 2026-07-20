import ApcOptimizer.Implementation.Dense.BusPairCancelIndex
import ApcOptimizer.Implementation.Dense.BusPairCancelJustifyProof
import ApcOptimizer.Implementation.Dense.BusUnifyNativeProof

set_option autoImplicit false

/-! # Native soundness of the dense hash index + entailed-equality maps (Task 3, chunk C3 — prover)

Native, `VarId`-native soundness layer for the per-invocation hash-indexing and entailed-equality
machinery defined (impl-only) in `Dense/BusPairCancelIndex.lean` — the dense mirror of the
proof-carrying spec structures `VarCsIdx`, `EqConstraintMap`, and the lemma
`payloadEntailedEq_sound` in `OptimizerPasses/BusPairCancel.lean` (:1278-1489). The impl structures
dropped their `sound` proof fields (and the `constraints` index parameter that existed only to
state `sound`); this file re-establishes those soundness invariants as **separate lookup-wise
`Sound` predicates**, exactly the shape of `DenseTwoRootMap.Sound`
(`Dense/AddrDiseqProof.lean`) — invariants proved by induction along the build ops, *not* whole-map
decode equality. Everything here is native over `VarId → ZMod p` environments; no `decode` appears
and no dependency on the reference `Variable` pass is introduced.

## What C5 (`checkCancel`) / C7 (the loop) consume

* `DenseVarCsIdx.Sound` + `build_sound` + `lookup_mem` — the dense mirror of the spec
  `VarCsIdx.sound` field and `VarCsIdx.lookup_mem` (:1346). C5 feeds `candsT.get.lookup` as the
  per-variable candidate list and `fun x => (build_sound …).lookup_mem x` as the membership witness
  (the spec's `candsT.get.lookup_mem`, :2474/:2496).
* `DenseEqConstraintMap.Sound` + `build_sound` + `test_sound` — the dense mirror of the spec
  `EqConstraintMap.sound` field and `EqConstraintMap.test_sound` (:1431). The non-aggressive cycle
  uses `DenseEqConstraintMap.empty` (`empty_sound`); the aggressive coda uses
  `DenseEqConstraintMap.build d.algebraicConstraints` (`build_sound`).
* `densePayloadEntailedEq_sound` — the dense mirror of `payloadEntailedEq_sound` (:1468), shaped so
  that C5 supplies `S.payload`/`R.payload` and obtains the *evaluated* payload equality
  `S.payload.map (·.eval denv) = R.payload.map (·.eval denv)`, which is definitionally
  `(denseBIEval S denv).payload = (denseBIEval R denv).payload` — **exactly** C2's `hpayEval`
  hypothesis in `Dense/BusPairCancelCore.lean`'s `denseDropPair_correct` (:217). The spec obtains
  the same at :2092 via `payloadEntailedEq_sound M S.payload R.payload hpay env hcon`.

## Native affine-normalization evaluation

`test_sound`/`densePayloadEntailedEq_sound` need `(DenseExpr.normalize e).eval denv = e.eval denv`
(the dense mirror of `Expression.normalize_eval`, `OptimizerPasses/Normalize.lean:318`). It is
assembled here natively from the existing `denseLinearize_eval` / `DenseLinExpr.norm_eval`
(`Dense/DomainBatchNativeProof.lean`) and a new `DenseLinExpr.toExpr_eval` (the dense mirror of
`LinExpr.toExpr_eval`, `OptimizerPasses/Affine.lean:160`). No prime hypothesis is required — these
are pure algebraic identities.

## Bucket lemmas left to C5

`denseRecvIndexAll` builds an ascending-bucket receive index (module header of
`BusPairCancelIndex.lean`); its bucket-membership / ascending-order properties feed `firstMatchAt`.
The spec proves *no* standalone `recvIndexAll` bucket lemma — `firstMatchAt`/`firstMatchAt_spec`
(:1731-2104 in the spec) reason about the index inline at their own use site. Following that
structure, no `denseRecvIndexAll` bucket lemma is proved here; it is left to C5 alongside
`firstMatchAt`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The per-variable candidate-constraint index: `DenseVarCsIdx.Sound`

The native affine-normalization eval lemmas this file consumes (`DenseLinExpr.toExpr_eval`,
`DenseExpr.normalize_eval`) now live at their definitions' home in `Dense/Affine.lean` and
`Dense/Normalize.lean` (shared, proved once). -/

/-- The dense mirror of `VarCsIdx.sound` (`OptimizerPasses/BusPairCancel.lean:1280`): every entry of
    every successfully-looked-up bucket is one of the indexed `constraints`. Proved lookup-wise by
    induction along the build ops, exactly like `DenseTwoRootMap.Sound`. -/
def DenseVarCsIdx.Sound (constraints : List (DenseExpr p)) (I : DenseVarCsIdx p) : Prop :=
  ∀ (x : VarId) (l : List (DenseExpr p)), I.map[x]? = some l → ∀ c ∈ l, c ∈ constraints

theorem DenseVarCsIdx.empty_sound (constraints : List (DenseExpr p)) :
    (DenseVarCsIdx.empty : DenseVarCsIdx p).Sound constraints := by
  intro x l h
  simp only [DenseVarCsIdx.empty, Std.HashMap.getElem?_empty] at h
  exact absurd h (by simp)

theorem DenseVarCsIdx.insertC_sound {constraints : List (DenseExpr p)} {I : DenseVarCsIdx p}
    (hI : I.Sound constraints) (x : VarId) (c : DenseExpr p) (hc : c ∈ constraints) :
    (I.insertC x c).Sound constraints := by
  intro y l hl c' hc'
  cases hb : I.map[x]? with
  | none =>
      simp only [DenseVarCsIdx.insertC, hb, Std.HashMap.getElem?_insert] at hl
      by_cases hxy : (x == y) = true
      · rw [if_pos hxy] at hl
        have hle : [c] = l := by simpa using hl
        rw [← hle, List.mem_singleton] at hc'
        exact hc' ▸ hc
      · rw [if_neg hxy] at hl
        exact hI y l hl c' hc'
  | some old =>
      by_cases hlen : old.length < maxDeepConstraints
      · simp only [DenseVarCsIdx.insertC, hb, hlen, if_true, Std.HashMap.getElem?_insert] at hl
        by_cases hxy : (x == y) = true
        · rw [if_pos hxy] at hl
          have hle : old ++ [c] = l := by simpa using hl
          rw [← hle, List.mem_append] at hc'
          rcases hc' with h' | h'
          · exact hI x old hb c' h'
          · rw [List.mem_singleton] at h'
            exact h' ▸ hc
        · rw [if_neg hxy] at hl
          exact hI y l hl c' hc'
      · simp only [DenseVarCsIdx.insertC, hb, hlen, if_false] at hl
        exact hI y l hl c' hc'

/-- Folding `insertC` over any variable list preserves `Sound` (given `c` is an indexed
    constraint). -/
theorem DenseVarCsIdx.foldlInsertC_sound {constraints : List (DenseExpr p)} {c : DenseExpr p}
    (hc : c ∈ constraints) : ∀ (I : DenseVarCsIdx p) (vs : List VarId), I.Sound constraints →
      (vs.foldl (fun I x => I.insertC x c) I).Sound constraints := by
  intro I vs
  induction vs generalizing I with
  | nil => intro hI; exact hI
  | cons v rest ih => intro hI; exact ih _ (DenseVarCsIdx.insertC_sound hI v c hc)

theorem DenseVarCsIdx.addConstraint_sound {constraints : List (DenseExpr p)} {I : DenseVarCsIdx p}
    (hI : I.Sound constraints) {c : DenseExpr p} (hc : c ∈ constraints) :
    (I.addConstraint c).Sound constraints :=
  DenseVarCsIdx.foldlInsertC_sound hc I c.vars.dedup hI

theorem DenseVarCsIdx.addAll_sound {constraints : List (DenseExpr p)} :
    ∀ (I : DenseVarCsIdx p) (pending : List (DenseExpr p)), (∀ c ∈ pending, c ∈ constraints) →
      I.Sound constraints → (I.addAll pending).Sound constraints := by
  intro I pending
  induction pending generalizing I with
  | nil => intro _ hI; exact hI
  | cons c rest ih =>
      intro hmem hI
      rw [DenseVarCsIdx.addAll]
      exact ih _ (fun c' h => hmem c' (List.mem_cons_of_mem _ h))
        (DenseVarCsIdx.addConstraint_sound hI (hmem c (List.mem_cons_self ..)))

/-- **The built index is sound.** Dense mirror of `VarCsIdx.build`'s soundness. -/
theorem DenseVarCsIdx.build_sound (constraints : List (DenseExpr p)) :
    (DenseVarCsIdx.build constraints).Sound constraints := by
  rw [DenseVarCsIdx.build]
  exact DenseVarCsIdx.addAll_sound DenseVarCsIdx.empty constraints (fun _ h => h)
    (DenseVarCsIdx.empty_sound constraints)

/-- Every looked-up candidate constraint is one of the indexed constraints. Dense mirror of
    `VarCsIdx.lookup_mem` (`OptimizerPasses/BusPairCancel.lean:1346`); the `Sound` invariant is an
    explicit argument (the impl structure dropped its `sound` field). -/
theorem DenseVarCsIdx.lookup_mem {constraints : List (DenseExpr p)} {I : DenseVarCsIdx p}
    (hI : I.Sound constraints) (x : VarId) : ∀ c ∈ I.lookup x, c ∈ constraints := by
  intro c hc
  unfold DenseVarCsIdx.lookup at hc
  cases hb : I.map[x]? with
  | none => rw [hb] at hc; simp at hc
  | some l => rw [hb] at hc; exact hI x l hb c hc

/-! ## The normalized-constraint hash index: `DenseEqConstraintMap.Sound` -/

/-- The dense mirror of `EqConstraintMap.sound` (`OptimizerPasses/BusPairCancel.lean:1377`): every
    entry of every bucket is witnessed as the normalization of an actual indexed constraint. Proved
    lookup-wise, not by decode-equality. -/
def DenseEqConstraintMap.Sound (constraints : List (DenseExpr p))
    (M : DenseEqConstraintMap p) : Prop :=
  ∀ (h : UInt64) (ns : List (DenseExpr p)), M.map[h]? = some ns →
    ∀ n ∈ ns, ∃ c ∈ constraints, c.normalize = n

theorem DenseEqConstraintMap.empty_sound (constraints : List (DenseExpr p)) :
    (DenseEqConstraintMap.empty : DenseEqConstraintMap p).Sound constraints := by
  intro h ns hns
  simp only [DenseEqConstraintMap.empty, Std.HashMap.getElem?_empty] at hns
  exact absurd hns (by simp)

theorem DenseEqConstraintMap.insertNorm_sound {constraints : List (DenseExpr p)}
    {M : DenseEqConstraintMap p} (hM : M.Sound constraints) (n : DenseExpr p)
    (hw : ∃ c ∈ constraints, c.normalize = n) : (M.insertNorm n).Sound constraints := by
  intro h ns hns m hm
  simp only [DenseEqConstraintMap.insertNorm, Std.HashMap.getElem?_insert] at hns
  by_cases hh : (n.bHash == h) = true
  · rw [if_pos hh] at hns
    have hns' : n :: (M.map[n.bHash]?).getD [] = ns := by simpa using hns
    rw [← hns'] at hm
    rcases List.mem_cons.1 hm with rfl | hm'
    · exact hw
    · cases hb : M.map[n.bHash]? with
      | none => rw [hb] at hm'; simp at hm'
      | some old => rw [hb] at hm'; exact hM n.bHash old hb m (by simpa using hm')
  · rw [if_neg hh] at hns
    exact hM h ns hns m hm

theorem DenseEqConstraintMap.addAll_sound {constraints : List (DenseExpr p)} :
    ∀ (M : DenseEqConstraintMap p) (pending : List (DenseExpr p)),
      (∀ c ∈ pending, c ∈ constraints) → M.Sound constraints →
      (M.addAll pending).Sound constraints := by
  intro M pending
  induction pending generalizing M with
  | nil => intro _ hM; exact hM
  | cons c rest ih =>
      intro hmem hM
      rw [DenseEqConstraintMap.addAll]
      exact ih _ (fun c' h => hmem c' (List.mem_cons_of_mem _ h))
        (DenseEqConstraintMap.insertNorm_sound hM c.normalize
          ⟨c, hmem c (List.mem_cons_self ..), rfl⟩)

/-- **The built map is sound.** Dense mirror of `EqConstraintMap.build`'s soundness. -/
theorem DenseEqConstraintMap.build_sound (constraints : List (DenseExpr p)) :
    (DenseEqConstraintMap.build constraints).Sound constraints := by
  rw [DenseEqConstraintMap.build]
  exact DenseEqConstraintMap.addAll_sound DenseEqConstraintMap.empty constraints (fun _ h => h)
    (DenseEqConstraintMap.empty_sound constraints)

/-- A passing `test d` means `d` evaluates to zero whenever the indexed constraints hold. Dense
    mirror of `EqConstraintMap.test_sound` (`OptimizerPasses/BusPairCancel.lean:1431`); the `Sound`
    invariant is an explicit argument. -/
theorem DenseEqConstraintMap.test_sound {constraints : List (DenseExpr p)}
    (M : DenseEqConstraintMap p) (hM : M.Sound constraints) (d : DenseExpr p)
    (h : M.test d = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ constraints, c.eval denv = 0) : d.eval denv = 0 := by
  unfold DenseEqConstraintMap.test at h
  cases hb : M.map[d.bHash]? with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some ns =>
      rw [hb] at h
      obtain ⟨n, hn, heq⟩ := List.any_eq_true.1 h
      obtain ⟨c, hc, hcn⟩ := hM d.bHash ns hb n hn
      have hnd : n = d := of_decide_eq_true heq
      rw [← hnd, ← hcn, DenseExpr.normalize_eval]
      exact hcon c hc

/-! ## Constraint-entailed payload matching: `densePayloadEntailedEq_sound` -/

/-- **A passing entailed-payload match makes the *evaluated* payloads equal whenever the constraints
    hold.** Dense mirror of `payloadEntailedEq_sound` (`OptimizerPasses/BusPairCancel.lean:1468`).
    The `Sound` invariant on the (forced) map is an explicit hypothesis. C5 supplies `S.payload` and
    `R.payload`; the resulting `S.payload.map (·.eval denv) = R.payload.map (·.eval denv)` is
    definitionally `(denseBIEval S denv).payload = (denseBIEval R denv).payload`, i.e. C2's
    `hpayEval` for `denseDropPair_correct`. -/
theorem densePayloadEntailedEq_sound {constraints : List (DenseExpr p)}
    (M : Thunk (DenseEqConstraintMap p)) (hM : M.get.Sound constraints) :
    ∀ (pl pl' : List (DenseExpr p)), densePayloadEntailedEq M pl pl' = true →
    ∀ (denv : VarId → ZMod p), (∀ c ∈ constraints, c.eval denv = 0) →
      pl.map (fun e => e.eval denv) = pl'.map (fun e => e.eval denv)
  | [], [], _, _, _ => rfl
  | e :: es, e' :: es', h, denv, hcon => by
      rw [densePayloadEntailedEq, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
      obtain ⟨hslot, hrest⟩ := h
      have hev : e.eval denv = e'.eval denv := by
        rcases hslot with (hs | hs) | hs
        · rw [of_decide_eq_true hs]
        · have := M.get.test_sound hM _ hs denv hcon
          rw [DenseExpr.normalize_eval, denseEqExpr_eval] at this
          exact sub_eq_zero.mp this
        · have := M.get.test_sound hM _ hs denv hcon
          rw [DenseExpr.normalize_eval, denseEqExpr_eval] at this
          exact (sub_eq_zero.mp this).symm
      simp only [List.map_cons, hev,
        densePayloadEntailedEq_sound M hM es es' hrest denv hcon]
  | [], _ :: _, h, _, _ => by simp [densePayloadEntailedEq] at h
  | _ :: _, [], h, _, _ => by simp [densePayloadEntailedEq] at h

end ApcOptimizer.Dense
