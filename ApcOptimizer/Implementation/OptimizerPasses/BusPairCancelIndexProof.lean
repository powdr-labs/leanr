import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelIndex
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustifyProof
import ApcOptimizer.Implementation.OptimizerPasses.BusUnifyProof

set_option autoImplicit false

/-! # Soundness of the dense hash index + entailed-equality maps

Over `VarId → ZMod p`, for the machinery in `BusPairCancelIndex.lean`. Those impl structures carry
no `sound` field; this file establishes their invariants as separate lookup-wise `Sound` predicates,
proved by induction along the build ops. No standalone `denseRecvIndexAll` bucket lemma is proved
here (`denseFirstMatchAt` reasons about the index inline at its own use site). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `DenseVarCsIdx.Sound` -/

/-- Every entry of every looked-up bucket is one of the indexed `constraints`. -/
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

/-- **The built index is sound.** -/
theorem DenseVarCsIdx.build_sound (constraints : List (DenseExpr p)) :
    (DenseVarCsIdx.build constraints).Sound constraints := by
  rw [DenseVarCsIdx.build]
  exact DenseVarCsIdx.addAll_sound DenseVarCsIdx.empty constraints (fun _ h => h)
    (DenseVarCsIdx.empty_sound constraints)

/-- Every looked-up candidate constraint is one of the indexed constraints. -/
theorem DenseVarCsIdx.lookup_mem {constraints : List (DenseExpr p)} {I : DenseVarCsIdx p}
    (hI : I.Sound constraints) (x : VarId) : ∀ c ∈ I.lookup x, c ∈ constraints := by
  intro c hc
  unfold DenseVarCsIdx.lookup at hc
  cases hb : I.map[x]? with
  | none => rw [hb] at hc; simp at hc
  | some l => rw [hb] at hc; exact hI x l hb c hc

/-! ## `DenseEqConstraintMap.Sound` -/

/-- Every entry of every bucket is witnessed as the normalization of an actual indexed constraint. -/
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

/-- **The built map is sound.** -/
theorem DenseEqConstraintMap.build_sound (constraints : List (DenseExpr p)) :
    (DenseEqConstraintMap.build constraints).Sound constraints := by
  rw [DenseEqConstraintMap.build]
  exact DenseEqConstraintMap.addAll_sound DenseEqConstraintMap.empty constraints (fun _ h => h)
    (DenseEqConstraintMap.empty_sound constraints)

/-- A passing `test d` means `d` evaluates to zero whenever the indexed constraints hold. -/
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

/-- A passing entailed-payload match makes the *evaluated* payloads equal whenever the constraints
    hold — the `hpayEval` hypothesis `denseDropPair_correct` takes. -/
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
