import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.ExprOps
import ApcOptimizer.Implementation.OptimizerPasses.Adapter

set_option autoImplicit false

/-! # Dense affine normalization

`DenseExpr.normalize` replaces every maximal affine subexpression by its **merged** normal form
(`denseLinearize`, combine coefficients of equal `VarId`s, drop zeros, rebuild via
`DenseLinExpr.toExpr`).

The pass (`denseNormalizePass`) computes through the fused walk `denseNormalizeFused` — one bottom-up
traversal returning both the normalized expression and the node's linear form, avoiding
`DenseExpr.normalize`'s own O(size × depth) `denseLinearize` re-walks along non-affine paths. Its
correctness is proved as a `DensePassCorrect` over `VarId → ZMod p` environments (the walk is
eval-preserving and introduces no variables) and lifted to the spec `PassCorrect` once, at the
pipeline edge, by `DenseVerifiedPassW.of`. Same shape as `denseConstantFoldPass`
(`Dense/ExprOps.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Merging a dense linear form's terms -/

/-- Add coefficient `c` to `VarId` `v` in a dense term list, merging into an existing entry. -/
def denseAddCoeff (v : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → List (VarId × ZMod p)
  | [] => [(v, c)]
  | (v', c') :: rest => if v' = v then (v', c' + c) :: rest else (v', c') :: denseAddCoeff v c rest

/-- Merge a dense term list, combining coefficients of equal `VarId`s (`foldl`, first-occurrence
    order preserved). -/
def denseMergeTerms (ts : List (VarId × ZMod p)) : List (VarId × ZMod p) :=
  ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) []

/-! ## Linear like-term merge (runtime `@[csimp]` replacement for `denseMergeTerms`)

`denseMergeTerms`/`denseAddCoeff` are O(terms²): every input term linearly scans the accumulated
deduped list. For long affine forms (post-substitution reduced constraints; large blocks such as the
sha256 APC) this is the dominant cost. `denseMergeTermsFast` accumulates each `VarId`'s coefficient
in a `Std.HashMap` while recording first-occurrence order in an `Array`, then rebuilds by walking the
recorded order — O(terms) expected. Below a small constant threshold the list fold is faster (no hash
setup), so a hybrid keeps the tiny-form path (asymptotically still linear: the bounded branch is
O(1)). Proven `= denseMergeTerms` and installed via `@[csimp]`, so every call site
(`DenseLinExpr.norm`, hence the fused normalize walk and gauss's per-constraint reduce) uses it at
runtime with no further proof obligation. -/

/-- The coefficient the first-occurrence-ordered accumulator holds for `v` after merging (the
    coefficient of the unique accumulator entry for `v`, if any). Follows `denseAddCoeff`'s
    structure so its update lemmas are one-line inductions. -/
def denseAssocCoeff : List (VarId × ZMod p) → VarId → Option (ZMod p)
  | [], _ => none
  | (v', c') :: rest, v => if v' = v then some c' else denseAssocCoeff rest v

theorem denseNotMem_of_assocCoeff_none (acc : List (VarId × ZMod p)) (v : VarId)
    (h : denseAssocCoeff acc v = none) : v ∉ acc.map Prod.fst := by
  induction acc with
  | nil => simp
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAssocCoeff] at h
      split at h
      · exact absurd h (by simp)
      · next hne =>
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨fun hh => hne hh.symm, ih h⟩

theorem denseMem_of_assocCoeff_some (acc : List (VarId × ZMod p)) (v : VarId) (c : ZMod p)
    (h : denseAssocCoeff acc v = some c) : v ∈ acc.map Prod.fst := by
  induction acc with
  | nil => simp [denseAssocCoeff] at h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAssocCoeff] at h
      simp only [List.map_cons, List.mem_cons]
      split at h
      · next he => exact Or.inl he.symm
      · next hne => exact Or.inr (ih h)

/-- The effect of one `denseAddCoeff` on `denseAssocCoeff`: bump `v`'s coefficient (0 if absent),
    leave every other variable untouched. -/
theorem denseAssocCoeff_addCoeff (v : VarId) (c : ZMod p) (acc : List (VarId × ZMod p))
    (w : VarId) :
    denseAssocCoeff (denseAddCoeff v c acc) w
      = if w = v then some ((denseAssocCoeff acc v).getD 0 + c) else denseAssocCoeff acc w := by
  induction acc with
  | nil =>
      simp only [denseAddCoeff, denseAssocCoeff, Option.getD_none, zero_add]
      by_cases hwv : w = v
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAddCoeff]
      by_cases hv' : v' = v
      · rw [if_pos hv']
        subst hv'
        simp only [denseAssocCoeff]
        by_cases hwv : w = v'
        · subst hwv; simp
        · have hwv' : ¬ v' = w := fun he => hwv he.symm
          simp only [if_neg hwv, if_neg hwv']
      · rw [if_neg hv']
        simp only [denseAssocCoeff, ih]
        rw [if_neg hv']
        by_cases hv'w : v' = w
        · have hwv : ¬ w = v := fun he => hv' (hv'w.trans he)
          rw [if_pos hv'w, if_neg hwv, if_pos hv'w]
        · rw [if_neg hv'w, if_neg hv'w]

theorem denseAddCoeff_map_fst_of_mem (v : VarId) (c : ZMod p) (acc : List (VarId × ZMod p))
    (h : v ∈ acc.map Prod.fst) : (denseAddCoeff v c acc).map Prod.fst = acc.map Prod.fst := by
  induction acc with
  | nil => simp at h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAddCoeff]
      split
      · next he => simp
      · next hne =>
          simp only [List.map_cons, List.mem_cons] at h
          have hmem : v ∈ rest.map Prod.fst := by
            rcases h with h | h
            · exact absurd h.symm hne
            · exact h
          simp [ih hmem]

theorem denseAddCoeff_append_of_not_mem (v : VarId) (c : ZMod p) (acc : List (VarId × ZMod p))
    (h : v ∉ acc.map Prod.fst) : denseAddCoeff v c acc = acc ++ [(v, c)] := by
  induction acc with
  | nil => simp [denseAddCoeff]
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [List.map_cons, List.mem_cons, not_or] at h
      obtain ⟨hne, hrest⟩ := h
      simp only [denseAddCoeff]
      rw [if_neg (fun he => hne he.symm)]
      simp [ih hrest]

/-- One step of the fast merge: bump `t.1`'s coefficient in the map, appending `t.1` to the order
    array on first occurrence. -/
def denseMtStep (st : Array VarId × Std.HashMap VarId (ZMod p)) (t : VarId × ZMod p) :
    Array VarId × Std.HashMap VarId (ZMod p) :=
  match st.2[t.1]? with
  | some c0 => (st.1, st.2.insert t.1 (c0 + t.2))
  | none => (st.1.push t.1, st.2.insert t.1 t.2)

/-- Correspondence invariant tying the fast `(order, map)` state to the `denseAddCoeff`-fold list. -/
def DenseMergeCorr (acc : List (VarId × ZMod p)) (order : Array VarId)
    (m : Std.HashMap VarId (ZMod p)) : Prop :=
  order.toList = acc.map Prod.fst ∧ (acc.map Prod.fst).Nodup ∧ ∀ v, m[v]? = denseAssocCoeff acc v

theorem denseMtStep_corr (acc : List (VarId × ZMod p)) (order : Array VarId)
    (m : Std.HashMap VarId (ZMod p)) (t : VarId × ZMod p) (h : DenseMergeCorr acc order m) :
    DenseMergeCorr (denseAddCoeff t.1 t.2 acc) (denseMtStep (order, m) t).1
      (denseMtStep (order, m) t).2 := by
  obtain ⟨hord, hnod, hm⟩ := h
  obtain ⟨tv, tc⟩ := t
  have hmtv := hm tv
  rcases hcase : (m[tv]? : Option (ZMod p)) with _ | c0
  · have habs : denseAssocCoeff acc tv = none := by rw [← hmtv, hcase]
    have hnmem : tv ∉ acc.map Prod.fst := denseNotMem_of_assocCoeff_none acc tv habs
    have hstep : denseMtStep (order, m) (tv, tc) = (order.push tv, m.insert tv tc) := by
      simp only [denseMtStep, hcase]
    have hfst : (denseAddCoeff tv tc acc).map Prod.fst = acc.map Prod.fst ++ [tv] := by
      rw [denseAddCoeff_append_of_not_mem tv tc acc hnmem]; simp
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfst, Array.toList_push, hord]
    · rw [hfst]
      exact hnod.append (List.nodup_singleton tv) (List.disjoint_singleton.2 hnmem)
    · intro w
      rw [Std.HashMap.getElem?_insert, denseAssocCoeff_addCoeff, habs]
      simp only [beq_iff_eq, Option.getD_none, zero_add]
      by_cases hwv : tv = w
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
        exact hm w
  · have hpres : denseAssocCoeff acc tv = some c0 := by rw [← hmtv, hcase]
    have hmem : tv ∈ acc.map Prod.fst := denseMem_of_assocCoeff_some acc tv c0 hpres
    have hstep : denseMtStep (order, m) (tv, tc) = (order, m.insert tv (c0 + tc)) := by
      simp only [denseMtStep, hcase]
    have hfst : (denseAddCoeff tv tc acc).map Prod.fst = acc.map Prod.fst :=
      denseAddCoeff_map_fst_of_mem tv tc acc hmem
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfst]; exact hord
    · rw [hfst]; exact hnod
    · intro w
      rw [Std.HashMap.getElem?_insert, denseAssocCoeff_addCoeff, hpres]
      simp only [beq_iff_eq, Option.getD_some]
      by_cases hwv : tv = w
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
        exact hm w

theorem denseMtFold_corr (ts : List (VarId × ZMod p)) :
    ∀ (acc : List (VarId × ZMod p)) (order : Array VarId)
      (m : Std.HashMap VarId (ZMod p)), DenseMergeCorr acc order m →
      DenseMergeCorr (ts.foldl (fun a t => denseAddCoeff t.1 t.2 a) acc)
        (ts.foldl denseMtStep (order, m)).1 (ts.foldl denseMtStep (order, m)).2 := by
  induction ts with
  | nil => intro acc order m h; simpa using h
  | cons t rest ih =>
      intro acc order m h
      simp only [List.foldl_cons]
      exact ih (denseAddCoeff t.1 t.2 acc) (denseMtStep (order, m) t).1
        (denseMtStep (order, m) t).2 (denseMtStep_corr acc order m t h)

theorem denseReconAssoc (acc : List (VarId × ZMod p)) (hnod : (acc.map Prod.fst).Nodup) :
    (acc.map Prod.fst).map (fun v => (v, (denseAssocCoeff acc v).getD 0)) = acc := by
  induction acc with
  | nil => simp
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [List.map_cons] at hnod ⊢
      rw [List.nodup_cons] at hnod
      obtain ⟨hnotin, hnod'⟩ := hnod
      have hhead : (denseAssocCoeff ((v', c') :: rest) v').getD 0 = c' := by simp [denseAssocCoeff]
      have htail : (rest.map Prod.fst).map
          (fun v => (v, (denseAssocCoeff ((v', c') :: rest) v).getD 0))
          = (rest.map Prod.fst).map (fun v => (v, (denseAssocCoeff rest v).getD 0)) := by
        apply List.map_congr_left
        intro v hv
        have hvne : ¬ v' = v := fun he => hnotin (he ▸ hv)
        simp [denseAssocCoeff, if_neg hvne]
      rw [hhead, htail, ih hnod']

theorem denseRecon (acc : List (VarId × ZMod p)) (order : Array VarId)
    (m : Std.HashMap VarId (ZMod p)) (h : DenseMergeCorr acc order m) :
    order.toList.map (fun v => (v, (m[v]?).getD 0)) = acc := by
  obtain ⟨hord, hnod, hm⟩ := h
  rw [hord]
  rw [show (fun v => (v, (m[v]?).getD 0)) = (fun v => (v, (denseAssocCoeff acc v).getD 0)) from
    funext (fun v => by rw [hm v])]
  exact denseReconAssoc acc hnod

/-- The dense linear like-term merge. Proven `= denseMergeTerms` and installed via `@[csimp]`. -/
def denseMergeTermsFast (ts : List (VarId × ZMod p)) : List (VarId × ZMod p) :=
  if ts.length ≤ 32 then
    ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) []
  else
    let st := ts.foldl denseMtStep (#[], ∅)
    st.1.toList.map (fun v => (v, (st.2[v]?).getD 0))

@[csimp] theorem denseMergeTerms_eq_fast : @denseMergeTerms = @denseMergeTermsFast := by
  funext p ts
  show denseMergeTerms ts = denseMergeTermsFast ts
  unfold denseMergeTermsFast
  split
  · rfl
  · have hbase : DenseMergeCorr ([] : List (VarId × ZMod p)) (#[] : Array VarId)
        (∅ : Std.HashMap VarId (ZMod p)) :=
      ⟨by simp, by simp, fun v => by simp [denseAssocCoeff]⟩
    have hcorr := denseMtFold_corr ts [] #[] ∅ hbase
    exact (denseRecon _ _ _ hcorr).symm

/-- The fully-merged normal form of a dense linear form: combine like terms, drop zeros. -/
def DenseLinExpr.norm (l : DenseLinExpr p) : DenseLinExpr p :=
  ⟨l.const, (denseMergeTerms l.terms).filter (fun t => t.2 ≠ 0)⟩

/-! ## The dense normalization traversal -/

/-- Recursively collect like terms: replace each maximal affine subexpression by its merged linear
    form; recurse into genuine variable×variable products. -/
def DenseExpr.normalize : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var x => .var x
  | .add a b =>
      match denseLinearize (DenseExpr.add a b) with
      | some l => l.norm.toExpr
      | none => .add a.normalize b.normalize
  | .mul a b =>
      match denseLinearize (DenseExpr.mul a b) with
      | some l => l.norm.toExpr
      | none => .mul a.normalize b.normalize

/-! ## Eval-preservation of the merge / normal form

Proved over `VarId → ZMod p` environments (no prime hypothesis needed). Consolidated here at their
definitions' home so every downstream proof shares one copy; the affine-form eval lemmas
(`denseLinearize_eval`, `DenseLinExpr.norm_eval`'s `add`/`scale`/`toExpr` pieces) live in
`Dense/Affine.lean`. -/

theorem denseAddCoeff_eval (v : VarId) (c : ZMod p) (ts : List (VarId × ZMod p))
    (denv : VarId → ZMod p) :
    ((denseAddCoeff v c ts).map (fun t => t.2 * denv t.1)).sum
      = c * denv v + (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts with
  | nil => simp [denseAddCoeff]
  | cons t rest ih =>
      simp only [denseAddCoeff]
      split
      · next h => subst h; simp only [List.map_cons, List.sum_cons]; ring
      · simp only [List.map_cons, List.sum_cons, ih]; ring

theorem denseFoldAddCoeff_eval (denv : VarId → ZMod p) (ts acc : List (VarId × ZMod p)) :
    ((ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) acc).map (fun t => t.2 * denv t.1)).sum
      = (acc.map (fun t => t.2 * denv t.1)).sum + (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, denseAddCoeff_eval]
      ring

theorem denseMergeTerms_eval (ts : List (VarId × ZMod p)) (denv : VarId → ZMod p) :
    ((denseMergeTerms ts).map (fun t => t.2 * denv t.1)).sum
      = (ts.map (fun t => t.2 * denv t.1)).sum := by
  simp [denseMergeTerms, denseFoldAddCoeff_eval]

theorem denseDropZero_eval (ts : List (VarId × ZMod p)) (denv : VarId → ZMod p) :
    ((ts.filter (fun t => t.2 ≠ 0)).map (fun t => t.2 * denv t.1)).sum
      = (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons, h]
        simp
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
            List.map_cons, List.sum_cons]

/-- **The dense normal form is eval-preserving.** -/
theorem DenseLinExpr.norm_eval (l : DenseLinExpr p) (denv : VarId → ZMod p) :
    l.norm.eval denv = l.eval denv := by
  simp only [DenseLinExpr.norm, DenseLinExpr.eval, denseDropZero_eval, denseMergeTerms_eval]

/-- **`DenseExpr.normalize` is eval-preserving.** No prime hypothesis needed. -/
theorem DenseExpr.normalize_eval (e : DenseExpr p) (denv : VarId → ZMod p) :
    e.normalize.eval denv = e.eval denv := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
      rw [DenseExpr.normalize]
      cases hl : denseLinearize (DenseExpr.add a b) with
      | some l =>
          rw [DenseLinExpr.toExpr_eval, DenseLinExpr.norm_eval, ← denseLinearize_eval _ l hl]
      | none =>
          simp only [DenseExpr.eval, iha, ihb]
  | mul a b iha ihb =>
      rw [DenseExpr.normalize]
      cases hl : denseLinearize (DenseExpr.mul a b) with
      | some l =>
          rw [DenseLinExpr.toExpr_eval, DenseLinExpr.norm_eval, ← denseLinearize_eval _ l hl]
      | none =>
          simp only [DenseExpr.eval, iha, ihb]

/-! ## Variable bounds (`normalize` introduces no new variable) -/

/-- Every variable of `denseAddCoeff v c ts` is `v` or one of `ts`'s. -/
theorem denseAddCoeff_fst (v : VarId) (c : ZMod p) (ts : List (VarId × ZMod p)) (x : VarId)
    (h : x ∈ (denseAddCoeff v c ts).map Prod.fst) : x = v ∨ x ∈ ts.map Prod.fst := by
  induction ts with
  | nil =>
      simp only [denseAddCoeff, List.map_cons, List.map_nil, List.mem_singleton] at h
      exact Or.inl h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAddCoeff] at h
      split at h
      · rename_i hv
        simp only [List.map_cons, List.mem_cons] at h ⊢
        tauto
      · simp only [List.map_cons, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact (ih h).imp id (Or.inr ·)

theorem denseFoldAddCoeff_fst (ts : List (VarId × ZMod p)) :
    ∀ (init : List (VarId × ZMod p)) (x : VarId),
      x ∈ (ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) init).map Prod.fst →
      x ∈ init.map Prod.fst ∨ x ∈ ts.map Prod.fst := by
  induction ts with
  | nil => intro init x hx; exact Or.inl hx
  | cons t rest ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with h | h
      · rcases denseAddCoeff_fst t.1 t.2 init x h with h | h
        · exact Or.inr (by simp [h])
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem denseMergeTerms_fst (ts : List (VarId × ZMod p)) (x : VarId)
    (h : x ∈ (denseMergeTerms ts).map Prod.fst) : x ∈ ts.map Prod.fst := by
  rcases denseFoldAddCoeff_fst ts [] x h with h | h
  · simp at h
  · exact h

theorem DenseLinExpr.norm_terms_fst (l : DenseLinExpr p) (x : VarId)
    (h : x ∈ l.norm.terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [DenseLinExpr.norm, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact denseMergeTerms_fst l.terms t.1 (List.mem_map.2 ⟨t, List.mem_of_mem_filter ht, rfl⟩)

theorem denseToExpr_foldl_vars (terms : List (VarId × ZMod p)) :
    ∀ (init : DenseExpr p) (x : VarId),
      x ∈ (terms.foldl
          (fun acc t => DenseExpr.add acc (DenseExpr.mul (.const t.2) (.var t.1))) init).vars →
      x ∈ init.vars ∨ x ∈ terms.map Prod.fst := by
  induction terms with
  | nil => intro init x hx; exact Or.inl hx
  | cons t rest ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with h | h
      · simp only [DenseExpr.vars, List.mem_append, List.nil_append, List.mem_singleton] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by subst h; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem DenseLinExpr.toExpr_vars (l : DenseLinExpr p) :
    ∀ x ∈ l.toExpr.vars, x ∈ l.terms.map Prod.fst := by
  intro x hx
  rcases denseToExpr_foldl_vars l.terms _ x hx with h | h
  · simp [DenseExpr.vars] at h
  · exact h

theorem DenseLinExpr.scale_terms_fst (k : ZMod p) (l : DenseLinExpr p) :
    (l.scale k).terms.map Prod.fst = l.terms.map Prod.fst := by
  simp [DenseLinExpr.scale, List.map_map, Function.comp_def]

/-- `denseLinearize` introduces no variable outside the expression. -/
theorem denseLinearize_vars (e : DenseExpr p) (l : DenseLinExpr p) (h : denseLinearize e = some l) :
    ∀ i ∈ l.terms.map Prod.fst, i ∈ e.vars := by
  induction e generalizing l with
  | const n => simp only [denseLinearize, Option.some.injEq] at h; subst h; simp
  | var y =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      intro x hx; simpa [DenseExpr.vars] using hx
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          intro x hx
          simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hx
          simp only [DenseExpr.vars, List.mem_append]
          exact hx.imp (iha la hla x) (ihb lb hlb x)
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            intro x hx
            rw [DenseLinExpr.scale_terms_fst] at hx
            exact List.mem_append.2 (Or.inr (ihb lb hlb x hx))
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              intro x hx
              rw [DenseLinExpr.scale_terms_fst] at hx
              exact List.mem_append.2 (Or.inl (iha la hla x hx))
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-- `DenseExpr.normalize` introduces no new variable. -/
theorem DenseExpr.normalize_vars (e : DenseExpr p) : ∀ i ∈ e.normalize.vars, i ∈ e.vars := by
  induction e with
  | const n => intro i hi; simpa [DenseExpr.normalize] using hi
  | var y => intro i hi; simpa [DenseExpr.normalize] using hi
  | add a b iha ihb =>
      intro i hi
      simp only [DenseExpr.normalize] at hi
      split at hi
      · rename_i l hl
        exact denseLinearize_vars _ l hl i (l.norm_terms_fst i (DenseLinExpr.toExpr_vars _ i hi))
      · simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        exact hi.imp (iha i) (ihb i)
  | mul a b iha ihb =>
      intro i hi
      simp only [DenseExpr.normalize] at hi
      split at hi
      · rename_i l hl
        exact denseLinearize_vars _ l hl i (l.norm_terms_fst i (DenseLinExpr.toExpr_vars _ i hi))
      · simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        exact hi.imp (iha i) (ihb i)

/-! ## Fused normalization walk

One bottom-up pass returning the normalized expression *and* the node's dense linear form
(`denseLinearize`'s value). `DenseExpr.normalize` re-runs `denseLinearize` — a full subtree walk — at
every `add`/`mul` node along non-affine paths (O(size × depth)); threading the linear form up removes
the re-walks. `denseNormalizeFused_eq` pins both components to the original functions. -/

def denseNormalizeFused : DenseExpr p → DenseExpr p × Option (DenseLinExpr p)
  | .const n => (.const n, some ⟨n, []⟩)
  | .var x => (.var x, some ⟨0, [(x, 1)]⟩)
  | .add a b =>
      let ra := denseNormalizeFused a
      let rb := denseNormalizeFused b
      match ra.2, rb.2 with
      | some la, some lb =>
          let l := la.add lb
          (l.norm.toExpr, some l)
      | _, _ => (.add ra.1 rb.1, none)
  | .mul a b =>
      let ra := denseNormalizeFused a
      let rb := denseNormalizeFused b
      match ra.2, rb.2 with
      | some la, some lb =>
          if la.terms.isEmpty then
            let l := lb.scale la.const
            (l.norm.toExpr, some l)
          else if lb.terms.isEmpty then
            let l := la.scale lb.const
            (l.norm.toExpr, some l)
          else (.mul ra.1 rb.1, none)
      | _, _ => (.mul ra.1 rb.1, none)

/-- The fused pass computes exactly (`normalize`, `denseLinearize`). -/
theorem denseNormalizeFused_eq (e : DenseExpr p) :
    denseNormalizeFused e = (e.normalize, denseLinearize e) := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
      simp only [denseNormalizeFused, iha, ihb]
      cases hla : denseLinearize a with
      | none => simp [DenseExpr.normalize, denseLinearize, hla]
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [DenseExpr.normalize, denseLinearize, hla, hlb]
        | some lb => simp [DenseExpr.normalize, denseLinearize, hla, hlb]
  | mul a b iha ihb =>
      simp only [denseNormalizeFused, iha, ihb]
      cases hla : denseLinearize a with
      | none => simp [DenseExpr.normalize, denseLinearize, hla]
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [DenseExpr.normalize, denseLinearize, hla, hlb]
        | some lb =>
          by_cases h1 : la.terms.isEmpty
          · simp [DenseExpr.normalize, denseLinearize, hla, hlb, h1]
          · by_cases h2 : lb.terms.isEmpty
            · simp [DenseExpr.normalize, denseLinearize, hla, hlb, h1, h2]
            · simp [DenseExpr.normalize, denseLinearize, hla, hlb, h1, h2]

theorem denseNormalizeFused_fst (e : DenseExpr p) : (denseNormalizeFused e).1 = e.normalize := by
  rw [denseNormalizeFused_eq]

/-- The fused walk is eval-preserving (transported from `DenseExpr.normalize_eval`). -/
theorem denseNormalizeFused_fst_eval (e : DenseExpr p) (denv : VarId → ZMod p) :
    ((denseNormalizeFused e).1).eval denv = e.eval denv := by
  rw [denseNormalizeFused_fst]; exact DenseExpr.normalize_eval e denv

/-- The fused walk introduces no new variables (transported from `DenseExpr.normalize_vars`). -/
theorem denseNormalizeFused_fst_vars (e : DenseExpr p) :
    ∀ i ∈ ((denseNormalizeFused e).1).vars, i ∈ e.vars := by
  rw [denseNormalizeFused_fst]; exact DenseExpr.normalize_vars e

/-! ## The dense normalization pass

The affine-normalization pass, computing through the fused walk. Its correctness is proved
as a `DensePassCorrect` (the fused walk is eval-preserving and introduces no variables)
and lifted to the spec `PassCorrect` by `DenseVerifiedPassW.of`. Same shape as
`denseConstantFoldPass` (`Dense/ExprOps.lean`). -/

/-- The dense affine-normalization pass (wired into `normalize1`/`normalize2`). -/
def denseNormalizePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => d.mapExpr (fun e => (denseNormalizeFused e).1))
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov =>
      DenseConstraintSystem.mapExpr_covered denseNormalizeFused_fst_vars hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => by
      have hfe : ∀ (e : DenseExpr p) (denv : VarId → ZMod p),
          ((denseNormalizeFused e).1).eval denv = e.eval denv :=
        fun e denv => denseNormalizeFused_fst_eval e denv
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- soundness: `(mapExpr fused).implies d`
        intro denv hsat
        refine ⟨denv, (DenseConstraintSystem.mapExpr_satisfies hfe d bs denv).mp hsat, ?_⟩
        rw [DenseConstraintSystem.mapExpr_sideEffects hfe]
        exact BusState.equiv_refl _
      · -- invariants
        exact fun h => DenseConstraintSystem.mapExpr_guaranteesInvariants hfe h
      · -- no new powdr column
        exact fun i hi _ =>
          DenseConstraintSystem.mapExpr_occ_subset denseNormalizeFused_fst_vars d i hi
      · -- completeness (witness = input env; no derivations)
        intro denv hadm hsat
        refine ⟨denv, (DenseConstraintSystem.mapExpr_satisfies hfe d bs denv).mpr hsat,
          (DenseConstraintSystem.mapExpr_admissible hfe d bs denv).mpr hadm, ?_, fun _ _ => rfl, ?_⟩
        · rw [DenseConstraintSystem.mapExpr_sideEffects hfe]
          exact BusState.equiv_refl _
        · intro _ _ i hi _
          exact ⟨DenseConstraintSystem.mapExpr_occ_subset denseNormalizeFused_fst_vars d i hi, rfl⟩)

end ApcOptimizer.Dense
