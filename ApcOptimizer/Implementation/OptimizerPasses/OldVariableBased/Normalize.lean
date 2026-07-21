import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Affine
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Rewrite
import ApcOptimizer.Implementation.OptimizerPasses.LinExprCore

set_option autoImplicit false

/-! # Affine normalization (collect like terms)

An eval-preserving rewrite that replaces every maximal *affine* subexpression by its **merged**
normal form: `linearize`, then combine coefficients of equal variables and drop zeros, then rebuild.
Correct for free via `mapExpr_correct` (it never changes a value).

Its purpose is as a cascade *enabler*. `linearize` only concatenates terms, so cancelling terms
(e.g. a selector's `add + sub + xor + or + and` after some flags are inlined) survive as
`x + (-1)·x`. Merging collapses them: the sum becomes the literal constant it equals, a product
`1 * X` folds to `X`, and a constraint `selector * X = 0` that was non-linear is exposed as the
affine constraint `X = 0` — which the affine pass then solves, eliminating a further variable.
Field-free (works over any commutative ring). -/

variable {p : ℕ}

/-! ## Merging a linear form's terms

`addCoeff` / `mergeTerms` and their eval lemmas now live in the neutral `LinExprCore.lean`
(imported above); the fast `@[csimp]` replacement below still targets them. -/

/-! ## Linear like-term merge (runtime `@[csimp]` replacement for `mergeTerms`)

`mergeTerms`/`addCoeff` are O(terms²): every input term linearly scans the accumulated deduped
list. For long affine forms (post-substitution reduced constraints; large blocks such as the sha256
APC) this is the dominant cost. `mergeTermsFast` accumulates each variable's coefficient in a
`Std.HashMap` while recording first-occurrence order in an `Array`, then rebuilds by walking the
recorded order — O(terms) expected. Below a small constant threshold the list fold is faster (no
hash setup), so a hybrid keeps the tiny-form path (asymptotically still linear: the bounded branch
is O(1)). Proven `= mergeTerms` and installed via `@[csimp]`, so every call site (`LinExpr.norm`,
hence `normalize`) uses it at runtime with **no proof churn** and the byte-identical result. -/

/-- The coefficient the first-occurrence-ordered accumulator holds for `v` after merging (the
    coefficient of the unique accumulator entry for `v`, if any). Mirrors `addCoeff`'s structure so
    its update lemmas are one-line inductions. -/
def assocCoeff : List (Variable × ZMod p) → Variable → Option (ZMod p)
  | [], _ => none
  | (v', c') :: rest, v => if v' = v then some c' else assocCoeff rest v

theorem not_mem_of_assocCoeff_none (acc : List (Variable × ZMod p)) (v : Variable)
    (h : assocCoeff acc v = none) : v ∉ acc.map Prod.fst := by
  induction acc with
  | nil => simp
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [assocCoeff] at h
      split at h
      · exact absurd h (by simp)
      · next hne =>
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨fun hh => hne hh.symm, ih h⟩

theorem mem_of_assocCoeff_some (acc : List (Variable × ZMod p)) (v : Variable) (c : ZMod p)
    (h : assocCoeff acc v = some c) : v ∈ acc.map Prod.fst := by
  induction acc with
  | nil => simp [assocCoeff] at h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [assocCoeff] at h
      simp only [List.map_cons, List.mem_cons]
      split at h
      · next he => exact Or.inl he.symm
      · next hne => exact Or.inr (ih h)

/-- The effect of one `addCoeff` on `assocCoeff`: bump `v`'s coefficient (0 if absent), leave every
    other variable untouched. -/
theorem assocCoeff_addCoeff (v : Variable) (c : ZMod p) (acc : List (Variable × ZMod p))
    (w : Variable) :
    assocCoeff (addCoeff v c acc) w
      = if w = v then some ((assocCoeff acc v).getD 0 + c) else assocCoeff acc w := by
  induction acc with
  | nil =>
      simp only [addCoeff, assocCoeff, Option.getD_none, zero_add]
      by_cases hwv : w = v
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [addCoeff]
      by_cases hv' : v' = v
      · rw [if_pos hv']
        subst hv'
        simp only [assocCoeff]
        by_cases hwv : w = v'
        · subst hwv; simp
        · have hwv' : ¬ v' = w := fun he => hwv he.symm
          simp only [if_neg hwv, if_neg hwv']
      · rw [if_neg hv']
        simp only [assocCoeff, ih]
        rw [if_neg hv']
        by_cases hv'w : v' = w
        · have hwv : ¬ w = v := fun he => hv' (hv'w.trans he)
          rw [if_pos hv'w, if_neg hwv, if_pos hv'w]
        · rw [if_neg hv'w, if_neg hv'w]

theorem addCoeff_map_fst_of_mem (v : Variable) (c : ZMod p) (acc : List (Variable × ZMod p))
    (h : v ∈ acc.map Prod.fst) : (addCoeff v c acc).map Prod.fst = acc.map Prod.fst := by
  induction acc with
  | nil => simp at h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [addCoeff]
      split
      · next he => simp
      · next hne =>
          simp only [List.map_cons, List.mem_cons] at h
          have hmem : v ∈ rest.map Prod.fst := by
            rcases h with h | h
            · exact absurd h.symm hne
            · exact h
          simp [ih hmem]

theorem addCoeff_append_of_not_mem (v : Variable) (c : ZMod p) (acc : List (Variable × ZMod p))
    (h : v ∉ acc.map Prod.fst) : addCoeff v c acc = acc ++ [(v, c)] := by
  induction acc with
  | nil => simp [addCoeff]
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [List.map_cons, List.mem_cons, not_or] at h
      obtain ⟨hne, hrest⟩ := h
      simp only [addCoeff]
      rw [if_neg (fun he => hne he.symm)]
      simp [ih hrest]

/-- One step of the fast merge: bump `t.1`'s coefficient in the map, appending `t.1` to the order
    array on first occurrence. -/
def mtStep (st : Array Variable × Std.HashMap Variable (ZMod p)) (t : Variable × ZMod p) :
    Array Variable × Std.HashMap Variable (ZMod p) :=
  match st.2[t.1]? with
  | some c0 => (st.1, st.2.insert t.1 (c0 + t.2))
  | none => (st.1.push t.1, st.2.insert t.1 t.2)

/-- Correspondence invariant tying the fast `(order, map)` state to the `addCoeff`-fold list. -/
def MergeCorr (acc : List (Variable × ZMod p)) (order : Array Variable)
    (m : Std.HashMap Variable (ZMod p)) : Prop :=
  order.toList = acc.map Prod.fst ∧ (acc.map Prod.fst).Nodup ∧ ∀ v, m[v]? = assocCoeff acc v

theorem mtStep_corr (acc : List (Variable × ZMod p)) (order : Array Variable)
    (m : Std.HashMap Variable (ZMod p)) (t : Variable × ZMod p) (h : MergeCorr acc order m) :
    MergeCorr (addCoeff t.1 t.2 acc) (mtStep (order, m) t).1 (mtStep (order, m) t).2 := by
  obtain ⟨hord, hnod, hm⟩ := h
  obtain ⟨tv, tc⟩ := t
  have hmtv := hm tv
  rcases hcase : (m[tv]? : Option (ZMod p)) with _ | c0
  · have habs : assocCoeff acc tv = none := by rw [← hmtv, hcase]
    have hnmem : tv ∉ acc.map Prod.fst := not_mem_of_assocCoeff_none acc tv habs
    have hstep : mtStep (order, m) (tv, tc) = (order.push tv, m.insert tv tc) := by
      simp only [mtStep, hcase]
    have hfst : (addCoeff tv tc acc).map Prod.fst = acc.map Prod.fst ++ [tv] := by
      rw [addCoeff_append_of_not_mem tv tc acc hnmem]; simp
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfst, Array.toList_push, hord]
    · rw [hfst]
      exact hnod.append (List.nodup_singleton tv) (List.disjoint_singleton.2 hnmem)
    · intro w
      rw [Std.HashMap.getElem?_insert, assocCoeff_addCoeff, habs]
      simp only [beq_iff_eq, Option.getD_none, zero_add]
      by_cases hwv : tv = w
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
        exact hm w
  · have hpres : assocCoeff acc tv = some c0 := by rw [← hmtv, hcase]
    have hmem : tv ∈ acc.map Prod.fst := mem_of_assocCoeff_some acc tv c0 hpres
    have hstep : mtStep (order, m) (tv, tc) = (order, m.insert tv (c0 + tc)) := by
      simp only [mtStep, hcase]
    have hfst : (addCoeff tv tc acc).map Prod.fst = acc.map Prod.fst :=
      addCoeff_map_fst_of_mem tv tc acc hmem
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfst]; exact hord
    · rw [hfst]; exact hnod
    · intro w
      rw [Std.HashMap.getElem?_insert, assocCoeff_addCoeff, hpres]
      simp only [beq_iff_eq, Option.getD_some]
      by_cases hwv : tv = w
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
        exact hm w

theorem mtFold_corr (ts : List (Variable × ZMod p)) :
    ∀ (acc : List (Variable × ZMod p)) (order : Array Variable)
      (m : Std.HashMap Variable (ZMod p)), MergeCorr acc order m →
      MergeCorr (ts.foldl (fun a t => addCoeff t.1 t.2 a) acc)
        (ts.foldl mtStep (order, m)).1 (ts.foldl mtStep (order, m)).2 := by
  induction ts with
  | nil => intro acc order m h; simpa using h
  | cons t rest ih =>
      intro acc order m h
      simp only [List.foldl_cons]
      exact ih (addCoeff t.1 t.2 acc) (mtStep (order, m) t).1 (mtStep (order, m) t).2
        (mtStep_corr acc order m t h)

theorem recon_assoc (acc : List (Variable × ZMod p)) (hnod : (acc.map Prod.fst).Nodup) :
    (acc.map Prod.fst).map (fun v => (v, (assocCoeff acc v).getD 0)) = acc := by
  induction acc with
  | nil => simp
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [List.map_cons] at hnod ⊢
      rw [List.nodup_cons] at hnod
      obtain ⟨hnotin, hnod'⟩ := hnod
      have hhead : (assocCoeff ((v', c') :: rest) v').getD 0 = c' := by simp [assocCoeff]
      have htail : (rest.map Prod.fst).map
          (fun v => (v, (assocCoeff ((v', c') :: rest) v).getD 0))
          = (rest.map Prod.fst).map (fun v => (v, (assocCoeff rest v).getD 0)) := by
        apply List.map_congr_left
        intro v hv
        have hvne : ¬ v' = v := fun he => hnotin (he ▸ hv)
        simp [assocCoeff, if_neg hvne]
      rw [hhead, htail, ih hnod']

theorem recon (acc : List (Variable × ZMod p)) (order : Array Variable)
    (m : Std.HashMap Variable (ZMod p)) (h : MergeCorr acc order m) :
    order.toList.map (fun v => (v, (m[v]?).getD 0)) = acc := by
  obtain ⟨hord, hnod, hm⟩ := h
  rw [hord]
  rw [show (fun v => (v, (m[v]?).getD 0)) = (fun v => (v, (assocCoeff acc v).getD 0)) from
    funext (fun v => by rw [hm v])]
  exact recon_assoc acc hnod

/-- The linear like-term merge. Proven `= mergeTerms` and installed via `@[csimp]`. -/
def mergeTermsFast (ts : List (Variable × ZMod p)) : List (Variable × ZMod p) :=
  if ts.length ≤ 32 then
    ts.foldl (fun acc t => addCoeff t.1 t.2 acc) []
  else
    let st := ts.foldl mtStep (#[], ∅)
    st.1.toList.map (fun v => (v, (st.2[v]?).getD 0))

@[csimp] theorem mergeTerms_eq_fast : @mergeTerms = @mergeTermsFast := by
  funext p ts
  show mergeTerms ts = mergeTermsFast ts
  unfold mergeTermsFast
  split
  · rfl
  · have hbase : MergeCorr ([] : List (Variable × ZMod p)) (#[] : Array Variable)
        (∅ : Std.HashMap Variable (ZMod p)) :=
      ⟨by simp, by simp, fun v => by simp [assocCoeff]⟩
    have hcorr := mtFold_corr ts [] #[] ∅ hbase
    exact (recon _ _ _ hcorr).symm

/-! `dropZero_eval`, `LinExpr.norm` and `LinExpr.norm_eval` now live in the neutral
    `LinExprCore.lean` (imported above). -/

/-! ## The normalization pass -/

/-- Recursively collect like terms: replace each maximal affine subexpression by its merged linear
    form. Non-affine nodes (a genuine variable×variable product) are recursed into. -/
def Expression.normalize : Expression p → Expression p
  | .const n => .const n
  | .var x => .var x
  | .add a b =>
      match linearize (Expression.add a b) with
      | some l => l.norm.toExpr
      | none => .add a.normalize b.normalize
  | .mul a b =>
      match linearize (Expression.mul a b) with
      | some l => l.norm.toExpr
      | none => .mul a.normalize b.normalize

theorem Expression.normalize_eval (e : Expression p) (env : Variable → ZMod p) :
    e.normalize.eval env = e.eval env := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
      simp only [Expression.normalize]
      split
      · next l hl => rw [LinExpr.toExpr_eval, LinExpr.norm_eval, ← linearize_eval _ l hl]
      · rw [Expression.eval, iha, ihb, Expression.eval]
  | mul a b iha ihb =>
      simp only [Expression.normalize]
      split
      · next l hl => rw [LinExpr.toExpr_eval, LinExpr.norm_eval, ← linearize_eval _ l hl]
      · rw [Expression.eval, iha, ihb, Expression.eval]

/-! ## Variable bounds -/

theorem addCoeff_fst (v : Variable) (c : ZMod p) (ts : List (Variable × ZMod p)) (x : Variable)
    (h : x ∈ (addCoeff v c ts).map Prod.fst) : x = v ∨ x ∈ ts.map Prod.fst := by
  induction ts with
  | nil => simp only [addCoeff, List.map_cons, List.map_nil, List.mem_singleton] at h; exact Or.inl h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [addCoeff] at h
      split at h
      · rename_i hv
        simp only [List.map_cons, List.mem_cons] at h ⊢
        tauto
      · simp only [List.map_cons, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact (ih h).imp id (Or.inr ·)

theorem foldl_addCoeff_fst (ts : List (Variable × ZMod p)) :
    ∀ (init : List (Variable × ZMod p)) (x : Variable),
      x ∈ (ts.foldl (fun acc t => addCoeff t.1 t.2 acc) init).map Prod.fst →
      x ∈ init.map Prod.fst ∨ x ∈ ts.map Prod.fst := by
  induction ts with
  | nil => intro init x hx; exact Or.inl hx
  | cons t rest ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with h | h
      · rcases addCoeff_fst t.1 t.2 init x h with h | h
        · exact Or.inr (by simp [h])
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mergeTerms_fst (ts : List (Variable × ZMod p)) (x : Variable)
    (h : x ∈ (mergeTerms ts).map Prod.fst) : x ∈ ts.map Prod.fst := by
  rcases foldl_addCoeff_fst ts [] x h with h | h
  · simp at h
  · exact h

theorem LinExpr.norm_terms_fst (l : LinExpr p) (x : Variable)
    (h : x ∈ l.norm.terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [LinExpr.norm, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact mergeTerms_fst l.terms t.1 (List.mem_map.2 ⟨t, List.mem_of_mem_filter ht, rfl⟩)

theorem Expression.normalize_vars (e : Expression p) : ∀ x ∈ e.normalize.vars, x ∈ e.vars := by
  induction e with
  | const n => intro x hx; simpa [Expression.normalize] using hx
  | var y => intro x hx; simpa [Expression.normalize] using hx
  | add a b iha ihb =>
      intro x hx
      simp only [Expression.normalize] at hx
      split at hx
      · rename_i l hl
        exact linearize_vars _ l hl x (l.norm_terms_fst x (LinExpr.toExpr_vars _ x hx))
      · simp only [Expression.vars, List.mem_append] at hx ⊢
        exact hx.imp (iha x) (ihb x)
  | mul a b iha ihb =>
      intro x hx
      simp only [Expression.normalize] at hx
      split at hx
      · rename_i l hl
        exact linearize_vars _ l hl x (l.norm_terms_fst x (LinExpr.toExpr_vars _ x hx))
      · simp only [Expression.vars, List.mem_append] at hx ⊢
        exact hx.imp (iha x) (ihb x)

/-- Fused normalization: one bottom-up pass returning the normalized expression *and* the node's
    linear form (`linearize`'s value). `Expression.normalize` re-runs `linearize` — a full
    subtree walk — at every `add`/`mul` node along non-affine paths (O(size × depth) on the deep
    sum spines circuits are full of); threading the linear form up removes the re-walks.
    `normalizeFused_eq` pins both components to the original functions, so consumers are provably
    unchanged. -/
def normalizeFused : Expression p → Expression p × Option (LinExpr p)
  | .const n => (.const n, some ⟨n, []⟩)
  | .var x => (.var x, some ⟨0, [(x, 1)]⟩)
  | .add a b =>
      let ra := normalizeFused a
      let rb := normalizeFused b
      match ra.2, rb.2 with
      | some la, some lb =>
          let l := la.add lb
          (l.norm.toExpr, some l)
      | _, _ => (.add ra.1 rb.1, none)
  | .mul a b =>
      let ra := normalizeFused a
      let rb := normalizeFused b
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

/-- The fused pass computes exactly (`normalize`, `linearize`). -/
theorem normalizeFused_eq (e : Expression p) :
    normalizeFused e = (e.normalize, linearize e) := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
      simp only [normalizeFused, iha, ihb]
      cases hla : linearize a with
      | none => simp [Expression.normalize, linearize, hla]
      | some la =>
        cases hlb : linearize b with
        | none => simp [Expression.normalize, linearize, hla, hlb]
        | some lb => simp [Expression.normalize, linearize, hla, hlb]
  | mul a b iha ihb =>
      simp only [normalizeFused, iha, ihb]
      cases hla : linearize a with
      | none => simp [Expression.normalize, linearize, hla]
      | some la =>
        cases hlb : linearize b with
        | none => simp [Expression.normalize, linearize, hla, hlb]
        | some lb =>
          by_cases h1 : la.terms.isEmpty
          · simp [Expression.normalize, linearize, hla, hlb, h1]
          · by_cases h2 : lb.terms.isEmpty
            · simp [Expression.normalize, linearize, hla, hlb, h1, h2]
            · simp [Expression.normalize, linearize, hla, hlb, h1, h2]

theorem normalizeFused_fst (e : Expression p) : (normalizeFused e).1 = e.normalize := by
  rw [normalizeFused_eq]

/-- The affine-normalization pass, computing through the fused walk (provably the same output).
    Correct via `mapExpr_correct` (only `normalize_eval`, transported along
    `normalizeFused_fst`). -/
def normalizePass : VerifiedPass p := fun cs bs =>
  ⟨cs.mapExpr (fun e => (normalizeFused e).1), [],
   ConstraintSystem.mapExpr_correct (g := fun e => (normalizeFused e).1)
     (fun e env => by
       show ((normalizeFused e).1).eval env = e.eval env
       rw [normalizeFused_fst]
       exact Expression.normalize_eval e env) cs bs
     (fun e x hx => Expression.normalize_vars e x (by
       have hx' : x ∈ ((normalizeFused e).1).vars := hx
       rwa [normalizeFused_fst] at hx'))⟩
