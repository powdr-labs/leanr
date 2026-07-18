import ApcOptimizer.Implementation.Dense.Affine
import ApcOptimizer.Implementation.Dense.ExprOps
import ApcOptimizer.Implementation.Dense.Adapter
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense affine normalization (Task 3)

The dense mirror of `Expression.normalize` (`OptimizerPasses/Normalize.lean`): replace every maximal
affine subexpression by its **merged** normal form (`denseLinearize`, combine coefficients of equal
`VarId`s, drop zeros, rebuild via `DenseLinExpr.toExpr`). Unlike the eval-preserving folds,
`mergeTerms`/`addCoeff` *compare variables* (`if v' = v`), so the decode-commutation is
**validity-gated**: `resolve` is injective only on valid ids, so `denseMergeTerms` mapped through
`resolve` equals the spec `mergeTerms` of the decoded terms only when every term's `VarId` is valid.
The commutation lemma `decodeLin_norm` therefore carries a validity hypothesis, discharged for the
pass from the threaded coverage invariant (via `denseLinearize_vars`).

The pass is built with `ofTransform`, inheriting `normalizePass`'s `PassCorrect`: the dense output
decodes to exactly `(decode d).mapExpr Expression.normalize`, the spec pass's output. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Merging a dense linear form's terms (mirrors `addCoeff`/`mergeTerms`) -/

/-- Add coefficient `c` to `VarId` `v` in a dense term list, merging into an existing entry. -/
def denseAddCoeff (v : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → List (VarId × ZMod p)
  | [] => [(v, c)]
  | (v', c') :: rest => if v' = v then (v', c' + c) :: rest else (v', c') :: denseAddCoeff v c rest

/-- Merge a dense term list, combining coefficients of equal `VarId`s (`foldl`, first-occurrence
    order preserved — mirrors `mergeTerms`). -/
def denseMergeTerms (ts : List (VarId × ZMod p)) : List (VarId × ZMod p) :=
  ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) []

/-- The fully-merged normal form of a dense linear form: combine like terms, drop zeros. -/
def DenseLinExpr.norm (l : DenseLinExpr p) : DenseLinExpr p :=
  ⟨l.const, (denseMergeTerms l.terms).filter (fun t => t.2 ≠ 0)⟩

/-! ## The dense normalization traversal (mirrors `Expression.normalize`) -/

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

/-- `denseLinearize` introduces no variable outside the expression (mirrors `linearize_vars`). -/
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

/-- `DenseExpr.normalize` introduces no new variable (mirrors `Expression.normalize_vars`). -/
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

/-! ## Decode-commutation of the merge (validity-gated) -/

/-- Resolving each term commutes with dropping zero-coefficient terms (the filter touches only
    `.2`, which `resolve`-decoding preserves). -/
theorem VarRegistry.map_resolve_filter (reg : VarRegistry) (l : List (VarId × ZMod p)) :
    (l.filter (fun t => t.2 ≠ 0)).map (fun t => (reg.resolve t.1, t.2))
      = (l.map (fun t => (reg.resolve t.1, t.2))).filter (fun t => t.2 ≠ 0) := by
  induction l with
  | nil => rfl
  | cons t rest ih =>
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simpa using h), List.map_cons,
            List.filter_cons_of_neg (by simpa using h), ih]
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.map_cons,
            List.filter_cons_of_pos (by simpa using h), ih]

/-- One `denseAddCoeff`, decoded, is one spec `addCoeff` on the decoded accumulator (validity-gated:
    `resolve` must be injective on the compared ids). -/
theorem VarRegistry.denseAddCoeff_map (reg : VarRegistry) (v : VarId) (c : ZMod p)
    (hv : reg.Valid v) :
    ∀ (acc : List (VarId × ZMod p)), (∀ i ∈ acc.map Prod.fst, reg.Valid i) →
    (denseAddCoeff v c acc).map (fun t => (reg.resolve t.1, t.2))
      = addCoeff (reg.resolve v) c (acc.map (fun t => (reg.resolve t.1, t.2))) := by
  intro acc
  induction acc with
  | nil => intro _; rfl
  | cons t rest ih =>
      intro hacc
      obtain ⟨v', c'⟩ := t
      have hv' : reg.Valid v' := hacc v' (by simp)
      have hrest : ∀ i ∈ rest.map Prod.fst, reg.Valid i :=
        fun i hi => hacc i (List.mem_cons_of_mem _ hi)
      by_cases hvv : v' = v
      · simp only [denseAddCoeff, if_pos hvv, List.map_cons, addCoeff]
        rw [if_pos (congrArg reg.resolve hvv)]
      · have hne : reg.resolve v' ≠ reg.resolve v := fun he => hvv (reg.resolve_inj hv' hv he)
        simp only [denseAddCoeff, if_neg hvv, List.map_cons, addCoeff, ih hrest]
        rw [if_neg hne]

/-- The full merge fold, decoded, is the spec merge fold on decoded terms (validity-gated). -/
theorem VarRegistry.denseFoldAddCoeff_map (reg : VarRegistry) :
    ∀ (ts : List (VarId × ZMod p)), (∀ i ∈ ts.map Prod.fst, reg.Valid i) →
    ∀ (acc : List (VarId × ZMod p)), (∀ i ∈ acc.map Prod.fst, reg.Valid i) →
      (ts.foldl (fun a t => denseAddCoeff t.1 t.2 a) acc).map (fun t => (reg.resolve t.1, t.2))
        = (ts.map (fun t => (reg.resolve t.1, t.2))).foldl
            (fun a t => addCoeff t.1 t.2 a) (acc.map (fun t => (reg.resolve t.1, t.2))) := by
  intro ts
  induction ts with
  | nil => intro _ acc _; rfl
  | cons t rest ih =>
      intro hts acc hacc
      have ht1 : reg.Valid t.1 := hts t.1 (by simp)
      have hrestts : ∀ i ∈ rest.map Prod.fst, reg.Valid i :=
        fun i hi => hts i (List.mem_cons_of_mem _ hi)
      have hacc' : ∀ i ∈ (denseAddCoeff t.1 t.2 acc).map Prod.fst, reg.Valid i := by
        intro i hi
        rcases denseAddCoeff_fst t.1 t.2 acc i hi with h | h
        · exact h ▸ ht1
        · exact hacc i h
      simp only [List.foldl_cons, List.map_cons]
      rw [ih hrestts (denseAddCoeff t.1 t.2 acc) hacc',
          reg.denseAddCoeff_map t.1 t.2 ht1 acc hacc]

theorem VarRegistry.denseMergeTerms_map (reg : VarRegistry) (ts : List (VarId × ZMod p))
    (hv : ∀ i ∈ ts.map Prod.fst, reg.Valid i) :
    (denseMergeTerms ts).map (fun t => (reg.resolve t.1, t.2))
      = mergeTerms (ts.map (fun t => (reg.resolve t.1, t.2))) := by
  have h := reg.denseFoldAddCoeff_map ts hv [] (by simp)
  simpa [denseMergeTerms, mergeTerms] using h

/-- **The dense normal form decodes to the spec normal form** (given all term ids valid). -/
theorem VarRegistry.decodeLin_norm (reg : VarRegistry) (l : DenseLinExpr p)
    (hv : ∀ i ∈ l.terms.map Prod.fst, reg.Valid i) :
    reg.decodeLin (DenseLinExpr.norm l) = (reg.decodeLin l).norm := by
  simp only [DenseLinExpr.norm, VarRegistry.decodeLin, LinExpr.norm]
  rw [reg.map_resolve_filter (denseMergeTerms l.terms), reg.denseMergeTerms_map l.terms hv]

/-- **`DenseExpr.normalize` commutes with decode** for covered expressions (validity-gated through
    `decodeLin_norm`). -/
theorem VarRegistry.decodeExpr_normalize (reg : VarRegistry) (e : DenseExpr p) : e.CoveredBy reg →
    reg.decodeExpr (DenseExpr.normalize e) = Expression.normalize (reg.decodeExpr e) := by
  induction e with
  | const n => intro _; rfl
  | var i => intro _; rfl
  | add a b iha ihb =>
      intro hc
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      have hvalid : ∀ (l : DenseLinExpr p), denseLinearize (DenseExpr.add a b) = some l →
          ∀ i ∈ l.terms.map Prod.fst, reg.Valid i :=
        fun l hl i hi => hc i (denseLinearize_vars (DenseExpr.add a b) l hl i hi)
      have hkey : (denseLinearize (DenseExpr.add a b)).map reg.decodeLin
          = linearize (Expression.add (reg.decodeExpr a) (reg.decodeExpr b)) :=
        reg.denseLinearize_decode (DenseExpr.add a b)
      simp only [DenseExpr.normalize, VarRegistry.decodeExpr, Expression.normalize]
      rw [← hkey]
      cases hP : denseLinearize (DenseExpr.add a b) with
      | none => simp only [Option.map_none, VarRegistry.decodeExpr, iha ha, ihb hb]
      | some l =>
          simp only [Option.map_some]
          rw [reg.decodeLin_toExpr l.norm, reg.decodeLin_norm l (hvalid l hP)]
  | mul a b iha ihb =>
      intro hc
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      have hvalid : ∀ (l : DenseLinExpr p), denseLinearize (DenseExpr.mul a b) = some l →
          ∀ i ∈ l.terms.map Prod.fst, reg.Valid i :=
        fun l hl i hi => hc i (denseLinearize_vars (DenseExpr.mul a b) l hl i hi)
      have hkey : (denseLinearize (DenseExpr.mul a b)).map reg.decodeLin
          = linearize (Expression.mul (reg.decodeExpr a) (reg.decodeExpr b)) :=
        reg.denseLinearize_decode (DenseExpr.mul a b)
      simp only [DenseExpr.normalize, VarRegistry.decodeExpr, Expression.normalize]
      rw [← hkey]
      cases hP : denseLinearize (DenseExpr.mul a b) with
      | none => simp only [Option.map_none, VarRegistry.decodeExpr, iha ha, ihb hb]
      | some l =>
          simp only [Option.map_some]
          rw [reg.decodeLin_toExpr l.norm, reg.decodeLin_norm l (hvalid l hP)]

/-! ## Coverage-aware `mapExpr` commutation -/

/-- Coverage-aware bus-interaction map commutation: if `g` decodes to `g'` on covered expressions,
    the mapped-then-decoded interaction is the decoded-then-mapped one. -/
theorem VarRegistry.decodeBI_mapExpr_covered (reg : VarRegistry)
    {g : DenseExpr p → DenseExpr p} {g' : Expression p → Expression p}
    (hg : ∀ e, e.CoveredBy reg → reg.decodeExpr (g e) = g' (reg.decodeExpr e))
    (bi : BusInteraction (DenseExpr p)) (hc : denseBICovered reg bi) :
    reg.decodeBI { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g }
      = (reg.decodeBI bi).mapExpr g' := by
  obtain ⟨hm, hp⟩ := hc
  simp only [VarRegistry.decodeBI, BusInteraction.mapExpr, List.map_map, Function.comp_def,
    hg bi.multiplicity hm]
  congr 1
  exact List.map_congr_left (fun e he => hg e (hp e he))

/-- **Coverage-aware `mapExpr` commutation.** If `g` decodes to `g'` on *covered* expressions, the
    dense map decodes to the spec map. Mirrors `decodeCS_mapExpr`, threading coverage. -/
theorem VarRegistry.decodeCS_mapExpr_covered (reg : VarRegistry)
    {g : DenseExpr p → DenseExpr p} {g' : Expression p → Expression p}
    (hg : ∀ e, e.CoveredBy reg → reg.decodeExpr (g e) = g' (reg.decodeExpr e))
    (d : DenseConstraintSystem p) (hc : d.CoveredBy reg) :
    reg.decodeCS (d.mapExpr g) = (reg.decodeCS d).mapExpr g' := by
  obtain ⟨hac, hbi⟩ := hc
  simp only [DenseConstraintSystem.mapExpr, VarRegistry.decodeCS, ConstraintSystem.mapExpr,
    List.map_map, Function.comp_def]
  congr 1
  · exact List.map_congr_left (fun e he => hg e (hac e he))
  · exact List.map_congr_left (fun bi hbimem => reg.decodeBI_mapExpr_covered hg bi (hbi bi hbimem))

/-! ## The dense normalization pass -/

/-- The dense affine-normalization pass. Its `PassCorrect` is inherited from the spec `normalizePass`
    — the dense output decodes to exactly `(decode d).mapExpr Expression.normalize`. -/
def denseNormalizePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofTransform
    (fun _ d => d.mapExpr DenseExpr.normalize)
    normalizePass.withFacts
    (fun _ _ _ hc =>
      DenseConstraintSystem.mapExpr_covered
        (fun e i hi => DenseExpr.normalize_vars e i hi) hc)
    (fun reg _ _ d hc =>
      reg.decodeCS_mapExpr_covered (fun e he => reg.decodeExpr_normalize e he) d hc)
    (fun _ _ _ => rfl)

end ApcOptimizer.Dense
