import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.Rewrite

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

/-! ## Merging a linear form's terms -/

/-- Add coefficient `c` to variable `v` in a term list, merging into an existing entry. -/
def addCoeff (v : Variable) (c : ZMod p) : List (Variable × ZMod p) → List (Variable × ZMod p)
  | [] => [(v, c)]
  | (v', c') :: rest => if v' = v then (v', c' + c) :: rest else (v', c') :: addCoeff v c rest

theorem addCoeff_eval (v : Variable) (c : ZMod p) (ts : List (Variable × ZMod p))
    (env : Variable → ZMod p) :
    ((addCoeff v c ts).map (fun t => t.2 * env t.1)).sum
    = c * env v + (ts.map (fun t => t.2 * env t.1)).sum := by
  induction ts with
  | nil => simp [addCoeff]
  | cons t rest ih =>
      simp only [addCoeff]
      split
      · next h => subst h; simp only [List.map_cons, List.sum_cons]; ring
      · simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Merge a term list, combining coefficients of equal variables. `foldl` (with `addCoeff`
    appending unseen variables at the tail) preserves first-occurrence order, making the merge
    *idempotent* — a `foldr` here would reverse the term order on every application, so
    normalization would oscillate with period 2 instead of reaching a fixpoint. -/
def mergeTerms (ts : List (Variable × ZMod p)) : List (Variable × ZMod p) :=
  ts.foldl (fun acc t => addCoeff t.1 t.2 acc) []

theorem foldl_addCoeff_eval (env : Variable → ZMod p) (ts acc : List (Variable × ZMod p)) :
    ((ts.foldl (fun acc t => addCoeff t.1 t.2 acc) acc).map (fun t => t.2 * env t.1)).sum
    = (acc.map (fun t => t.2 * env t.1)).sum + (ts.map (fun t => t.2 * env t.1)).sum := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, addCoeff_eval]
      ring

theorem mergeTerms_eval (ts : List (Variable × ZMod p)) (env : Variable → ZMod p) :
    ((mergeTerms ts).map (fun t => t.2 * env t.1)).sum
    = (ts.map (fun t => t.2 * env t.1)).sum := by
  simp [mergeTerms, foldl_addCoeff_eval]

theorem dropZero_eval (ts : List (Variable × ZMod p)) (env : Variable → ZMod p) :
    ((ts.filter (fun t => t.2 ≠ 0)).map (fun t => t.2 * env t.1)).sum
    = (ts.map (fun t => t.2 * env t.1)).sum := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons, h]
        simp
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
            List.map_cons, List.sum_cons]

/-- The fully-merged normal form of a linear form: combine like terms, drop zeros. A linear form
    that is really a constant thus normalizes to `⟨c, []⟩`, whose `toExpr` is the literal `c`. -/
def LinExpr.norm (l : LinExpr p) : LinExpr p :=
  ⟨l.const, (mergeTerms l.terms).filter (fun t => t.2 ≠ 0)⟩

theorem LinExpr.norm_eval (l : LinExpr p) (env : Variable → ZMod p) :
    l.norm.eval env = l.eval env := by
  simp only [LinExpr.norm, LinExpr.eval, dropZero_eval, mergeTerms_eval]

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

/-- The affine-normalization pass. Correct via `mapExpr_correct` (only `normalize_eval`). -/
def normalizePass : VerifiedPass p := fun cs bs =>
  ⟨cs.mapExpr Expression.normalize, [],
   ConstraintSystem.mapExpr_correct (g := Expression.normalize)
     (fun e env => Expression.normalize_eval e env) cs bs Expression.normalize_vars⟩
