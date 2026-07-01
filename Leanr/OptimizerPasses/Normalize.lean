import Leanr.OptimizerPasses.Affine
import Leanr.OptimizerPasses.Rewrite

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
def addCoeff (v : String) (c : ZMod p) : List (String × ZMod p) → List (String × ZMod p)
  | [] => [(v, c)]
  | (v', c') :: rest => if v' = v then (v', c' + c) :: rest else (v', c') :: addCoeff v c rest

theorem addCoeff_eval (v : String) (c : ZMod p) (ts : List (String × ZMod p))
    (env : String → ZMod p) :
    ((addCoeff v c ts).map (fun t => t.2 * env t.1)).sum
    = c * env v + (ts.map (fun t => t.2 * env t.1)).sum := by
  induction ts with
  | nil => simp [addCoeff]
  | cons t rest ih =>
      simp only [addCoeff]
      split
      · next h => subst h; simp only [List.map_cons, List.sum_cons]; ring
      · simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Merge a term list, combining coefficients of equal variables. -/
def mergeTerms (ts : List (String × ZMod p)) : List (String × ZMod p) :=
  ts.foldr (fun t acc => addCoeff t.1 t.2 acc) []

theorem mergeTerms_eval (ts : List (String × ZMod p)) (env : String → ZMod p) :
    ((mergeTerms ts).map (fun t => t.2 * env t.1)).sum
    = (ts.map (fun t => t.2 * env t.1)).sum := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      simp only [mergeTerms, List.foldr_cons] at *
      rw [addCoeff_eval, ih, List.map_cons, List.sum_cons]

theorem dropZero_eval (ts : List (String × ZMod p)) (env : String → ZMod p) :
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

theorem LinExpr.norm_eval (l : LinExpr p) (env : String → ZMod p) :
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

theorem Expression.normalize_eval (e : Expression p) (env : String → ZMod p) :
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

/-- The affine-normalization pass. Correct via `mapExpr_correct` (only `normalize_eval`). -/
def normalizePass : VerifiedPass p := fun cs bs =>
  ⟨cs.mapExpr Expression.normalize,
   ConstraintSystem.mapExpr_correct (g := Expression.normalize)
     (fun e env => Expression.normalize_eval e env) cs bs⟩
