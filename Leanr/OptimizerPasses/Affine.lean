import Leanr.OptimizerPasses.Subst
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

/-! # Affine substitution (linear/Gaussian elimination)

Generalizes constant substitution to any variable pinned by a *linear* constraint. Given a constraint
that, after normalization, reads `a₀ + Σ aᵢ·vᵢ = 0` and some variable `x` occurs with a unit
coefficient (`±1`), we can solve `x = ∓(a₀ + rest)` and substitute it away — eliminating `x` while
introducing no new variable (the solution only mentions variables already present).

The machinery:

* `LinExpr` — a normalized linear form (`const + Σ coeff·var`), with `linearize`/`linearize_eval`
  turning an `Expression` into one (returning `none` on a genuine variable×variable product);
* `LinExpr.eval_split` — the coefficient/remainder decomposition used to solve;
* `solveAffine` / `solveAffine_sound` — detect a unit-coefficient variable and produce the solution,
  with the entailment proof; fed to the generic `substFromConstraint`.

Purely equational — unit coefficients are units in *any* commutative ring, so no field/primality is
needed. This is a standard, general zkVM/circuit optimization (powdr's affine solver). -/

variable {p : ℕ}

/-- A linear (affine) form: a constant plus a list of `(variable, coefficient)` terms. -/
structure LinExpr (p : ℕ) where
  const : ZMod p
  terms : List (String × ZMod p)

/-- Evaluate a linear form. -/
def LinExpr.eval (l : LinExpr p) (env : String → ZMod p) : ZMod p :=
  l.const + (l.terms.map (fun t => t.2 * env t.1)).sum

def LinExpr.add (a b : LinExpr p) : LinExpr p := ⟨a.const + b.const, a.terms ++ b.terms⟩
def LinExpr.scale (k : ZMod p) (a : LinExpr p) : LinExpr p :=
  ⟨k * a.const, a.terms.map (fun t => (t.1, k * t.2))⟩

theorem LinExpr.add_eval (a b : LinExpr p) (env : String → ZMod p) :
    (a.add b).eval env = a.eval env + b.eval env := by
  simp only [LinExpr.add, LinExpr.eval, List.map_append, List.sum_append]
  ring

theorem LinExpr.scale_eval (k : ZMod p) (a : LinExpr p) (env : String → ZMod p) :
    (a.scale k).eval env = k * a.eval env := by
  simp only [LinExpr.scale, LinExpr.eval, List.map_map, mul_add]
  congr 1
  induction a.terms with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih, Function.comp_apply]; ring

/-- Try to view an expression as a linear form; `none` if it has a variable×variable product. -/
def linearize : Expression p → Option (LinExpr p)
  | .const n => some ⟨n, []⟩
  | .var x => some ⟨0, [(x, 1)]⟩
  | .add a b =>
      match linearize a, linearize b with
      | some la, some lb => some (la.add lb)
      | _, _ => none
  | .mul a b =>
      match linearize a, linearize b with
      | some la, some lb =>
          if la.terms.isEmpty then some (lb.scale la.const)
          else if lb.terms.isEmpty then some (la.scale lb.const)
          else none
      | _, _ => none

theorem linearize_eval (e : Expression p) (l : LinExpr p) (h : linearize e = some l)
    (env : String → ZMod p) : e.eval env = l.eval env := by
  induction e generalizing l with
  | const n => simp only [linearize, Option.some.injEq] at h; subst h; simp [LinExpr.eval, Expression.eval]
  | var x => simp only [linearize, Option.some.injEq] at h; subst h; simp [LinExpr.eval, Expression.eval]
  | add a b iha ihb =>
      cases hla : linearize a with
      | none => simp [linearize, hla] at h
      | some la =>
        cases hlb : linearize b with
        | none => simp [linearize, hla, hlb] at h
        | some lb =>
          simp only [linearize, hla, hlb, Option.some.injEq] at h
          subst h
          rw [Expression.eval, iha la hla, ihb lb hlb, LinExpr.add_eval]
  | mul a b iha ihb =>
      cases hla : linearize a with
      | none => simp [linearize, hla] at h
      | some la =>
        cases hlb : linearize b with
        | none => simp [linearize, hla, hlb] at h
        | some lb =>
          have hae : a.eval env = la.eval env := iha la hla
          have hbe : b.eval env = lb.eval env := ihb lb hlb
          by_cases h1 : la.terms.isEmpty = true
          · simp only [linearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            have hc : la.eval env = la.const := by
              simp only [LinExpr.eval, List.isEmpty_iff.1 h1, List.map_nil, List.sum_nil, add_zero]
            rw [Expression.eval, hae, hbe, LinExpr.scale_eval, hc]
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [linearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              have hc : lb.eval env = lb.const := by
                simp only [LinExpr.eval, List.isEmpty_iff.1 h2, List.map_nil, List.sum_nil, add_zero]
              rw [Expression.eval, hae, hbe, LinExpr.scale_eval, hc, mul_comm]
            · simp only [linearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-- Partition the evaluation of a term list by whether the variable is `x`. -/
theorem eval_terms_split (x : String) (env : String → ZMod p)
    (terms : List (String × ZMod p)) :
    (terms.map (fun t => t.2 * env t.1)).sum
    = ((terms.filter (fun t => t.1 = x)).map Prod.snd).sum * env x
      + ((terms.filter (fun t => t.1 ≠ x)).map (fun t => t.2 * env t.1)).sum := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
      by_cases hx : t.1 = x
      · rw [List.filter_cons_of_pos (by simpa using hx),
            List.filter_cons_of_neg (by simpa using hx),
            List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, hx]
        ring
      · rw [List.filter_cons_of_neg (by simpa using hx),
            List.filter_cons_of_pos (by simpa using hx),
            List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
        ring

/-- Total coefficient of `x` in a linear form. -/
def LinExpr.coeff (l : LinExpr p) (x : String) : ZMod p :=
  ((l.terms.filter (fun t => t.1 = x)).map Prod.snd).sum

/-- The linear form with all `x` terms removed. -/
def LinExpr.others (l : LinExpr p) (x : String) : LinExpr p :=
  ⟨l.const, l.terms.filter (fun t => t.1 ≠ x)⟩

theorem LinExpr.eval_split (l : LinExpr p) (x : String) (env : String → ZMod p) :
    l.eval env = l.coeff x * env x + (l.others x).eval env := by
  simp only [LinExpr.eval, LinExpr.coeff, LinExpr.others, eval_terms_split x env l.terms]
  ring

/-- Turn a linear form back into an expression. -/
def LinExpr.toExpr (l : LinExpr p) : Expression p :=
  l.terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) (.const l.const)

theorem toExpr_foldl_eval (env : String → ZMod p) (terms : List (String × ZMod p)) :
    ∀ init : Expression p,
      (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).eval env
      = init.eval env + (terms.map (fun t => t.2 * env t.1)).sum := by
  induction terms with
  | nil => intro init; simp
  | cons t rest ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      simp only [Expression.eval]
      ring

theorem LinExpr.toExpr_eval (l : LinExpr p) (env : String → ZMod p) :
    l.toExpr.eval env = l.eval env := by
  simp only [LinExpr.toExpr, LinExpr.eval, toExpr_foldl_eval, Expression.eval]

/-- Try to solve the linear form `= 0` for variable `v`, when `v` has coefficient `±1`. -/
def LinExpr.trySolve (l : LinExpr p) (v : String) : Option (String × Expression p) :=
  if l.coeff v = 1 then some (v, ((l.others v).scale (-1)).toExpr)
  else if l.coeff v = -1 then some (v, (l.others v).toExpr)
  else none

theorem LinExpr.trySolve_sound (l : LinExpr p) (v x : String) (t : Expression p)
    (h : l.trySolve v = some (x, t)) (env : String → ZMod p) (hl : l.eval env = 0) :
    env x = t.eval env := by
  unfold LinExpr.trySolve at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [LinExpr.toExpr_eval, LinExpr.scale_eval]
    have hs := l.eval_split v env
    rw [h1, one_mul] at hs; rw [hs] at hl
    linear_combination hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [LinExpr.toExpr_eval]
    have hs := l.eval_split v env
    rw [h2] at hs; rw [hs] at hl
    linear_combination -hl

/-- Solve the linear form for the first `±1`-coefficient variable. -/
def solveAffineLin (l : LinExpr p) : Option (String × Expression p) :=
  match (l.terms.map Prod.fst).find? (fun v => (l.trySolve v).isSome) with
  | some v => l.trySolve v
  | none => none

theorem solveAffineLin_sound (l : LinExpr p) (x : String) (t : Expression p)
    (h : solveAffineLin l = some (x, t)) (env : String → ZMod p) (hl : l.eval env = 0) :
    env x = t.eval env := by
  unfold solveAffineLin at h
  split at h
  · rename_i v _
    exact l.trySolve_sound v x t h env hl
  · exact absurd h (by simp)

/-- Solve a constraint expression for a unit-coefficient variable, if it is affine. -/
def solveAffine (c : Expression p) : Option (String × Expression p) :=
  (linearize c).bind solveAffineLin

theorem solveAffine_sound (c : Expression p) (x : String) (t : Expression p)
    (h : solveAffine c = some (x, t)) (env : String → ZMod p) (hc : c.eval env = 0) :
    env x = t.eval env := by
  simp only [solveAffine, Option.bind_eq_some_iff] at h
  obtain ⟨l, hlin, hsl⟩ := h
  have hl : l.eval env = 0 := by rw [← linearize_eval c l hlin env]; exact hc
  exact solveAffineLin_sound l x t hsl env hl

/-- The affine-substitution pass: eliminate one variable pinned by a linear constraint (unit
    coefficient). Generalizes `constantFixPass`. Iterate (with folding) for a fixpoint. -/
def affineSubstPass : VerifiedPass p := substFromConstraint solveAffine solveAffine_sound
