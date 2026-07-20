import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Subst
import ApcOptimizer.Utils.Size
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.MinMax

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
  terms : List (Variable × ZMod p)

/-- Evaluate a linear form. -/
def LinExpr.eval (l : LinExpr p) (env : Variable → ZMod p) : ZMod p :=
  l.const + (l.terms.map (fun t => t.2 * env t.1)).sum

def LinExpr.add (a b : LinExpr p) : LinExpr p := ⟨a.const + b.const, a.terms ++ b.terms⟩
def LinExpr.scale (k : ZMod p) (a : LinExpr p) : LinExpr p :=
  ⟨k * a.const, a.terms.map (fun t => (t.1, k * t.2))⟩

theorem LinExpr.add_eval (a b : LinExpr p) (env : Variable → ZMod p) :
    (a.add b).eval env = a.eval env + b.eval env := by
  simp only [LinExpr.add, LinExpr.eval, List.map_append, List.sum_append]
  ring

theorem LinExpr.scale_eval (k : ZMod p) (a : LinExpr p) (env : Variable → ZMod p) :
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
    (env : Variable → ZMod p) : e.eval env = l.eval env := by
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
theorem eval_terms_split (x : Variable) (env : Variable → ZMod p)
    (terms : List (Variable × ZMod p)) :
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
def LinExpr.coeff (l : LinExpr p) (x : Variable) : ZMod p :=
  ((l.terms.filter (fun t => t.1 = x)).map Prod.snd).sum

/-- The linear form with all `x` terms removed. -/
def LinExpr.others (l : LinExpr p) (x : Variable) : LinExpr p :=
  ⟨l.const, l.terms.filter (fun t => t.1 ≠ x)⟩

theorem LinExpr.eval_split (l : LinExpr p) (x : Variable) (env : Variable → ZMod p) :
    l.eval env = l.coeff x * env x + (l.others x).eval env := by
  simp only [LinExpr.eval, LinExpr.coeff, LinExpr.others, eval_terms_split x env l.terms]
  ring

/-- Turn a linear form back into an expression. -/
def LinExpr.toExpr (l : LinExpr p) : Expression p :=
  l.terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) (.const l.const)

theorem toExpr_foldl_eval (env : Variable → ZMod p) (terms : List (Variable × ZMod p)) :
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

theorem LinExpr.toExpr_eval (l : LinExpr p) (env : Variable → ZMod p) :
    l.toExpr.eval env = l.eval env := by
  simp only [LinExpr.toExpr, LinExpr.eval, toExpr_foldl_eval, Expression.eval]

/-! ## Variable bounds (for `out.vars ⊆ cs.vars`) -/

theorem toExpr_foldl_vars (terms : List (Variable × ZMod p)) :
    ∀ (init : Expression p) (x : Variable),
      x ∈ (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).vars →
      x ∈ init.vars ∨ x ∈ terms.map Prod.fst := by
  induction terms with
  | nil => intro init x hx; exact Or.inl hx
  | cons t rest ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with h | h
      · simp only [Expression.vars, List.mem_append, List.nil_append, List.mem_singleton] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by subst h; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- `toExpr` only mentions the term variables. -/
theorem LinExpr.toExpr_vars (l : LinExpr p) : ∀ x ∈ l.toExpr.vars, x ∈ l.terms.map Prod.fst := by
  intro x hx
  rcases toExpr_foldl_vars l.terms _ x hx with h | h
  · simp [Expression.vars] at h
  · exact h

theorem LinExpr.scale_terms_fst (k : ZMod p) (l : LinExpr p) :
    (l.scale k).terms.map Prod.fst = l.terms.map Prod.fst := by
  simp [LinExpr.scale, List.map_map, Function.comp]

theorem LinExpr.others_terms_fst_subset (l : LinExpr p) (v x : Variable)
    (h : x ∈ (l.others v).terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [LinExpr.others, List.mem_map] at h ⊢
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, List.mem_of_mem_filter ht, rfl⟩

/-- Linearization introduces no variable outside the expression. -/
theorem linearize_vars (e : Expression p) (l : LinExpr p) (h : linearize e = some l) :
    ∀ x ∈ l.terms.map Prod.fst, x ∈ e.vars := by
  induction e generalizing l with
  | const n => simp only [linearize, Option.some.injEq] at h; subst h; simp
  | var y =>
      simp only [linearize, Option.some.injEq] at h; subst h
      intro x hx; simpa [Expression.vars] using hx
  | add a b iha ihb =>
      cases hla : linearize a with
      | none => simp [linearize, hla] at h
      | some la => cases hlb : linearize b with
        | none => simp [linearize, hla, hlb] at h
        | some lb =>
          simp only [linearize, hla, hlb, Option.some.injEq] at h
          subst h
          intro x hx
          simp only [LinExpr.add, List.map_append, List.mem_append] at hx
          simp only [Expression.vars, List.mem_append]
          exact hx.imp (iha la hla x) (ihb lb hlb x)
  | mul a b iha ihb =>
      cases hla : linearize a with
      | none => simp [linearize, hla] at h
      | some la => cases hlb : linearize b with
        | none => simp [linearize, hla, hlb] at h
        | some lb =>
          by_cases h1 : la.terms.isEmpty = true
          · simp only [linearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            intro x hx
            rw [LinExpr.scale_terms_fst] at hx
            exact List.mem_append.2 (Or.inr (ihb lb hlb x hx))
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [linearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              intro x hx
              rw [LinExpr.scale_terms_fst] at hx
              exact List.mem_append.2 (Or.inl (iha la hla x hx))
            · simp only [linearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-- Try to solve the linear form `= 0` for variable `v`, when `v` has coefficient `±1`. -/
def LinExpr.trySolve (l : LinExpr p) (v : Variable) : Option (Variable × Expression p) :=
  if l.coeff v = 1 then some (v, ((l.others v).scale (-1)).toExpr)
  else if l.coeff v = -1 then some (v, (l.others v).toExpr)
  else none

theorem LinExpr.trySolve_sound (l : LinExpr p) (v x : Variable) (t : Expression p)
    (h : l.trySolve v = some (x, t)) (env : Variable → ZMod p) (hl : l.eval env = 0) :
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

/-- Try to solve the linear form `= 0` for `v` when `v`'s coefficient is a *unit*, verified by
    the decidable re-check `a * a⁻¹ = 1` (with the ring's `Inv`, so soundness never depends on
    inversion behaving well): over a prime field every nonzero coefficient qualifies, over
    `ZMod n` exactly the residues coprime to `n`. Generalizes `trySolve`; kept separate so the
    solver can *prefer* `±1` pivots, which substitute without rescaling the other coefficients. -/
def LinExpr.trySolveUnit (l : LinExpr p) (v : Variable) : Option (Variable × Expression p) :=
  if l.coeff v * (l.coeff v)⁻¹ = 1 then
    some (v, ((l.others v).scale (-(l.coeff v)⁻¹)).toExpr)
  else none

theorem LinExpr.trySolveUnit_sound (l : LinExpr p) (v x : Variable) (t : Expression p)
    (h : l.trySolveUnit v = some (x, t)) (env : Variable → ZMod p) (hl : l.eval env = 0) :
    env x = t.eval env := by
  unfold LinExpr.trySolveUnit at h
  split_ifs at h with h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [LinExpr.toExpr_eval, LinExpr.scale_eval]
  have hs := l.eval_split v env
  have h0 : l.coeff v * env v + (l.others v).eval env = 0 := by rw [← hs]; exact hl
  linear_combination (l.coeff v)⁻¹ * h0 - env v * h1

theorem LinExpr.trySolve_vars (l : LinExpr p) (v x : Variable) (t : Expression p)
    (h : l.trySolve v = some (x, t)) : ∀ y ∈ t.vars, y ∈ l.terms.map Prod.fst := by
  intro y hy
  unfold LinExpr.trySolve at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := LinExpr.toExpr_vars _ y hy
    rw [LinExpr.scale_terms_fst] at this
    exact l.others_terms_fst_subset v y this
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact l.others_terms_fst_subset v y (LinExpr.toExpr_vars _ y hy)

theorem LinExpr.trySolveUnit_vars (l : LinExpr p) (v x : Variable) (t : Expression p)
    (h : l.trySolveUnit v = some (x, t)) : ∀ y ∈ t.vars, y ∈ l.terms.map Prod.fst := by
  intro y hy
  unfold LinExpr.trySolveUnit at h
  split_ifs at h with h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have := LinExpr.toExpr_vars _ y hy
  rw [LinExpr.scale_terms_fst] at this
  exact l.others_terms_fst_subset v y this

/-- Solve the linear form for the first `±1`-coefficient variable; failing that, for the first
    variable whose coefficient is a unit. -/
def solveAffineLin (l : LinExpr p) : Option (Variable × Expression p) :=
  match (l.terms.map Prod.fst).find? (fun v => (l.trySolve v).isSome) with
  | some v => l.trySolve v
  | none =>
    match (l.terms.map Prod.fst).find? (fun v => (l.trySolveUnit v).isSome) with
    | some v => l.trySolveUnit v
    | none => none

theorem solveAffineLin_sound (l : LinExpr p) (x : Variable) (t : Expression p)
    (h : solveAffineLin l = some (x, t)) (env : Variable → ZMod p) (hl : l.eval env = 0) :
    env x = t.eval env := by
  unfold solveAffineLin at h
  split at h
  · rename_i v _
    exact l.trySolve_sound v x t h env hl
  · split at h
    · rename_i v _
      exact l.trySolveUnit_sound v x t h env hl
    · exact absurd h (by simp)

/-- Solve a constraint expression for a unit-coefficient variable, if it is affine. -/
def solveAffine (c : Expression p) : Option (Variable × Expression p) :=
  (linearize c).bind solveAffineLin

theorem solveAffine_sound (c : Expression p) (x : Variable) (t : Expression p)
    (h : solveAffine c = some (x, t)) (env : Variable → ZMod p) (hc : c.eval env = 0) :
    env x = t.eval env := by
  simp only [solveAffine, Option.bind_eq_some_iff] at h
  obtain ⟨l, hlin, hsl⟩ := h
  have hl : l.eval env = 0 := by rw [← linearize_eval c l hlin env]; exact hc
  exact solveAffineLin_sound l x t hsl env hl

/-! ## Occurrence-aware pivot selection

`substFromConstraint` substitutes the *first* solvable pivot, which can copy a large solution
expression into every other occurrence of a heavily-used variable (e.g. inlining a timestamp
into five bus payloads). Instead we enumerate *all* solvable pivots of all constraints and pick
the one minimizing an expression-duplication cost. Soundness is per-pivot (each candidate comes
with the same entailment as before), so the choice heuristic itself carries no proof burden. -/

/-- All `±1`-coefficient pivots of one constraint. -/
def pm1PivotsOf (c : Expression p) : List (Variable × Expression p) :=
  match linearize c with
  | none => []
  | some l => (l.terms.map Prod.fst).filterMap l.trySolve

theorem pm1PivotsOf_sound (c : Expression p) (x : Variable) (t : Expression p)
    (h : (x, t) ∈ pm1PivotsOf c) (env : Variable → ZMod p) (hc : c.eval env = 0) :
    env x = t.eval env := by
  unfold pm1PivotsOf at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    have hl : l.eval env = 0 := by rw [← linearize_eval c l hlin env]; exact hc
    obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
    exact l.trySolve_sound v x t hv env hl

/-- Unit-coefficient pivots of one constraint, for variables with no `±1` solution. -/
def unitPivotsOf (c : Expression p) : List (Variable × Expression p) :=
  match linearize c with
  | none => []
  | some l =>
    (l.terms.map Prod.fst).filterMap (fun v =>
      match l.trySolve v with
      | some _ => none
      | none => l.trySolveUnit v)

theorem unitPivotsOf_sound (c : Expression p) (x : Variable) (t : Expression p)
    (h : (x, t) ∈ unitPivotsOf c) (env : Variable → ZMod p) (hc : c.eval env = 0) :
    env x = t.eval env := by
  unfold unitPivotsOf at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    have hl : l.eval env = 0 := by rw [← linearize_eval c l hlin env]; exact hc
    obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
    cases htr : l.trySolve v with
    | some r => rw [htr] at hv; exact absurd hv (by simp)
    | none =>
        rw [htr] at hv
        exact l.trySolveUnit_sound v x t hv env hl

/-- All solvable pivots across a constraint list, `±1` pivots first: `List.argmin` keeps the
    *first* minimum, so on a cost tie a `±1` pivot (which substitutes without rescaling the
    remaining coefficients into inverse constants) beats a general unit pivot. -/
def solvableFrom (all : List (Expression p)) : List (Variable × Expression p) :=
  all.flatMap pm1PivotsOf ++ all.flatMap unitPivotsOf

theorem solvableFrom_sound (all : List (Expression p)) (x : Variable) (t : Expression p)
    (h : (x, t) ∈ solvableFrom all) (env : Variable → ZMod p)
    (hall : ∀ c ∈ all, c.eval env = 0) : env x = t.eval env := by
  rcases List.mem_append.1 h with h' | h' <;> obtain ⟨c, hc, hp⟩ := List.mem_flatMap.1 h'
  · exact pm1PivotsOf_sound c x t hp env (hall c hc)
  · exact unitPivotsOf_sound c x t hp env (hall c hc)

theorem pm1PivotsOf_vars (c : Expression p) (x : Variable) (t : Expression p)
    (h : (x, t) ∈ pm1PivotsOf c) : ∀ y ∈ t.vars, y ∈ c.vars := by
  intro y hy
  unfold pm1PivotsOf at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
    exact linearize_vars c l hlin y (l.trySolve_vars v x t hv y hy)

theorem unitPivotsOf_vars (c : Expression p) (x : Variable) (t : Expression p)
    (h : (x, t) ∈ unitPivotsOf c) : ∀ y ∈ t.vars, y ∈ c.vars := by
  intro y hy
  unfold unitPivotsOf at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
    cases htr : l.trySolve v with
    | some r => rw [htr] at hv; exact absurd hv (by simp)
    | none =>
        rw [htr] at hv
        exact linearize_vars c l hlin y (l.trySolveUnit_vars v x t hv y hy)

theorem solvableFrom_vars (all : List (Expression p)) (x : Variable) (t : Expression p)
    (h : (x, t) ∈ solvableFrom all) : ∀ y ∈ t.vars, ∃ c ∈ all, y ∈ c.vars := by
  intro y hy
  rcases List.mem_append.1 h with h' | h' <;> obtain ⟨c, hc, hp⟩ := List.mem_flatMap.1 h'
  · exact ⟨c, hc, pm1PivotsOf_vars c x t hp y hy⟩
  · exact ⟨c, hc, unitPivotsOf_vars c x t hp y hy⟩

/-- The duplication cost of substituting `x := t`: every *other* occurrence of `x` is replaced
    by a copy of `t`. A variable occurring only in its defining constraint costs `0`. -/
def pivotCost (cs : ConstraintSystem p) (x : Variable) (t : Expression p) : Nat :=
  (cs.occurrences x - 1) * (1 + t.vars.length)

/-- The cheapest solvable pivot of the whole system, if any. -/
def bestAffinePivot (cs : ConstraintSystem p) : Option (Variable × Expression p) :=
  (solvableFrom cs.algebraicConstraints).argmin (fun xt => pivotCost cs xt.1 xt.2)

/-- The affine-substitution pass: eliminate one variable pinned by a linear constraint (unit
    coefficient), choosing the occurrence-cheapest pivot. Generalizes `constantFixPass`.
    Iterate (with folding) for a fixpoint. -/
def affineSubstPass : VerifiedPass p := fun cs bs =>
  match hf : bestAffinePivot cs with
  | some (x, t) =>
      ⟨cs.subst x t, [], cs.subst_correct x t bs
        (fun env hsat =>
          solvableFrom_sound cs.algebraicConstraints x t
            (List.argmin_mem hf) env (fun c hc => hsat.1 c hc))
        (fun y hy => by
          obtain ⟨c, hc, hyc⟩ :=
            solvableFrom_vars cs.algebraicConstraints x t (List.argmin_mem hf) y hy
          exact ConstraintSystem.mem_vars_of_constraint hc hyc)⟩
  | none => ⟨cs, [], PassCorrect.refl cs bs⟩
