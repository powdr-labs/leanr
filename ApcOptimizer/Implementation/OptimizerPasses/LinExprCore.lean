import ApcOptimizer.Spec
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

/-! # Sparse linear-expression spec core

Representation-independent (`Variable`/`Expression`/`ZMod`/`List`) content re-homed here from the
reference `Variable` passes so the permanent `Variable`-side shared-facts files
(`DomainProp.lean`, `MemoryUnify.lean`) — and parts of the dense `Affine`/`Normalize`/`Gauss`
bridges — consume it from a neutral home. Every item keeps its original (fully-qualified) name, so
no consumer changed but its import.

Collected here:

* the `Expression` syntactic helpers `Expression.mentions` / `Expression.varCount` /
  `Expression.isVar` (from the reference `Gauss` pass);
* the constant-fold *value* core `Expression.foldAdd` / `foldMul` / `fold` and their eval lemmas,
  plus `Expression.constValue?` / `constValue?_sound` (from the reference `ConstantFold` and
  `TautoBus` passes);
* the sparse linear form `LinExpr` with its algebra (`add` / `scale` / `eval` / `coeff` / `others` /
  `eval_split` / `toExpr`), `linearize` / `linearize_eval` (from the reference `Affine` pass);
* the normalization chain `addCoeff` / `mergeTerms` / `LinExpr.norm` / `LinExpr.norm_eval` (from
  the reference `Normalize` pass). -/

variable {p : ℕ}

/-! ## Syntactic `Expression` helpers -/

/-- Does the expression mention variable `x`? -/
def Expression.mentions (x : Variable) : Expression p → Bool
  | .const _ => false
  | .var y => y == x
  | .add a b => a.mentions x || b.mentions x
  | .mul a b => a.mentions x || b.mentions x

/-- Number of variable occurrences (with multiplicity). -/
def Expression.varCount : Expression p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add a b => a.varCount + b.varCount
  | .mul a b => a.varCount + b.varCount

/-- Is the expression literally a variable? -/
def Expression.isVar : Expression p → Bool
  | .var _ => true
  | _ => false

/-! ## Constant-fold value core

The smart constructors and the bottom-up fold, plus `constValue?` (the constant an expression folds
to, if any). Only the *value*-level content lives here. -/

/-- Smart addition: fold two constants and drop `+ 0` on either side. -/
def Expression.foldAdd (a b : Expression p) : Expression p :=
  match a, b with
  | .const m, .const n => .const (m + n)
  | .const m, b => if m = 0 then b else .add (.const m) b
  | a, .const n => if n = 0 then a else .add a (.const n)
  | a, b => .add a b

/-- Smart multiplication: fold two constants, absorb `* 0`, drop `* 1`. -/
def Expression.foldMul (a b : Expression p) : Expression p :=
  match a, b with
  | .const m, .const n => .const (m * n)
  | .const m, b => if m = 0 then .const 0 else if m = 1 then b else .mul (.const m) b
  | a, .const n => if n = 0 then .const 0 else if n = 1 then a else .mul a (.const n)
  | a, b => .mul a b

theorem Expression.foldAdd_eval (a b : Expression p) (env : Variable → ZMod p) :
    (a.foldAdd b).eval env = a.eval env + b.eval env := by
  unfold Expression.foldAdd
  split <;> (try split_ifs) <;> simp_all [Expression.eval]

theorem Expression.foldMul_eval (a b : Expression p) (env : Variable → ZMod p) :
    (a.foldMul b).eval env = a.eval env * b.eval env := by
  unfold Expression.foldMul
  split <;> (try split_ifs) <;> simp_all [Expression.eval]

/-- One bottom-up constant-folding / algebraic-normalization pass over an expression. Children are
    normalized first, then the smart constructors fold the current node. -/
def Expression.fold : Expression p → Expression p
  | .const n => .const n
  | .var x => .var x
  | .add a b => a.fold.foldAdd b.fold
  | .mul a b => a.fold.foldMul b.fold

theorem Expression.fold_eval (e : Expression p) (env : Variable → ZMod p) :
    e.fold.eval env = e.eval env := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb => rw [Expression.fold, Expression.foldAdd_eval, iha, ihb]; rfl
  | mul a b iha ihb => rw [Expression.fold, Expression.foldMul_eval, iha, ihb]; rfl

/-- The constant value of an expression, if its fold is a literal constant. -/
def Expression.constValue? (e : Expression p) : Option (ZMod p) :=
  match e.fold with
  | .const c => some c
  | _ => none

theorem Expression.constValue?_sound (e : Expression p) (c : ZMod p)
    (h : e.constValue? = some c) (env : Variable → ZMod p) : e.eval env = c := by
  unfold Expression.constValue? at h
  split at h
  · rename_i c' hfold
    simp only [Option.some.injEq] at h
    subst h
    rw [← e.fold_eval env, hfold]
    rfl
  · exact absurd h (by simp)

/-! ## The sparse linear form

A normalized linear form (`const + Σ coeff·var`), with `linearize`/`linearize_eval` turning an
`Expression` into one (returning `none` on a genuine variable×variable product), and the
coefficient/remainder decomposition `eval_split` used to solve. Purely equational — no
field/primality is needed. -/

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

/-! ## Affine normalization (collect like terms)

Merge a linear form's terms — combine coefficients of equal variables and drop zeros — preserving
first-occurrence order so the merge is idempotent. `LinExpr.norm_eval` shows it is eval-preserving.
Field-free (works over any commutative ring). Only the value-level content lives here. -/

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
