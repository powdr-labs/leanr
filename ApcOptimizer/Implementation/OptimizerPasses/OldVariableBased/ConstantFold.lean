import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Rewrite

set_option autoImplicit false

/-! # Constant folding / algebraic normalization

The optimizer's foundational *enabler* pass. It rewrites every expression to a normal form using
only the ring identities that never change a value:

* `const a + const b ↝ const (a+b)`, `const a * const b ↝ const (a*b)`;
* `0 + e ↝ e`, `e + 0 ↝ e`;
* `0 * e ↝ 0`, `e * 0 ↝ 0`, `1 * e ↝ e`, `e * 1 ↝ e`.

Because the rewrite is *eval-preserving* (`Expression.fold_eval`), the whole pass is correct for
free via `ConstraintSystem.mapExpr_correct` — no field/primality assumptions, and the correctness
cannot be gamed (a wrong fold rule would fail `fold_eval`).

On its own it eliminates no variable (it changes shape, not the variable set), but it is what makes
the downstream detection passes robust: the DSL desugars `x - c` to `x + (-1)*c` and multiplicities
like `2013265920 * v`, and after a substitution plants a `const 0` factor, only folding collapses
`c * 0` / `0 * e` into the literal `const 0` that the removal passes key on. It is therefore the
first pass, and is re-run after substitution passes to propagate freshly-exposed constants. -/

variable {p : ℕ}

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

theorem Expression.foldAdd_vars (a b : Expression p) :
    ∀ x ∈ (a.foldAdd b).vars, x ∈ a.vars ++ b.vars := by
  intro x hx
  unfold Expression.foldAdd at hx
  split at hx <;> (try split_ifs at hx) <;> simp_all [Expression.vars]

theorem Expression.foldMul_vars (a b : Expression p) :
    ∀ x ∈ (a.foldMul b).vars, x ∈ a.vars ++ b.vars := by
  intro x hx
  unfold Expression.foldMul at hx
  split at hx <;> (try split_ifs at hx) <;> simp_all [Expression.vars]

theorem Expression.fold_vars (e : Expression p) : ∀ x ∈ e.fold.vars, x ∈ e.vars := by
  induction e with
  | const n => intro x hx; simp [Expression.fold, Expression.vars] at hx
  | var y => intro x hx; simpa [Expression.fold] using hx
  | add a b iha ihb =>
      intro x hx
      rw [Expression.fold] at hx
      rcases List.mem_append.1 (Expression.foldAdd_vars _ _ x hx) with h | h
      · exact List.mem_append.2 (Or.inl (iha x h))
      · exact List.mem_append.2 (Or.inr (ihb x h))
  | mul a b iha ihb =>
      intro x hx
      rw [Expression.fold] at hx
      rcases List.mem_append.1 (Expression.foldMul_vars _ _ x hx) with h | h
      · exact List.mem_append.2 (Or.inl (iha x h))
      · exact List.mem_append.2 (Or.inr (ihb x h))

/-- The constant-folding pass: normalize every expression. Correct via `mapExpr_correct`. -/
def constantFoldPass : VerifiedPass p := fun cs bs =>
  ⟨cs.mapExpr Expression.fold, [],
   ConstraintSystem.mapExpr_correct (g := Expression.fold)
     (fun e env => Expression.fold_eval e env) cs bs Expression.fold_vars⟩
