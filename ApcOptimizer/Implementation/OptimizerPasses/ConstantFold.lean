import ApcOptimizer.Implementation.OptimizerPasses.Rewrite

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

/-- Smart addition with the field `add` supplied by the caller (so the `ZMod p` ring dictionary is
    derived once, not per node): fold two constants (via `add`) and drop `+ 0` on either side. -/
def Expression.foldAddWith (add : ZMod p → ZMod p → ZMod p) (a b : Expression p) : Expression p :=
  match a, b with
  | .const m, .const n => .const (add m n)
  | .const m, b => if m = 0 then b else .add (.const m) b
  | a, .const n => if n = 0 then a else .add a (.const n)
  | a, b => .add a b

/-- Smart multiplication with the field `mul` supplied by the caller: fold two constants, absorb
    `* 0`, drop `* 1`. -/
def Expression.foldMulWith (mul : ZMod p → ZMod p → ZMod p) (a b : Expression p) : Expression p :=
  match a, b with
  | .const m, .const n => .const (mul m n)
  | .const m, b => if m = 0 then .const 0 else if m = 1 then b else .mul (.const m) b
  | a, .const n => if n = 0 then .const 0 else if n = 1 then a else .mul a (.const n)
  | a, b => .mul a b

theorem Expression.foldAddWith_eval (add : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ x y, add x y = x + y) (a b : Expression p) (env : Variable → ZMod p) :
    (a.foldAddWith add b).eval env = a.eval env + b.eval env := by
  unfold Expression.foldAddWith
  split <;> (try split_ifs) <;> simp_all [Expression.eval]

theorem Expression.foldMulWith_eval (mul : ZMod p → ZMod p → ZMod p)
    (hmul : ∀ x y, mul x y = x * y) (a b : Expression p) (env : Variable → ZMod p) :
    (a.foldMulWith mul b).eval env = a.eval env * b.eval env := by
  unfold Expression.foldMulWith
  split <;> (try split_ifs) <;> simp_all [Expression.eval]

/-- One bottom-up constant-folding pass with the ring operations supplied by the caller. -/
def Expression.foldWith (add mul : ZMod p → ZMod p → ZMod p) : Expression p → Expression p
  | .const n => .const n
  | .var x => .var x
  | .add a b => Expression.foldAddWith add (a.foldWith add mul) (b.foldWith add mul)
  | .mul a b => Expression.foldMulWith mul (a.foldWith add mul) (b.foldWith add mul)

theorem Expression.foldWith_eval (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ x y, add x y = x + y) (hmul : ∀ x y, mul x y = x * y)
    (e : Expression p) (env : Variable → ZMod p) : (e.foldWith add mul).eval env = e.eval env := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
      rw [Expression.foldWith, Expression.foldAddWith_eval add hadd, iha, ihb]; rfl
  | mul a b iha ihb =>
      rw [Expression.foldWith, Expression.foldMulWith_eval mul hmul, iha, ihb]; rfl

/-- One bottom-up constant-folding / algebraic-normalization pass over an expression. The two ring
    operations are derived from their instances **once per call** and threaded through the recursion:
    the direct (un-hoisted) version reconstructs the `ZMod p` ring dictionary at every constant fold,
    a measured hot cost on constant-heavy expressions (multiplicities, constant messages). It is the
    same fold — `fold_eval`/`fold_vars` are all downstream consumers see. -/
def Expression.fold (e : Expression p) : Expression p :=
  e.foldWith (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul

theorem Expression.fold_eval (e : Expression p) (env : Variable → ZMod p) :
    e.fold.eval env = e.eval env :=
  Expression.foldWith_eval _ _ (fun _ _ => rfl) (fun _ _ => rfl) e env

theorem Expression.foldAddWith_vars (add : ZMod p → ZMod p → ZMod p) (a b : Expression p) :
    ∀ x ∈ (a.foldAddWith add b).vars, x ∈ a.vars ++ b.vars := by
  intro x hx
  unfold Expression.foldAddWith at hx
  split at hx <;> (try split_ifs at hx) <;> simp_all [Expression.vars]

theorem Expression.foldMulWith_vars (mul : ZMod p → ZMod p → ZMod p) (a b : Expression p) :
    ∀ x ∈ (a.foldMulWith mul b).vars, x ∈ a.vars ++ b.vars := by
  intro x hx
  unfold Expression.foldMulWith at hx
  split at hx <;> (try split_ifs at hx) <;> simp_all [Expression.vars]

theorem Expression.foldWith_vars (add mul : ZMod p → ZMod p → ZMod p) (e : Expression p) :
    ∀ x ∈ (e.foldWith add mul).vars, x ∈ e.vars := by
  induction e with
  | const n => intro x hx; simp [Expression.foldWith, Expression.vars] at hx
  | var y => intro x hx; simpa [Expression.foldWith] using hx
  | add a b iha ihb =>
      intro x hx
      rw [Expression.foldWith] at hx
      rcases List.mem_append.1 (Expression.foldAddWith_vars add _ _ x hx) with h | h
      · exact List.mem_append.2 (Or.inl (iha x h))
      · exact List.mem_append.2 (Or.inr (ihb x h))
  | mul a b iha ihb =>
      intro x hx
      rw [Expression.foldWith] at hx
      rcases List.mem_append.1 (Expression.foldMulWith_vars mul _ _ x hx) with h | h
      · exact List.mem_append.2 (Or.inl (iha x h))
      · exact List.mem_append.2 (Or.inr (ihb x h))

theorem Expression.fold_vars (e : Expression p) : ∀ x ∈ e.fold.vars, x ∈ e.vars :=
  Expression.foldWith_vars _ _ e

/-- The constant-folding pass: normalize every expression. Correct via `mapExpr_correct`. -/
def constantFoldPass : VerifiedPass p := fun cs bs =>
  ⟨cs.mapExpr Expression.fold, [],
   ConstraintSystem.mapExpr_correct (g := Expression.fold)
     (fun e env => Expression.fold_eval e env) cs bs Expression.fold_vars⟩
