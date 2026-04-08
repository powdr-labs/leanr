import Leanr.Expression

theorem simplifying_add_eval {p : ℕ} (e1 e2 : Expression p) (env : String → ZMod p) :
    (Expression.simplifying_add e1 e2).eval env = e1.eval env + e2.eval env := by
  unfold Expression.simplifying_add
  split
  · simp [Expression.eval]
  · split
    · simp_all [Expression.eval]
    · split
      · simp [Expression.eval]
      · simp only [Expression.eval]; ring
      · simp only [Expression.eval]
  · split
    · simp_all [Expression.eval]
    · simp only [Expression.eval]; ring
  · simp only [Expression.eval]

theorem simplifying_add_correct {p : ℕ} (e1 e2 : Expression p) :
  Expression.equivalent (Expression.simplifying_add e1 e2) (.add e1 e2) := by
  unfold Expression.equivalent; funext env; exact simplifying_add_eval e1 e2 env

theorem simplifying_mul_eval {p : ℕ} (e1 e2 : Expression p) (env : String → ZMod p) :
    (Expression.simplifying_mul e1 e2).eval env = e1.eval env * e2.eval env := by
  unfold Expression.simplifying_mul
  split
  · simp [Expression.eval]
  · split
    · simp_all [Expression.eval]
    · split
      · simp_all [Expression.eval]
      · split
        · simp [Expression.eval]
        · simp [Expression.eval]; ring
        · simp [Expression.eval]; ring
        · simp [Expression.eval]
  · split
    · simp_all [Expression.eval]
    · split
      · simp_all [Expression.eval]
      · simp [Expression.eval]; ring
  · simp [Expression.eval]

theorem simplifying_mul_correct {p : ℕ} (e1 e2 : Expression p) :
  Expression.equivalent (Expression.simplifying_mul e1 e2) (.mul e1 e2) := by
  unfold Expression.equivalent; funext env; exact simplifying_mul_eval e1 e2 env

-- Expression.simplify does not modify the semantics of the expression.
theorem simplify_correct {p : ℕ} (e : Expression p) :
  Expression.equivalent e e.simplify := by
  unfold Expression.equivalent; funext env
  induction e with
  | const n => rfl
  | var x => rfl
  | add e1 e2 ih1 ih2 =>
    show _ = (Expression.simplifying_add _ _).eval env
    rw [simplifying_add_eval]; simp [Expression.eval, ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
    show _ = (Expression.simplifying_mul _ _).eval env
    rw [simplifying_mul_eval]; simp [Expression.eval, ih1, ih2]

/-- Substituting variables that agree with the environment preserves evaluation. -/
theorem Expression.substituteAll_eval {p : ℕ} (e : Expression p)
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h : ∀ x v, m[x]? = some v → env x = v) :
    (e.substituteAll m).eval env = e.eval env := by
  induction e with
  | const n => simp [substituteAll, eval]
  | var x =>
    simp only [substituteAll]
    cases hx : m[x]? with
    | none => simp [eval]
    | some v => simp [eval]; exact (h x v hx).symm
  | add e1 e2 ih1 ih2 =>
    unfold substituteAll
    rw [simplifying_add_eval, ih1, ih2]; rfl
  | mul e1 e2 ih1 ih2 =>
    unfold substituteAll
    rw [simplifying_mul_eval, ih1, ih2]; rfl

/-- Single-variable substitute preserves evaluation when env agrees. -/
theorem Expression.substitute_eval {p : ℕ} (e : Expression p)
    (x : String) (v : ZMod p) (env : String → ZMod p)
    (h : env x = v) :
    (e.substitute x v).eval env = e.eval env := by
  induction e with
  | const n => simp [substitute, eval]
  | var y =>
    simp only [substitute]
    split
    · simp_all [eval]
    · simp [eval]
  | add e1 e2 ih1 ih2 =>
    unfold substitute
    rw [simplifying_add_eval, ih1, ih2]; rfl
  | mul e1 e2 ih1 ih2 =>
    unfold substitute
    rw [simplifying_mul_eval, ih1, ih2]; rfl
