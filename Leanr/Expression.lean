import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Init.Data.ToString.Basic

-- TODO could use generic Field instead of ZMod p

inductive Expression (p : ℕ) where
  | const (n : ZMod p)
  | var (x : String)
  | add (e1 e2 : Expression p)
  | mul (e1 e2 : Expression p)

def Expression.eval {p : ℕ} (e : Expression p) (env : String → ZMod p): ZMod p :=
  match e with
  | .const n => n
  | .var x => env x
  | .add e1 e2 => e1.eval env + e2.eval env
  | .mul e1 e2 => e1.eval env * e2.eval env

def Expression.toConstant? {p : ℕ} : Expression p → Option (ZMod p)
  | .const n => some n
  | _ => none

def Expression.equivalent {p : ℕ} (e1 e2 : Expression p) : Prop :=
  e1.eval = e2.eval

@[simp]
def Expression.simplifying_add {p : ℕ} (e1 e2 : Expression p) : Expression p :=
  match e1, e2 with
  | .const n1, .const n2 => .const (n1 + n2)
  | .const n1, _ => if n1 = 0 then e2 else match e2 with
    | .const n2 => .const (n1 + n2)
    | .add (.const n2) e22 => .add (.const (n1 + n2)) e22
    | _ => .add e1 e2
  | _, .const n2 => if n2 = 0 then e1 else .add e2 e1 -- move the constant to the left
  | _, _ => .add e1 e2


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

def Expression.simplifying_mul {p : ℕ} (e1 e2 : Expression p) : Expression p :=
  match e1, e2 with
  | .const n1, .const n2 => .const (n1 * n2)
  | .const n1, _ => if n1 = 0 then
        .const 0
      else if n1 = 1 then
        e2
      else match e2 with
        | .const n2 => .const (n1 * n2)
        | .add e21 e22 => .simplifying_add (.mul e1 e21) (.mul e1 e22) -- distribute
        | .mul e21 e22 => .mul (.mul e1 e21) e22 -- associate to the left
        | _ => .mul e1 e2
  | _, .const n2 => if n2 = 0 then .const 0 else if n2 = 1 then e1 else .mul e2 e1 -- move the constant to the left
  | _, _ => .mul e1 e2

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

def Expression.simplify {p : ℕ} (e : Expression p) : Expression p :=
  match e with
  | .const n => .const n
  | .var x => .var x
  | .add e1 e2 =>
    let e1 := e1.simplify
    let e2 := e2.simplify
    e1.simplifying_add e2
  | .mul e1 e2 =>
    let e1 := e1.simplify
    let e2 := e2.simplify
    e1.simplifying_mul e2

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

def Expression.substitute {p : ℕ} (e : Expression p) (x : String) (v : ZMod p) : Expression p :=
  match e with
  | .const n => .const n
  | .var y => if x = y then .const v else e
  | .add e1 e2 => .simplifying_add (e1.substitute x v) (e2.substitute x v)
  | .mul e1 e2 => .simplifying_mul (e1.substitute x v) (e2.substitute x v)

/-- Substitute all variables in the map in a single tree walk. -/
def Expression.substituteAll {p : ℕ} (e : Expression p) (env : Std.HashMap String (ZMod p)) : Expression p :=
  match e with
  | .const n => .const n
  | .var y => match env[y]? with
    | some v => .const v
    | none => e
  | .add e1 e2 => .simplifying_add (e1.substituteAll env) (e2.substituteAll env)
  | .mul e1 e2 => .simplifying_mul (e1.substituteAll env) (e2.substituteAll env)

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


instance {p} : Add (Expression p) where
  add x y := Expression.simplifying_add x y

instance {p} : Mul (Expression p) where
  mul x y := Expression.simplifying_mul x y

instance {p} : OfNat (Expression p) (n : Nat) where
  ofNat := .const (n % p)

instance {p} : ToString (Expression p) where
  toString :=
    let rec toStr : Expression p → String
      | .const n => toString n.val
      | .var x => x
      | .add e1 e2 => s!"({toStr e1} + {toStr e2})"
      | .mul e1 e2 => s!"({toStr e1} * {toStr e2})"
    toStr
