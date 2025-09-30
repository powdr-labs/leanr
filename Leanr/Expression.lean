import Mathlib.Data.ZMod.Basic

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

def Expression.equivalent {p : ℕ} (e1 e2 : Expression p) : Prop :=
  ∀ env : String → ZMod p, e1.eval env = e2.eval env

def Expression.substitute {p : ℕ} (e : Expression p) (x : String) (v : ZMod p) : Expression p :=
  match e with
  | .const n => .const n
  | .var y => if x = y then .const v else e
  | .add e1 e2 => .add (e1.substitute x v) (e2.substitute x v)
  | .mul e1 e2 => .mul (e1.substitute x v) (e2.substitute x v)

def Expression.simplify {p : ℕ} (e : Expression p) : Expression p :=
  match e with
  | .const n => .const n
  | .var x => .var x
  | .add e1 e2 =>
    let e1 := e1.simplify
    let e2 := e2.simplify
    match e1, e2 with
    -- | .const 0, _ => e2
    -- | _, .const 0 => e1
    | .const n1, .const n2 => .const (n1 + n2)
    | _, _ => .add e1 e2
  | .mul e1 e2 =>
    let se1 := e1.simplify
    let se2 := e2.simplify
    match se1, se2 with
    | .const n1, .const n2 => .const (n1 * n2)
    -- | .const 0, _ => .const 0
    -- | _, .const 0 => .const 0
    -- | .const 1, _ => se2
    -- | _, .const 1 => se1
    | _, _ => .mul se1 se2

-- Expression.simplify does not modify the semantics of the expression.
theorem simplify_correct {p : ℕ} (e : Expression p) :
  Expression.equivalent e e.simplify := by
  intro env
  induction e with
  | const n => simp [Expression.eval, Expression.simplify]
  | var x => simp [Expression.eval, Expression.simplify]
  | add e1 e2 ih1 ih2 =>
      cases h1 : Expression.simplify e1 <;>
      cases h2 : Expression.simplify e2 <;>
      simp [Expression.eval, Expression.simplify, h1, h2, ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
      cases h1 : Expression.simplify e1 <;>
      cases h2 : Expression.simplify e2 <;>
      simp [Expression.eval, Expression.simplify, h1, h2, ih1, ih2]
