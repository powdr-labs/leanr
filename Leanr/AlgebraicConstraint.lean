import Leanr.Expression

structure AlgebraicConstraint (p : ℕ) where
  expression : Expression p

def AlgebraicConstraint.is_satisfied_by {p : ℕ}
  (c : AlgebraicConstraint p)
  (env : String → ZMod p) : Prop :=
  c.expression.eval env = 0

def AlgebraicConstraint.substitute {p : ℕ}
  (c : AlgebraicConstraint p)
  (x : String)
  (v : ZMod p) : AlgebraicConstraint p :=
  { expression := c.expression.substitute x v }

def AlgebraicConstraint.trivial {p : ℕ}
  (c : AlgebraicConstraint p) : Prop :=
  c.expression = .const 0

def AlgebraicConstraint.trivial? {p : ℕ}
  (c : AlgebraicConstraint p) : Bool :=
  match c.expression with
  | .const k => k.val = 0
  | _        => false
