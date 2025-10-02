import Leanr.GroupedExpression

structure AlgebraicConstraint (p : ℕ) where
  expression : GroupedExpression p

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
  c.expression.toConstant? = some 0

def AlgebraicConstraint.trivial? {p : ℕ}
  (c : AlgebraicConstraint p) : Bool :=
  c.expression.toConstant? = some 0

instance {p : ℕ} : ToString (AlgebraicConstraint p) where
  toString c := toString c.expression

instance {p : ℕ} : ToString (List (AlgebraicConstraint p)) where
  toString cs := String.intercalate "\n" (cs.map toString)
