import Leanr.AffineExpression
import Leanr.Expression

variable {p : ℕ} [Fact (Nat.Prime p)]

inductive AlgebraicConstraint (p : ℕ) where
  | affine (e : AffineExpression p)
  | general (e : Expression p)

def AlgebraicConstraint.assertZero (e : Expression p) : AlgebraicConstraint p :=
  match AffineExpression.ofExpression? e with
  | some ae => .affine ae
  | none => .general e

def AlgebraicConstraint.substitute
  (c : AlgebraicConstraint p)
  (x : String)
  (v : ZMod p) : AlgebraicConstraint p :=
  match c with
  | .affine e => .affine (e.substitute x v)
  | .general e => .general (e.substitute x v)

/-- Substitute all variables in the map at once. -/
def AlgebraicConstraint.substituteAll
  (c : AlgebraicConstraint p)
  (env : Std.HashMap String (ZMod p)) : AlgebraicConstraint p :=
  match c with
  | .affine e => .affine (e.substituteAll env)
  | .general e => .general (e.substituteAll env)

def AlgebraicConstraint.toConstant? {p : ℕ}
  (c : AlgebraicConstraint p) : Option (ZMod p) :=
  match c with
  | .affine e => e.toConstant?
  | .general e => e.toConstant?

def AlgebraicConstraint.eval {p : ℕ}
  (c : AlgebraicConstraint p) :
  (env : String → ZMod p) → ZMod p :=
  match c with
  | .affine e => e.eval
  | .general e => e.eval

def AlgebraicConstraint.is_satisfied_by {p : ℕ}
  (c : AlgebraicConstraint p)
  (env : String → ZMod p) : Prop :=
  c.eval env = 0

def AlgebraicConstraint.trivial {p : ℕ}
  (c : AlgebraicConstraint p) : Prop :=
  some 0 = match c with
  | .affine e => e.toConstant?
  | .general e => e.toConstant?

def AlgebraicConstraint.trivial? {p : ℕ}
  (c : AlgebraicConstraint p) : Bool :=
  some 0 = match c with
  | .affine e => e.toConstant?
  | .general e => e.toConstant?

instance : ToString (AlgebraicConstraint p) where
  toString c := match c with
    | .affine e => toString e
    | .general e => toString e

instance : ToString (List (AlgebraicConstraint p)) where
  toString cs := String.intercalate "\n" (cs.map toString)


structure Assignment {p : ℕ} where
  var : String
  value : ZMod p

instance {p : ℕ} : ToString (Assignment (p := p)) where
  toString a := a.var ++ " = " ++ toString a.value.val

--- Try to solve an affine constraint with at most one variable.
def AlgebraicConstraint.solve? {p : ℕ}
  (constraint : AlgebraicConstraint p) : Option (Assignment (p := p)) :=
  match constraint with
  | .general _ => none
  | .affine e =>
    match e.affine.toList with
    | [] => none
    | [(x, c)] =>
      if c = 0 then
        -- actually unreachable
        none
      else
        some { var := x, value := -c⁻¹ * e.offset }
    | _ => none -- more than one variable
