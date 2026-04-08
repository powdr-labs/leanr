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

/-- substituteAll preserves evaluation when the substitution map agrees with env. -/
theorem AlgebraicConstraint.substituteAll_eval
    (c : AlgebraicConstraint p)
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h : ∀ x v, m[x]? = some v → env x = v) :
    (c.substituteAll m).eval env = c.eval env := by
  cases c with
  | affine e => exact AffineExpression.substituteAll_eval e m env h
  | general e => exact Expression.substituteAll_eval e m env h

/-- If a constraint evaluates to zero under `env` and `solve?` succeeds,
    then `env` assigns the solved variable to the computed value. -/
theorem AlgebraicConstraint.solve?_sound {p : ℕ} [Fact (Nat.Prime p)]
    (c : AlgebraicConstraint p) (a : Assignment (p := p))
    (env : String → ZMod p)
    (h_solve : c.solve? = some a) (h_zero : c.eval env = 0) :
    env a.var = a.value := by
  cases c with
  | general e => simp [solve?] at h_solve
  | affine e =>
    simp only [solve?] at h_solve
    match h_list : e.affine.toList with
    | [] => simp [h_list] at h_solve
    | [(x, coeff)] =>
      simp only [h_list] at h_solve
      split at h_solve
      · contradiction
      · rename_i hc
        have ha := Option.some.inj h_solve
        rw [eval, AffineExpression.eval_eq_offset_add_sum] at h_zero
        simp [h_list] at h_zero
        -- h_zero : e.offset + coeff * env x = 0
        -- Goal: env a.var = a.value, i.e. env x = -coeff⁻¹ * e.offset
        have hci : coeff ≠ 0 := hc
        have key : env x = -coeff⁻¹ * e.offset := by
          have h1 : coeff * env x = -e.offset := by
            have := h_zero -- e.offset + coeff * env x = 0
            have : coeff * env x = -(e.offset) := by
              calc coeff * env x = 0 - e.offset := by rw [← this]; ring
              _ = -e.offset := by ring
            exact this
          rw [show env x = coeff⁻¹ * (coeff * env x) from by
            rw [← mul_assoc, inv_mul_cancel₀ hci, one_mul]]
          rw [h1]; ring
        rw [← ha]; simp [key]
    | _ :: _ :: _ => simp [h_list] at h_solve
