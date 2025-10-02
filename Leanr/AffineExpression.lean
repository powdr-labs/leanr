import Mathlib.Data.ZMod.Basic
import Init.Data.ToString.Basic

import Leanr.Expression

structure AffineExpression (p : ℕ) where
  offset : ZMod p
  affine : Std.TreeMap String (ZMod p)

-- TODO could add a Prop item saying taht coefficients are never zero.

def AffineExpression.toConstant? {p : ℕ} (e : AffineExpression p) : Option (ZMod p) :=
  if e.affine.isEmpty then
    some e.offset
  else
    none

instance {p} : Add (AffineExpression p) where
  add x y := {
    offset := x.offset + y.offset,
    affine := (x.affine.mergeWith (fun _ v1 v2 => (v1 + v2)) y.affine).filter (fun _ v => v ≠ 0),
  }

def mul_by_number {p : ℕ} (e : AffineExpression p) (n : ZMod p) : AffineExpression p :=
  {
    offset := n * e.offset,
    affine := (e.affine.map (fun _ v => n * v)).filter (fun _ v => v ≠ 0),
  }

def mul? {p : ℕ} (x y : AffineExpression p) : Option (AffineExpression p) :=
  match (x.toConstant?, y.toConstant?) with
    | (some n1, _) => some (mul_by_number y n1)
    | (_, some n2) => some (mul_by_number x n2)
    | (none, none) => none

def AffineExpression.ofExpression? {p : ℕ} : Expression p → Option (AffineExpression p)
  | .const n => some { offset := n, affine := Std.TreeMap.empty }
  | .var x => some { offset := 0, affine := Std.TreeMap.empty.insert x 1 }
  | .add e1 e2 => match (ofExpression? e1, ofExpression? e2) with
      | (some v1, some v2) => some (v1 + v2)
      | _ => none
  | .mul e1 e2 => match (ofExpression? e1, ofExpression? e2) with
      | (some v1, some v2) => mul? v1 v2
      | _ => none

def AffineExpression.eval {p : ℕ} (e : AffineExpression p) (env : String → ZMod p) : ZMod p :=
  e.offset +
  e.affine.foldl (fun acc k v => acc + v * env k) 0

--- If an expression can be converted to an affine expression, then their evaluations are the same.
theorem ofExpression_correct (p : ℕ) (e : Expression p) (ae : AffineExpression p) :
  some ae = AffineExpression.ofExpression? e
  → ae.eval = e.eval := by sorry

def AffineExpression.substitute {p : ℕ}
  (e : AffineExpression p)
  (x : String)
  (v : ZMod p) : AffineExpression p :=
  {
    offset := e.offset + e.affine.getD x 0 * v,
    affine := e.affine.erase x,
  }

def AffineExpression.toStr {p : ℕ} : AffineExpression p → String
  | { offset, affine } =>
    let parts : List String :=
      (if offset ≠ 0 then [toString offset.val] else []) ++
      (affine.toList.map (fun (k, v) => if v = 1 then s!"{k}" else s!"{v.val} * {k}"))
    if parts.isEmpty then "0" else String.intercalate " + " parts

instance {p} : ToString (AffineExpression p) where
  toString := fun e => e.toStr
