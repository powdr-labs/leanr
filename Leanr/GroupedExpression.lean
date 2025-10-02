import Mathlib.Data.ZMod.Basic
import Init.Data.ToString.Basic

import Leanr.Expression

structure GroupedExpression (p : ℕ) where
  offset : ZMod p
  affine : Std.TreeMap String (ZMod p)
  quadratic : List (GroupedExpression p × GroupedExpression p)

def GroupedExpression.toConstant? {p : ℕ} (e : GroupedExpression p) : Option (ZMod p) :=
  if e.affine.isEmpty && e.quadratic.isEmpty then
    some e.offset
  else
    none

instance {p} : Add (GroupedExpression p) where
  add x y := {
    offset := x.offset + y.offset,
    affine := (x.affine.mergeWith (fun _ v1 v2 => (v1 + v2)) y.affine).filter (fun _ v => v ≠ 0),
    quadratic := x.quadratic ++ y.quadratic}

partial def mul_by_number {p : ℕ} (e : GroupedExpression p) (n : ZMod p) : GroupedExpression p :=
  { offset := n * e.offset,
    affine := (e.affine.map (fun _ v => n * v)).filter (fun _ v => v ≠ 0),
    quadratic := e.quadratic.map (fun (e1, e2) => (mul_by_number e1 n, e2)) }

instance {p} : Mul (GroupedExpression p) where
  mul x y := match (x.toConstant?, y.toConstant?) with
    | (some n1, some n2) => { offset := n1 * n2, affine := default, quadratic := [] }
    | (some n1, none) => mul_by_number y n1
    | (none, some n2) => mul_by_number x n2
    | (none, none) => {
        offset := default,
        affine := default,
        quadratic := [(x, y)]}

def GroupedExpression.ofExpression {p : ℕ} : Expression p → GroupedExpression p
  | .const n => { offset := n, affine := Std.TreeMap.empty, quadratic := [] }
  | .var x => { offset := 0, affine := Std.TreeMap.empty.insert x 1, quadratic := [] }
  | .add e1 e2 => (ofExpression e1) + (ofExpression e2)
  | .mul e1 e2 => (ofExpression e1) * (ofExpression e2)


def eval_sum {p : ℕ} (l : List (String × ZMod p)) (env : String → ZMod p) : ZMod p :=
  l.foldl (fun acc (k, v) => acc + v * env k) 0

-- TODO show termination
partial def GroupedExpression.eval {p : ℕ} (e : GroupedExpression p) (env : String → ZMod p) : ZMod p :=
  e.offset +
  e.affine.foldl (fun acc k v => acc + v * env k) 0 +
  e.quadratic.foldl (fun acc (e1, e2) => acc + e1.eval env * e2.eval env) 0


theorem ofExpression_correct (p : ℕ) (e : Expression p) (env : String → ZMod p) :
  e.eval env = (GroupedExpression.ofExpression e).eval env := by sorry

partial def GroupedExpression.substitute {p : ℕ}
  (e : GroupedExpression p)
  (x : String)
  (v : ZMod p) : GroupedExpression p :=
  let affine := {
    offset := e.offset + e.affine.getD x 0 * v,
    affine := e.affine.erase x,
    quadratic := default }
  e.quadratic.foldl
    (fun acc (e1, e2) => acc + (e1.substitute x v) * (e2.substitute x v))
    affine

theorem substitute_correct {p : ℕ}
  (e : GroupedExpression p)
  (x : String)
  (v : ZMod p)
  (env : String → ZMod p) :
  env x = v → e.eval env = (e.substitute x v).eval env := by sorry

-- TODO show termination
partial def GroupedExpression.toStr {p : ℕ} : GroupedExpression p → String
  | { offset, affine, quadratic } =>
    let parts : List String :=
      (if offset ≠ 0 then [toString offset.val] else []) ++
      (affine.toList.map (fun (k, v) => if v = 1 then s!"{k}" else s!"{v.val} * {k}")) ++
      (quadratic.map (fun (e1, e2) => s!"({toStr e1}) * ({toStr e2})"))
    if parts.isEmpty then "0" else String.intercalate " + " parts

instance {p} : ToString (GroupedExpression p) where
  toString := fun e => e.toStr
