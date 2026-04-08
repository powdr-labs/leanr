import Mathlib.Data.ZMod.Basic
import Init.Data.ToString.Basic
import Std.Data.TreeMap.Lemmas
import Std
import Mathlib

import Leanr.Expression

variable {p : ℕ} [Fact (Nat.Prime p)]

structure AffineExpression (p : ℕ) where
  offset : ZMod p
  affine : Std.TreeMap String (ZMod p)
  nonzero : ∀ v : String, (affine[v]?) ≠ some 0 := by simp

def AffineExpression.eval (e : AffineExpression p) (env : String → ZMod p) : ZMod p :=
  e.offset +
  e.affine.foldl (fun acc k v => acc + v * env k) 0

def AffineExpression.const (n : ZMod p) : AffineExpression p :=
  { offset := n, affine := Std.TreeMap.empty }

def AffineExpression.var (x : String) : AffineExpression p :=
  { offset := 0, affine := Std.TreeMap.empty.insert x 1, nonzero := by grind }

def AffineExpression.toConstant? (e : AffineExpression p) : Option (ZMod p) :=
  if e.affine.isEmpty then
    some e.offset
  else
    none

instance {p} : Add (AffineExpression p) where
  add x y := {
    offset := x.offset + y.offset,
    affine := (x.affine.mergeWith (fun _ v1 v2 => (v1 + v2)) y.affine).filter (fun _ v => v ≠ 0),
  }

instance {p} : HMul (ZMod p) (AffineExpression p) (AffineExpression p) where
  hMul n e := {
    offset := n * e.offset,
    affine := (e.affine.map (fun _ v => n * v)).filter (fun _ v => v ≠ 0),
  }

def mul? (x y : AffineExpression p) : Option (AffineExpression p) :=
  match (x.toConstant?, y.toConstant?) with
    | (some n, _) => some (n * y)
    | (_, some n) => some (n * x)
    | (none, none) => none

def AffineExpression.ofExpression? [Fact (Nat.Prime p)] : Expression p → Option (AffineExpression p)
  | .const n => some (.const n)
  | .var x => some (.var x)
  | .add e1 e2 => do ((← ofExpression? e1) + (← ofExpression? e2))
  | .mul e1 e2 => do (mul? (← ofExpression? e1) (← ofExpression? e2))

def AffineExpression.substitute
  (e : AffineExpression p)
  (x : String)
  (v : ZMod p) : AffineExpression p :=
  {
    offset := e.offset + e.affine.getD x 0 * v,
    affine := e.affine.erase x,
    nonzero := by
      intro v'
      rw [Std.TreeMap.getElem?_erase]
      split
      · simp
      · exact e.nonzero v'
  }

/-- Substitute all variables in the map at once. -/
def AffineExpression.substituteAll (e : AffineExpression p) (env : Std.HashMap String (ZMod p)) : AffineExpression p :=
  let (offset, affine) := e.affine.foldl (init := (e.offset, Std.TreeMap.empty (α := String) (β := ZMod p)))
    fun (off, aff) k v =>
      match env[k]? with
      | some val => (off + v * val, aff)
      | none =>
        let aff' := aff.insert k v
        (off, aff')
  { offset := offset, affine := affine.filter (fun _ v => v ≠ 0) }

def AffineExpression.toStr (e : AffineExpression p) : String :=
    let parts : List String :=
      (if e.offset ≠ 0 then [toString e.offset.val] else []) ++
      (e.affine.toList.map (fun (k, v) => if v = 1 then s!"{k}" else s!"{v.val} * {k}"))
    if parts.isEmpty then "0" else String.intercalate " + " parts

instance {p} [Fact (Nat.Prime p)] : ToString (AffineExpression p) where
  toString := fun e => e.toStr
