import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold

set_option autoImplicit false

/-! # Dense one-hot annihilation

Impl-only: the recogniser chain (`denseAffineCloser`/`denseReadCloser`/`denseHasProd`/
`denseDeadFromCloser`/`denseDeadVars`) and the append transform. Correctness in
`Proofs/OneHotAnnihilate.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- An affine "closer" factor: `−1 + Σxᵢ` or `1 − Σxᵢ` with all unit coefficients (a one-hot
    indicator's complement). -/
def denseAffineCloser (a : DenseExpr p) : Option (DenseLinExpr p) :=
  match denseLinearize a with
  | some la =>
      if ((la.const = -1 ∧ la.terms.all (fun t => t.2 == 1)) ∨
          (la.const = 1 ∧ la.terms.all (fun t => t.2 == -1))) ∧ la.terms ≠ [] then some la else none
  | none => none

/-- Recognize a constraint `closer · x` as a one-hot closer applied to `x`. -/
def denseReadCloser (c : DenseExpr p) : Option (VarId × DenseLinExpr p) :=
  match c with
  | .mul a (.var i) => (denseAffineCloser a).map (fun la => (i, la))
  | _ => none

/-- The set of variable pairs `(a, b)` such that `a * b` is a present constraint. Built once so the
    product test is a hash lookup, not a per-query scan of every constraint. -/
def denseProdSet (cs : List (DenseExpr p)) : Std.HashSet (VarId × VarId) :=
  cs.foldl (fun s c =>
    match c with
    | .mul (.var a) (.var b) => s.insert (a, b)
    | _ => s) ∅

/-- Does the system contain a product constraint `v * x` (in either operand order)? Reads the
    precomputed `denseProdSet`. -/
def denseHasProdS (s : Std.HashSet (VarId × VarId)) (v x : VarId) : Bool :=
  s.contains (v, x) || s.contains (x, v)

/-- If `c` is a closer applied to `x` and every one-hot term of the closer has a recorded product
    with `x` (via the precomputed product set `s`), `x` is dead (one-hot-annihilated). -/
def denseDeadFromCloser (s : Std.HashSet (VarId × VarId)) (c : DenseExpr p) : Option VarId :=
  match denseReadCloser c with
  | some (x, la) => if la.terms.all (fun t => denseHasProdS s t.1 x) then some x else none
  | none => none

/-- All one-hot dead variables in the system. -/
def denseDeadVars (d : DenseConstraintSystem p) : List VarId :=
  let s := denseProdSet d.algebraicConstraints
  d.algebraicConstraints.filterMap (denseDeadFromCloser s)

end ApcOptimizer.Dense
