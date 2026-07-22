import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold

set_option autoImplicit false

/-! # Dense one-hot annihilation (impl-only)

Dense `VarId` definitions for the one-hot-annihilation pass: the recogniser chain
(`affineCloser`/`readCloser`/`hasProd`/`deadFromCloser`/`deadVars`) and the append transform. The
pass appends `x = 0` for every one-hot-annihilated variable `x`, read off the closer constraints.
It is **fact-free**. The `DensePassCorrect` proof and the pass wiring live in
`OneHotAnnihilateProof.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense recognizers -/

/-- Recognize an affine "closer" factor: `−1 + Σxᵢ` or `1 − Σxᵢ` with all unit coefficients (a
    one-hot indicator's complement). -/
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

/-- Does the system contain a product constraint `v * x` (in either operand order)? -/
def denseHasProd (d : DenseConstraintSystem p) (v x : VarId) : Bool :=
  d.algebraicConstraints.any
    (fun c => c == .mul (.var v) (.var x) || c == .mul (.var x) (.var v))

/-- If `c` is a closer applied to `x` and every one-hot term of the closer has a recorded product
    with `x`, `x` is dead (one-hot-annihilated). -/
def denseDeadFromCloser (d : DenseConstraintSystem p) (c : DenseExpr p) : Option VarId :=
  match denseReadCloser c with
  | some (x, la) => if la.terms.all (fun t => denseHasProd d t.1 x) then some x else none
  | none => none

/-- All one-hot dead variables in the system. -/
def denseDeadVars (d : DenseConstraintSystem p) : List VarId :=
  d.algebraicConstraints.filterMap (denseDeadFromCloser d)

/-! ## The dense transform -/

/-- The dense transform: append `x = 0` for every one-hot-annihilated dense variable. -/
def denseOneHotAnnihilateF (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { d with algebraicConstraints :=
      d.algebraicConstraints ++ (denseDeadVars d).map (fun i => DenseExpr.var i) }

end ApcOptimizer.Dense
