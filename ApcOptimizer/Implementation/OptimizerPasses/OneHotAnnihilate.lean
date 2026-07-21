import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold

set_option autoImplicit false

/-! # Dense one-hot annihilation (Task 3, impl-only)

Dense, `VarId`-native transliteration of the *runtime* content of
`OldVariableBased/OneHotAnnihilate.lean`: the recogniser chain
(`affineCloser`/`readCloser`/`hasProd`/`deadFromCloser`/`deadVars`) and the append transform. The
pass appends `x = 0` for every one-hot-annihilated variable `x`, read off the closer constraints.
It is **fact-free**. The native `DensePassCorrect` proof and the pass wiring live in
`OneHotAnnihilateProof.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense recognizers -/

/-- Dense affine-closer recognizer (see `OneHotAnnihilate.affineCloser`). -/
def denseAffineCloser (a : DenseExpr p) : Option (DenseLinExpr p) :=
  match denseLinearize a with
  | some la =>
      if ((la.const = -1 ∧ la.terms.all (fun t => t.2 == 1)) ∨
          (la.const = 1 ∧ la.terms.all (fun t => t.2 == -1))) ∧ la.terms ≠ [] then some la else none
  | none => none

/-- Dense closer recognizer (see `OneHotAnnihilate.readCloser`). -/
def denseReadCloser (c : DenseExpr p) : Option (VarId × DenseLinExpr p) :=
  match c with
  | .mul a (.var i) => (denseAffineCloser a).map (fun la => (i, la))
  | _ => none

/-- Dense `hasProd` (see `OneHotAnnihilate.hasProd`). -/
def denseHasProd (d : DenseConstraintSystem p) (v x : VarId) : Bool :=
  d.algebraicConstraints.any
    (fun c => c == .mul (.var v) (.var x) || c == .mul (.var x) (.var v))

/-- Dense dead-variable-from-closer recognizer (see `OneHotAnnihilate.deadFromCloser`). -/
def denseDeadFromCloser (d : DenseConstraintSystem p) (c : DenseExpr p) : Option VarId :=
  match denseReadCloser c with
  | some (x, la) => if la.terms.all (fun t => denseHasProd d t.1 x) then some x else none
  | none => none

/-- Dense one-hot dead variables (see `OneHotAnnihilate.deadVars`). -/
def denseDeadVars (d : DenseConstraintSystem p) : List VarId :=
  d.algebraicConstraints.filterMap (denseDeadFromCloser d)

/-! ## The dense transform -/

/-- The dense transform: append `x = 0` for every one-hot-annihilated dense variable. Mirrors the
    transform inside `OneHotAnnihilate.oneHotAnnihilatePass`. -/
def denseOneHotAnnihilateF (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { d with algebraicConstraints :=
      d.algebraicConstraints ++ (denseDeadVars d).map (fun i => DenseExpr.var i) }

end ApcOptimizer.Dense
