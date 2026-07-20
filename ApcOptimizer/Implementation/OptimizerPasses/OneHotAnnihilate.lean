import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.OneHotAnnihilate

set_option autoImplicit false

/-! # Dense one-hot annihilation (Task 3, impl-only)

Dense, `VarId`-native transliteration of the *runtime* content of
`OldVariableBased/OneHotAnnihilate.lean`: the recogniser chain
(`affineCloser`/`readCloser`/`hasProd`/`deadFromCloser`/`deadVars`) and the append transform. The
pass appends `x = 0` for every one-hot-annihilated variable `x`, read off the closer constraints.
It is **fact-free**. The native `DensePassCorrect` proof and the pass wiring live in
`OneHotAnnihilateProof.lean`.

This file still carries the shared decode helpers (`decodeExpr_beq`, `list_any_congr`,
`list_all_congr`, `decodeCS_append_constraints`) consumed by the remaining commutation-era proofs;
they are removed in the batch-1 deletion sweep once their last consumer converts. -/

namespace ApcOptimizer.Dense

open OneHotAnnihilate

variable {p : ℕ}

/-! ## A `==` correspondence and small `any`/`all` congruences (shared decode helpers) -/

/-- **`==` on covered dense expressions commutes with decode.** `resolve` is injective on valid ids,
    so `decodeExpr` is injective on covered values; hence structural equality of the decodes matches
    structural equality of the dense values. -/
theorem VarRegistry.decodeExpr_beq (reg : VarRegistry) {a b : DenseExpr p}
    (ha : a.CoveredBy reg) (hb : b.CoveredBy reg) :
    (reg.decodeExpr a == reg.decodeExpr b) = (a == b) := by
  show decide (reg.decodeExpr a = reg.decodeExpr b) = decide (a = b)
  exact decide_eq_decide.mpr
    ⟨fun he => reg.decodeExpr_inj ha hb he, fun he => congrArg reg.decodeExpr he⟩

/-- `any` respects a pointwise-equal predicate on the list's members. -/
theorem list_any_congr {α : Type _} {l : List α} {f g : α → Bool}
    (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.any_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `all` respects a pointwise-equal predicate on the list's members. -/
theorem list_all_congr {α : Type _} {l : List α} {f g : α → Bool}
    (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.all_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Decoding distributes over appending derived dense constraints. -/
theorem VarRegistry.decodeCS_append_constraints (reg : VarRegistry) (d : DenseConstraintSystem p)
    (dnew : List (DenseExpr p)) :
    reg.decodeCS { d with algebraicConstraints := d.algebraicConstraints ++ dnew }
      = { reg.decodeCS d with algebraicConstraints :=
            (reg.decodeCS d).algebraicConstraints ++ dnew.map reg.decodeExpr } := by
  simp only [VarRegistry.decodeCS, List.map_append]

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
