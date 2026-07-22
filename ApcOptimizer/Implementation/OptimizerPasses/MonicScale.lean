import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense monic scaling of constraint factors

Impl-only: canonicalizes every constraint's affine factors to monic form (`denseMonicScaleAffine`,
`denseMonicScale`, transform `denseMonicScaleF`); correctness in `Proofs/MonicScale.lean`. Soundness
is field-free — each scaling carries a checked unit certificate (`k * k⁻¹ = 1`, `ZMod p`'s junk
`Inv` verified before use), so no `PrimeWitness` is needed. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Scale an affine dense expression to monic form. Returns `(e', u, v)` with invariants
    `e'.eval denv = u * e.eval denv` and `u * v = 1`; `(e, 1, 1)` when not applicable. -/
def denseMonicScaleAffine (e : DenseExpr p) : DenseExpr p × ZMod p × ZMod p :=
  match denseLinearize e with
  | none => (e, 1, 1)
  | some l =>
    match l.norm.terms with
    | (_, k) :: _ =>
        if k * k⁻¹ = 1 ∧ k ≠ 1 then ((l.norm.scale k⁻¹).toExpr, k⁻¹, k)
        else (e, 1, 1)
    | [] => (e, 1, 1)

/-- Scale the affine factors of a product tree to monic form, with the accumulated unit
    certificate. -/
def denseMonicScale : DenseExpr p → DenseExpr p × ZMod p × ZMod p
  | .mul a b =>
      match denseLinearize (.mul a b) with
      | some _ => denseMonicScaleAffine (.mul a b)
      | none =>
          (.mul (denseMonicScale a).1 (denseMonicScale b).1,
           (denseMonicScale a).2.1 * (denseMonicScale b).2.1,
           (denseMonicScale a).2.2 * (denseMonicScale b).2.2)
  | e => denseMonicScaleAffine e

/-- Rewrite only the algebraic constraints; bus interactions untouched. -/
def DenseConstraintSystem.mapConstraints (d : DenseConstraintSystem p)
    (g : DenseExpr p → DenseExpr p) : DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map g }

/-- Rewrites every constraint's affine factors to monic form (leading coefficient scaled to `1`) —
    e.g. `3x − 6 = 0` becomes `x − 2 = 0` — which preserves each constraint's zero set. -/
def denseMonicScaleF (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.mapConstraints (fun c => (denseMonicScale c).1)

end ApcOptimizer.Dense
