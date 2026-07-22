import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense monic scaling of constraint factors

Canonicalizes every constraint's affine factors to monic form (`denseMonicScaleAffine`,
`denseMonicScale`, `DenseConstraintSystem.mapConstraints`, and the pass's computed output
`denseMonicScaleF`). This file is **impl-only**: it carries no `DensePassCorrect`/
`DenseVerifiedPassW` wrapper here.

The scheduled pass is fully fact-free and `bs`-free (it never consults either), so the dense
transform below is a plain `DenseConstraintSystem p → DenseConstraintSystem p`; the prover wraps it
with `DenseVerifiedPassW.of` under a `fun _ _ d => denseMonicScaleF d` that ignores its
`bs`/`facts` arguments.

Soundness of the scaling is field-free (works over any commutative ring, unconditional in `p`):
each scaling carries a *checked* unit certificate (`k * k⁻¹ = 1`, with `ZMod p`'s junk `Inv` only
ever *proposed* and then verified before use), gated by `k * k⁻¹ = 1 ∧ k ≠ 1` — no `PrimeWitness`
needed, none used.

## Notes

* `denseLinearize`/`DenseLinExpr` (`Dense/Affine.lean`) are what this pass's affine view of a
  product factor is built from; `DenseLinExpr.scale`/`.toExpr` scale and rebuild it.
* `DenseLinExpr.norm` (`Dense/Normalize.lean`) merges like terms and drops zero-coefficient ones —
  this pass reads the leading term's coefficient from the normalized form.

`DenseConstraintSystem.mapConstraints` (touching only `algebraicConstraints`, unlike
`ExprOps.lean`'s `mapExpr`, which also rewrites bus multiplicities/payloads) is defined locally
here rather than in the shared `Rewrite.lean`, since this is its only consumer. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Scaling with a unit certificate -/

/-- The core of `denseMonicScaleAffine`, over the already-normalized linear form `n` (taking it
    as an argument evaluates the normalization once for both its uses below). -/
def denseMonicScaleNormed (e : DenseExpr p) (n : DenseLinExpr p) :
    DenseExpr p × ZMod p × ZMod p :=
  match n.terms with
  | (_, k) :: _ =>
      if k * k⁻¹ = 1 ∧ k ≠ 1 then ((n.scale k⁻¹).toExpr, k⁻¹, k)
      else (e, 1, 1)
  | [] => (e, 1, 1)

/-- Scale an affine dense expression to monic form. Returns `(e', u, v)` with the intended
    invariants `e'.eval denv = u * e.eval denv` and `u * v = 1`; `(e, 1, 1)` when not applicable. -/
def denseMonicScaleAffine (e : DenseExpr p) : DenseExpr p × ZMod p × ZMod p :=
  match denseLinearize e with
  | none => (e, 1, 1)
  | some l => denseMonicScaleNormed e l.norm

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

/-! ## The correctness core's runtime shape: constraint-only rewrites -/

/-- Rewrite only the algebraic constraints; bus interactions untouched. -/
def DenseConstraintSystem.mapConstraints (d : DenseConstraintSystem p)
    (g : DenseExpr p → DenseExpr p) : DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map g }

/-! ## The pass -/

/-- The monic-scaling pass's computed output: canonicalize every constraint's affine factors to
    monic form. -/
def denseMonicScaleF (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.mapConstraints (fun c => (denseMonicScale c).1)

end ApcOptimizer.Dense
