import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense monic scaling of constraint factors (Task 3 — impl)

Dense, `VarId`-native transliteration of the reference `MonicScale` pass's *runtime* definitions
(`monicScaleAffine`, `monicScale`, `ConstraintSystem.mapConstraints`, and the pass's computed
output). This file is **impl-only**: no theorem/lemma from the spec file is ported
(`monicScaleAffine_eval`, `monicScaleAffine_unit`, `monicScaleAffine_vars`, `monicScale_eval`,
`monicScale_unit`, `monicScale_zero_iff`, `monicScale_vars`, and the
`ConstraintSystem.mapConstraintsIff_correct`-built `PassCorrect` term are all proof-side, the
prover's job), and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here.

The scheduled pass is `monicScalePass.withFacts` — `VerifiedPass.withFacts` (`FactPass.lean`) just
discards the `facts` argument (`fun cs bs _ => f cs bs`), and `monicScalePass` itself never
consults `bs` either, so the pass is fully fact-free and `bs`-free. The dense transform below is
correspondingly a plain `DenseConstraintSystem p → DenseConstraintSystem p`; the prover wraps it
with `DenseVerifiedPassW.of` under a `fun _ _ d => denseMonicScaleF d` that ignores its
`bs`/`facts` arguments, mirroring the `.withFacts` discard exactly.

Soundness of the scaling is field-free (works over any commutative ring, unconditional in `p`):
each scaling carries a *checked* unit certificate (`k * k⁻¹ = 1`, with `ZMod p`'s junk `Inv` only
ever *proposed* and then verified before use), matching the reference's gate `k * k⁻¹ = 1 ∧ k ≠ 1`
exactly — no `PrimeWitness` needed, none used.

## Reuse map (not re-derived)

* `denseLinearize`/`DenseLinExpr` (`Dense/Affine.lean`) are the dense `linearize`/`LinExpr` this
  pass's affine view of a product factor is built from; `DenseLinExpr.scale`/`.toExpr` are its
  `LinExpr.scale`/`.toExpr`.
* `DenseLinExpr.norm` (`Dense/Normalize.lean`) is the dense `LinExpr.norm` — merge like terms, drop
  zero-coefficient ones — this pass reads the leading term's coefficient from.

`ConstraintSystem.mapConstraints` (touching only `algebraicConstraints`, unlike `ExprOps.lean`'s
`mapExpr`, which also rewrites bus multiplicities/payloads) has no existing dense analogue, so
`DenseConstraintSystem.mapConstraints` is transliterated locally here — exactly where the reference
defines its own `mapConstraints`, not in the shared `Rewrite.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Scaling with a unit certificate -/

/-- Scale an affine dense expression to monic form. Returns `(e', u, v)` with the intended
    invariants `e'.eval denv = u * e.eval denv` and `u * v = 1`; `(e, 1, 1)` when not applicable.
    Mirrors `monicScaleAffine`. -/
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
    certificate. Mirrors `monicScale`. -/
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

/-- Rewrite only the algebraic constraints; bus interactions untouched. Mirrors
    `ConstraintSystem.mapConstraints`. -/
def DenseConstraintSystem.mapConstraints (d : DenseConstraintSystem p)
    (g : DenseExpr p → DenseExpr p) : DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map g }

/-! ## The pass -/

/-- The monic-scaling pass's computed output: canonicalize every constraint's affine factors to
    monic form. Mirrors `monicScalePass`'s `.out` (dropping its `PassCorrect` term). -/
def denseMonicScaleF (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.mapConstraints (fun c => (denseMonicScale c).1)

end ApcOptimizer.Dense
