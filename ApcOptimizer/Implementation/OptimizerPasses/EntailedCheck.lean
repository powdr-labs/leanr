import ApcOptimizer.Implementation.OptimizerPasses.Rewrite

set_option autoImplicit false

/-! # Entailed-check rewriting: the generic transform

Several passes share one shape: recognize a stateless check whose acceptance is exactly the
vanishing of an entailed algebraic constraint, append those constraints, and drop the recognized
checks. `denseCheckRewriteF` is that transform over a recognizer list; the correctness skeleton
and the pass builders (`DenseVerifiedPassW.ofCheckRules`, `DenseVerifiedPassW.ofAddConstraints`)
live in `Proofs/EntailedCheck.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The recognizers' finds, grouped: recognizer `k` runs on the interactions unmatched by the
    recognizers before it, and its constraints are listed after all of recognizer `k−1`'s — the
    order sequential per-recognizer passes would produce. -/
def denseGroupEmit (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  match recs with
  | [] => []
  | r :: rest => bis.filterMap r ++ denseGroupEmit rest (bis.filter (fun bi => (r bi).isNone))

/-- Append every recognized check's entailed constraint (grouped per recognizer), then drop the
    recognized checks. -/
def denseCheckRewriteF (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  ({ d with algebraicConstraints :=
      d.algebraicConstraints ++ denseGroupEmit recs d.busInteractions }
    : DenseConstraintSystem p).filterBus (fun bi => recs.all (fun r => (r bi).isNone))

end ApcOptimizer.Dense
