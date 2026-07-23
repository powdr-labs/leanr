import ApcOptimizer.Implementation.OptimizerPasses.Pass

set_option autoImplicit false

/-! # Dense constraint dedup up to commutativity (runtime defs; proof in `Proofs/CommDedup.lean`)

`List.dedup`-based `denseDedupPass` compares constraints structurally, so `(x − 1)·x = 0` and
`x·(x − 1) = 0` — the same booleanity check with its product factors swapped — both survive. This
pass drops a constraint when an earlier-kept one matches it up to commutativity of `+`/`*`
(`denseCommEq`), collapsing such twins to one. Bus interactions are untouched. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Structural equality of dense expressions up to commutativity of `+`/`*`: the trees agree after
    freely swapping the operands of matched `add`/`mul` nodes. Sound (`denseCommEq_eval`) but
    deliberately incomplete (no associativity reshaping) — a `false` only forfeits a dedup. -/
def denseCommEq : DenseExpr p → DenseExpr p → Bool
  | .const m, .const n => decide (m = n)
  | .var i, .var j => decide (i = j)
  | .add a b, .add c d =>
      (denseCommEq a c && denseCommEq b d) || (denseCommEq a d && denseCommEq b c)
  | .mul a b, .mul c d =>
      (denseCommEq a c && denseCommEq b d) || (denseCommEq a d && denseCommEq b c)
  | _, _ => false

/-- Keep the first constraint of each commutativity class: drop `c` if some already-kept `seen`
    entry is `denseCommEq` to it. -/
def denseCommDedupGo (seen : List (DenseExpr p)) :
    List (DenseExpr p) → List (DenseExpr p)
  | [] => []
  | c :: rest =>
    if seen.any (fun s => denseCommEq s c) then denseCommDedupGo seen rest
    else c :: denseCommDedupGo (c :: seen) rest

/-- Drops algebraic constraints equal to an earlier one up to commutativity of `+`/`*` — e.g. the
    twin booleanity checks `(x − 1)·x = 0` and `x·(x − 1) = 0` collapse to one. Bus untouched. -/
def DenseConstraintSystem.commDedup (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { d with algebraicConstraints := denseCommDedupGo [] d.algebraicConstraints }

end ApcOptimizer.Dense
