import ApcOptimizer.Implementation.OptimizerPasses.TrivialConstraint

set_option autoImplicit false

/-! # Zero-multiplicity bus-interaction removal

Drops bus interactions whose multiplicity folds to the literal constant `0`. Such an interaction
sends nothing, so removing it is equivalence- and invariant-preserving via the proven
`filterBus_correct` — and, crucially, it is sound for *arbitrary* bus semantics because the dropped
interaction's `violatesConstraint` obligation (`multiplicity ≠ 0 → …`) is vacuous. (This is the only
spec-safe form of bus removal: cancelling opposite-sign pairs would discard real obligations.)

Its payoff appears in the cascade: once a selector is substituted to `0`, the interactions it gated
have identically-`0` multiplicity, and dropping them removes the last occurrences of the auxiliary
variables that lived only in their payloads. Field-free (identity only in the degenerate `ZMod 1`,
see the pass docstring). -/

variable {p : ℕ}

/-- The zero-multiplicity bus-removal pass: drop every bus interaction whose multiplicity folds to
    `0`. Correct via `filterBus_correct`, discharging the multiplicity-is-zero obligation through
    `fold_eval` and `isConstZero_sound`. -/
def zeroMultBusDropPass : VerifiedPass p := fun cs bs =>
  if hp1 : (1 : ZMod p) = 0 then ⟨cs, [], PassCorrect.refl cs bs⟩
  else
    ⟨cs.filterBus (fun bi => !bi.multiplicity.fold.isConstZero), [],
     cs.filterBus_correct bs (fun bi => !bi.multiplicity.fold.isConstZero) hp1 (by
       intro bi _ hkf env
       have hz : bi.multiplicity.fold.isConstZero = true := by simpa using hkf
       show bi.multiplicity.eval env = 0
       rw [← bi.multiplicity.fold_eval env]
       exact bi.multiplicity.fold.isConstZero_sound hz env)⟩
