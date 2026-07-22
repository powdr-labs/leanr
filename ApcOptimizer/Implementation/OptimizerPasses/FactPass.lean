import ApcOptimizer.Implementation.OptimizerPasses.Basic
import ApcOptimizer.Implementation.BusFacts
import ApcOptimizer.Utils.Size
import Mathlib.Data.Prod.Lex

set_option autoImplicit false

/-! # Fact-aware verified passes

A `VerifiedPassW` is a `VerifiedPass` that may additionally consult proven `BusFacts` about the
bus semantics it is given (see `ApcOptimizer/Implementation/BusFacts.lean`). The correctness obligation is unchanged —
`PassCorrect` against the *semantics* — the facts only widen what a pass can decide, never what
it may claim: with `BusFacts.trivial` every fact-aware pass degrades to fact-free behavior. -/

variable {p : ℕ}

/-- A proof-carrying pass that may consult proven facts about the bus semantics. -/
abbrev VerifiedPassW (p : ℕ) :=
  (cs : ConstraintSystem p) → (bs : BusSemantics p) → (facts : BusFacts p bs) → PassResult cs bs

deriving instance DecidableEq for BusInteraction

/-! ## The lexicographic size key

The lexicographic size key `(#distinct variables, #bus interactions, #algebraic constraints)`,
with variables most significant — exactly the optimizer's effectiveness priority. The
distinct-variable count uses a `HashSet` (not `ConstraintSystem.size`'s quadratic `dedup`) so the
per-cycle measure stays cheap on large circuits. -/

/-- Number of distinct variables, computed with a `HashSet` (linear, unlike the audited
    `ConstraintSystem.size`, which uses `List.dedup`). Same value; used only for the loop measure. -/
def ConstraintSystem.varCount (cs : ConstraintSystem p) : Nat :=
  ((cs.algebraicConstraints.flatMap Expression.vars ++
      cs.busInteractions.flatMap BusInteraction.vars).foldl
        (init := (∅ : Std.HashSet Variable)) (·.insert ·)).size

/-- The lexicographic size key `(#distinct vars, #bus interactions, #constraints)` — variables most
    significant, matching the effectiveness priority. Well-founded under `<`, so it can serve as a
    termination measure; decreasing it is exactly "the circuit got strictly smaller". -/
def ConstraintSystem.sizeKey (cs : ConstraintSystem p) : Nat ×ₗ Nat ×ₗ Nat :=
  toLex (cs.varCount, toLex (cs.busInteractions.length, cs.algebraicConstraints.length))

/-! ## Degree guarding

`optimizerRespectsDegreeBound` is enforced compositionally with **zero** per-pass proof burden:
every pass is wrapped in a checked guard that falls back to its (unchanged) input if the
output would exceed the degree bound. `RespectsDeg` propagates through composition and iteration. -/

/-- A pass never pushes a within-bound system past the degree bound `b`. -/
def RespectsDeg (b : DegreeBound) (f : VerifiedPassW p) : Prop :=
  ∀ (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs),
    cs.withinDegree b → (f cs bs facts).out.withinDegree b
