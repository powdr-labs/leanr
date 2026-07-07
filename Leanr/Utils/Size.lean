import Leanr.Spec
import Mathlib.Data.Rat.Defs

/-!
# Circuit size and optimizer effectiveness

Utilities for *measuring* constraint systems (see `Leanr/Spec.lean`). Not tied to any
particular zkVM.

The **size** of a circuit is its number of distinct variables: every variable name that
appears anywhere — in an algebraic constraint, in a bus interaction's multiplicity, or in a
payload — counted once.

The **effectiveness** of an optimizer on a given input is the factor by which it shrinks the
circuit under some size measure: `measure original / measure optimized`, as a `ℚ` so that "no
change" is exactly `1`. There are three measures, in priority order:

1. **variable effectiveness** (`effectiveness`) — the primary metric, over distinct variables.
2. **bus-interaction effectiveness** (`busInteractionEffectiveness`) — over the number of bus
   interactions (some passes remove interactions without touching the variable count, e.g. PC-
   lookup removal, so this exposes progress the variable metric alone would miss).
3. **algebraic-constraint effectiveness** (`constraintEffectiveness`) — over the number of
   algebraic constraints.

`effectivenessBy` is the shared shape; the three named metrics instantiate it. When trading off
between passes, prefer improvements higher in this list.
-/

set_option autoImplicit false

variable {p : ℕ}

/-! ## Collecting variables -/

/-- All variable names occurring in an expression (with multiplicity / duplicates). -/
def Expression.vars : Expression p → List Variable
  | .const _ => []
  | .var x => [x]
  | .add a b => a.vars ++ b.vars
  | .mul a b => a.vars ++ b.vars

/-- All variable names occurring in a bus interaction (multiplicity and payload). -/
def BusInteraction.vars (bi : BusInteraction (Expression p)) : List Variable :=
  bi.multiplicity.vars ++ bi.payload.flatMap Expression.vars

/-- The distinct variables of a constraint system, across constraints and bus interactions. -/
def ConstraintSystem.variables (cs : ConstraintSystem p) : List Variable :=
  (cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars).dedup

/-! ## Size and effectiveness -/

/-- The circuit size: the number of distinct variables. -/
def ConstraintSystem.size (cs : ConstraintSystem p) : Nat := cs.variables.length

/-- The number of algebraic constraints — a coarser size measure than `size`. -/
def ConstraintSystem.constraintCount (cs : ConstraintSystem p) : Nat :=
  cs.algebraicConstraints.length

/-- The number of bus interactions. -/
def ConstraintSystem.busInteractionCount (cs : ConstraintSystem p) : Nat :=
  cs.busInteractions.length

/-- Number of occurrences of `x` (with multiplicity) across the whole system. Used e.g. to pick
    substitution pivots that minimize expression duplication. -/
def ConstraintSystem.occurrences (cs : ConstraintSystem p) (x : Variable) : Nat :=
  (cs.algebraicConstraints.flatMap Expression.vars
    ++ cs.busInteractions.flatMap BusInteraction.vars).count x

/-- How much an optimizer shrinks a given circuit under a size `measure`, as the factor
    `measure original / measure optimized`. Equals `1` when the measure is unchanged; larger is
    better. Yields `0` if the optimized measure is `0` (Lean's convention `x / 0 = 0`). -/
def effectivenessBy (measure : ConstraintSystem p → Nat)
    (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p)
    (cs : ConstraintSystem p) (bs : BusSemantics p) : ℚ :=
  (measure cs : ℚ) / (measure (optimizer cs bs) : ℚ)

/-- **Variable effectiveness** (primary): the factor by which the optimizer shrinks the distinct
    variable count. -/
def effectiveness (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p)
    (cs : ConstraintSystem p) (bs : BusSemantics p) : ℚ :=
  effectivenessBy ConstraintSystem.size optimizer cs bs

/-- **Bus-interaction effectiveness** (secondary): the factor by which the optimizer shrinks the
    number of bus interactions. -/
def busInteractionEffectiveness
    (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p)
    (cs : ConstraintSystem p) (bs : BusSemantics p) : ℚ :=
  effectivenessBy ConstraintSystem.busInteractionCount optimizer cs bs

/-- **Algebraic-constraint effectiveness** (tertiary): the factor by which the optimizer shrinks
    the number of algebraic constraints. -/
def constraintEffectiveness
    (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p)
    (cs : ConstraintSystem p) (bs : BusSemantics p) : ℚ :=
  effectivenessBy ConstraintSystem.constraintCount optimizer cs bs
