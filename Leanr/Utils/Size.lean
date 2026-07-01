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
circuit: `originalSize / optimizedSize`, as a `ℚ` so that "no change" is exactly `1`.
-/

set_option autoImplicit false

variable {p : ℕ}

/-! ## Collecting variables -/

/-- All variable names occurring in an expression (with multiplicity / duplicates). -/
def Expression.vars : Expression p → List String
  | .const _ => []
  | .var x => [x]
  | .add a b => a.vars ++ b.vars
  | .mul a b => a.vars ++ b.vars

/-- All variable names occurring in a bus interaction (multiplicity and payload). -/
def BusInteraction.vars (bi : BusInteraction (Expression p)) : List String :=
  bi.multiplicity.vars ++ bi.payload.flatMap Expression.vars

/-- The distinct variables of a constraint system, across constraints and bus interactions. -/
def ConstraintSystem.variables (cs : ConstraintSystem p) : List String :=
  (cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars).dedup

/-! ## Size and effectiveness -/

/-- The circuit size: the number of distinct variables. -/
def ConstraintSystem.size (cs : ConstraintSystem p) : Nat := cs.variables.length

/-- How much an optimizer shrinks a given circuit, as the factor `originalSize / optimizedSize`.
    Equals `1` when the size is unchanged; larger is better. Yields `0` if the optimized system
    has no variables (Lean's convention `x / 0 = 0`). -/
def effectiveness (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p)
    (cs : ConstraintSystem p) (bs : BusSemantics p) : ℚ :=
  (cs.size : ℚ) / ((optimizer cs bs).size : ℚ)
