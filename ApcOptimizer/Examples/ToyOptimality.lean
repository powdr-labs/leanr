import ApcOptimizer.Optimizer
import ApcOptimizer.Utils.Dsl
import ApcOptimizer.Utils.Size

/-!
# A worked example: the optimizer's output on a toy block is variable-optimal

The audited theorems (`ApcOptimizer/Optimizer.lean`) prove the optimizer is *correct* — its output
`refines` the input. They say nothing about *optimality*: that no even-smaller correct circuit
exists. This file proves optimality for one concrete toy block, on the primary effectiveness axis
(distinct variables, see `ApcOptimizer/Utils/Size.lean`).

Optimality is a strictly different and harder claim than refinement: refinement is `∀ input,
per output`; optimality is `∀ competing circuit, no smaller correct one exists` — a universally
quantified statement over the whole space of candidate circuits. Two facts make it tractable *here*:

* The block's real traces send **two distinct stateful side-effect states** to the bus. A circuit
  with **zero** variables evaluates every expression to a constant, so it sends a *single* fixed
  state and cannot be a complete replacement. Hence any correct replacement needs `≥ 1` variable
  (`toy_lower_bound`). This argument is field-independent — it only needs `1 ≠ 0`.
* That bound is **achieved**: `toyOptimum` (the input with `x = 1` propagated) is a sound, complete,
  within-degree replacement of size `1` (`toyOptimum_isCorrect`, `toyOptimum_size`).

So `1` is the optimal variable count (`toyOptimum_optimal`). The `#guard`s at the bottom then
witness — at build time, via the compiler, not a banned tactic — that the real optimizer emits
*exactly* `toyOptimum`. (That last equality is machine-*evaluated* rather than kernel-*proved*
because the cleanup fixpoint uses well-founded recursion, which does not reduce definitionally;
`rfl`/`decide` stall on it.)

Nothing here touches the audited surface; it is a standalone demonstration.

Reaching a `≥ k` lower bound for `k ≥ 2` is where the field size would start to matter: over a
large field a single variable already carries a whole field element, so the counting argument
above only ever yields `≥ 1`, and honest `≥ 2` bounds become algebraic-geometry (dimension)
arguments. A tiny field (here `ZMod 2`) is what would let a future `≥ k` toy stay a counting
argument.
-/

set_option autoImplicit false

namespace ApcOptimizer.ToyOptimality

open ApcOptimizer.Spec.Dsl

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The two variables of the toy block; both carry a powdr ID (so the input satisfies the
    completeness precondition that every input variable has one). -/
def x : Variable := { name := "x", powdrId? := some 0 }
def y : Variable := { name := "y", powdrId? := some 1 }

/-- Input block over `ZMod 2`: one constraint `x + 1 = 0` (forcing `x = 1`, since `-1 = 1`), and one
    stateful bus interaction sending `x + y`. -/
def toyInput : ConstraintSystem 2 :=
  { algebraicConstraints := [ .add (.var x) (.const 1) ],
    busInteractions :=
      [ { busId := 7, multiplicity := .const 1, payload := [ .add (.var x) (.var y) ] } ] }

/-- Trivial bus semantics: every bus is stateful, nothing violates or breaks anything, everything
    is admissible. This isolates the argument to the side-effect count. -/
def toyBS : BusSemantics 2 :=
  { isStateful := fun _ => true,
    violatesConstraint := fun _ => false,
    breaksInvariant := fun _ => false,
    admissible := fun _ => True }

def toyBound : DegreeBound := { identities := 1, busInteractions := 1 }

/-- The optimum: `x = 1` propagated into the bus payload, so the constraint and the variable `x`
    are gone. One variable (`y`) remains. -/
def toyOptimum : ConstraintSystem 2 :=
  { algebraicConstraints := [],
    busInteractions :=
      [ { busId := 7, multiplicity := .const 1, payload := [ .add (.const 1) (.var y) ] } ] }

/-- The assignment `x ↦ a`, `y ↦ c`, everything else `0`. -/
def tenv (a c : ZMod 2) : Variable → ZMod 2 :=
  fun v => if v = x then a else if v = y then c else 0

/-! ## The block's two real-trace side-effect states -/

theorem toyInput_sideEffects (c : ZMod 2) :
    toyInput.sideEffects toyBS (tenv 1 c) = [((7, [1 + c]), 1)] := by
  simp [ConstraintSystem.sideEffects, toyInput, toyBS, BusInteraction.eval,
    Expression.eval, tenv, x, y]

theorem tenv_satisfies (c : ZMod 2) : toyInput.satisfies toyBS (tenv 1 c) := by
  refine ⟨?_, ?_⟩
  · intro cc hcc
    simp only [toyInput, List.mem_singleton] at hcc
    subst hcc
    simp only [Expression.eval, tenv, if_pos]
    decide
  · intro bi _ _
    simp [toyBS]

theorem tenv_admissible (c : ZMod 2) : toyInput.admissible toyBS (tenv 1 c) := by
  simp [ConstraintSystem.admissible, toyBS]

/-! ## Lower bound: any complete replacement needs at least one variable -/

/-- A size-`0` circuit sends a fixed side-effect state, independent of the assignment. -/
theorem sideEffects_const_of_size_zero {O : ConstraintSystem 2} (h : O.size = 0)
    (f g : Variable → ZMod 2) : O.sideEffects toyBS f = O.sideEffects toyBS g := by
  apply ConstraintSystem.sideEffects_congr
  intro v hv
  exfalso
  have hmem : v ∈ O.variables := by
    unfold ConstraintSystem.variables
    rw [List.mem_dedup]
    exact hv
  have hnil : O.variables = [] := List.length_eq_zero_iff.mp h
  rw [hnil] at hmem
  simp at hmem

/-- **Lower bound.** Every complete replacement of `toyInput` uses at least one variable, because
    the block demands two distinct stateful side-effect states but a size-`0` circuit offers one. -/
theorem toy_lower_bound (O : ConstraintSystem 2) (ds : Derivations 2)
    (hcomplete : O.isCompleteReplacementOf toyInput toyBS ds) : 1 ≤ O.size := by
  by_contra hlt
  have hzero : O.size = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp hlt)
  have hpow : ∀ v ∈ toyInput.vars, v.powdrId?.isSome := by decide
  have h0 := (hcomplete hpow (tenv 1 0) (tenv_admissible 0) (tenv_satisfies 0)).2.2.2.2
  have h1 := (hcomplete hpow (tenv 1 1) (tenv_admissible 1) (tenv_satisfies 1)).2.2.2.2
  have hconst := sideEffects_const_of_size_zero hzero
    (Derivations.witgen ds (tenv 1 0)) (Derivations.witgen ds (tenv 1 1))
  -- Both input side-effects are equivalent to the (single) output state, hence to each other;
  -- evaluate that equivalence at the message `(7, [1])` for a `1 = 0` contradiction.
  have e0 := h0 ((7, [1]) : BusMessage 2)
  have e1 := h1 ((7, [1]) : BusMessage 2)
  rw [hconst] at e0
  rw [← e1] at e0
  rw [toyInput_sideEffects 0, toyInput_sideEffects 1] at e0
  revert e0
  decide

/-! ## Achievability: `toyOptimum` is a correct replacement of size 1 -/

theorem toyOptimum_size : toyOptimum.size = 1 := by decide

theorem toyOptimum_sideEffects (env : Variable → ZMod 2) :
    toyOptimum.sideEffects toyBS env = [((7, [1 + env y]), 1)] := by
  simp [ConstraintSystem.sideEffects, toyOptimum, toyBS, BusInteraction.eval, Expression.eval]

theorem toyOptimum_isSound : toyOptimum.isSoundReplacementOf toyInput toyBS := by
  refine ⟨?_, ?_⟩
  · intro env _
    refine ⟨fun v => if v = x then 1 else env v, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro cc hcc
        simp only [toyInput, List.mem_singleton] at hcc
        subst hcc
        simp only [Expression.eval, if_pos]
        decide
      · intro bi _ _; simp [toyBS]
    · rw [toyOptimum_sideEffects]
      have hrhs : toyInput.sideEffects toyBS (fun v => if v = x then 1 else env v)
          = [((7, [1 + env y]), 1)] := by
        simp [ConstraintSystem.sideEffects, toyInput, toyBS, BusInteraction.eval,
          Expression.eval, x, y]
      rw [hrhs]
      exact fun _ => rfl
  · intro _ env _ bi hbi _
    simp only [toyOptimum, List.mem_singleton] at hbi
    subst hbi
    simp [toyBS]

theorem toyOptimum_isComplete :
    toyOptimum.isCompleteReplacementOf toyInput toyBS [] := by
  intro _ env _ hsat
  have hx : env x = 1 := by
    have hc0 : (Expression.add (Expression.var x) (Expression.const 1)).eval env = 0 :=
      hsat.1 _ (by simp [toyInput])
    simp only [Expression.eval] at hc0
    have hneg : env x = -1 := by linear_combination hc0
    rw [hneg]; decide
  have hwit : Derivations.witgen ([] : Derivations 2) env = env := by
    funext v; cases hv : v.powdrId? <;> simp [Derivations.witgen, hv, Derivations.methodFor]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hvars : toyOptimum.vars = [y] := by decide
    rw [hvars, List.mem_singleton] at hv
    subst hv
    show y ∈ toyInput.vars
    decide
  · intro d hd; simp at hd
  · rw [hwit]
    exact ⟨fun cc hcc => by simp [toyOptimum] at hcc, fun bi _ _ => by simp [toyBS]⟩
  · rw [hwit]; simp [ConstraintSystem.admissible, toyBS]
  · rw [hwit, toyOptimum_sideEffects]
    have hin : toyInput.sideEffects toyBS env = [((7, [1 + env y]), 1)] := by
      simp [ConstraintSystem.sideEffects, toyInput, toyBS, BusInteraction.eval, Expression.eval, hx]
    rw [hin]
    exact fun _ => rfl

theorem toyOptimum_withinDegree : toyOptimum.withinDegree toyBound := by
  unfold ConstraintSystem.withinDegree; decide

/-- `toyOptimum` is a sound, complete, within-degree replacement of `toyInput`. -/
theorem toyOptimum_isCorrect :
    toyOptimum.isSoundReplacementOf toyInput toyBS ∧
      toyOptimum.isCompleteReplacementOf toyInput toyBS [] ∧
      toyOptimum.withinDegree toyBound :=
  ⟨toyOptimum_isSound, toyOptimum_isComplete, toyOptimum_withinDegree⟩

/-! ## Optimality -/

/-- **Optimality.** `toyOptimum` attains the minimum variable count over *all* complete
    replacements of `toyInput`: it is itself one (of size `1`), and no complete replacement is
    smaller (`toy_lower_bound`). -/
theorem toyOptimum_optimal (O : ConstraintSystem 2) (ds : Derivations 2)
    (hcomplete : O.isCompleteReplacementOf toyInput toyBS ds) :
    toyOptimum.size ≤ O.size := by
  rw [toyOptimum_size]; exact toy_lower_bound O ds hcomplete

/-- The optimizer's generated output is a complete replacement of `toyInput` (by the audited
    correctness theorem), so it cannot beat the optimum: its variable count is `≥ toyOptimum.size`.
    Together with the `#guard`s below (which evaluate the generated output to *exactly*
    `toyOptimum`), this shows the optimizer produces an optimal circuit for this block. -/
theorem toy_generated_at_least_optimum :
    toyOptimum.size ≤ (simpleOptimizer toyBS toyBound toyInput).1.size :=
  toyOptimum_optimal _ _ ((simpleOptimizer_maintainsCorrectness toyBS toyBound).1 toyInput).2

/-! ## Machine-evaluated bridge: the optimizer emits exactly `toyOptimum`

Evaluated by the compiler at build time (like `#eval`; unlike `rfl`/`decide` these see through the
well-founded fixpoint). `#guard` fails the build if false, and introduces no axiom. -/

#guard (simpleOptimizer toyBS toyBound toyInput).1.size == 1
#guard ApcOptimizer.Spec.Dsl.render (simpleOptimizer toyBS toyBound toyInput).1
  == ApcOptimizer.Spec.Dsl.render toyOptimum

end ApcOptimizer.ToyOptimality
