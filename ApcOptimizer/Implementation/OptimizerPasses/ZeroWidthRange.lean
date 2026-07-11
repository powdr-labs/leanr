import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.FlagFold

set_option autoImplicit false

/-! # Width-0 range-check → equality (C3)

powdr-exported blocks that compute effective addresses keep, on the variable range checker, a family
of **width-0 range checks** `[expr, 0]` (multiplicity `1`). A 0-bit range check asserts
`expr < 2⁰ = 1`, i.e. `expr = 0`; it is powdr/OpenVM's encoding of "this linear form is exactly
zero" — used to pin an intermediate address/data limb to a combination of others (e.g.
`-a__2 + b__3 = 0`, `7864320·(a__3 − b__0) = 0`). Because the optimizer's Gaussian elimination only
consumes *algebraic* constraints, these equalities — being carried on the **bus** — are never used
to eliminate a variable, so the intermediate limbs survive. powdr substitutes them away.

This pass converts each such interaction into the algebraic constraint `expr = 0` and drops the
interaction: the two have the *same* satisfying set (a stateless range check `[x, 0]` is accepted iff
`x = 0`, `BusFacts.zeroRangeEq`), so the transform is a sound, side-effect-preserving refinement.
Placed early in the cleanup cycle, it feeds the new equalities to Gauss, which then eliminates the
intermediate variables and cascades — a variable win (and, via the dropped interaction and the
range checks the eliminated variables no longer need, a bus win).

Proof shape: two `PassCorrect` steps composed by `andThen`.
1. **Add** the equality constraints, keeping every interaction — a `PassCorrect.ofEnvEq` whose only
   content is "each width-0 interaction, being accepted, forces its value to zero" (so the added
   constraints hold); side effects and admissibility are literally unchanged (same interactions).
2. **Drop** the now-entailed width-0 interactions via `filterBusEntailed_correct`: each dropped
   interaction is stateless, and is accepted under the filtered system because the equality
   constraint added in step 1 (which the drop keeps) forces its value to zero.

The pass gates on `(1 : ZMod p) ≠ 0` (true for every prime field, in particular OpenVM's BabyBear);
on the degenerate `ZMod 1` it degrades to the identity. -/

namespace ZeroWidthRange

variable {p : ℕ}

/-- Recognize a width-0 range check `[value, 0]` (multiplicity `1`) on a `zeroRangeEq` bus, returning
    the value expression whose zeroness it asserts; `none` otherwise. -/
def zeroRangeValue? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match bi.payload with
  | [v, c] =>
    if facts.zeroRangeEq bi.busId = true ∧ bi.multiplicity = Expression.const 1
        ∧ c = Expression.const 0 then some v else none
  | _ => none

/-- Structure of a recognized interaction: the bus admits the equality fact, the multiplicity is the
    constant `1`, and the payload is `[value, 0]`. -/
theorem zeroRangeValue?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (v : Expression p)
    (h : zeroRangeValue? bs facts bi = some v) :
    facts.zeroRangeEq bi.busId = true ∧ bi.multiplicity = Expression.const 1
      ∧ bi.payload = [v, Expression.const 0] := by
  unfold zeroRangeValue? at h
  split at h
  · rename_i v' c hpay
    split_ifs at h with hcond
    obtain ⟨hz, hm, hc⟩ := hcond
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hz, hm, by rw [hpay, hc]⟩
  · exact absurd h (by simp)

/-- A recognized interaction evaluates to the message `[value.eval, 0]` with multiplicity `1`. -/
theorem zeroRangeValue?_eval (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (v : Expression p) (env : Variable → ZMod p)
    (h : zeroRangeValue? bs facts bi = some v) :
    bi.eval env = { busId := bi.busId, multiplicity := 1, payload := [v.eval env, 0] } := by
  obtain ⟨_, hm, hp⟩ := zeroRangeValue?_spec bs facts bi v h
  unfold BusInteraction.eval
  rw [hm, hp]
  simp [Expression.eval]

/-- A recognized interaction lives on a stateless bus. -/
theorem zeroRangeValue?_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (v : Expression p)
    (h : zeroRangeValue? bs facts bi = some v) : bs.isStateful bi.busId = false :=
  (facts.zeroRangeEq_sound bi.busId (zeroRangeValue?_spec bs facts bi v h).1).1

/-- The evaluated message is accepted iff the value evaluates to zero. -/
theorem zeroRangeValue?_violates_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (v : Expression p) (env : Variable → ZMod p)
    (h : zeroRangeValue? bs facts bi = some v) :
    bs.violatesConstraint (bi.eval env) = false ↔ v.eval env = 0 := by
  rw [zeroRangeValue?_eval bs facts bi v env h]
  exact (facts.zeroRangeEq_sound bi.busId (zeroRangeValue?_spec bs facts bi v h).1).2 (v.eval env)

/-- Convert every width-0 range check into the equality `value = 0` and drop the interaction. -/
def zeroWidthRangePass : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    let newC := cs.busInteractions.filterMap (zeroRangeValue? bs facts)
    let out1 : ConstraintSystem p :=
      { cs with algebraicConstraints := cs.algebraicConstraints ++ newC }
    let keep := fun bi => (zeroRangeValue? bs facts bi).isNone
    -- Step 1: add the equality constraints; interactions (hence side effects, admissibility) unchanged.
    have hstep1 : PassCorrect cs out1 [] bs := by
      refine PassCorrect.ofEnvEq ?_ ?_ ?_ ?_
      · -- soundness: out1 has extra constraints, same interactions
        intro env hsat
        exact ⟨env, ⟨fun c hc => hsat.1 c (List.mem_append_left _ hc), hsat.2⟩,
          BusState.equiv_refl _⟩
      · -- invariant preservation
        intro hcs env hsat
        exact hcs env ⟨fun c hc => hsat.1 c (List.mem_append_left _ hc), hsat.2⟩
      · -- no new variables
        intro x hx
        rw [ConstraintSystem.mem_vars] at hx ⊢
        rcases hx with ⟨c, hc, hxc⟩ | ⟨bi, hbi, hbrest⟩
        · rcases List.mem_append.1 hc with hc | hc
          · exact Or.inl ⟨c, hc, hxc⟩
          · obtain ⟨bi, hbi, hval⟩ := List.mem_filterMap.1 hc
            obtain ⟨_, _, hp⟩ := zeroRangeValue?_spec bs facts bi c hval
            exact Or.inr ⟨bi, hbi, Or.inr ⟨c, by rw [hp]; simp, hxc⟩⟩
        · exact Or.inr ⟨bi, hbi, hbrest⟩
      · -- completeness: same env; the added equalities hold because the interactions are accepted
        intro env hadm hsat
        refine ⟨⟨fun c hc => ?_, hsat.2⟩, hadm, BusState.equiv_refl _⟩
        rcases List.mem_append.1 hc with hc | hc
        · exact hsat.1 c hc
        · obtain ⟨bi, hbi, hval⟩ := List.mem_filterMap.1 hc
          have hmult : (bi.eval env).multiplicity = 1 := by
            rw [zeroRangeValue?_eval bs facts bi c env hval]
          have hviol : bs.violatesConstraint (bi.eval env) = false :=
            hsat.2 bi hbi (by rw [hmult]; exact h1ne)
          exact (zeroRangeValue?_violates_iff bs facts bi c env hval).1 hviol
    -- Step 2: drop the now-entailed width-0 interactions.
    have hstep2 : PassCorrect out1 (out1.filterBus keep) [] bs := by
      refine out1.filterBusEntailed_correct bs keep ?_ ?_
      · intro bi _ hkf
        obtain ⟨v, hv⟩ : ∃ v, zeroRangeValue? bs facts bi = some v := by
          have hkf' : (zeroRangeValue? bs facts bi).isNone = false := hkf
          cases hopt : zeroRangeValue? bs facts bi with
          | none => rw [hopt] at hkf'; simp at hkf'
          | some v => exact ⟨v, rfl⟩
        exact zeroRangeValue?_stateless bs facts bi v hv
      · intro bi hbi hkf env hsatf _
        obtain ⟨v, hv⟩ : ∃ v, zeroRangeValue? bs facts bi = some v := by
          have hkf' : (zeroRangeValue? bs facts bi).isNone = false := hkf
          cases hopt : zeroRangeValue? bs facts bi with
          | none => rw [hopt] at hkf'; simp at hkf'
          | some v => exact ⟨v, rfl⟩
        have hvmem : v ∈ (out1.filterBus keep).algebraicConstraints :=
          List.mem_append_right _ (List.mem_filterMap.2 ⟨bi, hbi, hv⟩)
        rw [zeroRangeValue?_violates_iff bs facts bi v env hv]
        exact hsatf.1 v hvmem
    ⟨out1.filterBus keep, [], hstep1.andThen hstep2⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

end ZeroWidthRange
