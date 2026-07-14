import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.FlagFold

set_option autoImplicit false

/-! # Width-0 / width-1 range-check → equality / booleanity (C3 + idea 4(b))

powdr-exported blocks keep, on the variable range checker, two families of degenerate range
checks (multiplicity `1`):

* **width-0** `[expr, 0]`: asserts `expr < 2⁰ = 1`, i.e. `expr = 0` — powdr/OpenVM's encoding of
  "this linear form is exactly zero" (e.g. `-a__2 + b__3 = 0`). Converted to the algebraic
  equality `expr = 0`, which Gauss consumes — a variable win.
* **width-1** `[expr, 1]`: asserts `expr < 2`, i.e. booleanity. Converted to the degree-2
  constraint `expr·(expr − 1) = 0` — a bus win (bus ≻ constraints in the effectiveness order),
  and the booleanity feeds the finite-domain passes. The equivalence's backward direction
  (`x·(x−1) = 0 → x < 2`) needs an integral domain, so this arm is gated on `p` prime — decided
  once per pass invocation, the `deep`/`hdeep` pattern of `busPairCancel`. A per-candidate
  degree gate (`expr.degree ≤ 1`) keeps every emitted constraint within the identity bound, so
  the arm can never trip the whole-pass `guardDegree` revert.

Both conversions are *equivalences* over the accepted set (`BusFacts.zeroRangeEq` for width-0;
the mult-generic `BusFacts.varRangeBus` iff for width-1), so the transform is a sound,
side-effect-preserving refinement: add the constraint (entailed by the accepted interaction),
then drop the interaction (entailed by the kept constraint).

Proof shape: two `PassCorrect` steps composed by `andThen`.
1. **Add** the constraints, keeping every interaction — a `PassCorrect.ofEnvEq` whose only
   content is "each recognized interaction, being accepted, forces its constraint to zero";
   side effects and admissibility are literally unchanged (same interactions).
2. **Drop** the now-entailed interactions via `filterBusEntailed_correct`: each dropped
   interaction is stateless, and is accepted under the filtered system because the constraint
   added in step 1 (which the drop keeps) forces its value.

The pass gates on `(1 : ZMod p) ≠ 0` (true for every prime field, in particular OpenVM's
BabyBear); on the degenerate `ZMod 1` it degrades to the identity. -/

namespace ZeroWidthRange

variable {p : ℕ}

/-- `v·(v − 1)` as an expression — the booleanity constraint of `v`. -/
def boolC (v : Expression p) : Expression p := .mul v (.add v (.const (-1)))

theorem boolC_eval (v : Expression p) (env : Variable → ZMod p) :
    (boolC v).eval env = v.eval env * (v.eval env - 1) := by
  simp only [boolC, Expression.eval]; ring

theorem boolC_vars (v : Expression p) : ∀ x ∈ (boolC v).vars, x ∈ v.vars := by
  intro x hx
  simp only [boolC, Expression.vars, List.mem_append, List.not_mem_nil, or_false] at hx
  tauto

/-- On a prime field, `x < 2` (as a value) is exactly booleanity. -/
theorem val_lt_two_iff (hp : Nat.Prime p) (x : ZMod p) :
    x.val < 2 ↔ x * (x - 1) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hlt
    have : x.val = 0 ∨ x.val = 1 := by omega
    rcases this with h0 | h1
    · rw [ZMod.val_eq_zero] at h0; rw [h0]; ring
    · have hx1 : x = 1 := by
        have := (ZMod.natCast_rightInverse x).symm
        rw [this, h1]; norm_cast
      rw [hx1]; ring
  · intro hprod
    rcases mul_eq_zero.1 hprod with h0 | h1
    · rw [h0, ZMod.val_zero]; omega
    · have hx1 : x = 1 := by linear_combination h1
      rw [hx1, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt]; omega

/-- Recognize a degenerate range check (multiplicity `1`) and return the equivalent algebraic
    constraint: the value itself for width-0 (`zeroRangeEq` bus), its booleanity `boolC` for
    width-1 (`varRangeBus` bus, degree-gated, only when `one = true` — i.e. `p` prime). -/
def rangeEq? (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match bi.payload with
  | [v, c] =>
    if bi.multiplicity = Expression.const 1 then
      if facts.zeroRangeEq bi.busId = true ∧ c = Expression.const 0 then some v
      else if one = true ∧ facts.varRangeBus bi.busId = true ∧ c = Expression.const 1
          ∧ v.degree ≤ 1 then some (boolC v)
      else none
    else none
  | _ => none

/-- Structure of a recognized interaction: multiplicity `1`, payload `[v, width]`, and either
    the width-0 or the width-1 case with the matching constraint. -/
theorem rangeEq?_spec (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (e : Expression p)
    (h : rangeEq? one bs facts bi = some e) :
    bi.multiplicity = Expression.const 1 ∧
      ∃ v, ((facts.zeroRangeEq bi.busId = true ∧ bi.payload = [v, Expression.const 0] ∧ e = v)
        ∨ (one = true ∧ facts.varRangeBus bi.busId = true
            ∧ bi.payload = [v, Expression.const 1] ∧ e = boolC v)) := by
  unfold rangeEq? at h
  split at h
  · rename_i v' c hpay
    split_ifs at h with hm hA hB
    · obtain ⟨hz, hc⟩ := hA
      simp only [Option.some.injEq] at h
      exact ⟨hm, e, Or.inl ⟨hz, by rw [hpay, hc, h], rfl⟩⟩
    · obtain ⟨hone, hv, hc, _⟩ := hB
      simp only [Option.some.injEq] at h
      exact ⟨hm, v', Or.inr ⟨hone, hv, by rw [hpay, hc], h.symm⟩⟩
  · exact absurd h (by simp)

/-- A recognized interaction lives on a stateless bus. -/
theorem rangeEq?_stateless (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (e : Expression p)
    (h : rangeEq? one bs facts bi = some e) : bs.isStateful bi.busId = false := by
  obtain ⟨_, v, hcase⟩ := rangeEq?_spec one bs facts bi e h
  rcases hcase with ⟨hz, _, _⟩ | ⟨_, hv, _, _⟩
  · exact (facts.zeroRangeEq_sound bi.busId hz).1
  · exact (facts.varRangeBus_sound bi.busId hv).1

/-- The evaluated message is accepted iff the returned constraint evaluates to zero. -/
theorem rangeEq?_violates_iff (one : Bool) (hone : one = true → Nat.Prime p)
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (e : Expression p) (env : Variable → ZMod p)
    (h : rangeEq? one bs facts bi = some e) :
    bs.violatesConstraint (bi.eval env) = false ↔ e.eval env = 0 := by
  obtain ⟨hm, v, hcase⟩ := rangeEq?_spec one bs facts bi e h
  rcases hcase with ⟨hz, hp', rfl⟩ | ⟨hone', hv, hp', rfl⟩
  · have hev : bi.eval env = { busId := bi.busId, multiplicity := 1, payload := [e.eval env, 0] } := by
      unfold BusInteraction.eval; rw [hm, hp']; simp [Expression.eval]
    rw [hev]
    exact (facts.zeroRangeEq_sound bi.busId hz).2 (e.eval env)
  · have hev : bi.eval env = { busId := bi.busId, multiplicity := 1, payload := [v.eval env, 1] } := by
      unfold BusInteraction.eval; rw [hm, hp']; simp [Expression.eval]
    have hprime := hone hone'
    rw [hev, boolC_eval, ← val_lt_two_iff hprime]
    have h1val : (1 : ZMod p).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hprime.one_lt]
    rw [(facts.varRangeBus_sound bi.busId hv).2 (v.eval env) 1 1, h1val]
    constructor
    · exact fun ⟨_, hlt⟩ => by rwa [pow_one] at hlt
    · exact fun hlt => ⟨by omega, by rwa [pow_one]⟩

/-- Convert every width-0 range check into the equality `value = 0`, and — on a prime field —
    every width-1 range check into the booleanity `value·(value−1) = 0`, dropping the
    interactions. -/
def zeroWidthRangePass : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    let one : Bool := decide (Nat.Prime p)
    have hone : one = true → Nat.Prime p := fun h => of_decide_eq_true h
    let newC := cs.busInteractions.filterMap (rangeEq? one bs facts)
    let out1 : ConstraintSystem p :=
      { cs with algebraicConstraints := cs.algebraicConstraints ++ newC }
    let keep := fun bi => (rangeEq? one bs facts bi).isNone
    -- Step 1: add the constraints; interactions (hence side effects, admissibility) unchanged.
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
            obtain ⟨_, v, hcase⟩ := rangeEq?_spec one bs facts bi c hval
            rcases hcase with ⟨_, hp', rfl⟩ | ⟨_, _, hp', rfl⟩
            · exact Or.inr ⟨bi, hbi, Or.inr ⟨c, by rw [hp']; simp, hxc⟩⟩
            · exact Or.inr ⟨bi, hbi, Or.inr ⟨v, by rw [hp']; simp, boolC_vars v x hxc⟩⟩
        · exact Or.inr ⟨bi, hbi, hbrest⟩
      · -- completeness: same env; the added constraints hold because the interactions are accepted
        intro env hadm hsat
        refine ⟨⟨fun c hc => ?_, hsat.2⟩, hadm, BusState.equiv_refl _⟩
        rcases List.mem_append.1 hc with hc | hc
        · exact hsat.1 c hc
        · obtain ⟨bi, hbi, hval⟩ := List.mem_filterMap.1 hc
          have hmult : (bi.eval env).multiplicity = 1 := by
            obtain ⟨hm, _, _⟩ := rangeEq?_spec one bs facts bi c hval
            unfold BusInteraction.eval
            rw [hm]; simp [Expression.eval]
          have hviol : bs.violatesConstraint (bi.eval env) = false :=
            hsat.2 bi hbi (by rw [hmult]; exact h1ne)
          exact (rangeEq?_violates_iff one hone bs facts bi c env hval).1 hviol
    -- Step 2: drop the now-entailed interactions.
    have hstep2 : PassCorrect out1 (out1.filterBus keep) [] bs := by
      refine out1.filterBusEntailed_correct bs keep ?_ ?_
      · intro bi _ hkf
        obtain ⟨e, he⟩ : ∃ e, rangeEq? one bs facts bi = some e := by
          have hkf' : (rangeEq? one bs facts bi).isNone = false := hkf
          cases hopt : rangeEq? one bs facts bi with
          | none => rw [hopt] at hkf'; simp at hkf'
          | some e => exact ⟨e, rfl⟩
        exact rangeEq?_stateless one bs facts bi e he
      · intro bi hbi hkf env hsatf _
        obtain ⟨e, he⟩ : ∃ e, rangeEq? one bs facts bi = some e := by
          have hkf' : (rangeEq? one bs facts bi).isNone = false := hkf
          cases hopt : rangeEq? one bs facts bi with
          | none => rw [hopt] at hkf'; simp at hkf'
          | some e => exact ⟨e, rfl⟩
        have hemem : e ∈ (out1.filterBus keep).algebraicConstraints :=
          List.mem_append_right _ (List.mem_filterMap.2 ⟨bi, hbi, he⟩)
        rw [rangeEq?_violates_iff one hone bs facts bi e env he]
        exact hsatf.1 e hemem
    ⟨out1.filterBus keep, [], hstep1.andThen hstep2⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

end ZeroWidthRange
