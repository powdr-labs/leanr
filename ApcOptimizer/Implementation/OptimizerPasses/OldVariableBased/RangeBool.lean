import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroWidthRange
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck

set_option autoImplicit false

/-! # Width-1 range check → booleanity on SP1's op-6 (the `rangeCheckAt` half of `ZeroWidthRange`)

`ZeroWidthRange` converts a width-1 range check `[expr, 1]` (`expr < 2`, i.e. `expr ∈ {0,1}`) on
OpenVM's variable-range bus to the degree-2 booleanity `expr·(expr − 1) = 0`, dropping the bus
interaction (a bus win, `bus ≻ constraints`). SP1 carries the same checks on its byte bus as op-6
`[6, x, 1, 0]`. This pass reads them through the layout-agnostic `BusFacts.rangeCheckAt` fact: when
it reports `bound = 2` at a slot holding a bare variable `x`, an accepted mult-1 message is exactly
`x·(x−1) = 0`, so the pass adds that constraint and drops the check.

Two `PassCorrect` steps (as in `ZeroWidthRange`): **add** the booleanity — entailed by acceptance,
side effects unchanged — then **drop** the now-entailed checks (`filterBusEntailed_correct`). The
booleanity's backward direction (`x·(x−1) = 0 → x < 2`) needs an integral domain, so the pass is
prime-gated (`PrimeWitness`). Restricting the value slot to a bare variable keeps every added
constraint at degree 2, within the identity bound, so `guardDegree` never reverts the pass.
`trivial`/OpenVM declare no `rangeCheckAt`, so this is a no-op there. -/

namespace RangeBool

variable {p : ℕ}

/-- The booleanity constraint `x·(x−1)` of a width-1 (`bound = 2`) op-6 check whose value slot is a
    bare variable `x`; `none` otherwise. -/
def boolCheck? {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map Expression.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = Expression.const 1 ∧ bound = 2 then
      match bi.payload[valSlot]? with
      | some (Expression.var x) => some (ZeroWidthRange.boolC (Expression.var x))
      | _ => none
    else none
  | none => none

theorem boolCheck?_spec {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : boolCheck? facts bi = some c) :
    ∃ valSlot x, facts.rangeCheckAt bi.busId (bi.payload.map Expression.constValue?)
        = some (valSlot, 2) ∧ bi.multiplicity = Expression.const 1 ∧
        bi.payload[valSlot]? = some (Expression.var x) ∧ c = ZeroWidthRange.boolC (Expression.var x) := by
  unfold boolCheck? at h
  split at h
  · rename_i vs bd hrc
    split_ifs at h with hcond
    obtain ⟨hmc, rfl⟩ := hcond
    cases hp : bi.payload[vs]? with
    | none => simp only [hp] at h; simp at h
    | some ex =>
      cases ex with
      | var x =>
        simp only [hp] at h; simp only [Option.some.injEq] at h
        exact ⟨vs, x, hrc, hmc, hp, h.symm⟩
      | const _ => simp only [hp] at h; simp at h
      | add _ _ => simp only [hp] at h; simp at h
      | mul _ _ => simp only [hp] at h; simp at h
  · exact absurd h (by simp)

/-- A recognised width-1 check lives on a stateless bus. -/
theorem boolCheck?_stateless {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : boolCheck? facts bi = some c) :
    bs.isStateful bi.busId = false := by
  obtain ⟨valSlot, x, hrc, _, _, _⟩ := boolCheck?_spec facts bi c h
  exact (facts.rangeCheckAt_sound bi.busId (bi.payload.map Expression.constValue?) valSlot 2 hrc).1

/-- For a recognised width-1 check, acceptance is exactly the booleanity of its value variable. -/
theorem boolCheck?_violates_iff {bs : BusSemantics p} (hp : Nat.Prime p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : boolCheck? facts bi = some c)
    (env : Variable → ZMod p) : bs.violatesConstraint (bi.eval env) = false ↔ c.eval env = 0 := by
  obtain ⟨valSlot, x, hrc, hmc, hxp, rfl⟩ := boolCheck?_spec facts bi c h
  obtain ⟨_, hm⟩ := facts.rangeCheckAt_sound bi.busId (bi.payload.map Expression.constValue?)
    valSlot 2 hrc
  have hmult : (bi.eval env).multiplicity = 1 := by
    show bi.multiplicity.eval env = 1; rw [hmc]; rfl
  obtain ⟨_, hiff⟩ := hm (bi.eval env) rfl hmult (matches_evalPattern bi.payload env)
  have hget : (bi.eval env).payload[valSlot]? = some (env x) := by
    show (bi.payload.map (fun e => e.eval env))[valSlot]? = some (env x)
    rw [List.getElem?_map, hxp]; rfl
  rw [hiff (env x) hget, ZeroWidthRange.boolC_eval]
  simpa only [Expression.eval] using ZeroWidthRange.val_lt_two_iff hp (env x)

/-- The pass: replace every width-1 op-6 range check on a bare variable by its booleanity. -/
def rangeBoolPass (pw : PrimeWitness p) : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    if hpr : pw.isPrime = true then
      have hp : Nat.Prime p := pw.correct hpr
      let newC := cs.busInteractions.filterMap (boolCheck? facts)
      let out1 : ConstraintSystem p :=
        { cs with algebraicConstraints := cs.algebraicConstraints ++ newC }
      let keep := fun bi => (boolCheck? facts bi).isNone
      have hstep1 : PassCorrect cs out1 [] bs := by
        refine PassCorrect.ofEnvEq ?_ ?_ ?_ ?_
        · intro env hsat
          exact ⟨env, ⟨fun c hc => hsat.1 c (List.mem_append_left _ hc), hsat.2⟩, BusState.equiv_refl _⟩
        · intro hcs env hsat
          exact hcs env ⟨fun c hc => hsat.1 c (List.mem_append_left _ hc), hsat.2⟩
        · intro z hz
          rw [ConstraintSystem.mem_vars] at hz ⊢
          rcases hz with ⟨c, hc, hzc⟩ | ⟨bi, hbi, hbrest⟩
          · rcases List.mem_append.1 hc with hc | hc
            · exact Or.inl ⟨c, hc, hzc⟩
            · obtain ⟨bi, hbi, hval⟩ := List.mem_filterMap.1 hc
              obtain ⟨_, x, _, _, hxp, rfl⟩ := boolCheck?_spec facts bi c hval
              exact Or.inr ⟨bi, hbi, Or.inr ⟨Expression.var x, List.mem_of_getElem? hxp,
                ZeroWidthRange.boolC_vars _ z hzc⟩⟩
          · exact Or.inr ⟨bi, hbi, hbrest⟩
        · intro env hadm hsat
          refine ⟨⟨fun c hc => ?_, hsat.2⟩, hadm, BusState.equiv_refl _⟩
          rcases List.mem_append.1 hc with hc | hc
          · exact hsat.1 c hc
          · obtain ⟨bi, hbi, hval⟩ := List.mem_filterMap.1 hc
            have hmult : (bi.eval env).multiplicity = 1 := by
              obtain ⟨_, _, _, hm, _, _⟩ := boolCheck?_spec facts bi c hval
              show bi.multiplicity.eval env = 1; rw [hm]; rfl
            have hviol : bs.violatesConstraint (bi.eval env) = false :=
              hsat.2 bi hbi (by rw [hmult]; exact h1ne)
            exact (boolCheck?_violates_iff hp facts bi c hval env).1 hviol
      have hstep2 : PassCorrect out1 (out1.filterBus keep) [] bs := by
        refine out1.filterBusEntailed_correct bs keep ?_ ?_
        · intro bi _ hkf
          obtain ⟨e, he⟩ : ∃ e, boolCheck? facts bi = some e := by
            have hkf' : (boolCheck? facts bi).isNone = false := hkf
            cases hopt : boolCheck? facts bi with
            | none => rw [hopt] at hkf'; simp at hkf'
            | some e => exact ⟨e, rfl⟩
          exact boolCheck?_stateless facts bi e he
        · intro bi hbi hkf env hsatf _
          obtain ⟨e, he⟩ : ∃ e, boolCheck? facts bi = some e := by
            have hkf' : (boolCheck? facts bi).isNone = false := hkf
            cases hopt : boolCheck? facts bi with
            | none => rw [hopt] at hkf'; simp at hkf'
            | some e => exact ⟨e, rfl⟩
          have hemem : e ∈ (out1.filterBus keep).algebraicConstraints :=
            List.mem_append_right _ (List.mem_filterMap.2 ⟨bi, hbi, he⟩)
          rw [boolCheck?_violates_iff hp facts bi e he env]
          exact hsatf.1 e hemem
      ⟨out1.filterBus keep, [], hstep1.andThen hstep2⟩
    else ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

end RangeBool
