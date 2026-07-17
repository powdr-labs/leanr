import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.FlagFold

set_option autoImplicit false

/-! # Subsumed pure-range-check removal (the `rangeCheckAt` generalisation of `SubsumedRange`)

`SubsumedRange` drops a variable range check `[x, w]` on OpenVM's dedicated variable-range-checker
bus. SP1 has no such bus: its range checks ride the multi-op byte bus as `[6, x, w, 0]` (op 6,
`Range`). This pass generalises the same idea through the layout-agnostic `rangeCheckAt` fact:
`rangeCheckAt busId pattern = some (valSlot, bound)` says a mult-1 message matching `pattern` is
accepted **iff** `payload[valSlot] < bound`. A recognised check whose value variable is *already*
bounded `< bound` by the non-circular justification base (interactions this pass never drops) is
entailed, so dropping it is sound, variable-neutral, and removes one bus interaction.

Same two proven ingredients as `SubsumedRange`: `filterBusEntailed_correct` (drop a stateless
interaction accepted under every assignment satisfying the filtered system) and a non-circular
base via `findVarBound`. `trivial`/OpenVM declare no `rangeCheckAt`, so this pass is a no-op there
(OpenVM keeps using `SubsumedRange`); SP1 uses it to shed the op-6 checks whose result is a
16-bit memory limb already bounded by the surviving read. -/

namespace SubsumedCheck

variable {p : ℕ}

/-- Recognise a pure single-value range check (`facts.rangeCheckAt`) at multiplicity `1` whose
    value slot holds a bare variable: returns the checked variable, its slot, and its bound. -/
def checkOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Variable × Nat × Nat) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map Expression.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = Expression.const 1 then
      match bi.payload[valSlot]? with
      | some (Expression.var x) => some (x, valSlot, bound)
      | _ => none
    else none
  | none => none

theorem checkOf_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (valSlot bound : Nat)
    (h : checkOf bs facts bi = some (x, valSlot, bound)) :
    facts.rangeCheckAt bi.busId (bi.payload.map Expression.constValue?) = some (valSlot, bound) ∧
      bi.multiplicity = Expression.const 1 ∧ bi.payload[valSlot]? = some (Expression.var x) := by
  unfold checkOf at h
  split at h
  · rename_i vs bd hrc
    split_ifs at h with hmc
    split at h
    · rename_i x' hxp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hrc, hmc, hxp⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A recognised check lives on a stateless bus. -/
theorem checkOf_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (valSlot bound : Nat)
    (h : checkOf bs facts bi = some (x, valSlot, bound)) : bs.isStateful bi.busId = false :=
  (facts.rangeCheckAt_sound bi.busId (bi.payload.map Expression.constValue?) valSlot bound
    (checkOf_spec bs facts bi x valSlot bound h).1).1

/-- If the checked variable is in range (`< bound`), the recognised message is accepted. -/
theorem checkOf_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (valSlot bound : Nat)
    (h : checkOf bs facts bi = some (x, valSlot, bound)) (env : Variable → ZMod p)
    (hlt : (env x).val < bound) : bs.violatesConstraint (bi.eval env) = false := by
  obtain ⟨hrc, hmc, hxp⟩ := checkOf_spec bs facts bi x valSlot bound h
  obtain ⟨_, hm⟩ := facts.rangeCheckAt_sound bi.busId (bi.payload.map Expression.constValue?)
    valSlot bound hrc
  have hmult : (bi.eval env).multiplicity = 1 := by
    show bi.multiplicity.eval env = 1
    rw [hmc]; rfl
  have hmatch : Matches (bi.eval env).payload (bi.payload.map Expression.constValue?) :=
    matches_evalPattern bi.payload env
  obtain ⟨_, hiff⟩ := hm (bi.eval env) rfl hmult hmatch
  have hget : (bi.eval env).payload[valSlot]? = some (env x) := by
    show (bi.payload.map (fun e => e.eval env))[valSlot]? = some (env x)
    rw [List.getElem?_map, hxp]; rfl
  exact (hiff (env x) hget).mpr hlt

/-! ## The pass -/

/-- The justification base: interactions this pass never drops (not recognised as pure checks). -/
def dropBase (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (BusInteraction (Expression p)) :=
  cs.busInteractions.filter (fun bi => (checkOf bs facts bi).isNone)

/-- Keep `bi` unless it is a recognised pure check whose variable is already bounded `< bound` by a
    retained (base) interaction. -/
def dropKeep (bs : BusSemantics p) (facts : BusFacts p bs)
    (base : List (BusInteraction (Expression p))) (bi : BusInteraction (Expression p)) : Bool :=
  match checkOf bs facts bi with
  | some (x, _, bound) =>
    match findVarBound bs facts base x with
    | some b' => !decide (b' ≤ bound)
    | none => true
  | none => true

/-- Drop every pure single-value range check whose bound is already entailed by a stronger-or-equal
    retained stateless check on the same variable. -/
def subsumedCheckDropPass : VerifiedPassW p := fun cs bs facts =>
  ⟨cs.filterBus (dropKeep bs facts (dropBase bs facts cs)), [],
   cs.filterBusEntailed_correct bs _
     (by
       intro bi _ hkf
       cases hr : checkOf bs facts bi with
       | none => exact absurd hkf (by simp [dropKeep, hr])
       | some xvb =>
         obtain ⟨x, valSlot, bound⟩ := xvb
         exact checkOf_stateless bs facts bi x valSlot bound hr)
     (by
       intro bi hbimem hkf env hsat _
       cases hr : checkOf bs facts bi with
       | none => exact absurd hkf (by simp [dropKeep, hr])
       | some xvb =>
         obtain ⟨x, valSlot, bound⟩ := xvb
         cases hb : findVarBound bs facts (dropBase bs facts cs) x with
         | none => exact absurd hkf (by simp [dropKeep, hr, hb])
         | some b' =>
           have hble : b' ≤ bound := by
             simp only [dropKeep, hr, hb, Bool.not_eq_false', decide_eq_true_eq] at hkf
             exact hkf
           have hbase : (env x).val < b' := by
             refine findVarBound_sound bs facts (dropBase bs facts cs) x b' hb env
               (fun bi' hbi' hmult => ?_)
             have hbimem' : bi' ∈ cs.busInteractions := (List.mem_filter.1 hbi').1
             have hnone : checkOf bs facts bi' = none := by
               have := (List.mem_filter.1 hbi').2
               simpa using this
             have hkeep : dropKeep bs facts (dropBase bs facts cs) bi' = true := by
               simp only [dropKeep, hnone]
             exact hsat.2 bi' (List.mem_filter.2 ⟨hbimem', hkeep⟩) hmult
           exact checkOf_accepted bs facts bi x valSlot bound hr env
             (lt_of_lt_of_le hbase hble))⟩

end SubsumedCheck
