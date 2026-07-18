import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Width-0 range check → equality (the `rangeCheckAt` generalisation of `ZeroWidthRange`)

`ZeroWidthRange` converts a width-0 range check on OpenVM's dedicated variable-range-checker bus
(`[expr, 0]`, i.e. `expr < 2⁰ = 1`, i.e. `expr = 0`) to the algebraic equality `expr = 0`, which
Gauss consumes. SP1 carries the same degenerate checks on its byte bus as op-6 `[6, expr, 0, 0]`
(the layout `ZeroWidthRange`'s `zeroRangeEq`/`varRangeBus` facts do not describe), and their value
slot is often a whole **linear form** — a decomposition equality like
`higher_limb = result₀ + 256·result₁ + …`. This pass reads them through the layout-agnostic
`BusFacts.rangeCheckAt` fact: when it reports `bound = 1` at a slot, an accepted message forces that
slot's expression to `0`, so the pass **seeds that expression as an algebraic constraint**
(`ConstraintSystem.addConstraints_correct`). Gauss then eliminates a variable and the now-constant
`[6, 0, 0, 0]` check is dropped by `tautoBus`.

Purely the accepted-set `↔` of `rangeCheckAt` at `bound = 1`; no bus specifics beyond the fact.
`trivial`/OpenVM declare no `rangeCheckAt`, so this is a no-op there (OpenVM keeps `ZeroWidthRange`
on its own bus). Gated on `(1 : ZMod p) ≠ 0` (every prime field; identity on `ZMod 1`). -/

namespace RangeForceZero

variable {p : ℕ}

/-- The forced-zero expression of `bi`: its value-slot expression, when `bi` is a mult-1 range
    check whose `rangeCheckAt` bound is `1` (`= 2⁰`, so the slot is `< 1`, i.e. `0`). -/
def forceZeroAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map Expression.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = Expression.const 1 ∧ bound = 1 then
      -- skip an already-constant slot: it would seed a trivial `0` every cycle until `tautoBus`
      -- drops the now-constant check.
      match bi.payload[valSlot]? with
      | some e => if e.constValue?.isNone then some e else none
      | none => none
    else none
  | none => none

theorem forceZeroAt_spec {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (e : Expression p) (h : forceZeroAt facts bi = some e) :
    ∃ valSlot, facts.rangeCheckAt bi.busId (bi.payload.map Expression.constValue?)
        = some (valSlot, 1) ∧ bi.multiplicity = Expression.const 1 ∧ bi.payload[valSlot]? = some e := by
  unfold forceZeroAt at h
  split at h
  · rename_i vs bd hrc
    split_ifs at h with hcond
    obtain ⟨hmc, rfl⟩ := hcond
    cases hp : bi.payload[vs]? with
    | none => simp only [hp] at h; simp at h
    | some e' =>
      simp only [hp] at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨vs, hrc, hmc, hp⟩
  · exact absurd h (by simp)

/-- Every accepted-and-active width-0 check forces its slot expression to `0`. -/
theorem forceZeroAt_sound {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (bi : BusInteraction (Expression p)) (e : Expression p) (h1ne : (1 : ZMod p) ≠ 0)
    (h : forceZeroAt facts bi = some e) (env : Variable → ZMod p) (hsat : cs.satisfies bs env)
    (hbi : bi ∈ cs.busInteractions) : e.eval env = 0 := by
  obtain ⟨valSlot, hrc, hmc, hget⟩ := forceZeroAt_spec facts bi e h
  obtain ⟨_, hm⟩ := facts.rangeCheckAt_sound bi.busId (bi.payload.map Expression.constValue?)
    valSlot 1 hrc
  have hmult : (bi.eval env).multiplicity = 1 := by
    show bi.multiplicity.eval env = 1; rw [hmc]; rfl
  obtain ⟨_, hiff⟩ := hm (bi.eval env) rfl hmult (matches_evalPattern bi.payload env)
  have hviol : bs.violatesConstraint (bi.eval env) = false := by
    refine hsat.2 bi hbi ?_; rw [hmult]; exact h1ne
  have hgetEv : (bi.eval env).payload[valSlot]? = some (e.eval env) := by
    show (bi.payload.map (fun t => t.eval env))[valSlot]? = some (e.eval env)
    rw [List.getElem?_map, hget]; rfl
  have hlt : (e.eval env).val < 1 := (hiff (e.eval env) hgetEv).mp hviol
  exact (ZMod.val_eq_zero _).mp (by omega)

/-- The seeds: the forced-zero expression of every recognised width-0 check. -/
def forceZeroSeeds {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (Expression p) :=
  cs.busInteractions.filterMap (forceZeroAt facts)

theorem forceZeroSeeds_sound {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (env : Variable → ZMod p) (h1ne : (1 : ZMod p) ≠ 0) (hsat : cs.satisfies bs env) :
    ∀ e ∈ forceZeroSeeds facts cs, e.eval env = 0 := by
  intro e he
  obtain ⟨bi, hbi, hf⟩ := List.mem_filterMap.1 he
  exact forceZeroAt_sound facts cs bi e h1ne hf env hsat hbi

/-- The pass: seed `expr = 0` for every width-0 (`bound = 1`) range check. -/
def rangeForceZeroPass : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    let new := (forceZeroSeeds facts cs).filter (fun e => e.vars.all (fun z => cs.vars.contains z))
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
      cs.addConstraints_correct bs new
        (fun env _ hsat e he =>
          forceZeroSeeds_sound facts cs env h1ne hsat e (List.mem_of_mem_filter he))
        (fun e he z hz => by
          have hp := (List.mem_filter.1 he).2
          simp only [List.all_eq_true] at hp
          exact List.contains_iff_mem.mp (hp z hz))⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

end RangeForceZero
