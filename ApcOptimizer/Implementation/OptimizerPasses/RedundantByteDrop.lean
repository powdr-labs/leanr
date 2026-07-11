import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancel
import ApcOptimizer.Implementation.OptimizerPasses.FlagFold

set_option autoImplicit false

/-! # Redundant byte-check removal (C2)

After optimization, blocks keep stateless bitwise-lookup interactions whose *only* obligation is
"this operand is a byte" — the self-check form `[x, x, 0, 1]` (`BusFacts.byteCheck`) and the
packed-pair form `[x, y, 0, 0]` (`BusFacts.bytePairBus` + `byteCheck`). Many of their operands are
already byte-guaranteed by the *rest* of the system: they are raw payload slots of retained memory
receives (whose acceptance implies byte-ness, `BusFacts.slotBound`) or are pinned to bytes by
retained constraints (`deepBoundOk` on prime `p`). Such a check is *entailed* — every assignment
satisfying the rest of the system satisfies it — so dropping it is sound, variable-neutral, and
removes one bus interaction. powdr performs the same cleanup (e.g. it emits no bitwise bus at all on
the load/store blocks); this closes the measured residual bitwise-interaction gap.

Crucially it drops a check only when the operand's byte-ness is guaranteed *elsewhere*: a check on a
freshly *computed* value (whose byte-ness only the check itself enforces) is **kept**, because
`byteJustified` cannot justify it from the rest of the system. That is exactly powdr's behaviour
(keep checks on ALU results, drop them on memory-read words).

Two ingredients:

1. `ConstraintSystem.filterBusEntailed_correct` (reused from `FlagFold.lean`) — the generalization
   of `filterBusStateless_correct` where acceptance of a dropped interaction may be *conditional on
   satisfaction of the filtered system* rather than universal. That is exactly what "redundant"
   means.
2. A **non-circular justification base**: operands are justified only against interactions this
   pass can never drop (those not recognizable as byte checks). Otherwise two identical checks
   could each justify the other and both would be dropped unsoundly.

Justification reuses `byteJustified` from `BusPairCancel.lean` (constant bytes, bus-fact slot bounds
from retained interactions, deep one-hot analysis on prime `p`). Runs after the cleanup fixpoint:
dropping a check also drops the finite-domain knowledge the enumeration passes derive from its raw
slot, so it must not starve them mid-loop. -/

namespace RedundantByteDrop

variable {p : ℕ}

/-! ## Recognizing pure byte-check interactions -/

/-- The operands whose byte-ness *implies* this interaction's acceptance (for any multiplicity):
    `some ops` for the self-check form `[x, x, 0, 1]` (`BusFacts.byteCheck`), the XOR-with-zero form
    `[x, 0, x, 1]` (`BusFacts.xorZeroCheck`), and the packed-pair form `[x, y, 0, 0]`
    (`BusFacts.bytePairBus` + `byteCheck`); `none` otherwise. -/
def byteCheckOperands? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (List (Expression p)) :=
  match bi.payload with
  | [e1, e2, e3, e4] =>
    if facts.byteCheck bi.busId && e1 == e2
        && e3.constValue? == some 0 && e4.constValue? == some 1 then
      some [e1]
    else if facts.xorZeroCheck bi.busId && e2.constValue? == some 0 && e1 == e3
        && e4.constValue? == some 1 then
      some [e1]
    else if facts.bytePairBus bi.busId && facts.byteCheck bi.busId
        && e3.constValue? == some 0 && e4.constValue? == some 0 then
      some [e1, e2]
    else none
  | _ => none

/-- A recognized byte check lives on a stateless bus. -/
theorem byteCheckOperands?_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (ops : List (Expression p))
    (h : byteCheckOperands? bs facts bi = some ops) : bs.isStateful bi.busId = false := by
  unfold byteCheckOperands? at h
  split at h
  · split_ifs at h with h1 h2 h3
    · exact (facts.byteCheck_sound bi.busId (by
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
        exact h1.1.1.1)).1
    · exact (facts.xorZeroCheck_sound bi.busId (by
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
        exact h2.1.1.1)).1
    · exact (facts.bytePairBus_sound bi.busId (by
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h3
        exact h3.1.1.1)).1
  · exact absurd h (by simp)

/-- If every recognized operand evaluates to a byte, the evaluated message is accepted. -/
theorem byteCheckOperands?_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (ops : List (Expression p))
    (h : byteCheckOperands? bs facts bi = some ops) (env : Variable → ZMod p)
    (hops : ∀ e ∈ ops, (e.eval env).val < 256) :
    bs.violatesConstraint (bi.eval env) = false := by
  obtain ⟨busId, mult, payload⟩ := bi
  unfold byteCheckOperands? at h
  split at h
  case h_2 => exact absurd h (by simp)
  case h_1 e1 e2 e3 e4 hpay =>
    simp only at hpay
    subst hpay
    split_ifs at h with h1 h2 h3
    · -- self-check form `[x, x, 0, 1]`
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
      obtain ⟨⟨⟨hfact, heq⟩, hz⟩, ho⟩ := h1
      obtain rfl : [e1] = ops := by simpa using h
      obtain rfl : e1 = e2 := eq_of_beq heq
      have hz' : e3.constValue? = some 0 := by simpa using hz
      have ho' : e4.constValue? = some 1 := by simpa using ho
      show bs.violatesConstraint
        { busId := busId, multiplicity := mult.eval env,
          payload := [e1.eval env, e1.eval env, e3.eval env, e4.eval env] } = false
      rw [e3.constValue?_sound 0 hz' env, e4.constValue?_sound 1 ho' env]
      exact ((facts.byteCheck_sound busId hfact).2.2 (e1.eval env) (mult.eval env)).2
        (hops e1 (by simp))
    · -- XOR-with-zero form `[x, 0, x, 1]`
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
      obtain ⟨⟨⟨hfact, hz⟩, heq⟩, ho⟩ := h2
      obtain rfl : [e1] = ops := by simpa using h
      obtain rfl : e1 = e3 := eq_of_beq heq
      have hz' : e2.constValue? = some 0 := by simpa using hz
      have ho' : e4.constValue? = some 1 := by simpa using ho
      show bs.violatesConstraint
        { busId := busId, multiplicity := mult.eval env,
          payload := [e1.eval env, e2.eval env, e1.eval env, e4.eval env] } = false
      rw [e2.constValue?_sound 0 hz' env, e4.constValue?_sound 1 ho' env]
      exact ((facts.xorZeroCheck_sound busId hfact).2 (e1.eval env) (mult.eval env)).2
        (hops e1 (by simp))
    · -- packed-pair form `[x, y, 0, 0]`
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h3
      obtain ⟨⟨⟨hpair, hfact⟩, hz⟩, ho⟩ := h3
      obtain rfl : [e1, e2] = ops := by simpa using h
      have hz' : e3.constValue? = some 0 := by simpa using hz
      have ho' : e4.constValue? = some 0 := by simpa using ho
      show bs.violatesConstraint
        { busId := busId, multiplicity := mult.eval env,
          payload := [e1.eval env, e2.eval env, e3.eval env, e4.eval env] } = false
      rw [e3.constValue?_sound 0 hz' env, e4.constValue?_sound 0 ho' env]
      refine ((facts.bytePairBus_sound busId hpair).2.2 (e1.eval env) (e2.eval env)
        (mult.eval env)).2 ⟨?_, ?_⟩
      · exact ((facts.byteCheck_sound busId hfact).2.2 (e1.eval env) (mult.eval env)).2
          (hops e1 (by simp))
      · exact ((facts.byteCheck_sound busId hfact).2.2 (e2.eval env) (mult.eval env)).2
          (hops e2 (by simp))

/-! ## The pass -/

/-- The justification base: the interactions this pass can never drop (not recognizable as byte
    checks). Justifying only against these makes the drop non-circular. -/
def byteDropBase (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (BusInteraction (Expression p)) :=
  cs.busInteractions.filter (fun bi => (byteCheckOperands? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized byte check whose operands are all byte-justified from
    the constraints and the justification base. -/
def byteDropKeep (bs : BusSemantics p) (facts : BusFacts p bs) (all : List (Expression p))
    (rest : List (BusInteraction (Expression p))) (bi : BusInteraction (Expression p)) : Bool :=
  match byteCheckOperands? bs facts bi with
  | some ops => !(ops.all (fun e => byteJustified (decide p.Prime) all bs facts rest e))
  | none => true

/-- Drop every stateless byte-check interaction whose operands are all byte-justified from the
    parts of the system this pass can never remove. -/
def redundantByteDropPass : VerifiedPassW p := fun cs bs facts =>
  ⟨cs.filterBus (byteDropKeep bs facts cs.algebraicConstraints (byteDropBase bs facts cs)), [],
   cs.filterBusEntailed_correct bs _
     (by
       intro bi _ hkf
       unfold byteDropKeep at hkf
       cases hro : byteCheckOperands? bs facts bi with
       | none => rw [hro] at hkf; exact absurd hkf (by simp)
       | some ops => exact byteCheckOperands?_stateless bs facts bi ops hro)
     (by
       intro bi hbimem hkf env hsat _
       unfold byteDropKeep at hkf
       cases hro : byteCheckOperands? bs facts bi with
       | none => rw [hro] at hkf; exact absurd hkf (by simp)
       | some ops =>
         rw [hro] at hkf
         have hjust : ops.all (fun e => byteJustified (decide p.Prime)
             cs.algebraicConstraints bs facts (byteDropBase bs facts cs) e) = true := by
           simpa using hkf
         refine byteCheckOperands?_accepted bs facts bi ops hro env (fun e he => ?_)
         refine byteJustified_sound (decide p.Prime) cs.algebraicConstraints bs facts
           (byteDropBase bs facts cs) e (fun h => of_decide_eq_true h)
           (List.all_eq_true.mp hjust e he) env
           (fun c hc => hsat.1 c hc) (fun bi' hbi' hmult => ?_)
         -- every justification-base interaction survives the filter, so `hsat` accepts it
         have hnone : byteCheckOperands? bs facts bi' = none := by
           have := (List.mem_filter.1 hbi').2
           simpa using this
         have hkeep : byteDropKeep bs facts cs.algebraicConstraints
             (byteDropBase bs facts cs) bi' = true := by
           unfold byteDropKeep
           rw [hnone]
         exact hsat.2 bi' (List.mem_filter.2 ⟨(List.mem_filter.1 hbi').1, hkeep⟩) hmult)⟩

end RedundantByteDrop
