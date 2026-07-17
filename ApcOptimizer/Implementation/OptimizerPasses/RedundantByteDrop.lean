import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancel
import ApcOptimizer.Implementation.OptimizerPasses.FlagFold
import ApcOptimizer.Implementation.OptimizerPasses.BytePack

set_option autoImplicit false

/-! # Redundant byte-check removal (C2)

After optimization, blocks keep stateless bitwise-lookup interactions whose *only* obligation is
"this operand is a byte" — the self-check, XOR-with-`0`/`255`, and packed-pair forms, all recognized
through the VM-neutral `BusFacts.byteXorSpec` (`byteCheckOperands?`). Many of their operands are
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

/-! ## Recognizing the NOT-form complement -/

/-- `255 − e` as an expression. -/
def complExpr (e : Expression p) : Expression p := .add (.const 255) (.mul (.const (-1)) e)

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment? Decided by folding
    `b − (255 − a)` to a constant and checking it is `0` (`normalize` collects the affine terms so a
    genuine complement cancels to the literal `0`). Used to recognize the NOT-form byte check
    `[a, 255, 255 − a, 1]` that `xorEqExtractPass` (C4b) + Gauss leave on the bus. -/
def isByteCompl (a b : Expression p) : Bool :=
  (Expression.add b (.mul (.const (-1)) (complExpr a))).normalize.constValue? == some 0

theorem isByteCompl_sound (a b : Expression p) (h : isByteCompl a b = true)
    (env : Variable → ZMod p) : b.eval env = 255 - a.eval env := by
  unfold isByteCompl at h
  have hc : (Expression.add b (.mul (.const (-1)) (complExpr a))).normalize.constValue? = some 0 := by
    simpa using h
  have h0 : (Expression.add b (.mul (.const (-1)) (complExpr a))).eval env = 0 := by
    have := Expression.constValue?_sound _ (0 : ZMod p) hc env
    rwa [Expression.normalize_eval] at this
  simp only [complExpr, Expression.eval] at h0
  linear_combination h0

/-! ## Recognizing pure byte-check interactions -/

/-- `255 − a` with no wraparound is the byte complement, hence `a`'s XOR with `255`. -/
private theorem val_255_sub {p : ℕ} (hp : 256 ≤ p) (a : ZMod p) (ha : a.val < 256) :
    (255 - a).val = Nat.xor a.val 255 := by
  haveI : NeZero p := ⟨by omega⟩
  have hle : a.val ≤ 255 := by omega
  have ha' : a = ((a.val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse a).symm
  have hcast : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  have hval : (255 - a).val = 255 - a.val := by
    calc (255 - a).val
        = ((255 : ZMod p) - ((a.val : ℕ) : ZMod p)).val := by rw [← ha']
      _ = (((255 - a.val : ℕ) : ZMod p)).val := by rw [Nat.cast_sub hle, hcast]
      _ = 255 - a.val := ZMod.val_natCast_of_lt (by omega)
  rw [hval]; exact (nat_xor_255 _ ha).symm

/-- The operands whose byte-ness *implies* this interaction's acceptance (for any multiplicity),
    recognized through the VM-neutral `byteXorSpec` (byte bound `256`). Decoding to `(op, o₁, o₂, r)`:
    for `op = xorOp` the self-check `o₁ = o₂`, `r = 0` (`[x, x, 0]`), the two XOR-with-zero mirrors
    (`o₂ = 0, o₁ = r` / `o₁ = 0, o₂ = r`), and the two NOT forms (`o₂ = 255, r = 255 − o₁` /
    `o₁ = 255, r = 255 − o₂`, when `256 ≤ p`); for `op = pairOp` the packed pair `r = 0`.
    `none` otherwise. -/
def byteCheckOperands? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (List (Expression p)) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | none => none
      | some (op, o1, o2, r) =>
        if op.constValue? == some spec.xorOp then
          if o1 == o2 && r.constValue? == some 0 then some [o1]
          else if o2.constValue? == some 0 && o1 == r then some [o1]
          else if o1.constValue? == some 0 && o2 == r then some [o2]
          else if decide (256 ≤ p) && o2.constValue? == some 255 && isByteCompl o1 r then some [o1]
          else if decide (256 ≤ p) && o1.constValue? == some 255 && isByteCompl o2 r then some [o2]
          else none
        else if op.constValue? == some spec.pairOp && r.constValue? == some 0 then some [o1, o2]
        else none
    else none

/-- A recognized byte check lives on a stateless bus. -/
theorem byteCheckOperands?_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (ops : List (Expression p))
    (h : byteCheckOperands? bs facts bi = some ops) : bs.isStateful bi.busId = false := by
  unfold byteCheckOperands? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    exact (facts.byteXorSpec_sound bi.busId spec hspec).1

/-- If every recognized operand evaluates to a byte, the evaluated message is accepted. -/
theorem byteCheckOperands?_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (ops : List (Expression p))
    (h : byteCheckOperands? bs facts bi = some ops) (env : Variable → ZMod p)
    (hops : ∀ e ∈ ops, (e.eval env).val < 256) :
    bs.violatesConstraint (bi.eval env) = false := by
  unfold byteCheckOperands? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i hb
      have hbound : spec.bound = 256 := of_decide_eq_true hb
      split at h
      · exact absurd h (by simp)
      · rename_i op o1 o2 r hdec
        have key := byteXorSpec_decode_iff bs facts spec bi hspec op o1 o2 r hdec env
        split_ifs at h with hxor h1 h2 h3 h4 h5 hpair
        · -- self-check: o₁ = o₂, r = 0
          obtain ⟨heq, hr0⟩ := by rw [Bool.and_eq_true] at h1; exact h1
          obtain rfl : [o1] = ops := by simpa using h
          obtain rfl : o1 = o2 := eq_of_beq heq
          have hopEv : op.eval env = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) env
          have hr : r.eval env = 0 := r.constValue?_sound 0 (by simpa using hr0) env
          refine (key.1 hopEv).mpr ⟨hbound ▸ hops o1 (by simp), hbound ▸ hops o1 (by simp), ?_⟩
          rw [hr, ZMod.val_zero]; exact (Nat.xor_self _).symm
        · -- XOR-with-zero: o₂ = 0, o₁ = r
          obtain ⟨hz, heq⟩ := by rw [Bool.and_eq_true] at h2; exact h2
          obtain rfl : [o1] = ops := by simpa using h
          obtain rfl : o1 = r := eq_of_beq heq
          have hopEv : op.eval env = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) env
          have ho2 : o2.eval env = 0 := o2.constValue?_sound 0 (by simpa using hz) env
          refine (key.1 hopEv).mpr ⟨hbound ▸ hops o1 (by simp), hbound ▸ ?_, ?_⟩
          · rw [ho2, ZMod.val_zero]; omega
          · rw [ho2, ZMod.val_zero]; exact (Nat.xor_zero _).symm
        · -- mirror XOR-with-zero: o₁ = 0, o₂ = r
          obtain ⟨hz, heq⟩ := by rw [Bool.and_eq_true] at h3; exact h3
          obtain rfl : [o2] = ops := by simpa using h
          obtain rfl : o2 = r := eq_of_beq heq
          have hopEv : op.eval env = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) env
          have ho1 : o1.eval env = 0 := o1.constValue?_sound 0 (by simpa using hz) env
          refine (key.1 hopEv).mpr ⟨hbound ▸ ?_, hbound ▸ hops o2 (by simp), ?_⟩
          · rw [ho1, ZMod.val_zero]; omega
          · rw [ho1, ZMod.val_zero]; exact (Nat.zero_xor _).symm
        · -- NOT-form: o₂ = 255, r = 255 − o₁
          obtain ⟨⟨hp, h255⟩, hcompl⟩ := by rw [Bool.and_eq_true, Bool.and_eq_true] at h4; exact h4
          obtain rfl : [o1] = ops := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hp
          have hopEv : op.eval env = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) env
          have ho2 : o2.eval env = 255 := o2.constValue?_sound 255 (by simpa using h255) env
          have hr : r.eval env = 255 - o1.eval env := isByteCompl_sound o1 r hcompl env
          have hob : (o1.eval env).val < 256 := hops o1 (by simp)
          have h255v : (255 : ZMod p).val = 255 := by
            have hc : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
            rw [← hc, ZMod.val_natCast_of_lt (by omega)]
          refine (key.1 hopEv).mpr ⟨hbound ▸ hob, hbound ▸ ?_, ?_⟩
          · rw [ho2, h255v]; omega
          · rw [hr, ho2, h255v, val_255_sub hple _ hob]
        · -- mirror NOT-form: o₁ = 255, r = 255 − o₂
          obtain ⟨⟨hp, h255⟩, hcompl⟩ := by rw [Bool.and_eq_true, Bool.and_eq_true] at h5; exact h5
          obtain rfl : [o2] = ops := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hp
          have hopEv : op.eval env = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) env
          have ho1 : o1.eval env = 255 := o1.constValue?_sound 255 (by simpa using h255) env
          have hr : r.eval env = 255 - o2.eval env := isByteCompl_sound o2 r hcompl env
          have hob : (o2.eval env).val < 256 := hops o2 (by simp)
          have h255v : (255 : ZMod p).val = 255 := by
            have hc : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
            rw [← hc, ZMod.val_natCast_of_lt (by omega)]
          refine (key.1 hopEv).mpr ⟨hbound ▸ ?_, hbound ▸ hob, ?_⟩
          · rw [ho1, h255v]; omega
          · rw [hr, ho1, h255v, val_255_sub hple _ hob]; exact Nat.xor_comm _ _
        · -- packed-pair: r = 0
          obtain ⟨hpc, hr0⟩ := by rw [Bool.and_eq_true] at hpair; exact hpair
          obtain rfl : [o1, o2] = ops := by simpa using h
          have hopEv : op.eval env = spec.pairOp :=
            op.constValue?_sound spec.pairOp (by simpa using hpc) env
          have hr : r.eval env = 0 := r.constValue?_sound 0 (by simpa using hr0) env
          exact (key.2 hopEv).mpr ⟨hbound ▸ hops o1 (by simp), hbound ▸ hops o2 (by simp), hr⟩
    · exact absurd h (by simp)

/-! ## The pass -/

/-- The justification base: the interactions this pass can never drop (not recognizable as byte
    checks). Justifying only against these makes the drop non-circular. -/
def byteDropBase (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (BusInteraction (Expression p)) :=
  cs.busInteractions.filter (fun bi => (byteCheckOperands? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized byte check whose operands are all byte-justified from
    the constraints and the justification base. -/
def byteDropKeep (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (all : List (Expression p))
    (rest : List (BusInteraction (Expression p))) (bi : BusInteraction (Expression p)) : Bool :=
  match byteCheckOperands? bs facts bi with
  | some ops => !(ops.all (fun e => byteJustified pw.isPrime all bs facts rest e))
  | none => true

/-- Drop every stateless byte-check interaction whose operands are all byte-justified from the
    parts of the system this pass can never remove. -/
def redundantByteDropPass (pw : PrimeWitness p) : VerifiedPassW p := fun cs bs facts =>
  ⟨cs.filterBus (byteDropKeep pw bs facts cs.algebraicConstraints (byteDropBase bs facts cs)), [],
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
         have hjust : ops.all (fun e => byteJustified pw.isPrime
             cs.algebraicConstraints bs facts (byteDropBase bs facts cs) e) = true := by
           simpa using hkf
         refine byteCheckOperands?_accepted bs facts bi ops hro env (fun e he => ?_)
         refine byteJustified_sound pw.isPrime cs.algebraicConstraints bs facts
           (byteDropBase bs facts cs) e (fun h => pw.correct h)
           (List.all_eq_true.mp hjust e he) env
           (fun c hc => hsat.1 c hc) (fun bi' hbi' hmult => ?_)
         -- every justification-base interaction survives the filter, so `hsat` accepts it
         have hnone : byteCheckOperands? bs facts bi' = none := by
           have := (List.mem_filter.1 hbi').2
           simpa using this
         have hkeep : byteDropKeep pw bs facts cs.algebraicConstraints
             (byteDropBase bs facts cs) bi' = true := by
           unfold byteDropKeep
           rw [hnone]
         exact hsat.2 bi' (List.mem_filter.2 ⟨(List.mem_filter.1 hbi').1, hkeep⟩) hmult)⟩

end RedundantByteDrop
