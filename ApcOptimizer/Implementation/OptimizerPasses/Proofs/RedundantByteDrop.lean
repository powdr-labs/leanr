import ApcOptimizer.Implementation.OptimizerPasses.RedundantByteDrop
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusPairCancelJustify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagFoldDrops

set_option autoImplicit false

/-! # Soundness for the dense redundant byte-check drop

`DensePassCorrect` — over `VarId → ZMod p` — for the redundant byte-check dropper
(`RedundantByteDrop.lean`). Every dropped interaction is a recognised byte check whose operands are
all byte-justified from the non-circular base (`denseByteDropBase`), hence accepted under every
assignment satisfying the filtered system. Built via `denseFilterBusEntailed`
(`Proofs/FlagFoldDrops.lean`) and `denseByteJustified_sound` (`Proofs/BusPairCancelJustify.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A recognized byte check lives on a stateless bus. -/
theorem denseByteCheckOperands?_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (ops : List (DenseExpr p))
    (h : denseByteCheckOperands? bs facts bi = some ops) : bs.isStateful bi.busId = false := by
  grind [denseByteCheckOperands?, BusFacts.byteXorSpec_sound]

/-- If every recognized operand evaluates to a byte, the evaluated message is accepted. -/
theorem denseByteCheckOperands?_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (ops : List (DenseExpr p))
    (h : denseByteCheckOperands? bs facts bi = some ops) (denv : VarId → ZMod p)
    (hops : ∀ e ∈ ops, (e.eval denv).val < 256) :
    bs.violatesConstraint (denseBIEval bi denv) = false := by
  unfold denseByteCheckOperands? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i hb
      have hbound : spec.bound = 256 := of_decide_eq_true hb
      split at h
      · exact absurd h (by simp)
      · rename_i op o1 o2 r hdec
        have key := denseByteXorSpec_decode_iff bs facts spec bi hspec op o1 o2 r hdec denv
        split_ifs at h with hxor h1 h2 h3 h4 h5 hor hor1 hor2 hpair
        · -- self-check: o₁ = o₂, r = 0
          obtain ⟨heq, hr0⟩ := by rw [Bool.and_eq_true] at h1; exact h1
          obtain rfl : [o1] = ops := by simpa using h
          obtain rfl : o1 = o2 := eq_of_beq heq
          have hopEv : op.eval denv = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) denv
          have hr : r.eval denv = 0 := r.constValue?_sound 0 (by simpa using hr0) denv
          refine (key.1 hopEv).mpr ⟨hbound ▸ hops o1 (by simp), hbound ▸ hops o1 (by simp), ?_⟩
          rw [hr, ZMod.val_zero]; exact (Nat.xor_self _).symm
        · -- XOR-with-zero: o₂ = 0, o₁ = r
          obtain ⟨hz, heq⟩ := by rw [Bool.and_eq_true] at h2; exact h2
          obtain rfl : [o1] = ops := by simpa using h
          obtain rfl : o1 = r := eq_of_beq heq
          have hopEv : op.eval denv = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) denv
          have ho2 : o2.eval denv = 0 := o2.constValue?_sound 0 (by simpa using hz) denv
          refine (key.1 hopEv).mpr ⟨hbound ▸ hops o1 (by simp), hbound ▸ ?_, ?_⟩
          · rw [ho2, ZMod.val_zero]; omega
          · rw [ho2, ZMod.val_zero]; exact (Nat.xor_zero _).symm
        · -- mirror XOR-with-zero: o₁ = 0, o₂ = r
          obtain ⟨hz, heq⟩ := by rw [Bool.and_eq_true] at h3; exact h3
          obtain rfl : [o2] = ops := by simpa using h
          obtain rfl : o2 = r := eq_of_beq heq
          have hopEv : op.eval denv = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) denv
          have ho1 : o1.eval denv = 0 := o1.constValue?_sound 0 (by simpa using hz) denv
          refine (key.1 hopEv).mpr ⟨hbound ▸ ?_, hbound ▸ hops o2 (by simp), ?_⟩
          · rw [ho1, ZMod.val_zero]; omega
          · rw [ho1, ZMod.val_zero]; exact (Nat.zero_xor _).symm
        · -- NOT-form: o₂ = 255, r = 255 − o₁
          obtain ⟨⟨hp, h255⟩, hcompl⟩ := by rw [Bool.and_eq_true, Bool.and_eq_true] at h4; exact h4
          obtain rfl : [o1] = ops := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hp
          have hopEv : op.eval denv = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) denv
          have ho2 : o2.eval denv = 255 := o2.constValue?_sound 255 (by simpa using h255) denv
          have hr : r.eval denv = 255 - o1.eval denv := denseIsByteCompl_sound o1 r hcompl denv
          have hob : (o1.eval denv).val < 256 := hops o1 (by simp)
          have h255v : (255 : ZMod p).val = 255 := val_255 hple
          refine (key.1 hopEv).mpr ⟨hbound ▸ hob, hbound ▸ ?_, ?_⟩
          · rw [ho2, h255v]; omega
          · rw [hr, ho2, h255v, val_255_sub hple _ hob]
        · -- mirror NOT-form: o₁ = 255, r = 255 − o₂
          obtain ⟨⟨hp, h255⟩, hcompl⟩ := by rw [Bool.and_eq_true, Bool.and_eq_true] at h5; exact h5
          obtain rfl : [o2] = ops := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hp
          have hopEv : op.eval denv = spec.xorOp :=
            op.constValue?_sound spec.xorOp (by simpa using hxor) denv
          have ho1 : o1.eval denv = 255 := o1.constValue?_sound 255 (by simpa using h255) denv
          have hr : r.eval denv = 255 - o2.eval denv := denseIsByteCompl_sound o2 r hcompl denv
          have hob : (o2.eval denv).val < 256 := hops o2 (by simp)
          have h255v : (255 : ZMod p).val = 255 := val_255 hple
          refine (key.1 hopEv).mpr ⟨hbound ▸ ?_, hbound ▸ hob, ?_⟩
          · rw [ho1, h255v]; omega
          · rw [hr, ho1, h255v, val_255_sub hple _ hob]; exact Nat.xor_comm _ _
        · -- OR identity: o₂ = 0, o₁ = r
          obtain ⟨hz, heq⟩ := by rw [Bool.and_eq_true] at hor1; exact hor1
          obtain rfl : [o1] = ops := by simpa using h
          obtain rfl : o1 = r := eq_of_beq heq
          cases hoo : spec.orOp with
          | none => rw [hoo] at hor; simp [Option.any] at hor
          | some oop =>
            rw [hoo] at hor
            simp only [Option.any] at hor
            have hopEv : op.eval denv = oop := op.constValue?_sound oop (by simpa using hor) denv
            have keyOr := (denseByteBoolSound_decode_iff bs facts spec bi hspec op o1 o2 o1 hdec denv).1
              oop hoo hopEv
            have ho2 : o2.eval denv = 0 := o2.constValue?_sound 0 (by simpa using hz) denv
            refine keyOr.mpr ⟨hbound ▸ hops o1 (by simp), hbound ▸ ?_, ?_⟩
            · rw [ho2, ZMod.val_zero]; omega
            · rw [ho2, ZMod.val_zero]; simp
        · -- mirror OR identity: o₁ = 0, o₂ = r
          obtain ⟨hz, heq⟩ := by rw [Bool.and_eq_true] at hor2; exact hor2
          obtain rfl : [o2] = ops := by simpa using h
          obtain rfl : o2 = r := eq_of_beq heq
          cases hoo : spec.orOp with
          | none => rw [hoo] at hor; simp [Option.any] at hor
          | some oop =>
            rw [hoo] at hor
            simp only [Option.any] at hor
            have hopEv : op.eval denv = oop := op.constValue?_sound oop (by simpa using hor) denv
            have keyOr := (denseByteBoolSound_decode_iff bs facts spec bi hspec op o1 o2 o2 hdec denv).1
              oop hoo hopEv
            have ho1 : o1.eval denv = 0 := o1.constValue?_sound 0 (by simpa using hz) denv
            refine keyOr.mpr ⟨hbound ▸ ?_, hbound ▸ hops o2 (by simp), ?_⟩
            · rw [ho1, ZMod.val_zero]; omega
            · rw [ho1, ZMod.val_zero]; simp
        · -- packed-pair: r = 0
          obtain ⟨hpc, hr0⟩ := by rw [Bool.and_eq_true] at hpair; exact hpair
          obtain rfl : [o1, o2] = ops := by simpa using h
          have hopEv : op.eval denv = spec.pairOp :=
            op.constValue?_sound spec.pairOp (by simpa using hpc) denv
          have hr : r.eval denv = 0 := r.constValue?_sound 0 (by simpa using hr0) denv
          exact (key.2 hopEv).mpr ⟨hbound ▸ hops o1 (by simp), hbound ▸ hops o2 (by simp), hr⟩
    · exact absurd h (by simp)

/-- Every dropped interaction is a recognised byte check whose operands are all byte-justified from
    the retained base, so it is accepted under every assignment satisfying the filtered system. -/
theorem denseRedundantByteDropF_correct (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (isInput : VarId → Bool) (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d (denseRedundantByteDropF pw bs facts d) [] bs := by
  unfold denseRedundantByteDropF
  refine DensePassCorrect.denseFilterBusEntailed d bs isInput
    (denseByteDropKeep pw bs facts d.algebraicConstraints (denseByteDropBase bs facts d)) ?_ ?_
  · intro bi _ hkf
    unfold denseByteDropKeep at hkf
    cases hro : denseByteCheckOperands? bs facts bi with
    | none => rw [hro] at hkf; exact absurd hkf (by simp)
    | some ops => exact denseByteCheckOperands?_stateless bs facts bi ops hro
  · intro bi _ hkf denv hsat _
    unfold denseByteDropKeep at hkf
    cases hro : denseByteCheckOperands? bs facts bi with
    | none => rw [hro] at hkf; exact absurd hkf (by simp)
    | some ops =>
      rw [hro] at hkf
      have hjust : ops.all (fun e => denseByteJustified 256 pw.isPrime
          d.algebraicConstraints bs facts (denseByteDropBase bs facts d) e) = true := by
        simpa using hkf
      refine denseByteCheckOperands?_accepted bs facts bi ops hro denv (fun e he => ?_)
      refine denseByteJustified_sound 256 pw.isPrime d.algebraicConstraints bs facts
        (denseByteDropBase bs facts d) e (fun h => pw.correct h)
        (List.all_eq_true.mp hjust e he) denv
        (fun c hc => hsat.1 c hc) (fun bi' hbi' hmult => ?_)
      -- every justification-base interaction survives the filter, so `hsat` accepts it
      have hnone : denseByteCheckOperands? bs facts bi' = none := by
        have := (List.mem_filter.1 hbi').2
        simpa using this
      have hkeep : denseByteDropKeep pw bs facts d.algebraicConstraints
          (denseByteDropBase bs facts d) bi' = true := by
        unfold denseByteDropKeep
        rw [hnone]
      exact hsat.2 bi' (List.mem_filter.2 ⟨(List.mem_filter.1 hbi').1, hkeep⟩) hmult

/-- The dense redundant byte-check drop pass; transform `denseRedundantByteDropF`
    (`RedundantByteDrop.lean`). -/
def denseRedundantByteDropPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d => denseRedundantByteDropF pw bs facts d)
    (fun _ _ _ => [])
    (fun _ bs facts d hcov => by
      unfold denseRedundantByteDropF
      exact DenseConstraintSystem.filterBus_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseRedundantByteDropF_correct pw bs facts reg.isInput d)

end ApcOptimizer.Dense
