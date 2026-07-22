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
  unfold denseByteCheckOperands? at h
  cases hc : denseByteShape? denseCmpFolded bs facts bi with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some t =>
    obtain ⟨sh, spec, o1, o2⟩ := t
    exact (denseByteShape?_sound bs facts denseCmpFolded_sound bi sh spec o1 o2 hc).1

/-- If every recognized operand evaluates to a byte, the evaluated message is accepted. -/
theorem denseByteCheckOperands?_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (ops : List (DenseExpr p))
    (h : denseByteCheckOperands? bs facts bi = some ops) (denv : VarId → ZMod p)
    (hops : ∀ e ∈ ops, (e.eval denv).val < 256) :
    bs.violatesConstraint (denseBIEval bi denv) = false := by
  unfold denseByteCheckOperands? at h
  cases hc : denseByteShape? denseCmpFolded bs facts bi with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some t =>
    obtain ⟨sh, spec, o1, o2⟩ := t
    rw [hc] at h
    obtain rfl : sh.operands o1 o2 = ops := by simpa using h
    exact ((denseByteShape?_sound bs facts denseCmpFolded_sound bi sh spec o1 o2 hc).2.2
      denv).mpr hops

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
