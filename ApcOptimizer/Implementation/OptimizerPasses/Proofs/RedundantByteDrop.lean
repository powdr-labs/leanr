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
(`Proofs/FlagFoldDrops.lean`) and `denseByteJustifiedW_sound` (`Proofs/BusPairCancelJustify.lean`),
fed the per-variable bucket indexes built once per invocation. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Soundness of the per-variable bucket index: every looked-up item was indexed -/

/-- Inserting `a` (already in `S`) under any variable list preserves "every bucket value is in
    `S`". -/
theorem denseVarBucketAdd_mem {α : Type} {S : List α} (a : α) (ha : a ∈ S) :
    ∀ (vs : List VarId) (m : Std.HashMap VarId (List α)),
      (∀ x, ∀ b ∈ m.getD x [], b ∈ S) →
      ∀ x, ∀ b ∈ (denseVarBucketAdd m vs a).getD x [], b ∈ S := by
  intro vs
  induction vs with
  | nil => intro m hm; simpa [denseVarBucketAdd] using hm
  | cons y rest ih =>
    intro m hm
    have hstep : ∀ x, ∀ b ∈ (m.insert y (a :: m.getD y [])).getD x [], b ∈ S := by
      intro x b hb
      by_cases hxy : y = x
      · subst hxy
        rw [Std.HashMap.getD_insert_self] at hb
        rcases List.mem_cons.1 hb with h | h
        · exact h ▸ ha
        · exact hm y b h
      · rw [Std.HashMap.getD_insert, if_neg (by simpa using hxy)] at hb
        exact hm x b hb
    have := ih (m.insert y (a :: m.getD y [])) hstep
    simpa [denseVarBucketAdd, List.foldl_cons] using this

/-- Every item returned by a bucket lookup was one of the indexed items. -/
theorem denseVarBucket_mem {α : Type} (varsOf : α → List VarId) (items : List α) :
    ∀ x, ∀ a ∈ denseVarBucketLookup (denseVarBucket varsOf items) x, a ∈ items := by
  unfold denseVarBucketLookup denseVarBucket
  induction items with
  | nil =>
    intro x a ha; simp only [List.foldr_nil, Std.HashMap.getD_empty, List.not_mem_nil] at ha
  | cons c rest ih =>
    intro x a ha
    rw [List.foldr_cons] at ha
    exact denseVarBucketAdd_mem c (List.mem_cons_self ..) ((varsOf c).eraseDups)
      (List.foldr (fun a m => denseVarBucketAdd m ((varsOf a).eraseDups) a) ∅ rest)
      (fun x' b hb => List.mem_cons_of_mem _ (ih x' b hb)) x a ha

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
    (denseByteDropKeepW pw bs facts (d.algebraicConstraints.filter DenseExpr.isSingleVar)
      (denseVarBucketLookup (denseVarBucket DenseExpr.vars d.algebraicConstraints))
      (denseVarBucketLookup (denseVarBucket denseBIVars (denseByteDropBase bs facts d)))) ?_ ?_
  · intro bi _ hkf
    unfold denseByteDropKeepW at hkf
    cases hro : denseByteCheckOperands? bs facts bi with
    | none => rw [hro] at hkf; exact absurd hkf (by simp)
    | some ops => exact denseByteCheckOperands?_stateless bs facts bi ops hro
  · intro bi _ hkf denv hsat _
    unfold denseByteDropKeepW at hkf
    cases hro : denseByteCheckOperands? bs facts bi with
    | none => rw [hro] at hkf; exact absurd hkf (by simp)
    | some ops =>
      rw [hro] at hkf
      have hjust : ops.all (fun e => denseByteJustifiedW 256 pw.isPrime
          (d.algebraicConstraints.filter DenseExpr.isSingleVar)
          (denseVarBucketLookup (denseVarBucket DenseExpr.vars d.algebraicConstraints))
          bs facts
          (denseVarBucketLookup (denseVarBucket denseBIVars (denseByteDropBase bs facts d)))
          (fun _ => []) e) = true := by
        simpa using hkf
      -- every justification-base interaction survives the filter, so `hsat` accepts it
      have hbusbase : ∀ bi' ∈ denseByteDropBase bs facts d,
          (denseBIEval bi' denv).multiplicity ≠ 0 →
          bs.violatesConstraint (denseBIEval bi' denv) = false := by
        intro bi' hbi' hmult
        have hnone : denseByteCheckOperands? bs facts bi' = none := by
          have h := (List.mem_filter.1 hbi').2
          rw [Option.isNone_iff_eq_none] at h
          simpa using h
        have hkeep : denseByteDropKeepW pw bs facts
            (d.algebraicConstraints.filter DenseExpr.isSingleVar)
            (denseVarBucketLookup (denseVarBucket DenseExpr.vars d.algebraicConstraints))
            (denseVarBucketLookup (denseVarBucket denseBIVars (denseByteDropBase bs facts d)))
            bi' = true := by
          unfold denseByteDropKeepW; rw [hnone]
        exact hsat.2 bi' (List.mem_filter.2 ⟨(List.mem_filter.1 hbi').1, hkeep⟩) hmult
      refine denseByteCheckOperands?_accepted bs facts bi ops hro denv (fun e he => ?_)
      exact denseByteJustifiedW_sound 256 pw.isPrime d.algebraicConstraints
        (d.algebraicConstraints.filter DenseExpr.isSingleVar)
        (denseVarBucketLookup (denseVarBucket DenseExpr.vars d.algebraicConstraints))
        bs facts (denseByteDropBase bs facts d)
        (denseVarBucketLookup (denseVarBucket denseBIVars (denseByteDropBase bs facts d)))
        (fun _ => []) e
        (fun h => pw.correct h)
        (fun c hc => List.mem_of_mem_filter hc)
        (fun x c hc => denseVarBucket_mem DenseExpr.vars d.algebraicConstraints x c hc)
        (fun v bi'' hbi'' =>
          denseVarBucket_mem denseBIVars (denseByteDropBase bs facts d) v bi'' hbi'')
        (fun _ bi'' hbi'' => absurd hbi'' (by simp))
        (List.all_eq_true.mp hjust e he) denv
        (fun c hc => hsat.1 c hc) hbusbase

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
