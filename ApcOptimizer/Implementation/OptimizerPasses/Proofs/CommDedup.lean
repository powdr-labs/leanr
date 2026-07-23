import ApcOptimizer.Implementation.OptimizerPasses.CommDedup
import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Soundness for the commutativity-aware constraint dedup (`Proofs/CommDedup.lean`)

`denseCommDedupPass` drops a constraint only when an earlier-kept one is `denseCommEq` to it, and
`denseCommEq` implies equal evaluation (`denseCommEq_eval`), so the kept constraint pins the dropped
one to zero on any satisfying assignment. The output is thus a constraint subset that is
satisfaction-equivalent to the input, with bus interactions untouched. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `denseCommEq` is reflexive. -/
theorem denseCommEq_refl (e : DenseExpr p) : denseCommEq e e = true := by
  induction e with
  | const n => simp [denseCommEq]
  | var i => simp [denseCommEq]
  | add a b iha ihb => simp [denseCommEq, iha, ihb]
  | mul a b iha ihb => simp [denseCommEq, iha, ihb]

/-- A `denseCommEq` match implies equal evaluation under every assignment. -/
theorem denseCommEq_eval : ∀ {e1 e2 : DenseExpr p}, denseCommEq e1 e2 = true →
    ∀ denv, e1.eval denv = e2.eval denv := by
  intro e1
  induction e1 with
  | const m =>
    intro e2 h denv; cases e2 <;> simp_all [denseCommEq, DenseExpr.eval]
  | var i =>
    intro e2 h denv; cases e2 <;> simp_all [denseCommEq, DenseExpr.eval]
  | add a b iha ihb =>
    intro e2 h denv
    cases e2 with
    | const n => simp [denseCommEq] at h
    | var j => simp [denseCommEq] at h
    | mul c d => simp [denseCommEq] at h
    | add c d =>
      simp only [denseCommEq, Bool.or_eq_true, Bool.and_eq_true] at h
      simp only [DenseExpr.eval]
      rcases h with ⟨hac, hbd⟩ | ⟨had, hbc⟩
      · rw [iha hac denv, ihb hbd denv]
      · rw [iha had denv, ihb hbc denv, add_comm]
  | mul a b iha ihb =>
    intro e2 h denv
    cases e2 with
    | const n => simp [denseCommEq] at h
    | var j => simp [denseCommEq] at h
    | add c d => simp [denseCommEq] at h
    | mul c d =>
      simp only [denseCommEq, Bool.or_eq_true, Bool.and_eq_true] at h
      simp only [DenseExpr.eval]
      rcases h with ⟨hac, hbd⟩ | ⟨had, hbc⟩
      · rw [iha hac denv, ihb hbd denv]
      · rw [iha had denv, ihb hbc denv, mul_comm]

/-- Every kept constraint was in the input. -/
theorem denseCommDedupGo_subset (l : List (DenseExpr p)) :
    ∀ (seen : List (DenseExpr p)), ∀ c ∈ denseCommDedupGo seen l, c ∈ l := by
  induction l with
  | nil => intro seen c h; simp [denseCommDedupGo] at h
  | cons b rest ih =>
    intro seen c h
    rw [denseCommDedupGo] at h
    by_cases hs : (seen.any (fun s => denseCommEq s b)) = true
    · rw [if_pos hs] at h
      exact List.mem_cons_of_mem _ (ih seen c h)
    · rw [if_neg hs] at h
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (b :: seen) c h')

/-- Every input constraint is `denseCommEq`-matched by a kept one or by a `seen` entry. -/
theorem denseCommDedupGo_covers (l : List (DenseExpr p)) :
    ∀ (seen : List (DenseExpr p)), ∀ c ∈ l,
      (∃ c' ∈ denseCommDedupGo seen l, denseCommEq c' c = true) ∨
      (∃ s ∈ seen, denseCommEq s c = true) := by
  induction l with
  | nil => intro seen c h; simp at h
  | cons b rest ih =>
    intro seen c h
    rw [denseCommDedupGo]
    by_cases hs : (seen.any (fun s => denseCommEq s b)) = true
    · rw [if_pos hs]
      rcases List.mem_cons.1 h with rfl | h'
      · obtain ⟨s, hsmem, hcomm⟩ := List.any_eq_true.1 hs
        exact Or.inr ⟨s, hsmem, hcomm⟩
      · exact ih seen c h'
    · rw [if_neg hs]
      rcases List.mem_cons.1 h with rfl | h'
      · exact Or.inl ⟨c, List.mem_cons_self .., denseCommEq_refl c⟩
      · rcases ih (b :: seen) c h' with ⟨c', hc'mem, hcomm⟩ | ⟨s, hsmem, hcomm⟩
        · exact Or.inl ⟨c', List.mem_cons_of_mem _ hc'mem, hcomm⟩
        · rcases List.mem_cons.1 hsmem with rfl | hs'
          · exact Or.inl ⟨s, List.mem_cons_self .., hcomm⟩
          · exact Or.inr ⟨s, hs', hcomm⟩

/-- `commDedup` preserves coverage (constraints are a subset, bus untouched). -/
theorem DenseConstraintSystem.commDedup_covered {reg : VarRegistry} {d : DenseConstraintSystem p}
    (hc : d.CoveredBy reg) : d.commDedup.CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hc
  exact ⟨fun e he => hac e (denseCommDedupGo_subset d.algebraicConstraints [] e he), hbi⟩

/-- `commDedup`'s occurrences are a subset of the input's (constraints subset, bus identical). -/
theorem DenseConstraintSystem.commDedup_occ_subset (d : DenseConstraintSystem p) :
    ∀ i ∈ d.commDedup.occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.commDedup, List.mem_append,
    List.mem_flatMap] at hi ⊢
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · exact Or.inl ⟨c, denseCommDedupGo_subset d.algebraicConstraints [] c hc, hic⟩
  · exact Or.inr ⟨bi, hbi, hib⟩

/-- `commDedup` is satisfaction-equivalent: dropped constraints are pinned to zero by the kept
    `denseCommEq`-matching one, and kept constraints are a subset. -/
theorem DenseConstraintSystem.commDedup_satisfies_iff (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (denv : VarId → ZMod p) :
    d.commDedup.satisfies bs denv ↔ d.satisfies bs denv := by
  simp only [DenseConstraintSystem.satisfies, DenseConstraintSystem.commDedup]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hcmem => ?_, hb⟩
    rcases denseCommDedupGo_covers d.algebraicConstraints [] c hcmem with
      ⟨c', hc'mem, hcomm⟩ | ⟨s, hsmem, _⟩
    · exact (denseCommEq_eval hcomm denv) ▸ hc c' hc'mem
    · simp at hsmem
  · rintro ⟨hc, hb⟩
    exact ⟨fun c hcmem => hc c (denseCommDedupGo_subset d.algebraicConstraints [] c hcmem), hb⟩

/-- `commDedup` maintains `DensePassCorrect`: bus interactions (hence side effects and
    admissibility) are unchanged, and satisfaction is equivalent. -/
theorem DenseConstraintSystem.commDedup_correct (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d d.commDedup [] bs := by
  refine DensePassCorrect.ofEnvEq ?_ ?_ (d.commDedup_occ_subset) ?_
  · intro denv hsat
    exact ⟨denv, (d.commDedup_satisfies_iff bs denv).1 hsat, BusState.equiv_refl _⟩
  · intro hinv denv hsat bi hbi
    exact hinv denv ((d.commDedup_satisfies_iff bs denv).1 hsat) bi hbi
  · intro denv hadm hsat
    exact ⟨(d.commDedup_satisfies_iff bs denv).2 hsat, hadm, BusState.equiv_refl _⟩

/-- The commutativity-aware constraint-dedup pass. -/
def denseCommDedupPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => d.commDedup)
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov => DenseConstraintSystem.commDedup_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => DenseConstraintSystem.commDedup_correct reg bs d)

end ApcOptimizer.Dense
