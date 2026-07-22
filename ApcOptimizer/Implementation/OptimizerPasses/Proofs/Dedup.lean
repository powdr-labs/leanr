import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Correctness for the dense syntactic-duplicate removal pass

`DensePassCorrect` for `dedup` (`Dedup.lean`): dropping duplicate constraints and stateless
interactions leaves the satisfying set, stateful side effects and `admissible` unchanged, so
`env' = env` is the completeness witness. Proved for the reference `dedup` and transported to the
`dedupN` the pass runs along `dedupN_eq`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The active∧stateful *evaluated* message list is untouched (what dense `admissible` consults),
    stated over `denseBIEval` (`(denseBIEval bi denv).busId = bi.busId` is `rfl`). -/
theorem denseDedupStateless_evalFilter (bs : BusSemantics p) (denv : VarId → ZMod p) :
    ∀ (seen l : List (BusInteraction (DenseExpr p))),
      ((denseDedupStateless bs seen l).map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
        = (l.map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons b rest ih =>
    rw [denseDedupStateless]
    have hbus : (denseBIEval b denv).busId = b.busId := rfl
    split_ifs with h1 h2
    · simp only [List.map_cons, List.filter_cons, hbus, h1, ih]
    · -- dropped: its evaluated message fails the `isStateful` conjunct anyway
      rw [List.map_cons,
        List.filter_cons_of_neg (by
          have hf : bs.isStateful (denseBIEval b denv).busId = false := (by simpa using h1)
          simp [hf]), ih]
    · rw [List.map_cons,
        List.filter_cons_of_neg (by
          have hf : bs.isStateful (denseBIEval b denv).busId = false := (by simpa using h1)
          simp [hf]),
        List.map_cons,
        List.filter_cons_of_neg (by
          have hf : bs.isStateful (denseBIEval b denv).busId = false := (by simpa using h1)
          simp [hf]), ih]

/-- **Correctness of dedup.** Satisfaction, side effects and admissibility are all preserved, so
    `env' = env` witnesses completeness and no derivations arise. -/
theorem DenseConstraintSystem.dedup_denseCorrect {isInput : VarId → Bool}
    (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    DensePassCorrect isInput d (d.dedup bs) [] bs := by
  -- Satisfaction is preserved on the *same* environment.
  have hiff : ∀ denv, (d.dedup bs).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    simp only [DenseConstraintSystem.satisfies, DenseConstraintSystem.dedup]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨fun c hcm => hc c (List.mem_dedup.2 hcm), fun bi hbm => ?_⟩
      rcases denseDedupStateless_covers bs [] d.busInteractions bi hbm with hk | hs
      · exact hb bi hk
      · simp at hs
    · rintro ⟨hc, hb⟩
      exact ⟨fun c hcm => hc c (List.mem_dedup.1 hcm),
        fun bi hbm => hb bi (denseDedupStateless_subset bs [] d.busInteractions bi hbm)⟩
  -- Stateful side effects are unchanged (the stateful sublist is untouched).
  have hside : ∀ denv, (d.dedup bs).sideEffects bs denv = d.sideEffects bs denv := by
    intro denv
    simp only [DenseConstraintSystem.sideEffects, DenseConstraintSystem.dedup]
    rw [denseDedupStateless_statefulFilter bs [] d.busInteractions]
  -- Admissibility is unchanged (the evaluated active∧stateful message list is untouched).
  have hadm : ∀ denv, (d.dedup bs).admissible bs denv ↔ d.admissible bs denv := by
    intro denv
    unfold DenseConstraintSystem.admissible
    simp only [DenseConstraintSystem.dedup]
    rw [denseDedupStateless_evalFilter bs denv [] d.busInteractions]
  -- Output occurrences are input occurrences (dedup only drops).
  have hsub : ∀ i ∈ (d.dedup bs).occ, i ∈ d.occ := by
    intro i hi
    simp only [DenseConstraintSystem.occ, DenseConstraintSystem.dedup, List.mem_append,
      List.mem_flatMap] at hi ⊢
    rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
    · exact Or.inl ⟨c, List.mem_dedup.1 hc, hic⟩
    · exact Or.inr ⟨bi, denseDedupStateless_subset bs [] d.busInteractions bi hbi, hib⟩
  refine DensePassCorrect.ofEnvEq ?_ ?_ hsub ?_
  · -- soundness (`out.implies d`): same env, side effects equal
    intro denv hsat
    exact ⟨denv, (hiff denv).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · -- invariant preservation: kept interactions are a subset of the originals
    intro hgi denv hsat bi hbi
    refine hgi denv ((hiff denv).1 hsat) bi ?_
    simp only [DenseConstraintSystem.dedup] at hbi
    exact denseDedupStateless_subset bs [] d.busInteractions bi hbi
  · -- completeness (same env; admissibility/side effects unchanged)
    intro denv hadm' hsat
    exact ⟨(hiff denv).2 hsat, (hadm denv).2 hadm', by rw [hside]; exact BusState.equiv_refl _⟩

/-- The dense duplicate-removal pass (runs the hash-bucketed `dedupN`). -/
def denseDedupPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs _ d => d.dedupN bs)
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov => DenseConstraintSystem.dedupN_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun _ bs _ d _ => by
      dsimp only
      rw [DenseConstraintSystem.dedupN_eq]
      exact d.dedup_denseCorrect bs)

end ApcOptimizer.Dense
