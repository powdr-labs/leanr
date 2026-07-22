import ApcOptimizer.Implementation.OptimizerPasses.CarryBranch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FactBounds

set_option autoImplicit false

/-! # Correctness for the dense carry-branch resolution (`CarryBranch.lean`). Value bounds are
consumed through `denseBuild_sound` (`Proofs/FactBounds.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Two-sided interval certificate -/

/-- The term sum decomposes as `P − N` with `P.val ≤ maxPos`, `N.val ≤ maxNeg`. -/
theorem denseSplitSum_val (B : Std.HashMap VarId Nat)
    (terms : List (VarId × ZMod p)) (mp mn : Nat)
    (h : denseSplitSumMax B terms = some (mp, mn)) (hmp : mp < p) (hmn : mn < p)
    (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    ∃ P N : ZMod p, (terms.map (fun t => t.2 * denv t.1)).sum = P - N ∧
      P.val ≤ mp ∧ N.val ≤ mn := by
  induction terms generalizing mp mn with
  | nil =>
      simp only [denseSplitSumMax, Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨0, 0, by simp, ?_, ?_⟩ <;> simp [← h.1, ← h.2]
  | cons t rest ih =>
      obtain ⟨v, a⟩ := t
      rw [denseSplitSumMax] at h
      split at h
      case _ bound acc hBd hrest =>
        obtain ⟨mp', mn'⟩ := acc
        have hv : (denv v).val < bound := hB v bound hBd
        split_ifs at h with hb1 hcmp
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨P', N', hsum', hP'le, hN'le⟩ := ih mp' mn' hrest (by omega) hmn
          have hle : a.val * (denv v).val ≤ a.val * (bound - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have hheadval : (a * denv v).val = a.val * (denv v).val :=
            ZMod.val_mul_of_lt (by omega)
          have haddlt : (a * denv v).val + P'.val < p := by rw [hheadval]; omega
          refine ⟨a * denv v + P', N', ?_, ?_, hN'le⟩
          · simp only [List.map_cons, List.sum_cons, hsum']; ring
          · rw [ZMod.val_add_of_lt haddlt, hheadval]; omega
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨P', N', hsum', hP'le, hN'le⟩ := ih mp' mn' hrest hmp (by omega)
          have hle : (-a).val * (denv v).val ≤ (-a).val * (bound - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have hheadval : ((-a) * denv v).val = (-a).val * (denv v).val :=
            ZMod.val_mul_of_lt (by omega)
          have haddlt : ((-a) * denv v).val + N'.val < p := by rw [hheadval]; omega
          refine ⟨P', (-a) * denv v + N', ?_, hP'le, ?_⟩
          · simp only [List.map_cons, List.sum_cons, hsum']; ring
          · rw [ZMod.val_add_of_lt haddlt, hheadval]; omega
      case _ => exact absurd h (by simp)

/-- An affine form whose bounded value interval stays strictly inside `(0, p)` never vanishes. -/
theorem denseLinNeverZeroSplit (B : Std.HashMap VarId Nat) (l : DenseLinExpr p) (mp mn : Nat)
    (hp : 0 < p) (h : denseSplitSumMax B l.terms = some (mp, mn))
    (hlo : mn < l.const.val) (hhi : l.const.val + mp < p)
    (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    l.eval denv ≠ 0 := by
  intro h0
  haveI : NeZero p := ⟨hp.ne'⟩
  have hcp : l.const.val < p := ZMod.val_lt l.const
  obtain ⟨P, N, hsum, hPle, hNle⟩ :=
    denseSplitSum_val B l.terms mp mn h (by omega) (by omega) denv hB
  have hPN : N = l.const + P := by
    rw [DenseLinExpr.eval, hsum] at h0
    linear_combination -h0
  have hval : (l.const + P).val = l.const.val + P.val :=
    ZMod.val_add_of_lt (by omega)
  rw [hPN, hval] at hNle
  omega

/-- The interval condition on one concrete normalized form is a sound never-zero certificate. -/
theorem denseIntervalCert_sound (hp : 0 < p) (B : Std.HashMap VarId Nat) (l : DenseLinExpr p)
    (h : denseIntervalCert B l = true) (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    l.eval denv ≠ 0 := by
  grind [denseIntervalCert, denseLinNeverZeroSplit]

/-- Checked never-zero certificate for an expression (over the candidate rescalings). -/
theorem denseNeverZeroB_sound (hp : 0 < p) (B : Std.HashMap VarId Nat) (e : DenseExpr p)
    (h : denseNeverZeroB B e = true) (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    e.eval denv ≠ 0 := by
  unfold denseNeverZeroB at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hl
    rw [List.any_eq_true] at h
    obtain ⟨k, _, hcert⟩ := h
    intro h0
    have hs : ((l.norm.scale k).norm).eval denv = 0 := by
      rw [DenseLinExpr.norm_eval, DenseLinExpr.scale_eval, DenseLinExpr.norm_eval,
          ← denseLinearize_eval e l hl denv, h0, mul_zero]
    exact denseIntervalCert_sound hp B _ hcert denv hB hs

/-- The resolution is an *equivalence* on satisfying assignments: with the bounds valid and `p`
    prime, `f·g = 0 ↔ f = 0` whenever `g` is certified never-zero. -/
theorem denseResolveExpr_eval_iff [Fact p.Prime] (B : Std.HashMap VarId Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    (denseResolveExpr B e).eval denv = 0 ↔ e.eval denv = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction e with
  | mul f g ihf ihg =>
      simp only [denseResolveExpr]
      split_ifs with h1 h2
      · have hg : g.eval denv ≠ 0 := denseNeverZeroB_sound hp B g h1 denv hB
        refine ihf.trans ?_
        show f.eval denv = 0 ↔ f.eval denv * g.eval denv = 0
        exact ⟨fun h => by rw [h, zero_mul], fun h => (mul_eq_zero.mp h).resolve_right hg⟩
      · have hf : f.eval denv ≠ 0 := denseNeverZeroB_sound hp B f h2 denv hB
        refine ihg.trans ?_
        show g.eval denv = 0 ↔ f.eval denv * g.eval denv = 0
        exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hf⟩
      · exact Iff.rfl
  | const n => exact Iff.rfl
  | var x => exact Iff.rfl
  | add a b iha ihb => exact Iff.rfl

/-! ## The pass correctness -/

/-- Carry-branch correctness: the `denseResolveExpr` rewrite preserves the satisfying set exactly;
    value bounds hold for every satisfying assignment via `denseBuild_sound`. -/
theorem denseCarryBranchF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseCarryBranchF pw bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    have hout : denseCarryBranchF pw bs facts d = { d with
          algebraicConstraints :=
            d.algebraicConstraints.map (denseResolveExpr (denseBuild bs facts d.busInteractions)) } := by
      unfold denseCarryBranchF; rw [if_pos hpB]
    rw [hout]
    set B := denseBuild bs facts d.busInteractions with hBdef
    -- for any assignment whose bus interactions are non-violating, the built bounds are valid
    have hBof : ∀ denv, (∀ bi ∈ d.busInteractions,
        (denseBIEval bi denv).multiplicity ≠ 0 →
          bs.violatesConstraint (denseBIEval bi denv) = false) →
        ∀ v bound, B[v]? = some bound → (denv v).val < bound := by
      intro denv hbus v bound hlk
      rw [hBdef] at hlk
      exact denseBuild_sound bs facts d.busInteractions v bound hlk denv hbus
    -- satisfaction is preserved under the constraint rewrite
    have hsat_iff : ∀ denv, (∀ v bound, B[v]? = some bound → (denv v).val < bound) →
        (d.satisfies bs denv ↔
          ({ d with algebraicConstraints :=
              d.algebraicConstraints.map (denseResolveExpr B) } :
            DenseConstraintSystem p).satisfies bs denv) := by
      intro denv hB
      constructor
      · rintro ⟨hc, hb⟩
        refine ⟨fun c' hc' => ?_, hb⟩
        obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
        exact (denseResolveExpr_eval_iff B c denv hB).mpr (hc c hcmem)
      · rintro ⟨hc, hb⟩
        refine ⟨fun c hcmem => ?_, hb⟩
        exact (denseResolveExpr_eval_iff B c denv hB).mp (hc _ (List.mem_map_of_mem hcmem))
    refine DensePassCorrect.ofEnvEq ?_ ?_ ?_ ?_
    · -- soundness: the same assignment satisfies the input
      intro denv hsatout
      have hB := hBof denv hsatout.2
      exact ⟨denv, (hsat_iff denv hB).mpr hsatout, BusState.equiv_refl _⟩
    · -- invariant preservation (bus interactions are untouched)
      intro hgi denv hsatout
      have hB := hBof denv hsatout.2
      exact hgi denv ((hsat_iff denv hB).mpr hsatout)
    · -- no new variables
      intro i hi
      have hocc :
          ({ d with algebraicConstraints := d.algebraicConstraints.map (denseResolveExpr B) }
              : DenseConstraintSystem p).occ
            = (d.algebraicConstraints.map (denseResolveExpr B)).flatMap DenseExpr.vars
              ++ d.busInteractions.flatMap denseBIVars := rfl
      rw [hocc, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨c', hc', hic'⟩ := List.mem_flatMap.1 hi
        obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
        exact DenseConstraintSystem.mem_occ_of_constraint hcmem (denseResolveExpr_vars B c i hic')
      · obtain ⟨bi, hbi, hib⟩ := List.mem_flatMap.1 hi
        exact DenseConstraintSystem.mem_occ_of_bi hbi hib
    · -- completeness: same assignment, same side effects, `admissible` untouched
      intro denv hadm hsat
      have hB := hBof denv hsat.2
      exact ⟨(hsat_iff denv hB).mp hsat, hadm, BusState.equiv_refl _⟩
  · rw [show denseCarryBranchF pw bs facts d = d from by unfold denseCarryBranchF; rw [if_neg hpB]]
    exact DensePassCorrect.refl reg.isInput d bs

/-- The dense carry-branch-resolution pass; correctness via `denseCarryBranchF_correct`. -/
def denseCarryBranchPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (denseCarryBranchF pw)
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseCarryBranchF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseCarryBranchF_correct pw reg bs facts d)

end ApcOptimizer.Dense
