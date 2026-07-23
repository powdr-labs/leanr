import ApcOptimizer.Implementation.OptimizerPasses.IsZeroFold
import ApcOptimizer.Implementation.OptimizerPasses.Bridge
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DigitFold

set_option autoImplicit false

/-! # Soundness for the multi-limb is-zero fold (`IsZeroFold.lean`)

`denseIsZeroFoldF` replaces a group of per-limb zero constraints `L·vᵢ = 0` (shared factor `L`, each
`vᵢ` byte-bounded and not in `L`) by the single `L·(Σvᵢ) = 0`, dropping the members. The two systems
are satisfaction-equivalent:

* input ⟹ output: summing the members gives `L·(Σvᵢ) = 0` (no bounds needed);
* output ⟹ input: `L·(Σvᵢ) = 0` factors (prime field) as `L = 0 ∨ Σvᵢ = 0`; when `L = 0` every
  `L·vᵢ = 0`, and when `Σvᵢ = 0` each `vᵢ = 0` by a no-wraparound argument (bytes summing to `0` in
  `ZMod p`, with `256·|vs| ≤ p`, are individually `0`), so again every `L·vᵢ = 0`.

Bus interactions are untouched, so side effects/admissibility carry over by `rfl`; byte bounds come
from `denseBuild_sound` (`Proofs/DigitFold.lean`), agnostic to whether the range check lives on the
bitwise-lookup or the memory bus. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `denseSumVars` -/

theorem denseSumVars_eval (vs : List VarId) (denv : VarId → ZMod p) :
    (denseSumVars vs).eval denv = (vs.map (fun v => denv v)).sum := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
      simp only [denseSumVars, DenseExpr.eval, ih, List.map_cons, List.sum_cons]

theorem denseSumVars_vars (vs : List VarId) : (denseSumVars vs : DenseExpr p).vars = vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp only [denseSumVars, DenseExpr.vars, ih, List.singleton_append]

/-! ## No-wraparound: a bounded byte sum that is `0` forces each summand `0` -/

theorem zmod_val_sum_le_of_lt256 (xs : List (ZMod p)) (hb : ∀ x ∈ xs, x.val < 256) :
    (xs.map ZMod.val).sum ≤ 255 * xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx : x.val ≤ 255 := by have := hb x (List.mem_cons_self ..); omega
      have hr := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem zmod_val_of_sum [NeZero p] (xs : List (ZMod p))
    (h : (xs.map ZMod.val).sum < p) : xs.sum.val = (xs.map ZMod.val).sum := by
  induction xs with
  | nil => simp [ZMod.val_zero]
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons] at h ⊢
      have hr : (rest.map ZMod.val).sum < p := by omega
      rw [ZMod.val_add, ih hr, Nat.mod_eq_of_lt h]

theorem zmod_each_zero_of_sum_zero [NeZero p] (xs : List (ZMod p))
    (hb : ∀ x ∈ xs, x.val < 256) (hlen : 256 * xs.length ≤ p) (hz : xs.sum = 0) :
    ∀ x ∈ xs, x = 0 := by
  have hle := zmod_val_sum_le_of_lt256 xs hb
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hlt : (xs.map ZMod.val).sum < p := by omega
  have hval : xs.sum.val = (xs.map ZMod.val).sum := zmod_val_of_sum xs hlt
  have hsum0 : (xs.map ZMod.val).sum = 0 := by rw [← hval, hz]; exact ZMod.val_zero
  intro x hx
  have hxmem : x.val ∈ xs.map ZMod.val := List.mem_map.2 ⟨x, hx, rfl⟩
  have hxle : x.val ≤ (xs.map ZMod.val).sum := List.single_le_sum (fun y _ => Nat.zero_le y) _ hxmem
  exact (ZMod.val_eq_zero x).1 (by omega)

/-- The folded-sum-zero forces each group variable to `0` (the crux of the output ⟹ input step). -/
theorem denseSumVars_forces_zero [NeZero p] (vs : List VarId) (denv : VarId → ZMod p)
    (hb : ∀ v ∈ vs, (denv v).val < 256) (hlen : 256 * vs.length ≤ p)
    (hz : (denseSumVars vs).eval denv = 0) : ∀ v ∈ vs, denv v = 0 := by
  have hz' : (vs.map (fun v => denv v)).sum = 0 := (denseSumVars_eval vs denv).symm.trans hz
  intro v hv
  exact zmod_each_zero_of_sum_zero (vs.map (fun v => denv v))
    (fun x hx => by obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx; exact hb w hw)
    (by rw [List.length_map]; exact hlen) hz' (denv v) (List.mem_map.2 ⟨v, hv, rfl⟩)

/-- `L·(Σvᵢ) = 0` from `L·vᵢ = 0` for every member (the input ⟹ output step). -/
theorem denseFactor_mul_sum_zero (L : DenseExpr p) (vs : List VarId) (denv : VarId → ZMod p)
    (h : ∀ v ∈ vs, L.eval denv * denv v = 0) :
    L.eval denv * (vs.map (fun v => denv v)).sum = 0 := by
  induction vs with
  | nil => simp
  | cons v rest ih =>
      rw [List.map_cons, List.sum_cons, mul_add, h v (List.mem_cons_self ..),
        ih (fun w hw => h w (List.mem_cons_of_mem _ hw)), add_zero]

/-! ## Reading off the plan -/

theorem denseIsZeroPlanOK_facts (pw : PrimeWitness p) (Bm : Std.HashMap VarId Nat)
    (d : DenseConstraintSystem p) (L : DenseExpr p) (vs : List VarId)
    (h : denseIsZeroPlanOK pw Bm d L vs = true) :
    pw.isPrime = true ∧ 2 ≤ vs.length ∧ 256 * vs.length ≤ p ∧
      (∀ v ∈ vs, ∃ b, Bm[v]? = some b ∧ b ≤ 256) ∧
      (∀ v ∈ vs, DenseExpr.mul L (.var v) ∈ d.algebraicConstraints) := by
  unfold denseIsZeroPlanOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hp, h2⟩, hlp⟩, hbyte⟩, hmem⟩ := h
  refine ⟨hp, h2, hlp, ?_, ?_⟩
  · intro v hv
    have hb : (match Bm[v]? with | some b => decide (b ≤ 256) | none => false) = true := hbyte v hv
    split at hb
    · rename_i b hlk; exact ⟨b, hlk, of_decide_eq_true hb⟩
    · exact absurd hb (by simp)
  · intro v hv
    exact List.contains_iff_mem.mp (hmem v hv)

theorem denseIsZeroFindPlan_plan_ok (pw : PrimeWitness p) (Bm : Std.HashMap VarId Nat)
    (d : DenseConstraintSystem p) (L : DenseExpr p) (vs : List VarId)
    (h : denseIsZeroFindPlan pw Bm d = some (L, vs)) :
    denseIsZeroPlanOK pw Bm d L vs = true := by
  unfold denseIsZeroFindPlan at h
  obtain ⟨m, _, hf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hok : denseIsZeroPlanOK pw Bm d m.1
      (denseIsZeroGroupVars Bm (d.algebraicConstraints.filterMap denseIsZeroMember?) m.1) = true
  · rw [if_pos hok] at hf
    injection hf with hf'
    rw [Prod.mk.injEq] at hf'
    obtain ⟨h1, h2⟩ := hf'
    rw [← h1, ← h2]; exact hok
  · rw [if_neg hok] at hf; exact absurd hf (by simp)

/-! ## Satisfaction equivalence of the single-group fold -/

theorem denseIsZeroFoldSystem_satisfies_iff (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (L : DenseExpr p) (vs : List VarId)
    (hplan : denseIsZeroPlanOK pw (denseBuild bs facts d.busInteractions) d L vs = true)
    (denv : VarId → ZMod p) :
    (denseIsZeroFoldSystem d L vs).satisfies bs denv ↔ d.satisfies bs denv := by
  obtain ⟨hprimeB, _hlen2, hlenp, hbyteB, hmem⟩ := denseIsZeroPlanOK_facts pw _ d L vs hplan
  have hprime : Nat.Prime p := pw.correct hprimeB
  haveI : Fact (Nat.Prime p) := ⟨hprime⟩
  haveI : NeZero p := ⟨by have := hprime.two_le; omega⟩
  have hsummed_eval : ∀ e : VarId → ZMod p,
      (DenseExpr.mul L (denseSumVars vs)).eval e = L.eval e * (vs.map (fun v => e v)).sum :=
    fun e => by
      rw [show (DenseExpr.mul L (denseSumVars vs)).eval e
        = L.eval e * (denseSumVars vs).eval e from rfl, denseSumVars_eval]
  simp only [DenseConstraintSystem.satisfies, denseIsZeroFoldSystem]
  constructor
  · rintro ⟨hcout, hbus⟩
    refine ⟨fun c hc => ?_, hbus⟩
    have hbytes : ∀ v ∈ vs, (denv v).val < 256 := by
      intro v hv
      obtain ⟨b, hlk, hb256⟩ := hbyteB v hv
      have := denseBuild_sound bs facts d.busInteractions v b hlk denv
        (fun bi hbi hne => hbus bi hbi hne)
      omega
    by_cases hcm : (vs.map (fun v => DenseExpr.mul L (.var v))).contains c = true
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.contains_iff_mem.mp hcm)
      show L.eval denv * denv v = 0
      have hsummed0 : (DenseExpr.mul L (denseSumVars vs)).eval denv = 0 :=
        hcout _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
      rw [hsummed_eval denv] at hsummed0
      rcases mul_eq_zero.1 hsummed0 with hL | hS
      · rw [hL, zero_mul]
      · rw [denseSumVars_forces_zero vs denv hbytes hlenp
          ((denseSumVars_eval vs denv).trans hS) v hv, mul_zero]
    · have hf : (vs.map (fun v => DenseExpr.mul L (.var v))).contains c = false := by
        cases hh : (vs.map (fun v => DenseExpr.mul L (.var v))).contains c with
        | true => exact absurd hh hcm
        | false => rfl
      exact hcout c (List.mem_append_left _ (List.mem_filter.2 ⟨hc, by rw [hf, Bool.not_false]⟩))
  · rintro ⟨hcd, hbus⟩
    refine ⟨fun c' hc' => ?_, hbus⟩
    rcases List.mem_append.1 hc' with hcf | hcs
    · exact hcd c' (List.mem_of_mem_filter hcf)
    · rw [List.mem_singleton] at hcs
      subst hcs
      rw [hsummed_eval denv]
      exact denseFactor_mul_sum_zero L vs denv (fun v hv => hcd _ (hmem v hv))

/-! ## `occ`/coverage of the single-group fold -/

private theorem group_nonempty {vs : List VarId} (hne : vs ≠ []) : ∃ v0, v0 ∈ vs := by
  cases vs with
  | nil => exact absurd rfl hne
  | cons a t => exact ⟨a, by simp⟩

theorem denseIsZeroFoldSystem_occ_subset (d : DenseConstraintSystem p) (L : DenseExpr p)
    (vs : List VarId) (hmem : ∀ v ∈ vs, DenseExpr.mul L (.var v) ∈ d.algebraicConstraints)
    (hne : vs ≠ []) : ∀ i ∈ (denseIsZeroFoldSystem d L vs).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, denseIsZeroFoldSystem] at hi
  rcases List.mem_append.1 hi with hac | hbi
  · obtain ⟨c, hc, hic⟩ := List.mem_flatMap.1 hac
    rcases List.mem_append.1 hc with hcf | hcs
    · exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hcf) hic
    · rw [List.mem_singleton] at hcs
      subst hcs
      rw [show (DenseExpr.mul L (denseSumVars vs)).vars = L.vars ++ (denseSumVars vs).vars from rfl,
        denseSumVars_vars, List.mem_append] at hic
      rcases hic with hiL | hiv
      · obtain ⟨v0, hv0⟩ := group_nonempty hne
        exact DenseConstraintSystem.mem_occ_of_constraint (hmem v0 hv0)
          (by rw [show (DenseExpr.mul L (.var v0)).vars = L.vars ++ [v0] from rfl, List.mem_append]
              exact Or.inl hiL)
      · exact DenseConstraintSystem.mem_occ_of_constraint (hmem i hiv)
          (by rw [show (DenseExpr.mul L (.var i)).vars = L.vars ++ [i] from rfl, List.mem_append]
              exact Or.inr (List.mem_singleton.2 rfl))
  · obtain ⟨bi, hbimem, hib⟩ := List.mem_flatMap.1 hbi
    exact DenseConstraintSystem.mem_occ_of_bi hbimem hib

theorem denseIsZeroFoldSystem_covered {reg : VarRegistry} (d : DenseConstraintSystem p)
    (L : DenseExpr p) (vs : List VarId) (hcovd : d.CoveredBy reg)
    (hmem : ∀ v ∈ vs, DenseExpr.mul L (.var v) ∈ d.algebraicConstraints) (hne : vs ≠ []) :
    (denseIsZeroFoldSystem d L vs).CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hcovd
  refine ⟨fun c hc => ?_, fun bi hbimem => hbi bi hbimem⟩
  simp only [denseIsZeroFoldSystem] at hc
  rcases List.mem_append.1 hc with hcf | hcs
  · exact hac c (List.mem_of_mem_filter hcf)
  · rw [List.mem_singleton] at hcs
    subst hcs
    rw [DenseExpr.coveredBy_mul]
    obtain ⟨v0, hv0⟩ := group_nonempty hne
    have hmemL := hac _ (hmem v0 hv0)
    rw [DenseExpr.coveredBy_mul] at hmemL
    refine ⟨hmemL.1, fun i hi => ?_⟩
    rw [denseSumVars_vars] at hi
    have hci := hac _ (hmem i hi)
    rw [DenseExpr.coveredBy_mul] at hci
    exact hci.2 i (by simp [DenseExpr.vars])

/-! ## The single-group fold is `DensePassCorrect` -/

theorem denseIsZeroFoldSystem_correct (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (L : DenseExpr p) (vs : List VarId)
    (hplan : denseIsZeroPlanOK pw (denseBuild bs facts d.busInteractions) d L vs = true) :
    DensePassCorrect isInput d (denseIsZeroFoldSystem d L vs) [] bs := by
  obtain ⟨_, hlen2, _, _, hmem⟩ := denseIsZeroPlanOK_facts pw _ d L vs hplan
  have hne : vs ≠ [] := by rintro rfl; simp only [List.length_nil] at hlen2; omega
  refine DensePassCorrect.ofEnvEq ?_ ?_ (denseIsZeroFoldSystem_occ_subset d L vs hmem hne) ?_
  · intro denv hsat
    exact ⟨denv, (denseIsZeroFoldSystem_satisfies_iff pw bs facts d L vs hplan denv).1 hsat,
      BusState.equiv_refl _⟩
  · intro hinv denv hsat bi hbi
    exact hinv denv ((denseIsZeroFoldSystem_satisfies_iff pw bs facts d L vs hplan denv).1 hsat)
      bi hbi
  · intro denv hadm hsat
    exact ⟨(denseIsZeroFoldSystem_satisfies_iff pw bs facts d L vs hplan denv).2 hsat, hadm,
      BusState.equiv_refl _⟩

/-! ## The full transform and its wiring -/

theorem denseIsZeroFoldF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcovd : d.CoveredBy reg) :
    (denseIsZeroFoldF pw bs facts d).CoveredBy reg := by
  unfold denseIsZeroFoldF
  split
  · next L vs hpl =>
      have hplan := denseIsZeroFindPlan_plan_ok pw _ d L vs hpl
      obtain ⟨_, hlen2, _, _, hmem⟩ := denseIsZeroPlanOK_facts pw _ d L vs hplan
      have hne : vs ≠ [] := by rintro rfl; simp only [List.length_nil] at hlen2; omega
      exact denseIsZeroFoldSystem_covered d L vs hcovd hmem hne
  · next => exact hcovd

theorem denseIsZeroFoldF_correct (pw : PrimeWitness p) (isInput : VarId → Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d (denseIsZeroFoldF pw bs facts d) [] bs := by
  unfold denseIsZeroFoldF
  split
  · next L vs hpl =>
      exact denseIsZeroFoldSystem_correct pw bs facts isInput d L vs
        (denseIsZeroFindPlan_plan_ok pw _ d L vs hpl)
  · next => exact DensePassCorrect.refl isInput d bs

/-- The multi-limb is-zero fold pass; transform `denseIsZeroFoldF` (`IsZeroFold.lean`). -/
def denseIsZeroFoldPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d => denseIsZeroFoldF pw bs facts d)
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseIsZeroFoldF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseIsZeroFoldF_correct pw reg.isInput bs facts d)

end ApcOptimizer.Dense
