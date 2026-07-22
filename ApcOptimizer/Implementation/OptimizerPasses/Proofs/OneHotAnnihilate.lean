import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify

set_option autoImplicit false

/-! # Dense one-hot annihilation: proof and wiring

`DensePassCorrect` proof for `OneHotAnnihilate.lean` via `DensePassCorrect.denseAddConstraints`,
lifted through `DenseVerifiedPassW.of`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The affine-closer recogniser's guarantee: the cofactor is `Σ mᵢ − 1` (`k = 1`) or `1 − Σ mᵢ`
    (`k = −1`); in both, `const = −k` and every coefficient is `k`. -/
theorem denseAffineCloser_spec (a : DenseExpr p) (la : DenseLinExpr p)
    (h : denseAffineCloser a = some la) :
    denseLinearize a = some la ∧
      ((la.const = -1 ∧ ∀ t ∈ la.terms, t.2 = 1) ∨ (la.const = 1 ∧ ∀ t ∈ la.terms, t.2 = -1)) := by
  grind [denseAffineCloser, List.all_eq_true]

/-- `denseReadCloser` succeeds only on `A · x` with `A` linearizing to `la`, `la.const = −1` and
    every coefficient `1` (or the flipped sign). -/
theorem denseReadCloser_spec (c : DenseExpr p) (x : VarId) (la : DenseLinExpr p)
    (h : denseReadCloser c = some (x, la)) :
    (∃ A, c = .mul A (.var x) ∧ denseLinearize A = some la) ∧
      ((la.const = -1 ∧ ∀ t ∈ la.terms, t.2 = 1) ∨ (la.const = 1 ∧ ∀ t ∈ la.terms, t.2 = -1)) := by
  cases c with
  | const n => simp [denseReadCloser] at h
  | var y => simp [denseReadCloser] at h
  | add a b => simp [denseReadCloser] at h
  | mul a b =>
    cases b with
    | const n => simp [denseReadCloser] at h
    | var y =>
      simp only [denseReadCloser, Option.map_eq_some_iff] at h
      obtain ⟨la', hla', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨hlin, hform⟩ := denseAffineCloser_spec a la' hla'
      exact ⟨⟨a, rfl, hlin⟩, hform⟩
    | add e1 e2 => simp [denseReadCloser] at h
    | mul e1 e2 => simp [denseReadCloser] at h

/-- `Σ (denv mᵢ) · x = 0` from `denv mᵢ · x = 0` for every marker. -/
theorem denseSum_mul_eq_zero (terms : List (VarId × ZMod p)) (denv : VarId → ZMod p) (xe : ZMod p)
    (hv : ∀ t ∈ terms, denv t.1 * xe = 0) : (terms.map (fun t => denv t.1)).sum * xe = 0 := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
    rw [List.map_cons, List.sum_cons, add_mul, hv t (List.mem_cons_self ..),
      ih (fun t' ht' => hv t' (List.mem_cons_of_mem _ ht')), add_zero]

/-- `Σ (k · denv mᵢ) = k · Σ (denv mᵢ)`. -/
theorem denseSum_map_mul_left (l : List (VarId × ZMod p)) (k : ZMod p) (denv : VarId → ZMod p) :
    (l.map (fun t => k * denv t.1)).sum = k * (l.map (fun t => denv t.1)).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, mul_add]

/-- The one-hot annihilation identity: `mᵢ·x = 0` for all markers plus `±(Σmᵢ − 1)·x = 0` force
    `x = 0`. -/
theorem denseAnnihilate {terms : List (VarId × ZMod p)} {denv : VarId → ZMod p} {xe : ZMod p}
    (hv : ∀ t ∈ terms, denv t.1 * xe = 0)
    (hq : ((terms.map (fun t => denv t.1)).sum - 1) * xe = 0 ∨
          (1 - (terms.map (fun t => denv t.1)).sum) * xe = 0) : xe = 0 := by
  have hsum := denseSum_mul_eq_zero terms denv xe hv
  rcases hq with h | h
  · rw [sub_mul, one_mul, hsum, zero_sub, neg_eq_zero] at h; exact h
  · rw [sub_mul, one_mul, hsum, sub_zero] at h; exact h

/-- The affine cofactor of a closer with common coefficient `k` evaluates to
    `la.const + k · Σ (denv marker)`. -/
theorem denseCofactor_eval {A : DenseExpr p} {la : DenseLinExpr p}
    (hlin : denseLinearize A = some la) (k : ZMod p) (hcoeff : ∀ t ∈ la.terms, t.2 = k)
    (denv : VarId → ZMod p) :
    A.eval denv = la.const + k * (la.terms.map (fun t => denv t.1)).sum := by
  rw [denseLinearize_eval A la hlin]
  unfold DenseLinExpr.eval
  rw [show (la.terms.map (fun t => t.2 * denv t.1)) = (la.terms.map (fun t => k * denv t.1)) from
    List.map_congr_left (fun t ht => by rw [hcoeff t ht])]
  rw [denseSum_map_mul_left]

/-- Every `x ∈ denseDeadVars d` is forced to `0` by the system's constraints. -/
theorem denseDeadVars_entailed (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) (x : VarId)
    (hx : x ∈ denseDeadVars d) : (DenseExpr.var x).eval denv = 0 := by
  obtain ⟨cq, hcq_mem, hdead⟩ := List.mem_filterMap.1 hx
  have hconstr : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  cases hrc : denseReadCloser cq with
  | none => simp only [denseDeadFromCloser, hrc] at hdead; exact absurd hdead (by simp)
  | some xla =>
    obtain ⟨x', la⟩ := xla
    simp only [denseDeadFromCloser, hrc] at hdead
    split_ifs at hdead with hgate
    have hxeq : x' = x := by simpa using hdead
    obtain ⟨⟨A, hcform, hlin⟩, hform⟩ := denseReadCloser_spec cq x' la hrc
    show denv x = 0
    rw [← hxeq]
    have hcq0 : A.eval denv * denv x' = 0 := by
      have := hconstr cq hcq_mem; rw [hcform] at this; simpa only [DenseExpr.eval] using this
    have hqeval : ((la.terms.map (fun t => denv t.1)).sum - 1) * denv x' = 0 ∨
        (1 - (la.terms.map (fun t => denv t.1)).sum) * denv x' = 0 := by
      rcases hform with ⟨hconst, hcoeff⟩ | ⟨hconst, hcoeff⟩
      · left
        rw [denseCofactor_eval hlin 1 hcoeff denv, hconst] at hcq0
        linear_combination hcq0
      · right
        rw [denseCofactor_eval hlin (-1) hcoeff denv, hconst] at hcq0
        linear_combination hcq0
    have hveval : ∀ t ∈ la.terms, denv t.1 * denv x' = 0 := by
      intro t ht
      have hp : denseHasProd d t.1 x' = true := (List.all_eq_true.1 hgate) t ht
      unfold denseHasProd at hp
      obtain ⟨cv, hcv_mem, hcv⟩ := List.any_eq_true.1 hp
      have hcv0 : cv.eval denv = 0 := hconstr cv hcv_mem
      simp only [Bool.or_eq_true] at hcv
      rcases hcv with he | he
      · obtain rfl := eq_of_beq he
        simpa only [DenseExpr.eval] using hcv0
      · obtain rfl := eq_of_beq he
        simp only [DenseExpr.eval] at hcv0
        rw [mul_comm] at hcv0
        exact hcv0
    exact denseAnnihilate hveval hqeval

/-- Every variable of an added `x = 0` occurs in `d`: the closer `.mul A (.var x)` is a present
    constraint mentioning `x`. -/
theorem denseDeadVarsNew_vars (d : DenseConstraintSystem p) :
    ∀ c ∈ (denseDeadVars d).map (fun i => (DenseExpr.var i : DenseExpr p)),
      ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
  have hzy : z = y := by simpa only [DenseExpr.vars, List.mem_singleton] using hz
  rw [hzy]
  obtain ⟨cq, hcq_mem, hdead⟩ := List.mem_filterMap.1 hy
  cases hrc : denseReadCloser cq with
  | none => simp only [denseDeadFromCloser, hrc] at hdead; exact absurd hdead (by simp)
  | some xla =>
    obtain ⟨x', la⟩ := xla
    simp only [denseDeadFromCloser, hrc] at hdead
    split_ifs at hdead with hgate
    have hxeq : x' = y := by simpa using hdead
    obtain ⟨⟨A, hcform, _⟩, _⟩ := denseReadCloser_spec cq x' la hrc
    rw [← hxeq]
    refine DenseConstraintSystem.mem_occ_of_constraint hcq_mem ?_
    rw [hcform]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- The dense one-hot annihilation pass: when a one-hot closer `(x₁ + … + xₙ − 1)·x = 0` is
    present together with every product `xᵢ·x = 0`, the variable `x` is forced to `0`; appends
    `x = 0` for each such annihilated `x`. -/
def denseOneHotAnnihilatePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofAddConstraints
    (fun _ _ d => (denseDeadVars d).map (fun i => DenseExpr.var i))
    (fun _ _ d => denseDeadVarsNew_vars d)
    (fun bs _ d denv _ hsat c hc => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      exact denseDeadVars_entailed d bs denv hsat x hx)

end ApcOptimizer.Dense
