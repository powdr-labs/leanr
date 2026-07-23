import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify

set_option autoImplicit false

/-! # Dense one-hot annihilation: proof and wiring

`DensePassCorrect` proof for `OneHotAnnihilate.lean` via `DensePassCorrect.denseAddConstraints`,
lifted through `DenseVerifiedPassW.of`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Soundness of the product-pair set: an indexed pair was a present product constraint -/

private theorem denseProdSet_foldl_mem (cs : List (DenseExpr p)) :
    ∀ (s0 : Std.HashSet (VarId × VarId)) (a b : VarId),
      (a, b) ∈ cs.foldl (fun s c =>
        match c with | .mul (.var a') (.var b') => s.insert (a', b') | _ => s) s0 →
      (a, b) ∈ s0 ∨ (DenseExpr.mul (.var a) (.var b) : DenseExpr p) ∈ cs := by
  induction cs with
  | nil => intro s0 a b h; exact Or.inl (by simpa using h)
  | cons c rest ih =>
    intro s0 a b h
    rw [List.foldl_cons] at h
    have hstep : (a, b) ∈ (match c with
        | .mul (.var a') (.var b') => s0.insert (a', b') | _ => s0) ∨
        (DenseExpr.mul (.var a) (.var b) : DenseExpr p) ∈ c :: rest := by
      rcases ih _ a b h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')
    rcases hstep with h' | h'
    · match c with
      | .const _ => exact Or.inl (by simpa using h')
      | .var _ => exact Or.inl (by simpa using h')
      | .add _ _ => exact Or.inl (by simpa using h')
      | .mul (.const _) _ => exact Or.inl (by simpa using h')
      | .mul (.add _ _) _ => exact Or.inl (by simpa using h')
      | .mul (.mul _ _) _ => exact Or.inl (by simpa using h')
      | .mul (.var a') (.const _) => exact Or.inl (by simpa using h')
      | .mul (.var a') (.add _ _) => exact Or.inl (by simpa using h')
      | .mul (.var a') (.mul _ _) => exact Or.inl (by simpa using h')
      | .mul (.var a') (.var b') =>
        simp only [Std.HashSet.mem_insert, beq_iff_eq, Prod.mk.injEq] at h'
        rcases h' with ⟨rfl, rfl⟩ | hin
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl hin
    · exact Or.inr h'

/-- Every pair the product set records is a present `a * b` constraint. -/
theorem denseProdSet_mem {cs : List (DenseExpr p)} {a b : VarId}
    (h : (a, b) ∈ denseProdSet cs) :
    (DenseExpr.mul (.var a) (.var b) : DenseExpr p) ∈ cs := by
  rcases denseProdSet_foldl_mem cs ∅ a b h with h' | h'
  · simp at h'
  · exact h'

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
      have hp : denseHasProdS (denseProdSet d.algebraicConstraints) t.1 x' = true :=
        (List.all_eq_true.1 hgate) t ht
      unfold denseHasProdS at hp
      rw [Bool.or_eq_true] at hp
      have hcv0 : (DenseExpr.mul (.var t.1) (.var x') : DenseExpr p).eval denv = 0 ∨
          (DenseExpr.mul (.var x') (.var t.1) : DenseExpr p).eval denv = 0 := by
        rcases hp with h1 | h1
        · exact Or.inl (hconstr _ (denseProdSet_mem (Std.HashSet.mem_iff_contains.mpr h1)))
        · exact Or.inr (hconstr _ (denseProdSet_mem (Std.HashSet.mem_iff_contains.mpr h1)))
      rcases hcv0 with he | he
      · simpa only [DenseExpr.eval] using he
      · simp only [DenseExpr.eval] at he
        rw [mul_comm] at he
        exact he
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
