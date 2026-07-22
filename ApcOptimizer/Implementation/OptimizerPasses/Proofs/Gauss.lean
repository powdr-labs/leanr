import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagUnify

set_option autoImplicit false

/-! # Correctness for the dense Gauss-elimination pass.
Substitution-shaped: correctness rides on `DenseConstraintSystem.substF_denseCorrect`
(`Proofs/DomainBatch.lean`), fed the final solution map's entailment and occurrence closure, both
established by `denseGaussLoop_sound`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Substituting `i := t` and evaluating equals evaluating with `i` rebound to `t.eval denv`. -/
theorem DenseExpr.eval_subst (e : DenseExpr p) (i : VarId) (t : DenseExpr p)
    (denv : VarId → ZMod p) :
    (e.subst i t).eval denv = e.eval (Function.update denv i (t.eval denv)) := by
  induction e with
  | const n => simp [DenseExpr.subst, DenseExpr.eval]
  | var j =>
      simp only [DenseExpr.subst]
      by_cases h : j = i
      · subst h; simp [DenseExpr.eval, Function.update_self]
      · rw [if_neg h]; simp [DenseExpr.eval, Function.update_of_ne h]
  | add a b iha ihb => simp only [DenseExpr.subst, DenseExpr.eval, iha, ihb]
  | mul a b iha ihb => simp only [DenseExpr.subst, DenseExpr.eval, iha, ihb]

/-! ## Affine soundness -/

/-- If `l.trySolve v` returns `(x, t)` and `l` evaluates to zero, then `x = t` under `denv`. -/
theorem DenseLinExpr.trySolve_sound (l : DenseLinExpr p) (v x : VarId) (t : DenseExpr p)
    (h : l.trySolve v = some (x, t)) (denv : VarId → ZMod p) (hl : l.eval denv = 0) :
    denv x = t.eval denv := by
  unfold DenseLinExpr.trySolve at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [DenseLinExpr.toExpr_eval, DenseLinExpr.scale_eval]
    have hs := l.eval_split v denv
    rw [h1, one_mul] at hs; rw [hs] at hl
    linear_combination hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [DenseLinExpr.toExpr_eval]
    have hs := l.eval_split v denv
    rw [h2] at hs; rw [hs] at hl
    linear_combination -hl

/-- If `l.trySolveUnit v` returns `(x, t)` and `l` evaluates to zero, then `x = t` under `denv`. -/
theorem DenseLinExpr.trySolveUnit_sound (l : DenseLinExpr p) (v x : VarId) (t : DenseExpr p)
    (h : l.trySolveUnit v = some (x, t)) (denv : VarId → ZMod p) (hl : l.eval denv = 0) :
    denv x = t.eval denv := by
  unfold DenseLinExpr.trySolveUnit at h
  split_ifs at h with h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [DenseLinExpr.toExpr_eval, DenseLinExpr.scale_eval]
  have hs := l.eval_split v denv
  have h0 : l.coeff v * denv v + (l.others v).eval denv = 0 := by rw [← hs]; exact hl
  linear_combination (l.coeff v)⁻¹ * h0 - denv v * h1

/-- Every `±1`-pivot of a dense constraint entails its equality. -/
theorem densePm1PivotsOf_sound (c : DenseExpr p) (x : VarId) (t : DenseExpr p)
    (h : (x, t) ∈ densePm1PivotsOf c) (denv : VarId → ZMod p) (hc : c.eval denv = 0) :
    denv x = t.eval denv := by
  unfold densePm1PivotsOf at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    have hl : l.eval denv = 0 := by rw [← denseLinearize_eval c l hlin denv]; exact hc
    obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
    exact DenseLinExpr.trySolve_sound l v x t hv denv hl

/-- Every unit-pivot of a dense constraint entails its equality. -/
theorem denseUnitPivotsOf_sound (c : DenseExpr p) (x : VarId) (t : DenseExpr p)
    (h : (x, t) ∈ denseUnitPivotsOf c) (denv : VarId → ZMod p) (hc : c.eval denv = 0) :
    denv x = t.eval denv := by
  unfold denseUnitPivotsOf at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    have hl : l.eval denv = 0 := by rw [← denseLinearize_eval c l hlin denv]; exact hc
    obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
    cases htr : l.trySolve v with
    | some r => rw [htr] at hv; exact absurd hv (by simp)
    | none =>
        rw [htr] at hv
        exact DenseLinExpr.trySolveUnit_sound l v x t hv denv hl

/-! ## Pivot-vars bounds -/

/-- A `±1`-pivot solution mentions only the constraint's variables. -/
theorem densePm1PivotsOf_vars (c : DenseExpr p) (x : VarId) (t : DenseExpr p)
    (h : (x, t) ∈ densePm1PivotsOf c) : ∀ y ∈ t.vars, y ∈ c.vars := by
  intro y hy
  unfold densePm1PivotsOf at h
  cases hL : denseLinearize c with
  | none => rw [hL] at h; simp at h
  | some l =>
      rw [hL] at h
      obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
      exact denseLinearize_mem_vars c l hL y (denseTrySolve_vars_subset l v (x, t) hv y hy)

/-- A unit-pivot solution mentions only the constraint's variables. -/
theorem denseUnitPivotsOf_vars (c : DenseExpr p) (x : VarId) (t : DenseExpr p)
    (h : (x, t) ∈ denseUnitPivotsOf c) : ∀ y ∈ t.vars, y ∈ c.vars := by
  intro y hy
  unfold denseUnitPivotsOf at h
  cases hL : denseLinearize c with
  | none => rw [hL] at h; simp at h
  | some l =>
      rw [hL] at h
      obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
      cases htr : l.trySolve v with
      | some r => rw [htr] at hv; simp at hv
      | none =>
          rw [htr] at hv
          exact denseLinearize_mem_vars c l hL y (denseTrySolveUnit_vars_subset l v (x, t) hv y hy)

/-! ## The Gauss-loop invariant: the `DenseSolved` accumulator stays entailed and
occurrence-closed, by structural induction over the pending constraints. -/

theorem denseGaussLoop_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    ∀ (pending : List (DenseExpr p)) (dσ : DenseSolved p),
      (∀ c ∈ pending, c ∈ d.algebraicConstraints) →
      (∀ denv, d.satisfies bs denv → ∀ i t, dσ.fn i = some t → denv i = t.eval denv) →
      (∀ i t, dσ.fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
          (denseGaussLoop occ prot pending dσ).fn i = some t → denv i = t.eval denv) ∧
      (∀ i t, (denseGaussLoop occ prot pending dσ).fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) := by
  intro pending
  induction pending with
  | nil => intro dσ _ hσs hσv; exact ⟨hσs, hσv⟩
  | cons c rest ih =>
      intro dσ hpend hσs hσv
      have hcmem : c ∈ d.algebraicConstraints := hpend c (List.mem_cons_self ..)
      have hrest : ∀ c' ∈ rest, c' ∈ d.algebraicConstraints :=
        fun c' h' => hpend c' (List.mem_cons_of_mem _ h')
      cases hfb : denseFastBest ((c.substF dσ.fn).normalize) occ prot with
      | none =>
          simp only [denseGaussLoop, hfb]
          exact ih dσ hrest hσs hσv
      | some xt =>
          obtain ⟨x, t⟩ := xt
          have hmem : (x, t) ∈ densePm1PivotsOf ((c.substF dσ.fn).normalize)
              ++ denseUnitPivotsOf ((c.substF dσ.fn).normalize) := by
            have hfb2 := hfb
            rw [denseFastBest_eq] at hfb2
            exact List.argmin_mem (by rw [hfb2]; exact Option.mem_some_self _)
          have hc'occ : ∀ z ∈ ((c.substF dσ.fn).normalize).vars, z ∈ d.occ := by
            intro z hz
            have hz2 : z ∈ (c.substF dσ.fn).vars := DenseExpr.normalize_vars _ z hz
            rcases DenseExpr.substF_vars dσ.fn c z hz2 with h | ⟨i, _, tt, hft, hzt⟩
            · exact DenseConstraintSystem.mem_occ_of_constraint hcmem h
            · exact hσv i tt hft z hzt
          have hx : ∀ denv, d.satisfies bs denv → denv x = t.eval denv := by
            intro denv hsat
            have hc0 : c.eval denv = 0 := hsat.1 c hcmem
            have hc'z : ((c.substF dσ.fn).normalize).eval denv = 0 := by
              rw [DenseExpr.normalize_eval, DenseExpr.eval_substF,
                  denseEnvF_eq_self dσ.fn denv (hσs denv hsat)]
              exact hc0
            rcases List.mem_append.1 hmem with hp | hu
            · exact densePm1PivotsOf_sound ((c.substF dσ.fn).normalize) x t hp denv hc'z
            · exact denseUnitPivotsOf_sound ((c.substF dσ.fn).normalize) x t hu denv hc'z
          have htocc : ∀ z ∈ t.vars, z ∈ d.occ := by
            intro z hz
            rcases List.mem_append.1 hmem with hp | hu
            · exact hc'occ z (densePm1PivotsOf_vars ((c.substF dσ.fn).normalize) x t hp z hz)
            · exact hc'occ z (denseUnitPivotsOf_vars ((c.substF dσ.fn).normalize) x t hu z hz)
          have htouched : ∀ y s, (y, s) ∈ ((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
                (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none)) →
              dσ.fn y = some s := by
            intro y s hys
            obtain ⟨_, _, hy'⟩ := List.mem_filterMap.1 hys
            obtain ⟨s', hs', hif⟩ := Option.bind_eq_some_iff.1 hy'
            by_cases hm : s'.mentions x
            · rw [if_pos hm] at hif
              simp only [Option.some.injEq, Prod.mk.injEq] at hif
              obtain ⟨rfl, rfl⟩ := hif
              exact hs'
            · rw [if_neg hm] at hif; exact absurd hif (by simp)
          simp only [denseGaussLoop, hfb]
          refine ih _ hrest ?_ ?_
          · intro denv hsat
            refine DenseSolved.insertAll_preserves _ dσ (hσs denv hsat) ?_
            intro pr hpr
            rcases List.mem_append.1 hpr with hin | hin
            · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
              have hmemys : dσ.fn y = some s := htouched y s hys
              have hy : denv y = s.eval denv := hσs denv hsat y s hmemys
              have hxe : denv x = t.eval denv := hx denv hsat
              show denv y = ((s.subst x t).normalize).eval denv
              rw [DenseExpr.normalize_eval, DenseExpr.eval_subst, ← hxe, Function.update_eq_self, hy]
            · rw [List.mem_singleton] at hin; subst hin
              exact hx denv hsat
          · refine DenseSolved.insertAll_preserves _ dσ hσv ?_
            intro pr hpr
            rcases List.mem_append.1 hpr with hin | hin
            · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
              have hmemys : dσ.fn y = some s := htouched y s hys
              intro z hz
              have hz2 : z ∈ (s.subst x t).vars := DenseExpr.normalize_vars _ z hz
              rcases DenseExpr.subst_vars s x t z hz2 with h | h
              · exact hσv y s hmemys z h
              · exact htocc z h
            · rw [List.mem_singleton] at hin; subst hin
              exact htocc

/-! ## The pass's correctness -/

/-- The final Gauss-loop solution map (from the pass's initial accumulators) is entailed and
    occurrence-closed. -/
theorem denseGaussElim_loop_invariant (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
          d.algebraicConstraints
          (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
            d.algebraicConstraints DenseSolved.empty)).fn i = some t →
          denv i = t.eval denv) ∧
    (∀ i t, (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
        d.algebraicConstraints
        (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
          d.algebraicConstraints DenseSolved.empty)).fn i = some t →
        ∀ z ∈ t.vars, z ∈ d.occ) := by
  have hfirst := denseGaussLoop_sound bs d (denseOccurrenceMap d) (denseProtectedVars d bs)
    d.algebraicConstraints DenseSolved.empty (fun _c hc => hc)
    (fun _ _ _ _ hti => absurd hti (by simp [DenseSolved.fn, DenseSolved.empty]))
    (fun _ _ hti => absurd hti (by simp [DenseSolved.fn, DenseSolved.empty]))
  exact denseGaussLoop_sound bs d (denseOccurrenceMap d) (denseProtectedVars d bs)
    d.algebraicConstraints
    (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
      d.algebraicConstraints DenseSolved.empty)
    (fun _c hc => hc) hfirst.1 hfirst.2

/-- `denseGaussElim` preserves coverage: on the non-trivial branch it substitutes an
    occurrence-closed solution map, whose solutions are covered because their variables occur in a
    covered system. -/
theorem denseGaussElim_covered (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseGaussElim bs d).CoveredBy reg := by
  rw [denseGaussElim_eq]
  split_ifs with hempty
  · exact hcov
  · refine DenseConstraintSystem.substF_covered hcov ?_
    intro i _ t hti z hz
    exact DenseConstraintSystem.occ_valid hcov z
      ((denseGaussElim_loop_invariant bs d).2 i t hti z hz)

/-- **Correctness of `denseGaussElim`.** The empty-map branch is the identity (`refl`); the
    substitution branch is `substF_denseCorrect`, fed the entailment and occurrence-closure of the
    final solution map. -/
theorem denseGaussElim_correct (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseGaussElim bs d) [] bs := by
  have hinv := denseGaussElim_loop_invariant bs d
  rw [denseGaussElim_eq]
  split_ifs with hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DenseConstraintSystem.substF_denseCorrect d _ bs reg.isInput
      (fun denv hsat i t hti => hinv.1 denv hsat i t hti)
      (fun i t hti z hz => hinv.2 i t hti z hz)

/-- The wired dense Gauss-elimination pass (transform `denseGaussElim`, `Gauss.lean`). -/
def denseGaussElimPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs _ d => denseGaussElim bs d)
    (fun _ _ _ => [])
    (fun reg bs _ d hcov => denseGaussElim_covered reg bs d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseGaussElim_correct reg bs d)

end ApcOptimizer.Dense
