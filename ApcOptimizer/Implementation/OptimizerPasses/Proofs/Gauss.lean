import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagUnify

set_option autoImplicit false

/-! # Correctness for the dense Gauss-elimination pass.
Substitution-shaped: correctness rides on `DenseConstraintSystem.substF_denseCorrect`
(`Proofs/DomainBatch.lean`), fed the final solution map's entailment and occurrence closure, both
established by `denseMarkowitzLoop_sound`. -/

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
  grind [densePm1PivotsOf, denseLinearize_eval, DenseLinExpr.trySolve_sound]

/-- Every unit-pivot of a dense constraint entails its equality. -/
theorem denseUnitPivotsOf_sound (c : DenseExpr p) (x : VarId) (t : DenseExpr p)
    (h : (x, t) ∈ denseUnitPivotsOf c) (denv : VarId → ZMod p) (hc : c.eval denv = 0) :
    denv x = t.eval denv := by
  grind [denseUnitPivotsOf, denseLinearize_eval, DenseLinExpr.trySolveUnit_sound]

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

theorem denseSolveAt_sound (c : DenseExpr p) (x y : VarId) (t : DenseExpr p)
    (h : denseSolveAt c x = some (y, t)) (denv : VarId → ZMod p) (hc : c.eval denv = 0) :
    denv y = t.eval denv := by
  unfold denseSolveAt at h
  cases hlin : denseLinearize c with
  | none => simp [hlin] at h
  | some l =>
      rw [hlin] at h
      have hl : l.eval denv = 0 := by rw [← denseLinearize_eval c l hlin]; exact hc
      cases hs : l.trySolve x with
      | none =>
          have hunit : l.trySolveUnit x = some (y, t) := by simpa [hlin, hs] using h
          exact DenseLinExpr.trySolveUnit_sound l x y t hunit denv hl
      | some xt =>
          have hxt : xt = (y, t) := Option.some.inj (by simpa [hlin, hs] using h)
          rw [hxt] at hs
          exact DenseLinExpr.trySolve_sound l x y t hs denv hl

theorem denseSolveAt_vars (c : DenseExpr p) (x y : VarId) (t : DenseExpr p)
    (h : denseSolveAt c x = some (y, t)) : ∀ z ∈ t.vars, z ∈ c.vars := by
  intro z hz
  unfold denseSolveAt at h
  cases hlin : denseLinearize c with
  | none => simp [hlin] at h
  | some l =>
      rw [hlin] at h
      cases hs : l.trySolve x with
      | none =>
          have hunit : l.trySolveUnit x = some (y, t) := by simpa [hlin, hs] using h
          exact denseLinearize_mem_vars c l hlin z
            (denseTrySolveUnit_vars_subset l x (y, t) hunit z hz)
      | some xt =>
          have hxt : xt = (y, t) := Option.some.inj (by simpa [hlin, hs] using h)
          rw [hxt] at hs
          exact denseLinearize_mem_vars c l hlin z
            (denseTrySolve_vars_subset l x (y, t) hs z hz)

theorem denseMarkowitzPick_sound (c : DenseExpr p) (hint y : VarId) (t : DenseExpr p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (h : denseMarkowitzPick c hint occ prot = some (y, t))
    (denv : VarId → ZMod p) (hc : c.eval denv = 0) :
    denv y = t.eval denv := by
  unfold denseMarkowitzPick at h
  cases hs : denseSolveAt c hint with
  | some xt =>
      have hxt : xt = (y, t) := Option.some.inj (by simpa [hs] using h)
      rw [hxt] at hs
      exact denseSolveAt_sound c hint y t hs denv hc
  | none =>
      simp only [hs] at h
      have hfb := h
      rw [denseFastBest_eq] at hfb
      have hmem : (y, t) ∈ densePm1PivotsOf c ++ denseUnitPivotsOf c :=
        List.argmin_mem (by rw [hfb]; exact Option.mem_some_self _)
      rcases List.mem_append.1 hmem with hp | hu
      · exact densePm1PivotsOf_sound c y t hp denv hc
      · exact denseUnitPivotsOf_sound c y t hu denv hc

theorem denseMarkowitzPick_vars (c : DenseExpr p) (hint y : VarId) (t : DenseExpr p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (h : denseMarkowitzPick c hint occ prot = some (y, t)) :
    ∀ z ∈ t.vars, z ∈ c.vars := by
  intro z hz
  unfold denseMarkowitzPick at h
  cases hs : denseSolveAt c hint with
  | some xt =>
      have hxt : xt = (y, t) := Option.some.inj (by simpa [hs] using h)
      rw [hxt] at hs
      exact denseSolveAt_vars c hint y t hs z hz
  | none =>
      simp only [hs] at h
      have hfb := h
      rw [denseFastBest_eq] at hfb
      have hmem : (y, t) ∈ densePm1PivotsOf c ++ denseUnitPivotsOf c :=
        List.argmin_mem (by rw [hfb]; exact Option.mem_some_self _)
      rcases List.mem_append.1 hmem with hp | hu
      · exact densePm1PivotsOf_vars c y t hp z hz
      · exact denseUnitPivotsOf_vars c y t hu z hz

theorem denseMarkowitzLoop_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (sources : Array (DenseExpr p))
    (hsrc : ∀ (i : Nat) (c : DenseExpr p),
      sources[i]? = some c → c ∈ d.algebraicConstraints) :
    ∀ (fuel : Nat) (st : DenseMarkowitzState p) (dσ : DenseSolved p),
      (∀ denv, d.satisfies bs denv → ∀ i t, dσ.fn i = some t → denv i = t.eval denv) →
      (∀ i t, dσ.fn i = some t → ∀ z ∈ t.vars, z ∈ d.occ) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
          (denseMarkowitzLoop occ prot sources fuel st dσ).fn i = some t →
          denv i = t.eval denv) ∧
      (∀ i t, (denseMarkowitzLoop occ prot sources fuel st dσ).fn i = some t →
          ∀ z ∈ t.vars, z ∈ d.occ) := by
  intro fuel
  induction fuel with
  | zero => intro st dσ hσs hσv; exact ⟨hσs, hσv⟩
  | succ fuel ih =>
      intro st dσ hσs hσv
      cases hpop : denseMarkowitzPopValid (st.heap.size + 1) st with
      | none =>
          simp only [denseMarkowitzLoop, hpop]
          exact ⟨hσs, hσv⟩
      | some out =>
          obtain ⟨entry, st'⟩ := out
          cases hsource : sources[entry.rowId]? with
          | none =>
              simp only [denseMarkowitzLoop, hpop, hsource]
              exact ih _ _ hσs hσv
          | some c =>
              have hcmem : c ∈ d.algebraicConstraints := hsrc entry.rowId c hsource
              let c' := (c.substF dσ.fn).normalize
              cases hpick : denseMarkowitzPick c' entry.pivot occ prot with
              | none =>
                  dsimp [c'] at hpick
                  simp only [denseMarkowitzLoop, hpop, hsource, hpick]
                  exact ih _ _ hσs hσv
              | some xt =>
                  obtain ⟨x, t⟩ := xt
                  dsimp [c'] at hpick
                  have hc'occ : ∀ z ∈ c'.vars, z ∈ d.occ := by
                    intro z hz
                    have hz2 : z ∈ (c.substF dσ.fn).vars :=
                      DenseExpr.normalize_vars _ z hz
                    rcases DenseExpr.substF_vars dσ.fn c z hz2 with h | ⟨i, _, tt, hft, hzt⟩
                    · exact DenseConstraintSystem.mem_occ_of_constraint hcmem h
                    · exact hσv i tt hft z hzt
                  have hx : ∀ denv, d.satisfies bs denv → denv x = t.eval denv := by
                    intro denv hsat
                    have hc0 : c.eval denv = 0 := hsat.1 c hcmem
                    have hc'z : c'.eval denv = 0 := by
                      rw [DenseExpr.normalize_eval, DenseExpr.eval_substF,
                          denseEnvF_eq_self dσ.fn denv (hσs denv hsat)]
                      exact hc0
                    exact denseMarkowitzPick_sound c' entry.pivot x t occ prot hpick denv hc'z
                  have htocc : ∀ z ∈ t.vars, z ∈ d.occ := by
                    intro z hz
                    exact hc'occ z (denseMarkowitzPick_vars c' entry.pivot x t occ prot hpick z hz)
                  have htouched : ∀ y s, (y, s) ∈
                        ((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
                          (dσ.map[y]?).bind
                            (fun s => if s.mentions x then some (y, s) else none)) →
                      dσ.fn y = some s := by
                    intro y s hys
                    obtain ⟨_, _, hy'⟩ := List.mem_filterMap.1 hys
                    obtain ⟨s', hs', hif⟩ := Option.bind_eq_some_iff.1 hy'
                    by_cases hm : s'.mentions x
                    · rw [if_pos hm] at hif
                      simp only [Option.some.injEq, Prod.mk.injEq] at hif
                      obtain ⟨rfl, rfl⟩ := hif
                      exact hs'
                    · rw [if_neg hm] at hif
                      exact absurd hif (by simp)
                  let pairs := denseMarkowitzAdoptPairs dσ x t
                  let dσ' := dσ.insertAll pairs
                  have hnexts : ∀ denv, d.satisfies bs denv → ∀ i u,
                      dσ'.fn i = some u → denv i = u.eval denv := by
                    intro denv hsat
                    refine DenseSolved.insertAll_preserves pairs dσ (hσs denv hsat) ?_
                    intro pr hpr
                    unfold denseMarkowitzAdoptPairs at hpr
                    rcases List.mem_append.1 hpr with hin | hin
                    · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
                      have hmemys : dσ.fn y = some s := htouched y s hys
                      have hy : denv y = s.eval denv := hσs denv hsat y s hmemys
                      have hxe : denv x = t.eval denv := hx denv hsat
                      show denv y = ((s.subst x t).normalize).eval denv
                      rw [DenseExpr.normalize_eval, DenseExpr.eval_subst, ← hxe,
                        Function.update_eq_self, hy]
                    · rw [List.mem_singleton] at hin
                      subst hin
                      exact hx denv hsat
                  have hnextv : ∀ i u, dσ'.fn i = some u → ∀ z ∈ u.vars, z ∈ d.occ := by
                    refine DenseSolved.insertAll_preserves pairs dσ hσv ?_
                    intro pr hpr
                    unfold denseMarkowitzAdoptPairs at hpr
                    rcases List.mem_append.1 hpr with hin | hin
                    · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
                      have hmemys : dσ.fn y = some s := htouched y s hys
                      intro z hz
                      have hz2 : z ∈ (s.subst x t).vars := DenseExpr.normalize_vars _ z hz
                      rcases DenseExpr.subst_vars s x t z hz2 with h | h
                      · exact hσv y s hmemys z h
                      · exact htocc z h
                    · rw [List.mem_singleton] at hin
                      subst hin
                      exact htocc
                  simp only [denseMarkowitzLoop, hpop, hsource, hpick]
                  exact ih _ dσ' hnexts hnextv

theorem denseMarkowitzSchedule_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseMarkowitzSchedule d.algebraicConstraints occ prot).fn i = some t →
        denv i = t.eval denv) ∧
    (∀ i t, (denseMarkowitzSchedule d.algebraicConstraints occ prot).fn i = some t →
        ∀ z ∈ t.vars, z ∈ d.occ) := by
  apply denseMarkowitzLoop_sound bs d occ prot d.algebraicConstraints.toArray
  · intro i c hc
    rw [List.getElem?_toArray] at hc
    exact List.mem_of_getElem? hc
  · intro _ _ _ _ h
    exact absurd h (by simp [DenseSolved.fn, DenseSolved.empty])
  · intro _ _ h
    exact absurd h (by simp [DenseSolved.fn, DenseSolved.empty])

/-! ## The pass's correctness -/

/-- The scheduled solution map is entailed and occurrence-closed. -/
theorem denseGaussElim_loop_invariant (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseMarkowitzSchedule d.algebraicConstraints
          (denseOccurrenceMap d) (denseProtectedVars d bs)).fn i = some t →
          denv i = t.eval denv) ∧
    (∀ i t, (denseMarkowitzSchedule d.algebraicConstraints
        (denseOccurrenceMap d) (denseProtectedVars d bs)).fn i = some t →
        ∀ z ∈ t.vars, z ∈ d.occ) := by
  exact denseMarkowitzSchedule_sound bs d (denseOccurrenceMap d) (denseProtectedVars d bs)

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
