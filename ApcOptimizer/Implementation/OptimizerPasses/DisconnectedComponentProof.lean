import ApcOptimizer.Implementation.OptimizerPasses.DisconnectedComponent

set_option autoImplicit false

/-! # Disconnected-component removal — native dense correctness (Task 3, prover)

Native `DensePassCorrect` for the dense disconnected-component transform (`denseDisconnectedF`,
`DisconnectedComponent.lean`), lifted to the audited `Variable` spec through
`DenseVerifiedPassW.ofNative` (`Bridge.lean`), and wired at the `disconnected` cleanup label.

The proof is a direct native re-derivation of the spec's `dropComponent_correct`
 over `VarId → ZMod p` environments — **it does not
depend on the spec pass**. Exactly as in the spec, correctness is *generic in the removable set*
(`DensePassCorrect.denseDropComponent`, stated for an arbitrary `remV`/`keepCon`/`keepBi`), so the
well-founded connectivity search (`denseBfsClosure`/`denseConnBad`) is never reasoned about: the
pass re-checks the induced partition at run time (`denseDropCheck`) and the seven hypotheses of
`denseDropComponent` are read off that check. This is the mandated route for a `partial def` spec
helper (no equational lemmas): prove correctness over the checked property, not over the search.

## The argument (mirrors `dropComponent_correct`)

The drop keeps `env` on kept variables and substitutes the all-zero witness `w` on removed ones
(`m env`). Soundness (`out.implies d`) extends an output assignment by `w`: removed constraints
vanish and removed interactions non-violate under `w` (from the check), kept items are untouched by
the substitution (their variables are non-removable, so `m env = env` on them). Removed
interactions are stateless (from the check), so side effects and admissibility are unchanged
(`denseSideEffects_drop_eq`/`denseAdmissibleFilter_eq`). Completeness is on the same env (the output
is a sub-system). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Evaluation congruence (file-local) -/

/-- Dense expression evaluation depends only on the variables that occur. (File-local; the public
    copy lives in `DomainBatch.lean`, off this module's import path.) -/
private theorem dcExprEvalCongr (e : DenseExpr p) (f g : VarId → ZMod p)
    (h : ∀ i ∈ e.vars, f i = g i) : e.eval f = e.eval g := by
  induction e with
  | const n => rfl
  | var i => exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
      simp only [DenseExpr.eval]
      rw [iha (fun i hi => h i (by simp [DenseExpr.vars, hi])),
          ihb (fun i hi => h i (by simp [DenseExpr.vars, hi]))]
  | mul a b iha ihb =>
      simp only [DenseExpr.eval]
      rw [iha (fun i hi => h i (by simp [DenseExpr.vars, hi])),
          ihb (fun i hi => h i (by simp [DenseExpr.vars, hi]))]

/-! ## Side effects are unchanged when dropping stateless interactions

Native mirror of `sideEffects_drop_eq`: the evaluated stateful interactions of the filtered system
(under `e1`) equal those of the original (under `e2`), given every dropped interaction is stateless
and every *stateful* interaction evaluates the same under `e1` and `e2`. -/
theorem denseSideEffects_drop_eq (bs : BusSemantics p) (keepBi : BusInteraction (DenseExpr p) → Bool)
    (e1 e2 : VarId → ZMod p) (L : List (BusInteraction (DenseExpr p)))
    (hst : ∀ bi ∈ L, keepBi bi = false → bs.isStateful bi.busId = false)
    (heq : ∀ bi ∈ L, bs.isStateful bi.busId = true → denseBIEval bi e2 = denseBIEval bi e1) :
    ((L.filter keepBi).filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := denseBIEval bi e1; ((m.busId, m.payload), m.multiplicity))
      = (L.filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := denseBIEval bi e2; ((m.busId, m.payload), m.multiplicity)) := by
  induction L with
  | nil => rfl
  | cons bi rest ih =>
    have ihr := ih (fun b hb => hst b (List.mem_cons_of_mem _ hb))
                   (fun b hb => heq b (List.mem_cons_of_mem _ hb))
    by_cases hstate : bs.isStateful bi.busId = true
    · have hkeep : keepBi bi = true := by
        by_contra hk
        have hkf : keepBi bi = false := by simpa using hk
        rw [hst bi (List.mem_cons_self ..) hkf] at hstate
        exact absurd hstate (by simp)
      rw [List.filter_cons_of_pos hkeep,
          List.filter_cons_of_pos (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate,
          List.filter_cons_of_pos (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate]
      simp only [List.map_cons]
      rw [heq bi (List.mem_cons_self ..) hstate, ihr]
    · have hns : bs.isStateful bi.busId = false := by simpa using hstate
      rw [List.filter_cons_of_neg (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) (by simp [hns])]
      by_cases hkeep : keepBi bi = true
      · rw [List.filter_cons_of_pos hkeep,
            List.filter_cons_of_neg (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) (by simp [hns])]
        exact ihr
      · rw [List.filter_cons_of_neg hkeep]
        exact ihr

/-- Admissibility is unchanged when dropping stateless interactions: the stateful-non-zero filter of
    the mapped, filtered list equals that of the mapped full list. Native mirror of the effect of
    `admissible_filterBus`. -/
theorem denseAdmissibleFilter_eq (bs : BusSemantics p) (keepBi : BusInteraction (DenseExpr p) → Bool)
    (denv : VarId → ZMod p) (L : List (BusInteraction (DenseExpr p)))
    (hst : ∀ bi ∈ L, keepBi bi = false → bs.isStateful bi.busId = false) :
    ((L.filter keepBi).map (fun bi => denseBIEval bi denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = (L.map (fun bi => denseBIEval bi denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
  induction L with
  | nil => rfl
  | cons bi rest ih =>
    have hrest := ih (fun b hb hkf => hst b (List.mem_cons_of_mem _ hb) hkf)
    by_cases hk : keepBi bi = true
    · rw [List.filter_cons_of_pos hk]
      simp only [List.map_cons, List.filter_cons, hrest]
    · have hbusId : (denseBIEval bi denv).busId = bi.busId := rfl
      have hstf : bs.isStateful bi.busId = false := hst bi (List.mem_cons_self ..) (by simpa using hk)
      have hPfalse : (decide ((denseBIEval bi denv).multiplicity ≠ 0)
          && bs.isStateful (denseBIEval bi denv).busId) = false := by
        rw [hbusId, hstf, Bool.and_false]
      rw [List.filter_cons_of_neg (by simpa using hk), List.map_cons]
      simp only [List.filter_cons, hPfalse, Bool.false_eq_true, if_false]
      exact hrest

/-! ## The general correctness lemma -/

/-- **Native disconnected-component drop correctness.** Dropping a disconnected, witness-satisfiable
    component preserves correctness. Native mirror of `dropComponent_correct`, generic in the
    removable set `remV` and the keep predicates `keepCon`/`keepBi`: removed items have all-removable
    variables, the witness `w` zeroes removed constraints and non-violates removed interactions,
    removed interactions are stateless, and kept items use only non-removable variables. -/
theorem DensePassCorrect.denseDropComponent (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (isInput : VarId → Bool) (w : VarId → ZMod p) (remV : VarId → Bool)
    (keepCon : DenseExpr p → Bool) (keepBi : BusInteraction (DenseExpr p) → Bool)
    (hCrem : ∀ c ∈ d.algebraicConstraints, keepCon c = false → ∀ x ∈ c.vars, remV x = true)
    (hCsat : ∀ c ∈ d.algebraicConstraints, keepCon c = false → c.eval w = 0)
    (hCkeep : ∀ c ∈ d.algebraicConstraints, keepCon c = true → ∀ x ∈ c.vars, remV x = false)
    (hBrem : ∀ bi ∈ d.busInteractions, keepBi bi = false → ∀ x ∈ denseBIVars bi, remV x = true)
    (hBsat : ∀ bi ∈ d.busInteractions, keepBi bi = false →
        bs.violatesConstraint (denseBIEval bi w) = false)
    (hBstateless : ∀ bi ∈ d.busInteractions, keepBi bi = false → bs.isStateful bi.busId = false)
    (hBkeep : ∀ bi ∈ d.busInteractions, keepBi bi = true → ∀ x ∈ denseBIVars bi, remV x = false) :
    DensePassCorrect isInput d
      { algebraicConstraints := d.algebraicConstraints.filter keepCon,
        busInteractions := d.busInteractions.filter keepBi } [] bs := by
  -- the merge: keep `env` on kept variables, use the witness on removed ones
  set m : (VarId → ZMod p) → (VarId → ZMod p) :=
    fun env x => if remV x = true then w x else env x with hm
  have hmwC : ∀ env (e : DenseExpr p), (∀ x ∈ e.vars, remV x = true) →
      e.eval (m env) = e.eval w := by
    intro env e he
    exact dcExprEvalCongr e _ _ (fun x hx => by simp [hm, he x hx])
  have hmeC : ∀ env (e : DenseExpr p), (∀ x ∈ e.vars, remV x = false) →
      e.eval (m env) = e.eval env := by
    intro env e he
    exact dcExprEvalCongr e _ _ (fun x hx => by simp [hm, he x hx])
  have hmwB : ∀ env (bi : BusInteraction (DenseExpr p)), (∀ x ∈ denseBIVars bi, remV x = true) →
      denseBIEval bi (m env) = denseBIEval bi w := by
    intro env bi hbi
    exact denseBIEval_congr bi _ _ (fun x hx => by simp [hm, hbi x hx])
  have hmeB : ∀ env (bi : BusInteraction (DenseExpr p)), (∀ x ∈ denseBIVars bi, remV x = false) →
      denseBIEval bi (m env) = denseBIEval bi env := by
    intro env bi hbi
    exact denseBIEval_congr bi _ _ (fun x hx => by simp [hm, hbi x hx])
  -- a stateful interaction is always kept
  have hstKeep : ∀ bi ∈ d.busInteractions, bs.isStateful bi.busId = true → keepBi bi = true := by
    intro bi hbi hstate
    by_contra hk
    rw [hBstateless bi hbi (by simpa using hk)] at hstate
    exact absurd hstate (by simp)
  -- extending a satisfying assignment of the output by the witness satisfies the input
  have keySat : ∀ env,
      (∀ c ∈ d.algebraicConstraints.filter keepCon, c.eval env = 0) →
      (∀ bi ∈ d.busInteractions.filter keepBi,
        (denseBIEval bi env).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi env) = false) →
      d.satisfies bs (m env) := by
    intro env hsc hsb
    refine ⟨fun c hc => ?_, fun bi hbi hne => ?_⟩
    · by_cases hk : keepCon c = true
      · rw [hmeC env c (hCkeep c hc hk)]
        exact hsc c (List.mem_filter.2 ⟨hc, hk⟩)
      · rw [hmwC env c (hCrem c hc (by simpa using hk))]
        exact hCsat c hc (by simpa using hk)
    · by_cases hk : keepBi bi = true
      · rw [hmeB env bi (hBkeep bi hbi hk)] at hne ⊢
        exact hsb bi (List.mem_filter.2 ⟨hbi, hk⟩) hne
      · rw [hmwB env bi (hBrem bi hbi (by simpa using hk))]
        exact hBsat bi hbi (by simpa using hk)
  refine DensePassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  · -- soundness: out.implies d
    intro env hsat
    refine ⟨m env, keySat env hsat.1 hsat.2, ?_⟩
    have hse : ({ algebraicConstraints := d.algebraicConstraints.filter keepCon,
                  busInteractions := d.busInteractions.filter keepBi } :
                  DenseConstraintSystem p).sideEffects bs env = d.sideEffects bs (m env) :=
      denseSideEffects_drop_eq bs keepBi env (m env) d.busInteractions
        (fun bi hbi hkf => hBstateless bi hbi hkf)
        (fun bi hbi hstate => hmeB env bi (hBkeep bi hbi (hstKeep bi hbi hstate)))
    rw [hse]; exact BusState.equiv_refl _
  · -- invariant preservation
    intro hgi env hsat bi hbi
    show (denseBIEval bi env).multiplicity ≠ 0 → bs.breaksInvariant (denseBIEval bi env) = false
    have hbimem : bi ∈ d.busInteractions := (List.mem_filter.1 hbi).1
    have hbikeep : keepBi bi = true := (List.mem_filter.1 hbi).2
    have hsatm : d.satisfies bs (m env) := keySat env hsat.1 hsat.2
    have heval : denseBIEval bi (m env) = denseBIEval bi env := hmeB env bi (hBkeep bi hbimem hbikeep)
    have key := hgi (m env) hsatm bi hbimem
    simp only [heval] at key
    exact key
  · -- introduces no new variable (both lists filtered)
    intro i hi
    simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi ⊢
    rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
    · exact Or.inl ⟨c, List.mem_of_mem_filter hc, hic⟩
    · exact Or.inr ⟨bi, List.mem_of_mem_filter hbi, hib⟩
  · -- completeness: same env
    intro env hadm hsat
    refine ⟨⟨fun c hc => hsat.1 c (List.mem_of_mem_filter hc),
             fun bi hbi => hsat.2 bi (List.mem_of_mem_filter hbi)⟩, ?_, ?_⟩
    · -- admissibility carries over (dropped interactions are stateless)
      show bs.admissible ((((d.algebraicConstraints.filter keepCon,
        d.busInteractions.filter keepBi).2).map (fun bi => denseBIEval bi env)).filter
          (fun msg => decide (msg.multiplicity ≠ 0) && bs.isStateful msg.busId))
      rw [denseAdmissibleFilter_eq bs keepBi env d.busInteractions
        (fun bi hbi hkf => hBstateless bi hbi hkf)]
      exact hadm
    · -- side effects: d under env = out under env
      have hse : ({ algebraicConstraints := d.algebraicConstraints.filter keepCon,
                    busInteractions := d.busInteractions.filter keepBi } :
                    DenseConstraintSystem p).sideEffects bs env = d.sideEffects bs env :=
        denseSideEffects_drop_eq bs keepBi env env d.busInteractions
          (fun bi hbi hkf => hBstateless bi hbi hkf) (fun _ _ _ => rfl)
      rw [hse]; exact BusState.equiv_refl _

/-! ## The guarded drop -/

/-- The guarded drop preserves coverage: both lists are filtered (subsets); the identity branch is
    the input. -/
theorem denseDropGuarded_covered {reg : VarRegistry} (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (remV : VarId → Bool) (hc : d.CoveredBy reg) :
    (denseDropGuarded bs d remV).CoveredBy reg := by
  unfold denseDropGuarded
  split_ifs with h
  · exact ⟨fun e he => hc.1 e (List.mem_of_mem_filter he),
           fun bi hbi => hc.2 bi (List.mem_of_mem_filter hbi)⟩
  · exact hc

/-- **The guarded drop is natively correct** for *any* `remV` — the run-time re-check
    (`denseDropCheck`) supplies exactly the seven `denseDropComponent` hypotheses, so correctness is
    independent of the connectivity search that produced `remV`. Native mirror of the spec pass's
    `hchk`-guarded body. -/
theorem denseDropGuarded_correct (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (remV : VarId → Bool) :
    DensePassCorrect isInput d (denseDropGuarded bs d remV) [] bs := by
  unfold denseDropGuarded
  split_ifs with hchk
  · unfold denseDropCheck at hchk
    simp only [Bool.and_eq_true, and_assoc] at hchk
    obtain ⟨_hne, hcz, hbz, hck, hbk⟩ := hchk
    refine DensePassCorrect.denseDropComponent d bs isInput (fun _ => 0) remV
      (denseKeepConWith remV) (denseKeepBiWith bs remV) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- hCrem
      intro c _ hkf x hx
      simp only [denseKeepConWith, Bool.or_eq_false_iff] at hkf
      exact (List.all_eq_true.1 (by simpa using hkf.2)) x hx
    · -- hCsat
      intro c hc hkf
      have h1 := (List.all_eq_true.1 hcz) c hc
      rw [hkf, Bool.false_or] at h1
      exact of_decide_eq_true h1
    · -- hCkeep
      intro c hc hkt x hx
      have h1 := (List.all_eq_true.1 hck) c hc
      rw [hkt] at h1
      simp only [Bool.not_true, Bool.false_or] at h1
      simpa using (List.all_eq_true.1 h1) x hx
    · -- hBrem
      intro bi _ hkf x hx
      simp only [denseKeepBiWith, Bool.or_eq_false_iff] at hkf
      exact (List.all_eq_true.1 (by simpa using hkf.2)) x hx
    · -- hBsat
      intro bi hbi hkf
      have h1 := (List.all_eq_true.1 hbz) bi hbi
      rw [hkf, Bool.false_or] at h1
      simpa using h1
    · -- hBstateless
      intro bi _ hkf
      simp only [denseKeepBiWith, Bool.or_eq_false_iff] at hkf
      exact hkf.1.1
    · -- hBkeep
      intro bi hbi hkt x hx
      have h1 := (List.all_eq_true.1 hbk) bi hbi
      rw [hkt] at h1
      simp only [Bool.not_true, Bool.false_or] at h1
      simpa using (List.all_eq_true.1 h1) x hx
  · exact DensePassCorrect.refl isInput d bs

/-! ## The dense pass -/

theorem denseDisconnectedF_covered {reg : VarRegistry} (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (hc : d.CoveredBy reg) :
    (denseDisconnectedF bs d).CoveredBy reg := by
  unfold denseDisconnectedF
  exact denseDropGuarded_covered bs d _ hc

theorem denseDisconnectedF_correct (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d (denseDisconnectedF bs d) [] bs := by
  unfold denseDisconnectedF
  exact denseDropGuarded_correct bs isInput d _

/-- **The native dense disconnected-component pass.** Fact-free — the `ofNative` transform ignores
    `facts` (the spec pass is a `VerifiedPass`). Registry unchanged (no fresh variables), no
    derivations. -/
def denseDisconnectedPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofNative (fun bs _ d => denseDisconnectedF bs d) (fun _ _ _ => [])
    (fun reg bs _ d hcov => denseDisconnectedF_covered bs d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseDisconnectedF_correct bs reg.isInput d)

end ApcOptimizer.Dense
