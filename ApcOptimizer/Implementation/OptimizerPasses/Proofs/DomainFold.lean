import ApcOptimizer.Implementation.OptimizerPasses.DomainFoldRuntime
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch

set_option autoImplicit false

/-! # Correctness for the value-only dense `domainFold`

Proves `DensePassCorrect` for the fold of `DomainFoldRuntime.lean`. The fold is a pure rewrite: any
assignment satisfying either system pins the group to a survivor, under which the rewrite agrees
with the identity — so `env' = env` is the completeness witness and no derivations are produced. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Domain soundness -/

theorem denseFindDomainAlg_sound [Fact p.Prime] (denv : VarId → ZMod p) :
    ∀ (all : List (DenseExpr p)) (i : VarId) (dm : List (ZMod p)),
      denseFindDomainAlg all i = some dm → (∀ c ∈ all, c.eval denv = 0) → denv i ∈ dm := by
  intro all
  induction all with
  | nil => intro i dm h _; simp [denseFindDomainAlg] at h
  | cons c rest ih =>
      intro i dm h hsat
      rw [denseFindDomainAlg] at h
      by_cases hm : c.mentions i = true
      · rw [if_pos hm] at h
        cases hr : denseRootsIn i c with
        | some d' =>
            rw [hr] at h; simp only [Option.some.injEq] at h; subst h
            exact denseRootsIn_sound i c d' hr denv (hsat c (List.mem_cons_self ..))
        | none =>
            rw [hr] at h
            exact ih i dm h (fun c' hc' => hsat c' (List.mem_cons_of_mem _ hc'))
      · rw [if_neg (by simpa using hm)] at h
        exact ih i dm h (fun c' hc' => hsat c' (List.mem_cons_of_mem _ hc'))

theorem denseGroupDoms_sound [Fact p.Prime] (denv : VarId → ZMod p) (es : List (DenseExpr p))
    (hsat : ∀ c ∈ es, c.eval denv = 0) :
    ∀ (xs : List VarId) (doms : List (VarId × List (ZMod p))),
      denseGroupDoms es xs = some doms → ∀ yd ∈ doms, denv yd.1 ∈ yd.2 := by
  intro xs
  induction xs with
  | nil =>
      intro doms h yd hyd
      simp only [denseGroupDoms, Option.some.injEq] at h; subst h; simp at hyd
  | cons i rest ih =>
      intro doms h yd hyd
      rw [denseGroupDoms] at h
      cases hd : denseFindDomainAlg es i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some dm =>
          cases hr : denseGroupDoms es rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds =>
              rw [hd, hr] at h; simp only [Option.some.injEq] at h; subst h
              rcases List.mem_cons.1 hyd with rfl | hmem
              · exact denseFindDomainAlg_sound denv es i dm hd hsat
              · exact ih ds hr yd hmem

/-! ## Value-only survivor certificate -/

theorem mem_denseAssignmentsV_of_sound (denv : VarId → ZMod p) :
    ∀ (doms : List (VarId × List (ZMod p))), (∀ yd ∈ doms, denv yd.1 ∈ yd.2) →
      (doms.map (fun yd => denv yd.1)) ∈ denseAssignmentsV (doms.map Prod.snd) := by
  intro doms
  induction doms with
  | nil => intro _; simp [denseAssignmentsV]
  | cons yd rest ih =>
      intro hsound
      obtain ⟨i, dm⟩ := yd
      have hhead : denv i ∈ dm := hsound (i, dm) (List.mem_cons_self ..)
      have htail : (rest.map (fun yd => denv yd.1)) ∈ denseAssignmentsV (rest.map Prod.snd) :=
        ih (fun yd hyd => hsound yd (List.mem_cons_of_mem _ hyd))
      show (denv i :: rest.map (fun yd => denv yd.1)) ∈ denseAssignmentsV (dm :: rest.map Prod.snd)
      rw [denseAssignmentsV, List.mem_flatMap]
      exact ⟨rest.map (fun yd => denv yd.1), htail, List.mem_map.2 ⟨denv i, hhead, rfl⟩⟩

theorem denseGroupSurvivorsEV_eq (es : List (DenseExpr p)) (xs : List VarId)
    (domVals : List (List (ZMod p))) :
    denseGroupSurvivorsEV es xs domVals
      = (denseAssignmentsV domVals).filter
          (fun a => es.all (fun c => decide (c.eval (denseEnvOfKeysV xs a) = 0))) := by
  unfold denseGroupSurvivorsEV
  cases hce : denseCompileEs xs es with
  | none => rfl
  | some ces =>
      apply List.filter_congr
      intro a _
      show denseSurvZeroCWV denseZModOps (fun v => decide (v = denseZModOps.zero)) ces a
        = es.all (fun c => decide (c.eval (denseEnvOfKeysV xs a) = 0))
      unfold denseSurvZeroCWV
      exact denseCompileEs_allV denseZModOps _ (fun _ => rfl) xs a es ces hce

theorem mem_denseGroupSurvivorsEV (es : List (DenseExpr p)) (xs : List VarId)
    (domVals : List (List (ZMod p))) (pt : List (ZMod p)) (hmem : pt ∈ denseAssignmentsV domVals)
    (hzero : ∀ c ∈ es, c.eval (denseEnvOfKeysV xs pt) = 0) :
    pt ∈ denseGroupSurvivorsEV es xs domVals := by
  rw [denseGroupSurvivorsEV_eq, List.mem_filter]
  refine ⟨hmem, ?_⟩
  rw [List.all_eq_true]
  intro c hc
  rw [decide_eq_true_eq]
  exact hzero c hc

theorem denseConstOnSurvsV_sound (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) (c : ZMod p) (h : denseConstOnSurvsV xs survsV e = some c) :
    ∀ s ∈ survsV, e.eval (denseEnvOfKeysV xs s) = c := by
  rcases survsV with _ | ⟨s₀, rest⟩ <;> grind [denseConstOnSurvsV, denseCompileE_evalV]

/-! ## The fold rewrite: agreement and variable containment (value-only) -/

theorem denseFoldRewriteGoV_agree (xs : List VarId) (survsV : List (List (ZMod p)))
    (denv : VarId → ZMod p) (pt : List (ZMod p)) (hpt : pt ∈ survsV)
    (hcongr : ∀ e : DenseExpr p, e.varsInF xs = true →
      e.eval denv = e.eval (denseEnvOfKeysV xs pt)) :
    ∀ e : DenseExpr p, (denseFoldRewriteGoV xs survsV e).eval denv = e.eval denv := by
  intro e
  induction e with
  | const c => rfl
  | var y => rfl
  | add a b iha ihb =>
      unfold denseFoldRewriteGoV
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]
        cases hc : denseConstOnSurvsV xs survsV (DenseExpr.add a b) with
        | none =>
            show (denseFoldRewriteGoV xs survsV a).eval denv + (denseFoldRewriteGoV xs survsV b).eval denv
              = a.eval denv + b.eval denv
            rw [iha, ihb]
        | some c =>
            have h2 := denseConstOnSurvsV_sound xs survsV (DenseExpr.add a b) c hc pt hpt
            have h1 := hcongr (DenseExpr.add a b) hin
            show c = (DenseExpr.add a b).eval denv
            rw [h1, h2]
      · rw [if_neg (by simpa using hin)]
        show (denseFoldRewriteGoV xs survsV a).eval denv + (denseFoldRewriteGoV xs survsV b).eval denv
          = a.eval denv + b.eval denv
        rw [iha, ihb]
  | mul a b iha ihb =>
      unfold denseFoldRewriteGoV
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]
        cases hc : denseConstOnSurvsV xs survsV (DenseExpr.mul a b) with
        | none =>
            show (denseFoldRewriteGoV xs survsV a).eval denv * (denseFoldRewriteGoV xs survsV b).eval denv
              = a.eval denv * b.eval denv
            rw [iha, ihb]
        | some c =>
            have h2 := denseConstOnSurvsV_sound xs survsV (DenseExpr.mul a b) c hc pt hpt
            have h1 := hcongr (DenseExpr.mul a b) hin
            show c = (DenseExpr.mul a b).eval denv
            rw [h1, h2]
      · rw [if_neg (by simpa using hin)]
        show (denseFoldRewriteGoV xs survsV a).eval denv * (denseFoldRewriteGoV xs survsV b).eval denv
          = a.eval denv * b.eval denv
        rw [iha, ihb]

theorem denseFoldRewriteV_agree_covered [Fact p.Prime] (d : DenseConstraintSystem p)
    (xs : List VarId) (doms : List (VarId × List (ZMod p)))
    (hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs = some doms) (denv : VarId → ZMod p)
    (hcov : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0) :
    ∀ e : DenseExpr p,
      (denseFoldRewriteV xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd)) e).eval denv
        = e.eval denv := by
  have hkeys : doms.map Prod.fst = xs := denseGroupDoms_fst (denseCoveredCsOf d xs) xs doms hdoms
  have hsound_doms : ∀ yd ∈ doms, denv yd.1 ∈ yd.2 :=
    denseGroupDoms_sound denv (denseCoveredCsOf d xs) hcov xs doms hdoms
  have hpteq : xs.map denv = doms.map (fun yd => denv yd.1) := by
    rw [← hkeys, List.map_map]; rfl
  have hmemA : (xs.map denv) ∈ denseAssignmentsV (doms.map Prod.snd) := by
    rw [hpteq]; exact mem_denseAssignmentsV_of_sound denv doms hsound_doms
  have hcovVars : ∀ c ∈ denseCoveredCsOf d xs, c.varsInF xs = true := by
    intro c hc
    have hcf : c ∈ d.algebraicConstraints.filter (denseCoveredBy xs) := hc
    have hcb : denseCoveredBy xs c = true := (List.mem_filter.1 hcf).2
    rw [denseCoveredBy, Bool.and_eq_true] at hcb
    exact hcb.2
  have hzero : ∀ c ∈ denseCoveredCsOf d xs, c.eval (denseEnvOfKeysV xs (xs.map denv)) = 0 := by
    intro c hc
    have hvin := denseVarsInF_sound xs c (hcovVars c hc)
    have hce : c.eval (denseEnvOfKeysV xs (xs.map denv)) = c.eval denv :=
      DenseExpr.eval_congr c _ _ (fun v hv => denseEnvOfKeysV_map denv xs v (hvin v hv))
    rw [hce]; exact hcov c hc
  have hptSurv : (xs.map denv) ∈ denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd) :=
    mem_denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd) (xs.map denv) hmemA hzero
  have hcongr : ∀ e : DenseExpr p, e.varsInF xs = true →
      e.eval denv = e.eval (denseEnvOfKeysV xs (xs.map denv)) := by
    intro e he
    refine DenseExpr.eval_congr e _ _ (fun v hv => ?_)
    exact (denseEnvOfKeysV_map denv xs v (denseVarsInF_sound xs e he v hv)).symm
  intro e
  unfold denseFoldRewriteV
  split
  · exact denseFoldRewriteGoV_agree xs
      (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd)) denv (xs.map denv)
      hptSurv hcongr e
  · rfl

/-- Folding introduces no `VarId` (value-only core). -/
theorem denseFoldRewriteGoV_vars (xs : List VarId) (survsV : List (List (ZMod p))) (e : DenseExpr p) :
    ∀ i ∈ (denseFoldRewriteGoV xs survsV e).vars, i ∈ e.vars := by
  induction e with
  | const c => intro i hi; simp [denseFoldRewriteGoV, DenseExpr.vars] at hi
  | var y => intro i hi; exact hi
  | add a b iha ihb =>
      unfold denseFoldRewriteGoV
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]
        cases denseConstOnSurvsV xs survsV (DenseExpr.add a b) with
        | none =>
            intro i hi; simp only [DenseExpr.vars, List.mem_append] at hi ⊢
            rcases hi with hi | hi
            · exact Or.inl (iha i hi)
            · exact Or.inr (ihb i hi)
        | some c => intro i hi; simp [DenseExpr.vars] at hi
      · rw [if_neg (by simpa using hin)]
        intro i hi; simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inl (iha i hi)
        · exact Or.inr (ihb i hi)
  | mul a b iha ihb =>
      unfold denseFoldRewriteGoV
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]
        cases denseConstOnSurvsV xs survsV (DenseExpr.mul a b) with
        | none =>
            intro i hi; simp only [DenseExpr.vars, List.mem_append] at hi ⊢
            rcases hi with hi | hi
            · exact Or.inl (iha i hi)
            · exact Or.inr (ihb i hi)
        | some c => intro i hi; simp [DenseExpr.vars] at hi
      · rw [if_neg (by simpa using hin)]
        intro i hi; simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inl (iha i hi)
        · exact Or.inr (ihb i hi)

theorem denseFoldRewriteV_vars (xs : List VarId) (survsV : List (List (ZMod p))) (e : DenseExpr p) :
    ∀ i ∈ (denseFoldRewriteV xs survsV e).vars, i ∈ e.vars := by
  intro i hi
  unfold denseFoldRewriteV at hi
  split at hi
  · exact denseFoldRewriteGoV_vars xs survsV e i hi
  · exact hi

theorem denseFoldRewriteV_covered (reg : VarRegistry) (xs : List VarId)
    (survsV : List (List (ZMod p))) {e : DenseExpr p} (hc : e.CoveredBy reg) :
    (denseFoldRewriteV xs survsV e).CoveredBy reg :=
  fun i hi => hc i (denseFoldRewriteV_vars xs survsV e i hi)

/-! ## Single-fold correctness -/

theorem denseFoldOutV_correct [Fact p.Prime] (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (doms : List (VarId × List (ZMod p)))
    (hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs = some doms) (isInput : VarId → Bool) :
    DensePassCorrect isInput d
      (denseFoldOutV d xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd))) [] bs := by
  set survsV := denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd) with hsurv_def
  have hagCov : ∀ denv : VarId → ZMod p, (∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0) →
      ∀ e : DenseExpr p, (denseFoldRewriteV xs survsV e).eval denv = e.eval denv := by
    intro denv hcov
    rw [hsurv_def]
    exact denseFoldRewriteV_agree_covered d xs doms hdoms denv hcov
  refine DensePassCorrect.ofEvalAgree
    (fun denv => ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0)
    (denseFoldRewriteV xs survsV) rfl ?_ ?_ hagCov ?_ ?_ ?_
    (fun e i hi => denseFoldRewriteV_vars xs survsV e i hi)
  · -- a covered constraint sits verbatim in the output
    intro denv hsatout c hc
    exact hsatout.1 c (show c ∈ (denseFoldOutV d xs survsV).algebraicConstraints from
      List.mem_append_right _ hc)
  · exact fun denv hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  · -- input constraints vanish when the output's do
    intro denv hA hout c hc
    by_cases hccov : denseCoveredBy xs c = true
    · exact hA c (List.mem_filter.2 ⟨hc, hccov⟩)
    · have hz := hout _ (show denseFoldRewriteV xs survsV c
          ∈ (denseFoldOutV d xs survsV).algebraicConstraints from
        List.mem_append_left _
          (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hccov⟩, rfl⟩))
      rwa [hagCov denv hA c] at hz
  · -- output constraints vanish when the input's do
    intro denv hA hd c' hc'
    have hc'2 : c' ∈ (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseFoldRewriteV xs survsV) ++ denseCoveredCsOf d xs := hc'
    rcases List.mem_append.1 hc'2 with h | h
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
      rw [hagCov denv hA c0]
      exact hd c0 (List.mem_of_mem_filter hc0)
    · exact hd c' (List.mem_of_mem_filter h)
  · -- output constraints read only occurring variables
    intro c' hc' i hi
    have hc'2 : c' ∈ (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseFoldRewriteV xs survsV) ++ denseCoveredCsOf d xs := hc'
    rcases List.mem_append.1 hc'2 with h | h
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
      exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc0)
        (denseFoldRewriteV_vars xs survsV c0 i hi)
    · exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter h) hi

/-! ## Coverage preservation (value-only fold) -/

theorem denseFoldOutV_covered (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (xs : List VarId) (survsV : List (List (ZMod p))) :
    (denseFoldOutV d xs survsV).CoveredBy reg := by
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · have he' : e ∈ (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseFoldRewriteV xs survsV) ++ denseCoveredCsOf d xs := he
    rcases List.mem_append.1 he' with h | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact denseFoldRewriteV_covered reg xs survsV (hcov.1 c (List.mem_of_mem_filter hc))
    · exact hcov.1 e (List.mem_of_mem_filter h)
  · have hbi' : bi ∈ d.busInteractions.map
        (fun bi => { bi with
          multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
          payload := bi.payload.map (denseFoldRewriteV xs survsV) }) := hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    obtain ⟨hm, hp⟩ := hcov.2 bi0 hbi0
    refine ⟨denseFoldRewriteV_covered reg xs survsV hm, fun e he => ?_⟩
    have he' : e ∈ bi0.payload.map (denseFoldRewriteV xs survsV) := he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he'
    exact denseFoldRewriteV_covered reg xs survsV (hp e0 he0)

/-! ## The direct fold loop -/

theorem denseFoldStepWithV_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (xs : List VarId) (es csRest : List (DenseExpr p))
    (hes : es = denseCoveredCsOf d xs) :
    DensePassCorrect isInput d (denseFoldStepWithV d xs es csRest) [] bs := by
  subst hes
  unfold denseFoldStepWithV
  split
  · exact DensePassCorrect_refl isInput d bs
  · rename_i doms hgd
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hgate : (1 ≤ (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd)).length
          && denseSystemHasFoldableWV d xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd)) csRest) = true
      · rw [if_pos hgate]
        exact denseFoldOutV_correct bs d xs doms hgd isInput
      · rw [if_neg (by simpa using hgate)]; exact DensePassCorrect_refl isInput d bs
    · rw [if_neg hp]; exact DensePassCorrect_refl isInput d bs

theorem denseFoldStepWithV_covered (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (xs : List VarId) (es csRest : List (DenseExpr p)) :
    (denseFoldStepWithV d xs es csRest).CoveredBy reg := by
  unfold denseFoldStepWithV
  split
  · exact hcov
  · rename_i doms _
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hgate : (1 ≤ (denseGroupSurvivorsEV es xs (doms.map Prod.snd)).length
          && denseSystemHasFoldableWV d xs (denseGroupSurvivorsEV es xs (doms.map Prod.snd)) csRest) = true
      · rw [if_pos hgate]; exact denseFoldOutV_covered reg d hcov xs _
      · rw [if_neg (by simpa using hgate)]; exact hcov
    · rw [if_neg hp]; exact hcov

theorem denseFoldLoopDirectV_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p),
      DensePassCorrect isInput d (denseFoldLoopDirectV targets d) [] bs := by
  intro targets
  induction targets with
  | nil => intro d; exact DensePassCorrect_refl isInput d bs
  | cons xs rest ih =>
      intro d
      simp only [denseFoldLoopDirectV, List.partition_eq_filter_filter]
      exact DensePassCorrect.trans
        (denseFoldStepWithV_correct bs isInput d xs _ _ rfl) (ih _)

theorem denseFoldLoopDirectV_covered (reg : VarRegistry) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p),
      d.CoveredBy reg → (denseFoldLoopDirectV targets d).CoveredBy reg := by
  intro targets
  induction targets with
  | nil => intro d hcov; exact hcov
  | cons xs rest ih =>
      intro d hcov
      simp only [denseFoldLoopDirectV, List.partition_eq_filter_filter]
      exact ih _ (denseFoldStepWithV_covered reg d hcov xs _ _)

/-! ## The indexed fold loop -/

/-- `.1` of one indexed step as a plain match/if. -/
theorem denseFoldStepV_fst (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    (denseFoldStepV d fidx xs).1 =
      (match denseGroupDoms (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs with
       | none => d
       | some doms =>
         if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
           (if 1 ≤ (denseGroupSurvivorsEV (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs
                    (doms.map Prod.snd)).length
                && denseSystemHasFoldableIdxV fidx xs
                    (denseGroupSurvivorsEV (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs
                      (doms.map Prod.snd))
            then denseFoldOutIdxV d fidx xs
                (denseGroupSurvivorsEV (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs
                  (doms.map Prod.snd))
            else d)
           else d) := by
  simp only [denseFoldStepV]
  cases hgd : denseGroupDoms (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs with
  | none => rfl
  | some doms => simp only [apply_ite Prod.fst]

/-- The step's refreshed index keeps the input's constraint bucket map (`refresh` sets
    `idx := old.idx`). -/
theorem denseFoldStepV_snd_idx_eq (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    (denseFoldStepV d fidx xs).2.idx = fidx.idx := by
  simp only [denseFoldStepV]; split
  · rfl
  · split_ifs <;> rfl

/-- The step's refreshed index keeps the input's interaction bucket map (no-rebuild refresh). -/
theorem denseFoldStepV_snd_bisIdx_eq (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    (denseFoldStepV d fidx xs).2.bisIdx = fidx.bisIdx := by
  simp only [denseFoldStepV]; split
  · rfl
  · split_ifs <;> rfl

theorem denseFoldStepV_snd_arr (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (harr : fidx.arr = d.algebraicConstraints.toArray) :
    (denseFoldStepV d fidx xs).2.arr = (denseFoldStepV d fidx xs).1.algebraicConstraints.toArray := by
  simp only [denseFoldStepV]; split
  · exact harr
  · split_ifs <;> first | rfl | exact harr

/-- The step's output is either the input verbatim or the sparse fold (`denseFoldOutIdxV`) — the
    case split shared by the completeness/array invariants. -/
theorem denseFoldStepV_fst_alg (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    (denseFoldStepV d fidx xs).1 = d ∨
      ∃ survsV, (denseFoldStepV d fidx xs).1 = denseFoldOutIdxV d fidx xs survsV := by
  rw [denseFoldStepV_fst]
  split
  · exact Or.inl rfl
  · split_ifs
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl

/-- Under bucket-completeness (and array-sync), the covered set the index serves equals the direct
    covered set — a stale superset index is fine, bucket completeness is all that is needed. -/
theorem denseFoldStepV_es_eq (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : ∀ (i : Nat) (_ : i < d.algebraicConstraints.length),
      ∀ v ∈ d.algebraicConstraints[i].vars, i ∈ fidx.idx.buckets.getD v [])
    (harr : fidx.arr = d.algebraicConstraints.toArray) :
    denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs = denseCoveredCsOf d xs := by
  rw [harr, denseCoveredCsOf]
  exact denseCoveredIdx_eq_filter_of_complete fidx.idx d.algebraicConstraints (denseCoveredBy xs) xs
    (fun i hi hQ => by
      obtain ⟨v, hv, hvxs⟩ := denseCoveredBy_shares_var xs d.algebraicConstraints[i] hQ
      exact denseMem_candidates fidx.idx xs v i hvxs (hidx i hi v hv))

/-! ## The index-preserving indexed path

Correctness for the `anyVarIn`-only-gated rewrite, the in-place fold, and the sparse fold's equality
to it. -/

/-- `DenseExpr.anyVarIn` finds a genuinely shared variable. -/
theorem denseAnyVarIn_exists {xs : List VarId} {e : DenseExpr p}
    (h : e.anyVarIn xs = true) : ∃ i ∈ e.vars, i ∈ xs := by
  induction e with
  | const c => simp [DenseExpr.anyVarIn] at h
  | var y =>
    rw [DenseExpr.anyVarIn] at h
    exact ⟨y, by simp [DenseExpr.vars], denseContainsFast_sound xs y h⟩
  | add a b iha ihb =>
    rw [DenseExpr.anyVarIn, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨i, hi, hx⟩ := iha h
      exact ⟨i, by rw [DenseExpr.vars]; exact List.mem_append_left _ hi, hx⟩
    · obtain ⟨i, hi, hx⟩ := ihb h
      exact ⟨i, by rw [DenseExpr.vars]; exact List.mem_append_right _ hi, hx⟩
  | mul a b iha ihb =>
    rw [DenseExpr.anyVarIn, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨i, hi, hx⟩ := iha h
      exact ⟨i, by rw [DenseExpr.vars]; exact List.mem_append_left _ hi, hx⟩
    · obtain ⟨i, hi, hx⟩ := ihb h
      exact ⟨i, by rw [DenseExpr.vars]; exact List.mem_append_right _ hi, hx⟩

/-- `denseFoldRewriteIdxV` is the identity on an expression sharing no variable with the group — what
    lets the sparse `denseFoldOutIdxV` pass untouched items through by position. -/
theorem denseFoldRewriteIdxV_eq_self {xs : List VarId} {survsV : List (List (ZMod p))}
    {e : DenseExpr p} (h : e.anyVarIn xs = false) : denseFoldRewriteIdxV xs survsV e = e := by
  rw [denseFoldRewriteIdxV, h]; rfl

/-- Folding never introduces a `VarId` (gated indexed form). -/
theorem denseFoldRewriteIdxV_vars (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : ∀ i ∈ (denseFoldRewriteIdxV xs survsV e).vars, i ∈ e.vars := by
  intro i hi
  unfold denseFoldRewriteIdxV at hi
  split at hi
  · exact denseFoldRewriteGoV_vars xs survsV e i hi
  · exact hi

theorem denseFoldRewriteIdxV_covered (reg : VarRegistry) (xs : List VarId)
    (survsV : List (List (ZMod p))) {e : DenseExpr p} (hc : e.CoveredBy reg) :
    (denseFoldRewriteIdxV xs survsV e).CoveredBy reg :=
  fun i hi => hc i (denseFoldRewriteIdxV_vars xs survsV e i hi)

/-- On an env agreeing with a survivor `pt` on `xs`, `denseFoldRewriteIdxV` is
    evaluation-preserving. -/
theorem denseFoldRewriteIdxV_agree (xs : List VarId) (survsV : List (List (ZMod p)))
    (denv : VarId → ZMod p) (pt : List (ZMod p)) (hpt : pt ∈ survsV)
    (hcongr : ∀ e : DenseExpr p, e.varsInF xs = true →
      e.eval denv = e.eval (denseEnvOfKeysV xs pt)) :
    ∀ e : DenseExpr p, (denseFoldRewriteIdxV xs survsV e).eval denv = e.eval denv := by
  intro e
  unfold denseFoldRewriteIdxV
  split
  · exact denseFoldRewriteGoV_agree xs survsV denv pt hpt hcongr e
  · rfl

/-- If `denv` zeroes every covered constraint, the group is pinned to a survivor `pt` (the witness
    `xs.map denv`) that `denv` agrees with on `xs`. -/
theorem denseGroupSurvivorsEV_mem_agree [Fact p.Prime] (d : DenseConstraintSystem p)
    (xs : List VarId) (doms : List (VarId × List (ZMod p)))
    (hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs = some doms) (denv : VarId → ZMod p)
    (hcov : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0) :
    ∃ pt ∈ denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd),
      ∀ e : DenseExpr p, e.varsInF xs = true → e.eval denv = e.eval (denseEnvOfKeysV xs pt) := by
  have hkeys : doms.map Prod.fst = xs := denseGroupDoms_fst (denseCoveredCsOf d xs) xs doms hdoms
  have hsound_doms : ∀ yd ∈ doms, denv yd.1 ∈ yd.2 :=
    denseGroupDoms_sound denv (denseCoveredCsOf d xs) hcov xs doms hdoms
  have hpteq : xs.map denv = doms.map (fun yd => denv yd.1) := by
    rw [← hkeys, List.map_map]; rfl
  have hmemA : (xs.map denv) ∈ denseAssignmentsV (doms.map Prod.snd) := by
    rw [hpteq]; exact mem_denseAssignmentsV_of_sound denv doms hsound_doms
  have hcovVars : ∀ c ∈ denseCoveredCsOf d xs, c.varsInF xs = true := by
    intro c hc
    have hcf : c ∈ d.algebraicConstraints.filter (denseCoveredBy xs) := hc
    have hcb : denseCoveredBy xs c = true := (List.mem_filter.1 hcf).2
    rw [denseCoveredBy, Bool.and_eq_true] at hcb
    exact hcb.2
  have hzero : ∀ c ∈ denseCoveredCsOf d xs, c.eval (denseEnvOfKeysV xs (xs.map denv)) = 0 := by
    intro c hc
    have hvin := denseVarsInF_sound xs c (hcovVars c hc)
    have hce : c.eval (denseEnvOfKeysV xs (xs.map denv)) = c.eval denv :=
      DenseExpr.eval_congr c _ _ (fun v hv => denseEnvOfKeysV_map denv xs v (hvin v hv))
    rw [hce]; exact hcov c hc
  have hptSurv : (xs.map denv) ∈ denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd) :=
    mem_denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd) (xs.map denv) hmemA hzero
  have hcongr : ∀ e : DenseExpr p, e.varsInF xs = true →
      e.eval denv = e.eval (denseEnvOfKeysV xs (xs.map denv)) := by
    intro e he
    refine DenseExpr.eval_congr e _ _ (fun v hv => ?_)
    exact (denseEnvOfKeysV_map denv xs v (denseVarsInF_sound xs e he v hv)).symm
  exact ⟨xs.map denv, hptSurv, hcongr⟩

theorem denseFoldRewriteIdxV_agree_covered [Fact p.Prime] (d : DenseConstraintSystem p)
    (xs : List VarId) (doms : List (VarId × List (ZMod p)))
    (hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs = some doms) (denv : VarId → ZMod p)
    (hcov : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0) :
    ∀ e : DenseExpr p,
      (denseFoldRewriteIdxV xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd)) e).eval denv
        = e.eval denv := by
  obtain ⟨pt, hpt, hcongr⟩ := denseGroupSurvivorsEV_mem_agree d xs doms hdoms denv hcov
  intro e
  exact denseFoldRewriteIdxV_agree xs _ denv pt hpt hcongr e

/-! ### The in-place fold `denseFoldOutInPlaceV` -/

/-- Correctness of one in-place fold: the covered constraints pin the group so the rewrite agrees
    with the identity. -/
theorem denseFoldOutInPlaceV_correct [Fact p.Prime] (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (doms : List (VarId × List (ZMod p)))
    (hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs = some doms) (isInput : VarId → Bool) :
    DensePassCorrect isInput d
      (denseFoldOutInPlaceV d xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd))) [] bs := by
  set survsV := denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd) with hsurv_def
  have hagCov : ∀ denv : VarId → ZMod p, (∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0) →
      ∀ e : DenseExpr p, (denseFoldRewriteIdxV xs survsV e).eval denv = e.eval denv := by
    intro denv hcov
    rw [hsurv_def]
    exact denseFoldRewriteIdxV_agree_covered d xs doms hdoms denv hcov
  have hceval : ∀ (denv : VarId → ZMod p), (∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0) →
      ∀ c : DenseExpr p,
      (if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c).eval denv
        = c.eval denv := by
    intro denv hA c
    by_cases hcov : denseCoveredBy xs c = true
    · rw [if_pos hcov]
    · rw [if_neg hcov]; exact hagCov denv hA c
  refine DensePassCorrect.ofEvalAgree
    (fun denv => ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0)
    (denseFoldRewriteIdxV xs survsV) rfl ?_ ?_ hagCov ?_ ?_ ?_
    (fun e i hi => denseFoldRewriteIdxV_vars xs survsV e i hi)
  · -- a covered constraint sits verbatim in the output (its `if` keeps it)
    intro denv hsatout c hc
    have hcb : denseCoveredBy xs c = true := (List.mem_filter.mp hc).2
    have hmem : (if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c)
        ∈ (denseFoldOutInPlaceV d xs survsV).algebraicConstraints :=
      List.mem_map.2 ⟨c, List.mem_of_mem_filter hc, rfl⟩
    rw [if_pos hcb] at hmem
    exact hsatout.1 c hmem
  · exact fun denv hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  · -- input constraints vanish when the output's do
    intro denv hA hout c hc
    have hz := hout _ (show (if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c)
        ∈ (denseFoldOutInPlaceV d xs survsV).algebraicConstraints from
      List.mem_map.2 ⟨c, hc, rfl⟩)
    rwa [hceval denv hA c] at hz
  · -- output constraints vanish when the input's do
    intro denv hA hd c' hc'
    have hc'2 : c' ∈ d.algebraicConstraints.map
        (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c) := hc'
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'2
    rw [hceval denv hA c0]
    exact hd c0 hc0
  · -- output constraints read only occurring variables
    intro c' hc' i hi
    have hc'2 : c' ∈ d.algebraicConstraints.map
        (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c) := hc'
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'2
    by_cases hcc : denseCoveredBy xs c0 = true
    · rw [if_pos hcc] at hi
      exact DenseConstraintSystem.mem_occ_of_constraint hc0 hi
    · rw [if_neg hcc] at hi
      exact DenseConstraintSystem.mem_occ_of_constraint hc0
        (denseFoldRewriteIdxV_vars xs survsV c0 i hi)

/-! ### The sparse indexed fold `denseFoldOutIdxV` -/

/-- Membership in the touched set is membership in some bucket of `xs`. -/
theorem denseTouchedSet_contains_iff (idx : DenseCovIndex) (xs : List VarId) (i : Nat) :
    (denseTouchedSet idx xs).contains i = true ↔ ∃ v ∈ xs, i ∈ idx.buckets.getD v [] := by
  rw [← Std.HashSet.mem_iff_contains, denseTouchedSet, mem_foldl_insert,
    List.mem_flatMap]
  simp [Std.HashSet.not_mem_empty]

/-- An untouched interaction maps to itself under an inline rewrite that fixes each of its
    expressions. -/
theorem denseMapExpr_eq_self {bi : BusInteraction (DenseExpr p)} {g : DenseExpr p → DenseExpr p}
    (hm : g bi.multiplicity = bi.multiplicity) (hp : ∀ e ∈ bi.payload, g e = e) :
    { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g } = bi := by
  have hpl : bi.payload.map g = bi.payload :=
    (List.map_congr_left (g := id) hp).trans (List.map_id _)
  rw [hm, hpl]

/-- A rewrite that introduces no variables per expression keeps an interaction's variables. -/
theorem denseMapExpr_vars_subset (g : DenseExpr p → DenseExpr p)
    (hg : ∀ (e : DenseExpr p) (i : VarId), i ∈ (g e).vars → i ∈ e.vars)
    (bi : BusInteraction (DenseExpr p)) :
    ∀ i ∈ denseBIVars { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g },
      i ∈ denseBIVars bi := by
  grind [denseBIVars]

/-- The sparse fold is the in-place fold: every non-candidate position holds an item sharing no
    variable with `xs` (bucket completeness, contraposed), on which `denseFoldRewriteIdxV` is the
    identity, so skipping it is exact. `hidx`/`hbis` are the bucket-completeness hypotheses. -/
theorem denseFoldOutIdxV_eq (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (survsV : List (List (ZMod p)))
    (hidx : ∀ (i : Nat) (_ : i < d.algebraicConstraints.length),
      ∀ v ∈ d.algebraicConstraints[i].vars, i ∈ fidx.idx.buckets.getD v [])
    (hbis : ∀ (i : Nat) (_ : i < d.busInteractions.length),
      ∀ v ∈ denseBIVars d.busInteractions[i], i ∈ fidx.bisIdx.buckets.getD v []) :
    denseFoldOutIdxV d fidx xs survsV = denseFoldOutInPlaceV d xs survsV := by
  show DenseConstraintSystem.mk
      (d.algebraicConstraints.zipIdx.map (fun ci =>
        if (denseTouchedSet fidx.idx xs).contains ci.2 then
          (if denseCoveredBy xs ci.1 then ci.1 else denseFoldRewriteIdxV xs survsV ci.1)
        else ci.1))
      (d.busInteractions.zipIdx.map (fun bii =>
        if (denseTouchedSet fidx.bisIdx xs).contains bii.2 then
          { bii.1 with
            multiplicity := denseFoldRewriteIdxV xs survsV bii.1.multiplicity,
            payload := bii.1.payload.map (denseFoldRewriteIdxV xs survsV) }
        else bii.1)) = denseFoldOutInPlaceV d xs survsV
  unfold denseFoldOutInPlaceV
  congr 1
  · -- constraint side
    refine zipIdx_map_sparse d.algebraicConstraints
      (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c)
      (fun i => (denseTouchedSet fidx.idx xs).contains i) ?_
    intro i hi hm
    have hm' : (denseTouchedSet fidx.idx xs).contains i = false := hm
    have hnb : ¬ ∃ v ∈ xs, i ∈ fidx.idx.buckets.getD v [] := by
      rw [← denseTouchedSet_contains_iff fidx.idx xs i, hm']
      simp
    have hnav : d.algebraicConstraints[i].anyVarIn xs = false := by
      by_contra hav
      obtain ⟨v, hvc, hvxs⟩ := denseAnyVarIn_exists (Bool.ne_false_iff.mp hav)
      exact hnb ⟨v, hvxs, hidx i hi v hvc⟩
    show (if denseCoveredBy xs d.algebraicConstraints[i] then d.algebraicConstraints[i]
        else denseFoldRewriteIdxV xs survsV d.algebraicConstraints[i]) = d.algebraicConstraints[i]
    rw [denseFoldRewriteIdxV_eq_self hnav, ite_self]
  · -- interaction side
    refine zipIdx_map_sparse d.busInteractions
      (fun bi => { bi with
        multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
        payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) })
      (fun i => (denseTouchedSet fidx.bisIdx xs).contains i) ?_
    intro i hi hm
    have hm' : (denseTouchedSet fidx.bisIdx xs).contains i = false := hm
    have hnb : ¬ ∃ v ∈ xs, i ∈ fidx.bisIdx.buckets.getD v [] := by
      rw [← denseTouchedSet_contains_iff fidx.bisIdx xs i, hm']
      simp
    have hnoshare : ∀ v ∈ denseBIVars (d.busInteractions[i]), v ∉ xs := by
      intro v hvbi hvxs
      exact hnb ⟨v, hvxs, hbis i hi v hvbi⟩
    have hfix : ∀ e : DenseExpr p, (∀ v ∈ e.vars, v ∈ denseBIVars (d.busInteractions[i])) →
        denseFoldRewriteIdxV xs survsV e = e := by
      intro e hsub
      refine denseFoldRewriteIdxV_eq_self ?_
      by_contra hav
      obtain ⟨v, hvc, hvxs⟩ := denseAnyVarIn_exists (Bool.ne_false_iff.mp hav)
      exact hnoshare v (hsub v hvc) hvxs
    show { d.busInteractions[i] with
        multiplicity := denseFoldRewriteIdxV xs survsV (d.busInteractions[i]).multiplicity,
        payload := (d.busInteractions[i]).payload.map (denseFoldRewriteIdxV xs survsV) }
        = d.busInteractions[i]
    exact denseMapExpr_eq_self
      (hfix (d.busInteractions[i]).multiplicity (fun v hv => by
        rw [denseBIVars]; exact List.mem_append_left _ hv))
      (fun e he => hfix e (fun v hv => by
        rw [denseBIVars]
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, hv⟩)))

/-! ### Completeness preservation across an in-place fold

The in-place fold is order- and length-preserving and only shrinks variable sets, so a bucket map
complete for the input stays complete for the output. -/

/-- Constraint-side bucket completeness survives an in-place fold. -/
theorem denseFoldOutInPlaceV_hidx (bkts : Std.HashMap VarId (List Nat)) (d : DenseConstraintSystem p)
    (xs : List VarId) (survsV : List (List (ZMod p)))
    (hidx : ∀ (i : Nat) (_ : i < d.algebraicConstraints.length),
      ∀ v ∈ d.algebraicConstraints[i].vars, i ∈ bkts.getD v []) :
    ∀ (i : Nat) (_ : i < (denseFoldOutInPlaceV d xs survsV).algebraicConstraints.length),
      ∀ v ∈ (denseFoldOutInPlaceV d xs survsV).algebraicConstraints[i].vars,
        i ∈ bkts.getD v [] := by
  intro i hi v hv
  have hlen : i < d.algebraicConstraints.length := by
    simpa only [denseFoldOutInPlaceV, List.length_map] using hi
  have hv' : v ∈ d.algebraicConstraints[i].vars := by
    have hgm : (denseFoldOutInPlaceV d xs survsV).algebraicConstraints[i]'hi
        = (if denseCoveredBy xs (d.algebraicConstraints[i]'hlen) then
            d.algebraicConstraints[i]'hlen
           else denseFoldRewriteIdxV xs survsV (d.algebraicConstraints[i]'hlen)) := by
      simp only [denseFoldOutInPlaceV, List.getElem_map]
    rw [hgm] at hv
    by_cases hcov : denseCoveredBy xs (d.algebraicConstraints[i]'hlen) = true
    · rwa [if_pos hcov] at hv
    · rw [if_neg hcov] at hv
      exact denseFoldRewriteIdxV_vars xs survsV _ v hv
  exact hidx i hlen v hv'

/-- Interaction-side bucket completeness survives an in-place fold. -/
theorem denseFoldOutInPlaceV_hbis (bkts : Std.HashMap VarId (List Nat)) (d : DenseConstraintSystem p)
    (xs : List VarId) (survsV : List (List (ZMod p)))
    (hbis : ∀ (i : Nat) (_ : i < d.busInteractions.length),
      ∀ v ∈ denseBIVars d.busInteractions[i], i ∈ bkts.getD v []) :
    ∀ (i : Nat) (_ : i < (denseFoldOutInPlaceV d xs survsV).busInteractions.length),
      ∀ v ∈ denseBIVars (denseFoldOutInPlaceV d xs survsV).busInteractions[i],
        i ∈ bkts.getD v [] := by
  intro i hi v hv
  have hlen : i < d.busInteractions.length := by
    simpa only [denseFoldOutInPlaceV, List.length_map] using hi
  have hv' : v ∈ denseBIVars (d.busInteractions[i]'hlen) := by
    have hgm : (denseFoldOutInPlaceV d xs survsV).busInteractions[i]'hi
        = { d.busInteractions[i]'hlen with
            multiplicity := denseFoldRewriteIdxV xs survsV (d.busInteractions[i]'hlen).multiplicity,
            payload := (d.busInteractions[i]'hlen).payload.map (denseFoldRewriteIdxV xs survsV) } := by
      simp only [denseFoldOutInPlaceV, List.getElem_map]
    rw [hgm] at hv
    exact denseMapExpr_vars_subset (denseFoldRewriteIdxV xs survsV)
      (denseFoldRewriteIdxV_vars xs survsV) (d.busInteractions[i]'hlen) v hv
  exact hbis i hlen v hv'

/-- Coverage survives the sparse indexed fold: it only rewrites, never introduces, variables. Proved
    without the completeness hypotheses, so the coverage loop needs none. -/
theorem denseFoldOutIdxV_covered (reg : VarRegistry) (d : DenseConstraintSystem p)
    (fidx : DenseFoldIdx p) (hcov : d.CoveredBy reg) (xs : List VarId)
    (survsV : List (List (ZMod p))) :
    (denseFoldOutIdxV d fidx xs survsV).CoveredBy reg := by
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · have he' : e ∈ d.algebraicConstraints.zipIdx.map (fun ci =>
        if (denseTouchedSet fidx.idx xs).contains ci.2 then
          (if denseCoveredBy xs ci.1 then ci.1 else denseFoldRewriteIdxV xs survsV ci.1)
        else ci.1) := he
    obtain ⟨⟨c0, j⟩, hp, rfl⟩ := List.mem_map.1 he'
    have hc0mem : c0 ∈ d.algebraicConstraints := by
      have h2 : c0 ∈ d.algebraicConstraints.zipIdx.map Prod.fst :=
        List.mem_map.2 ⟨(c0, j), hp, rfl⟩
      rwa [List.zipIdx_map_fst] at h2
    have hc0cov : c0.CoveredBy reg := hcov.1 c0 hc0mem
    dsimp only
    by_cases ht : (denseTouchedSet fidx.idx xs).contains j = true
    · rw [if_pos ht]
      by_cases hcc : denseCoveredBy xs c0 = true
      · rw [if_pos hcc]; exact hc0cov
      · rw [if_neg hcc]; exact denseFoldRewriteIdxV_covered reg xs survsV hc0cov
    · rw [if_neg ht]; exact hc0cov
  · have hbi' : bi ∈ d.busInteractions.zipIdx.map (fun bii =>
        if (denseTouchedSet fidx.bisIdx xs).contains bii.2 then
          { bii.1 with
            multiplicity := denseFoldRewriteIdxV xs survsV bii.1.multiplicity,
            payload := bii.1.payload.map (denseFoldRewriteIdxV xs survsV) }
        else bii.1) := hbi
    obtain ⟨⟨bi0, j⟩, hp, rfl⟩ := List.mem_map.1 hbi'
    have hbi0mem : bi0 ∈ d.busInteractions := by
      have h2 : bi0 ∈ d.busInteractions.zipIdx.map Prod.fst :=
        List.mem_map.2 ⟨(bi0, j), hp, rfl⟩
      rwa [List.zipIdx_map_fst] at h2
    obtain ⟨hm, hpl⟩ := hcov.2 bi0 hbi0mem
    dsimp only
    by_cases ht : (denseTouchedSet fidx.bisIdx xs).contains j = true
    · rw [if_pos ht]
      refine ⟨denseFoldRewriteIdxV_covered reg xs survsV hm, fun e he => ?_⟩
      have he'' : e ∈ bi0.payload.map (denseFoldRewriteIdxV xs survsV) := he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he''
      exact denseFoldRewriteIdxV_covered reg xs survsV (hpl e0 he0)
    · rw [if_neg ht]; exact ⟨hm, hpl⟩

/-! ## The indexed fold loop (index-preserving path) -/

/-- Constraint-side index completeness survives one step: the refreshed index keeps the old bucket
    map, which stays complete for the step's output. -/
theorem denseFoldStepV_snd_idx (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : ∀ (i : Nat) (_ : i < d.algebraicConstraints.length),
      ∀ v ∈ d.algebraicConstraints[i].vars, i ∈ fidx.idx.buckets.getD v [])
    (hbis : ∀ (i : Nat) (_ : i < d.busInteractions.length),
      ∀ v ∈ denseBIVars d.busInteractions[i], i ∈ fidx.bisIdx.buckets.getD v []) :
    ∀ (i : Nat) (_ : i < (denseFoldStepV d fidx xs).1.algebraicConstraints.length),
      ∀ v ∈ (denseFoldStepV d fidx xs).1.algebraicConstraints[i].vars,
        i ∈ (denseFoldStepV d fidx xs).2.idx.buckets.getD v [] := by
  rw [denseFoldStepV_snd_idx_eq]
  rcases denseFoldStepV_fst_alg d fidx xs with h | ⟨survsV, h⟩
  · rw [h]; exact hidx
  · rw [h, denseFoldOutIdxV_eq d fidx xs survsV hidx hbis]
    exact denseFoldOutInPlaceV_hidx fidx.idx.buckets d xs survsV hidx

/-- Interaction-side completeness survives one step (dual of `denseFoldStepV_snd_idx`). -/
theorem denseFoldStepV_snd_bis (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : ∀ (i : Nat) (_ : i < d.algebraicConstraints.length),
      ∀ v ∈ d.algebraicConstraints[i].vars, i ∈ fidx.idx.buckets.getD v [])
    (hbis : ∀ (i : Nat) (_ : i < d.busInteractions.length),
      ∀ v ∈ denseBIVars d.busInteractions[i], i ∈ fidx.bisIdx.buckets.getD v []) :
    ∀ (i : Nat) (_ : i < (denseFoldStepV d fidx xs).1.busInteractions.length),
      ∀ v ∈ denseBIVars (denseFoldStepV d fidx xs).1.busInteractions[i],
        i ∈ (denseFoldStepV d fidx xs).2.bisIdx.buckets.getD v [] := by
  rw [denseFoldStepV_snd_bisIdx_eq]
  rcases denseFoldStepV_fst_alg d fidx xs with h | ⟨survsV, h⟩
  · rw [h]; exact hbis
  · rw [h, denseFoldOutIdxV_eq d fidx xs survsV hidx hbis]
    exact denseFoldOutInPlaceV_hbis fidx.bisIdx.buckets d xs survsV hbis

theorem denseFoldStepV_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : ∀ (i : Nat) (_ : i < d.algebraicConstraints.length),
      ∀ v ∈ d.algebraicConstraints[i].vars, i ∈ fidx.idx.buckets.getD v [])
    (hbis : ∀ (i : Nat) (_ : i < d.busInteractions.length),
      ∀ v ∈ denseBIVars d.busInteractions[i], i ∈ fidx.bisIdx.buckets.getD v [])
    (harr : fidx.arr = d.algebraicConstraints.toArray) :
    DensePassCorrect isInput d (denseFoldStepV d fidx xs).1 [] bs := by
  have hes := denseFoldStepV_es_eq d fidx xs hidx harr
  rw [denseFoldStepV_fst, hes]
  split
  · exact DensePassCorrect_refl isInput d bs
  · rename_i doms hgd
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hgate : (1 ≤ (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd)).length
          && denseSystemHasFoldableIdxV fidx xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd))) = true
      · rw [if_pos hgate, denseFoldOutIdxV_eq d fidx xs _ hidx hbis]
        exact denseFoldOutInPlaceV_correct bs d xs doms hgd isInput
      · rw [if_neg (by simpa using hgate)]; exact DensePassCorrect_refl isInput d bs
    · rw [if_neg hp]; exact DensePassCorrect_refl isInput d bs

theorem denseFoldStepV_covered (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (fidx : DenseFoldIdx p) (xs : List VarId) :
    (denseFoldStepV d fidx xs).1.CoveredBy reg := by
  rw [denseFoldStepV_fst]
  split
  · exact hcov
  · rename_i doms _
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hgate : (1 ≤ (denseGroupSurvivorsEV (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs
              (doms.map Prod.snd)).length
          && denseSystemHasFoldableIdxV fidx xs (denseGroupSurvivorsEV (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs
              (doms.map Prod.snd))) = true
      · rw [if_pos hgate]; exact denseFoldOutIdxV_covered reg d fidx hcov xs _
      · rw [if_neg (by simpa using hgate)]; exact hcov
    · rw [if_neg hp]; exact hcov

theorem denseFoldLoopV_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p),
      (∀ (i : Nat) (_ : i < d.algebraicConstraints.length),
        ∀ v ∈ d.algebraicConstraints[i].vars, i ∈ fidx.idx.buckets.getD v []) →
      (∀ (i : Nat) (_ : i < d.busInteractions.length),
        ∀ v ∈ denseBIVars d.busInteractions[i], i ∈ fidx.bisIdx.buckets.getD v []) →
      fidx.arr = d.algebraicConstraints.toArray →
      DensePassCorrect isInput d (denseFoldLoopV targets d fidx) [] bs := by
  intro targets
  induction targets with
  | nil => intro d fidx _ _ _; exact DensePassCorrect_refl isInput d bs
  | cons xs rest ih =>
      intro d fidx hidx hbis harr
      show DensePassCorrect isInput d
        (denseFoldLoopV rest (denseFoldStepV d fidx xs).1 (denseFoldStepV d fidx xs).2) [] bs
      refine DensePassCorrect.trans (denseFoldStepV_correct bs isInput d fidx xs hidx hbis harr)
        (ih _ _ ?_ ?_ ?_)
      · exact denseFoldStepV_snd_idx d fidx xs hidx hbis
      · exact denseFoldStepV_snd_bis d fidx xs hidx hbis
      · exact denseFoldStepV_snd_arr d fidx xs harr

theorem denseFoldLoopV_covered (reg : VarRegistry) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p),
      d.CoveredBy reg → (denseFoldLoopV targets d fidx).CoveredBy reg := by
  intro targets
  induction targets with
  | nil => intro d fidx hcov; exact hcov
  | cons xs rest ih =>
      intro d fidx hcov
      exact ih _ _ (denseFoldStepV_covered reg d hcov fidx xs)

/-! ## The whole pass -/

theorem denseDomainFoldFV_correct (pw : PrimeWitness p) (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d (denseDomainFoldFV pw d) [] bs := by
  unfold denseDomainFoldFV
  by_cases hpB : pw.isPrime = true
  · rw [if_pos hpB]
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    by_cases hthr : domainFoldIndexThreshold ≤ d.algebraicConstraints.length
    · rw [if_pos hthr]
      exact denseFoldLoopV_correct bs isInput (denseTargetsV d) d (DenseFoldIdx.mk' d)
        (fun i hi v hv => denseBuild_complete denseDedupVarsOf d.algebraicConstraints i hi v (by
          rw [denseDedupVarsOf, HashedDedup.hashedEraseDups_eq]
          exact List.mem_eraseDups.2 hv))
        (fun i hi v hv => denseBuild_complete denseDedupBiVarsOf d.busInteractions i hi v (by
          rw [denseDedupBiVarsOf, HashedDedup.hashedEraseDups_eq]
          exact List.mem_eraseDups.2 hv))
        rfl
    · rw [if_neg hthr]
      exact denseFoldLoopDirectV_correct bs isInput (denseTargetsV d) d
  · rw [if_neg hpB]
    exact DensePassCorrect_refl isInput d bs

theorem denseDomainFoldFV_covered (pw : PrimeWitness p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseDomainFoldFV pw d).CoveredBy reg := by
  unfold denseDomainFoldFV
  by_cases hpB : pw.isPrime = true
  · rw [if_pos hpB]
    by_cases hthr : domainFoldIndexThreshold ≤ d.algebraicConstraints.length
    · rw [if_pos hthr]
      exact denseFoldLoopV_covered reg (denseTargetsV d) d (DenseFoldIdx.mk' d) hcov
    · rw [if_neg hthr]
      exact denseFoldLoopDirectV_covered reg (denseTargetsV d) d hcov
  · rw [if_neg hpB]; exact hcov

/-- The registered domain-fold pass (transform `denseDomainFoldFV`, `DomainFoldRuntime.lean`). -/
def denseDomainFoldPassV (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => denseDomainFoldFV pw d)
    (fun _ _ _ => [])
    (fun reg _ _ d hcov => denseDomainFoldFV_covered pw reg d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseDomainFoldFV_correct pw bs reg.isInput d)

end ApcOptimizer.Dense
