import ApcOptimizer.Implementation.OptimizerPasses.DomainFoldRuntime
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Native correctness for the value-only dense `domainFold` (Task 3)

This module proves `DensePassCorrect` for the value-only rebuild of `domainFold`
(`Dense/DomainFoldNative.lean`) **natively** over dense environments `VarId → ZMod p`, with no
commutation to the spec pass and no `decode` in the discharged obligations. The spec pass's own
`PassCorrect` proof (`OptimizerPasses/DomainFold.lean`) is only the roadmap: its argument structure
(`foldOut_correct` via `PassCorrect.ofEnvEq`, the survivor-agreement chain, `foldLoop` composition)
is mirrored here over the native dense semantics of `Dense/Bridge.lean`.

The fold is a pure rewrite: every wholly-in-group subexpression constant on the group's surviving
joint assignments is replaced by that constant, keeping the group's variables, and keeping the
group's covered (domain-pinning) constraints verbatim. Any assignment satisfying either system pins
the group to a survivor, under which the rewrite agrees with the identity — so `env' = env` is the
completeness witness and no derivations are produced.

Reused from `Dense/DomainBatchNativeProof.lean`: the native root/domain soundness
(`denseRootsIn_sound`), the value-only compiled-evaluation correspondence (`denseCompileE_evalV`,
`denseCompileEs_allV`, `denseEnvOfKeysV_map`), `DensePassCorrect_refl`, and the `DenseExpr.eval`
congruence/`filter_map_busId_comm` glue. Newly proved here: `denseFindDomainAlg`/`denseGroupDoms`
native soundness, the value-only survivor certificate (`mem_denseAssignmentsV_of_sound`,
`denseGroupSurvivorsEV_eq`, `mem_denseGroupSurvivorsEV`, `denseConstOnSurvsV_sound`), the fold
agreement (`denseFoldRewriteGoV_agree`, `denseFoldRewriteV_agree_covered`), the single-fold
correctness (`denseFoldOutV_correct`), the loop composition (`DensePassCorrect.trans`), and the
whole-pass correctness/coverage. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Native domain soundness (mirrors `findDomainAlg`/`groupDoms` roots soundness) -/

/-- If `denseFindDomainAlg all i = some dm`, every assignment zeroing every `c ∈ all` puts `denv i`
    in `dm` (native mirror of `findDomainAlg_sound`). -/
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

/-- If `denseGroupDoms es xs = some doms`, every assignment zeroing every `c ∈ es` puts each group
    variable in its domain (native mirror of `groupDoms_sound`). -/
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

/-- The value-only assignment of `denv` over `doms` is one of the enumerated points. -/
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

/-- The compiled survivor filter equals the direct one (value-only). -/
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
      show denseSurvZeroCWV (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul ces a
        = es.all (fun c => decide (c.eval (denseEnvOfKeysV xs a) = 0))
      unfold denseSurvZeroCWV
      exact denseCompileEs_allV (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul
        (fun _ _ => rfl) (fun _ _ => rfl) (fun v => decide (v = 0)) (fun _ => rfl) xs a es ces hce

/-- A point in the enumeration that zeroes every covered constraint survives. -/
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

/-- If `denseConstOnSurvsV` accepts `e` with value `c`, then `e` evaluates to `c` on every survivor
    (native mirror of `constOnSurvs_sound`). -/
theorem denseConstOnSurvsV_sound (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) (c : ZMod p) (h : denseConstOnSurvsV xs survsV e = some c) :
    ∀ s ∈ survsV, e.eval (denseEnvOfKeysV xs s) = c := by
  intro s hs
  cases survsV with
  | nil => simp at hs
  | cons s₀ rest =>
      cases hce : denseCompileE xs e with
      | some ie =>
          simp only [denseConstOnSurvsV, hce] at h
          split at h
          · rename_i hall
            simp only [Option.some.injEq] at h
            have hthis := List.all_eq_true.mp hall s hs
            rw [decide_eq_true_eq] at hthis
            have hev := denseCompileE_evalV (inferInstance : Add (ZMod p)).add
              (inferInstance : Mul (ZMod p)).mul (fun _ _ => rfl) (fun _ _ => rfl) xs s e ie hce
            rw [← hev, hthis]; exact h
          · exact absurd h (by simp)
      | none =>
          simp only [denseConstOnSurvsV, hce] at h
          split at h
          · rename_i hall
            simp only [Option.some.injEq] at h
            have hthis := List.all_eq_true.mp hall s hs
            rw [decide_eq_true_eq] at hthis
            rw [hthis]; exact h
          · exact absurd h (by simp)

/-! ## The fold rewrite: agreement and variable containment (value-only) -/

/-- On an environment agreeing on `xs` with a survivor `pt`, `denseFoldRewriteGoV` is
    evaluation-preserving (native mirror of `foldRewriteGo_agree`). -/
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

/-- On any environment zeroing all the covered constraints, `denseFoldRewriteV` (over the survivors of
    those constraints) is evaluation-preserving (native mirror of `foldRewrite_agree_covered`). -/
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

/-! ## `denseFoldOutV` semantic agreement helpers -/

/-- A rewritten interaction evaluates identically, given expression-level agreement. -/
theorem denseBIEval_foldRewriteV (xs : List VarId) (survsV : List (List (ZMod p)))
    (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (denseFoldRewriteV xs survsV e).eval denv = e.eval denv)
    (bi : BusInteraction (DenseExpr p)) :
    denseBIEval { bi with
        multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
        payload := bi.payload.map (denseFoldRewriteV xs survsV) } denv
      = denseBIEval bi denv := by
  unfold denseBIEval
  simp only [hag bi.multiplicity, List.map_map]
  congr 1
  exact List.map_congr_left (fun e _ => by simp only [Function.comp_apply]; exact hag e)

theorem denseFoldOutV_sideEffects_eq (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (survsV : List (List (ZMod p))) (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (denseFoldRewriteV xs survsV e).eval denv = e.eval denv) :
    (denseFoldOutV d xs survsV).sideEffects bs denv = d.sideEffects bs denv := by
  unfold DenseConstraintSystem.sideEffects
  simp only [denseFoldOutV]
  rw [filter_map_busId_comm d.busInteractions
    (fun bi => { bi with
      multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
      payload := bi.payload.map (denseFoldRewriteV xs survsV) }) bs (fun _ => rfl), List.map_map]
  refine List.map_congr_left (fun bi _ => ?_)
  simp only [Function.comp_apply]
  rw [denseBIEval_foldRewriteV xs survsV denv hag bi]

theorem denseFoldOutV_admissible_iff (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (survsV : List (List (ZMod p))) (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (denseFoldRewriteV xs survsV e).eval denv = e.eval denv) :
    (denseFoldOutV d xs survsV).admissible bs denv ↔ d.admissible bs denv := by
  unfold DenseConstraintSystem.admissible
  have hmap : (denseFoldOutV d xs survsV).busInteractions.map (fun bi => denseBIEval bi denv)
      = d.busInteractions.map (fun bi => denseBIEval bi denv) := by
    simp only [denseFoldOutV, List.map_map]
    exact List.map_congr_left (fun bi _ => by
      simp only [Function.comp_apply]; exact denseBIEval_foldRewriteV xs survsV denv hag bi)
  rw [hmap]

theorem denseFoldOutV_occ_subset (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : ∀ i ∈ (denseFoldOutV d xs survsV).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · have hc2 : c ∈ (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseFoldRewriteV xs survsV) ++ denseCoveredCsOf d xs := hc
    rcases List.mem_append.1 hc2 with h | h
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
      exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc0)
        (denseFoldRewriteV_vars xs survsV c0 i hic)
    · exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter h) hic
  · have hbi2 : bi ∈ d.busInteractions.map
        (fun bi => { bi with
          multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
          payload := bi.payload.map (denseFoldRewriteV xs survsV) }) := hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi2
    simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hib
    rcases hib with hm | ⟨e, he, hie⟩
    · exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
        rw [denseBIVars, List.mem_append]
        exact Or.inl (denseFoldRewriteV_vars xs survsV bi0.multiplicity i hm))
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
        rw [denseBIVars, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨e0, he0, denseFoldRewriteV_vars xs survsV e0 i hie⟩)

/-! ## Single-fold native correctness (mirrors `foldOut_correct`) -/

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
  refine DensePassCorrect.ofEnvEq ?hsound ?hinv ?hsub ?hcomp
  case hsub => exact denseFoldOutV_occ_subset d xs survsV
  case hsound =>
    intro denv hsatout
    have hcovsat : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 := by
      intro c hc
      exact hsatout.1 c (by
        show c ∈ (denseFoldOutV d xs survsV).algebraicConstraints
        simp only [denseFoldOutV, List.mem_append]; exact Or.inr hc)
    have hag := hagCov denv hcovsat
    refine ⟨denv, ⟨?_, ?_⟩, ?_⟩
    · intro c hc
      by_cases hccov : denseCoveredBy xs c = true
      · exact hcovsat c (List.mem_filter.2 ⟨hc, hccov⟩)
      · have hmem : denseFoldRewriteV xs survsV c ∈ (denseFoldOutV d xs survsV).algebraicConstraints := by
          simp only [denseFoldOutV, List.mem_append]
          exact Or.inl (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hccov⟩, rfl⟩)
        have hz := hsatout.1 _ hmem
        rwa [hag c] at hz
    · intro bi hbi
      have hmem : { bi with
          multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
          payload := bi.payload.map (denseFoldRewriteV xs survsV) }
            ∈ (denseFoldOutV d xs survsV).busInteractions := List.mem_map.2 ⟨bi, hbi, rfl⟩
      have hval := denseBIEval_foldRewriteV xs survsV denv hag bi
      have hz := hsatout.2 _ hmem
      rw [hval] at hz; exact hz
    · rw [denseFoldOutV_sideEffects_eq bs d xs survsV denv hag]; exact BusState.equiv_refl _
  case hinv =>
    intro hgi denv hsatout bi' hbi'
    have hcovsat : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 := by
      intro c hc
      exact hsatout.1 c (by
        show c ∈ (denseFoldOutV d xs survsV).algebraicConstraints
        simp only [denseFoldOutV, List.mem_append]; exact Or.inr hc)
    have hag := hagCov denv hcovsat
    have hsatd : d.satisfies bs denv := by
      refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
      · by_cases hccov : denseCoveredBy xs c = true
        · exact hcovsat c (List.mem_filter.2 ⟨hc, hccov⟩)
        · have hmem : denseFoldRewriteV xs survsV c ∈ (denseFoldOutV d xs survsV).algebraicConstraints := by
            simp only [denseFoldOutV, List.mem_append]
            exact Or.inl (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hccov⟩, rfl⟩)
          have hz := hsatout.1 _ hmem
          rwa [hag c] at hz
      · have hmem : { bi with
            multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
            payload := bi.payload.map (denseFoldRewriteV xs survsV) }
              ∈ (denseFoldOutV d xs survsV).busInteractions := List.mem_map.2 ⟨bi, hbi, rfl⟩
        have hval := denseBIEval_foldRewriteV xs survsV denv hag bi
        have hz := hsatout.2 _ hmem
        rw [hval] at hz; exact hz
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    rw [denseBIEval_foldRewriteV xs survsV denv hag bi0]
    exact hgi denv hsatd bi0 hbi0
  case hcomp =>
    intro denv hadm hsat
    have hcovsat : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 :=
      fun c hc => hsat.1 c (List.mem_of_mem_filter hc)
    have hag := hagCov denv hcovsat
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro c hc
      have hc' : c ∈ (denseFoldOutV d xs survsV).algebraicConstraints := hc
      simp only [denseFoldOutV, List.mem_append] at hc'
      rcases hc' with hc' | hc'
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
        rw [hag c0]; exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hsat.1 c (List.mem_of_mem_filter hc')
    · intro bi hbi
      have hbi' : bi ∈ (denseFoldOutV d xs survsV).busInteractions := hbi
      obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
      rw [denseBIEval_foldRewriteV xs survsV denv hag bi0]
      exact hsat.2 bi0 hbi0
    · exact (denseFoldOutV_admissible_iff bs d xs survsV denv hag).2 hadm
    · rw [denseFoldOutV_sideEffects_eq bs d xs survsV denv hag]; exact BusState.equiv_refl _

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

/-- `.1` of one indexed step as a plain match/if (mirrors `denseFoldStep_fst`). -/
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

/-- The step's refreshed index keeps the input's constraint bucket map (the flip's no-rebuild
    refresh: `DenseFoldIdx.refresh` sets `idx := old.idx`). -/
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

/-- The step's output system is either the input verbatim (no fold accepted) or the sparse fold of
    it (`denseFoldOutIdxV`). The single case analysis all three completeness/array invariants share. -/
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

/-- Under the constraint-side bucket-completeness invariant (and array-sync), the covered set the
    index serves equals the direct covered set (mirrors #165's `coveredCsIdx_eq`,
    `OptimizerPasses/DomainFold.lean:865`, which likewise needs only completeness — refreshed
    stale-superset indexes work exactly like fresh builds). -/
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

/-! ## The index-preserving indexed path (delta re-port chunk C3)

Native correctness for the value-only twins of #165's index-preserving indexed-path rewrite
(`Dense/DomainFoldNative.lean`'s `denseFoldRewriteIdxV`/`denseFoldOutInPlaceV`/`denseTouchedSet`/
`denseFoldOutIdxV`, mirroring the NEW spec `foldRewrite`/`foldOut`/`touchedSet`/`foldOutIdx` at
`OptimizerPasses/DomainFold.lean:121,374-378,887,899`). Line-parallel to the spec's new proof layer
(`OptimizerPasses/DomainFold.lean` roughly lines 60-1000): the `anyVarIn`-only-gated rewrite, the
in-place fold's satisfies/admissible/side-effect/coverage/occurrence lemmas, and the sparse fold's
equality to the in-place fold. Additive: nothing here is wired yet (chunk C4 flips
`denseFoldStepV`/`denseFoldLoopV` onto this path and supplies the completeness hypotheses
`denseFoldOutIdxV_eq` is parameterized by). Reuses the spec's fully generic `zipIdx_map_sparse`
(`OptimizerPasses/DomainFold.lean:923`) directly, and C1's
`denseCoveredIdx_eq_filter_of_complete`/`denseBuild_complete` are the completeness facts C4 will feed
in. -/

/-- `DenseExpr.anyVarIn` finds a genuinely shared variable (native mirror of
    `Expression.anyVarIn_exists`, `DomainFold.lean:71`). -/
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

/-- `denseFoldRewriteIdxV` is (definitionally) the identity on an expression sharing no variable with
    the group — the linchpin that lets the sparse `denseFoldOutIdxV` pass untouched items through by
    position (native mirror of `foldRewrite_eq_self`, `DomainFold.lean:127`). -/
theorem denseFoldRewriteIdxV_eq_self {xs : List VarId} {survsV : List (List (ZMod p))}
    {e : DenseExpr p} (h : e.anyVarIn xs = false) : denseFoldRewriteIdxV xs survsV e = e := by
  rw [denseFoldRewriteIdxV, h]; rfl

/-- Folding never introduces a `VarId` (gated indexed form; native mirror of `foldRewrite_vars`,
    `DomainFold.lean:291`). Wraps the same core as `denseFoldRewriteV_vars`. -/
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

/-- On an environment agreeing on `xs` with a survivor `pt`, `denseFoldRewriteIdxV` is
    evaluation-preserving (native mirror of `foldRewrite_agree`, `DomainFold.lean:213`). Factors
    exactly as the spec factors `foldRewrite`/`foldRewriteC` over the shared `foldRewriteGo`: the
    weaker (`anyVarIn`-only) gate splits and delegates to the same `denseFoldRewriteGoV_agree`
    `denseFoldRewriteV_agree_covered` already uses. -/
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

/-- If `denv` zeroes every covered constraint, the group is pinned to a survivor `pt` that `denv`
    agrees with on `xs` (native mirror of the extracted `groupSurvivors_mem_agree`,
    `DomainFold.lean:317`). The witness is the value-only assignment `xs.map denv`. Shared by both
    rewrites' covered-agreement lemmas. -/
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

/-- On any environment zeroing all the covered constraints, `denseFoldRewriteIdxV` (over the survivors
    of those constraints) is evaluation-preserving (native mirror of `foldRewrite_agree_covered`,
    `DomainFold.lean:347`). -/
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

/-! ### The in-place fold `denseFoldOutInPlaceV` (mirrors `foldOut`, `DomainFold.lean:374`) -/

/-- A rewritten interaction evaluates identically, given expression-level agreement — the general
    form over any rewrite `g` (the bus side of `denseFoldOutInPlaceV` is structurally identical to
    `denseFoldOutV`'s, only `g` differs; `denseBIEval_foldRewriteV` is the `g = denseFoldRewriteV`
    instance). Native mirror of `mapExpr_eval_of_agree`, `DomainFold.lean:236`. -/
theorem denseBIEval_mapExpr_of_agree (g : DenseExpr p → DenseExpr p) (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (g e).eval denv = e.eval denv)
    (bi : BusInteraction (DenseExpr p)) :
    denseBIEval { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g } denv
      = denseBIEval bi denv := by
  unfold denseBIEval
  simp only [hag bi.multiplicity, List.map_map]
  congr 1
  exact List.map_congr_left (fun e _ => by simp only [Function.comp_apply]; exact hag e)

theorem denseFoldOutInPlaceV_sideEffects_eq (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (survsV : List (List (ZMod p))) (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (denseFoldRewriteIdxV xs survsV e).eval denv = e.eval denv) :
    (denseFoldOutInPlaceV d xs survsV).sideEffects bs denv = d.sideEffects bs denv := by
  unfold DenseConstraintSystem.sideEffects
  simp only [denseFoldOutInPlaceV]
  rw [filter_map_busId_comm d.busInteractions
    (fun bi => { bi with
      multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
      payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }) bs (fun _ => rfl), List.map_map]
  refine List.map_congr_left (fun bi _ => ?_)
  simp only [Function.comp_apply]
  rw [denseBIEval_mapExpr_of_agree (denseFoldRewriteIdxV xs survsV) denv hag bi]

theorem denseFoldOutInPlaceV_admissible_iff (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (survsV : List (List (ZMod p))) (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (denseFoldRewriteIdxV xs survsV e).eval denv = e.eval denv) :
    (denseFoldOutInPlaceV d xs survsV).admissible bs denv ↔ d.admissible bs denv := by
  unfold DenseConstraintSystem.admissible
  have hmap : (denseFoldOutInPlaceV d xs survsV).busInteractions.map (fun bi => denseBIEval bi denv)
      = d.busInteractions.map (fun bi => denseBIEval bi denv) := by
    simp only [denseFoldOutInPlaceV, List.map_map]
    exact List.map_congr_left (fun bi _ => by
      simp only [Function.comp_apply]
      exact denseBIEval_mapExpr_of_agree (denseFoldRewriteIdxV xs survsV) denv hag bi)
  rw [hmap]

/-- Folding introduces no `VarId` (in-place form; native mirror of `foldOut_vars_subset`,
    `DomainFold.lean:410`). -/
theorem denseFoldOutInPlaceV_occ_subset (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : ∀ i ∈ (denseFoldOutInPlaceV d xs survsV).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · have hc2 : c ∈ d.algebraicConstraints.map
        (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c) := hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc2
    by_cases hcc : denseCoveredBy xs c0 = true
    · rw [if_pos hcc] at hic
      exact DenseConstraintSystem.mem_occ_of_constraint hc0 hic
    · rw [if_neg hcc] at hic
      exact DenseConstraintSystem.mem_occ_of_constraint hc0
        (denseFoldRewriteIdxV_vars xs survsV c0 i hic)
  · have hbi2 : bi ∈ d.busInteractions.map
        (fun bi => { bi with
          multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
          payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }) := hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi2
    simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hib
    rcases hib with hm | ⟨e, he, hie⟩
    · exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
        rw [denseBIVars, List.mem_append]
        exact Or.inl (denseFoldRewriteIdxV_vars xs survsV bi0.multiplicity i hm))
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
        rw [denseBIVars, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨e0, he0, denseFoldRewriteIdxV_vars xs survsV e0 i hie⟩)

theorem denseFoldOutInPlaceV_covered (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (xs : List VarId) (survsV : List (List (ZMod p))) :
    (denseFoldOutInPlaceV d xs survsV).CoveredBy reg := by
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · have he' : e ∈ d.algebraicConstraints.map
        (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c) := he
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 he'
    by_cases hcc : denseCoveredBy xs c0 = true
    · rw [if_pos hcc]; exact hcov.1 c0 hc0
    · rw [if_neg hcc]; exact denseFoldRewriteIdxV_covered reg xs survsV (hcov.1 c0 hc0)
  · have hbi' : bi ∈ d.busInteractions.map
        (fun bi => { bi with
          multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
          payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }) := hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    obtain ⟨hm, hp⟩ := hcov.2 bi0 hbi0
    refine ⟨denseFoldRewriteIdxV_covered reg xs survsV hm, fun e he => ?_⟩
    have he' : e ∈ bi0.payload.map (denseFoldRewriteIdxV xs survsV) := he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he'
    exact denseFoldRewriteIdxV_covered reg xs survsV (hp e0 he0)

/-- Under an agreeing `denv`, the in-place folded system is satisfied iff the input is (native mirror
    of `foldOut_satisfies_iff`, `DomainFold.lean:434`): every covered constraint is kept verbatim in
    place, every other expression is rewritten evaluation-preservingly. -/
theorem denseFoldOutInPlaceV_satisfies_iff (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (survsV : List (List (ZMod p))) (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (denseFoldRewriteIdxV xs survsV e).eval denv = e.eval denv) :
    (denseFoldOutInPlaceV d xs survsV).satisfies bs denv ↔ d.satisfies bs denv := by
  have hceval : ∀ c : DenseExpr p,
      (if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c).eval denv = c.eval denv := by
    intro c
    by_cases hcov : denseCoveredBy xs c = true
    · rw [if_pos hcov]
    · rw [if_neg hcov]; exact hag c
  constructor
  · intro hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · have := hsat.1 _ (List.mem_map.2 ⟨c, hc, rfl⟩ :
        (if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c)
          ∈ (denseFoldOutInPlaceV d xs survsV).algebraicConstraints)
      rwa [hceval c] at this
    · have := hsat.2 _ (List.mem_map.2 ⟨bi, hbi, rfl⟩ :
        { bi with
          multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
          payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }
          ∈ (denseFoldOutInPlaceV d xs survsV).busInteractions)
      rwa [denseBIEval_mapExpr_of_agree (denseFoldRewriteIdxV xs survsV) denv hag bi] at this
  · intro hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · have hc' : c ∈ (denseFoldOutInPlaceV d xs survsV).algebraicConstraints := hc
      simp only [denseFoldOutInPlaceV, List.mem_map] at hc'
      obtain ⟨c0, hc0, rfl⟩ := hc'
      rw [hceval c0]; exact hsat.1 c0 hc0
    · have hbi' : bi ∈ (denseFoldOutInPlaceV d xs survsV).busInteractions := hbi
      simp only [denseFoldOutInPlaceV, List.mem_map] at hbi'
      obtain ⟨bi0, hbi0, rfl⟩ := hbi'
      rw [denseBIEval_mapExpr_of_agree (denseFoldRewriteIdxV xs survsV) denv hag bi0]
      exact hsat.2 bi0 hbi0

/-- **Correctness of one in-place fold** (native mirror of `foldOut_correct`, `DomainFold.lean:470`):
    routes through `denseFoldOutInPlaceV_satisfies_iff`, the covered constraints (kept verbatim in
    place) pinning the group so the rewrite agrees with the identity. Same `DensePassCorrect`-shaped
    conclusion (via `ofEnvEq`) `denseFoldOutV_correct` gives. -/
theorem denseFoldOutInPlaceV_correct [Fact p.Prime] (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (xs : List VarId) (doms : List (VarId × List (ZMod p)))
    (hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs = some doms) (isInput : VarId → Bool) :
    DensePassCorrect isInput d
      (denseFoldOutInPlaceV d xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd))) [] bs := by
  set survsV := denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd) with hsurv_def
  have hcov_out : ∀ denv : VarId → ZMod p, (denseFoldOutInPlaceV d xs survsV).satisfies bs denv →
      ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 := by
    intro denv hsat c hc
    have hcb : denseCoveredBy xs c = true := (List.mem_filter.mp hc).2
    have hmem : c ∈ (denseFoldOutInPlaceV d xs survsV).algebraicConstraints := by
      have hm : (if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c)
          ∈ (denseFoldOutInPlaceV d xs survsV).algebraicConstraints :=
        List.mem_map.2 ⟨c, List.mem_of_mem_filter hc, rfl⟩
      rwa [if_pos hcb] at hm
    exact hsat.1 c hmem
  have hcov_cs : ∀ denv : VarId → ZMod p, d.satisfies bs denv →
      ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 :=
    fun denv hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  have hagCov : ∀ denv : VarId → ZMod p, (∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0) →
      ∀ e : DenseExpr p, (denseFoldRewriteIdxV xs survsV e).eval denv = e.eval denv := by
    intro denv hcov
    rw [hsurv_def]
    exact denseFoldRewriteIdxV_agree_covered d xs doms hdoms denv hcov
  refine DensePassCorrect.ofEnvEq ?hsound ?hinv ?hsub ?hcomp
  case hsub => exact denseFoldOutInPlaceV_occ_subset d xs survsV
  case hsound =>
    intro denv hsatout
    have hag := hagCov denv (hcov_out denv hsatout)
    exact ⟨denv, (denseFoldOutInPlaceV_satisfies_iff bs d xs survsV denv hag).1 hsatout,
      by rw [denseFoldOutInPlaceV_sideEffects_eq bs d xs survsV denv hag]; exact BusState.equiv_refl _⟩
  case hinv =>
    intro hgi denv hsatout bi' hbi'
    have hag := hagCov denv (hcov_out denv hsatout)
    have hsatd : d.satisfies bs denv :=
      (denseFoldOutInPlaceV_satisfies_iff bs d xs survsV denv hag).1 hsatout
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    rw [denseBIEval_mapExpr_of_agree (denseFoldRewriteIdxV xs survsV) denv hag bi0]
    exact hgi denv hsatd bi0 hbi0
  case hcomp =>
    intro denv hadm hsat
    have hag := hagCov denv (hcov_cs denv hsat)
    exact ⟨(denseFoldOutInPlaceV_satisfies_iff bs d xs survsV denv hag).2 hsat,
      (denseFoldOutInPlaceV_admissible_iff bs d xs survsV denv hag).2 hadm,
      by rw [denseFoldOutInPlaceV_sideEffects_eq bs d xs survsV denv hag]; exact BusState.equiv_refl _⟩

/-! ### The sparse indexed fold `denseFoldOutIdxV` (mirrors `foldOutIdx`, `DomainFold.lean:899`) -/

/-- Membership in the touched set is membership in some bucket of `xs` (native mirror of
    `touchedSet_contains_iff`, `DomainFold.lean:891`). -/
theorem denseTouchedSet_contains_iff (idx : DenseCovIndex) (xs : List VarId) (i : Nat) :
    (denseTouchedSet idx xs).contains i = true ↔ ∃ v ∈ xs, i ∈ idx.buckets.getD v [] := by
  rw [← Std.HashSet.mem_iff_contains, denseTouchedSet, mem_foldl_insert,
    List.mem_flatMap]
  simp [Std.HashSet.not_mem_empty]

/-- An untouched interaction maps to itself under an inline rewrite that fixes each of its
    expressions (native mirror of `mapExpr_eq_self`, `DomainFold.lean:911`; the dense fold rewrites
    interactions field-by-field, no `BusInteraction.mapExpr`). -/
theorem denseMapExpr_eq_self {bi : BusInteraction (DenseExpr p)} {g : DenseExpr p → DenseExpr p}
    (hm : g bi.multiplicity = bi.multiplicity) (hp : ∀ e ∈ bi.payload, g e = e) :
    { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g } = bi := by
  have hpl : bi.payload.map g = bi.payload :=
    (List.map_congr_left (g := id) hp).trans (List.map_id _)
  rw [hm, hpl]

/-- A rewrite that introduces no variables per expression keeps an interaction's variables (native
    mirror of `mapExpr_vars_subset`, `DomainFold.lean:759`; inline field-by-field rewrite form). -/
theorem denseMapExpr_vars_subset (g : DenseExpr p → DenseExpr p)
    (hg : ∀ (e : DenseExpr p) (i : VarId), i ∈ (g e).vars → i ∈ e.vars)
    (bi : BusInteraction (DenseExpr p)) :
    ∀ i ∈ denseBIVars { bi with multiplicity := g bi.multiplicity, payload := bi.payload.map g },
      i ∈ denseBIVars bi := by
  intro i hi
  simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hi ⊢
  rcases hi with hi | ⟨e, he, hi⟩
  · exact Or.inl (hg _ i hi)
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact Or.inr ⟨e0, he0, hg e0 i hi⟩

/-- **The sparse fold is the in-place fold** (native mirror of `foldOutIdx_eq`,
    `DomainFold.lean:943`): every non-candidate position holds an item sharing no variable with `xs`
    (bucket completeness, contraposed), on which `denseFoldRewriteIdxV` is the identity — so skipping
    it is exact. Parameterized by the constraint- and interaction-side bucket-completeness hypotheses
    `hidx`/`hbis` shaped exactly like the spec's `FoldIdx.hidx`/`hbis` fields
    (`DomainFold.lean:729-738`), so chunk C4 can supply them from the restructured `DenseFoldIdx`
    (via C1's `denseBuild_complete`/`denseCoveredIdx_eq_filter_of_complete`). Reuses the spec's fully
    generic `zipIdx_map_sparse` directly. -/
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

/-! ### Completeness preservation across an in-place fold (mirrors #165's `FoldIdx.refresh` field
proofs, `OptimizerPasses/DomainFold.lean:781-810`)

`denseFoldOutInPlaceV` rewrites items in place (order- and length-preserving) and only ever shrinks
an expression's variable set (`denseFoldRewriteIdxV_vars` on the constraint side, that plus
`denseMapExpr_vars_subset` on the interaction side), so a bucket map complete for the input stays
complete for the folded output. These are exactly the two proofs #165's dependent `FoldIdx.refresh`
carries as its `hidx`/`hbis` fields; on the data-only dense `DenseFoldIdx` they live as standalone
lemmas the loop threads. -/

/-- Constraint-side bucket completeness survives an in-place fold (mirrors `FoldIdx.refresh`'s `hidx`
    field proof, `DomainFold.lean:781`). -/
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

/-- Interaction-side bucket completeness survives an in-place fold (mirrors `FoldIdx.refresh`'s
    `hbis` field proof, `DomainFold.lean:800`). -/
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

/-- Coverage survives the sparse indexed fold (native mirror of the coverage half of
    `foldOutIdx`'s soundness; the sparse fold only rewrites — never introduces — variables at each
    position, so every item stays registered). Proved directly, without the completeness hypotheses,
    so the coverage loop needs none. -/
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

/-- Constraint-side completeness of the input's index survives one step: the refreshed index keeps
    the old bucket map (`denseFoldStepV_snd_idx_eq`), which stays complete for the step's output
    (identity, or the sparse fold via `denseFoldOutInPlaceV_hidx`). -/
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

/-- Interaction-side completeness survives one step (dual of `denseFoldStepV_snd_idx`, via
    `denseFoldOutInPlaceV_hbis`). -/
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

/-- **The native value-only dense domain-fold pass.** Connects to the audited spec via
    `DensePassCorrect.lift` (through `of`) on the native `DensePassCorrect` proof — no
    commutation with the reference pass, no `decode` in a discharged obligation. -/
def denseDomainFoldPassV (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => denseDomainFoldFV pw d)
    (fun _ _ _ => [])
    (fun reg _ _ d hcov => denseDomainFoldFV_covered pw reg d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseDomainFoldFV_correct pw bs reg.isInput d)

end ApcOptimizer.Dense
