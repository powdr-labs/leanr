import ApcOptimizer.Implementation.Dense.DomainFoldNative
import ApcOptimizer.Implementation.Dense.DomainBatchNativeProof

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

/-! ## Native `DensePassCorrect` shortcuts (env'=env, and composition) -/

/-- The env'=env native correctness shape (mirrors `PassCorrect.ofEnvEq`): the fold's completeness
    witness is the input assignment and it introduces no variable. -/
theorem DensePassCorrect.ofEnvEq {isInput : VarId → Bool} {d out : DenseConstraintSystem p}
    {bs : BusSemantics p}
    (hsound : out.implies d bs)
    (hinv : d.guaranteesInvariants bs → out.guaranteesInvariants bs)
    (hsub : ∀ i ∈ out.occ, i ∈ d.occ)
    (hcomp : ∀ denv, d.admissible bs denv → d.satisfies bs denv →
      out.satisfies bs denv ∧ out.admissible bs denv ∧
        d.sideEffects bs denv ≈ out.sideEffects bs denv) :
    DensePassCorrect isInput d out [] bs := by
  refine ⟨hsound, hinv, fun i hi _ => hsub i hi, ?_⟩
  intro denv hadm hsat
  obtain ⟨ho1, ho2, ho3⟩ := hcomp denv hadm hsat
  refine ⟨denv, ho1, ho2, ho3, fun _ _ => rfl, ?_⟩
  intro inputVarIds _ i hi _
  show i ∈ d.occ ∧ denv i = denv i
  exact ⟨hsub i hi, rfl⟩

/-- `DensePassCorrect` composes (derivations empty on both sides). Mirrors `PassCorrect.andThen`
    specialised to no derivations. -/
theorem DensePassCorrect.trans {isInput : VarId → Bool} {d1 d2 d3 : DenseConstraintSystem p}
    {bs : BusSemantics p} (h12 : DensePassCorrect isInput d1 d2 [] bs)
    (h23 : DensePassCorrect isInput d2 d3 [] bs) : DensePassCorrect isInput d1 d3 [] bs := by
  obtain ⟨hs12, hi12, hv12, hc12⟩ := h12
  obtain ⟨hs23, hi23, hv23, hc23⟩ := h23
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro denv hsat3
    obtain ⟨e1, hsat2, hse23⟩ := hs23 denv hsat3
    obtain ⟨e0, hsat1, hse12⟩ := hs12 e1 hsat2
    exact ⟨e0, hsat1, BusState.equiv_trans hse23 hse12⟩
  · intro h; exact hi23 (hi12 h)
  · intro i hi3 hii; exact hv12 i (hv23 i hi3 hii) hii
  · intro denv hadm1 hsat1
    obtain ⟨e1, hsat2, hadm2, hse12, hii12, hrec12⟩ := hc12 denv hadm1 hsat1
    obtain ⟨e2, hsat3, hadm3, hse23, hii23, hrec23⟩ := hc23 e1 hadm2 hsat2
    refine ⟨e2, hsat3, hadm3, BusState.equiv_trans hse12 hse23, ?_, ?_⟩
    · intro i hii; rw [hii23 i hii, hii12 i hii]
    · intro inputVarIds hcov1 i hi3 hisF
      have H23 := hrec23 d2.occ (fun j hj _ => hj) i hi3 hisF
      have b23 : i ∈ d2.occ ∧ e2 i = e1 i := H23
      have H12 := hrec12 inputVarIds hcov1 i b23.1 hisF
      have b12 : i ∈ d1.occ ∧ e1 i = denv i := H12
      show i ∈ d1.occ ∧ e2 i = denv i
      exact ⟨b12.1, by rw [b23.2, b12.2]⟩

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
    (d : DenseConstraintSystem p) (xs : List VarId) :
    DensePassCorrect isInput d (denseFoldStepWithV d xs (denseCoveredCsOf d xs)) [] bs := by
  unfold denseFoldStepWithV
  split
  · exact DensePassCorrect_refl isInput d bs
  · rename_i doms hgd
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hgate : (1 ≤ (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd)).length
          && denseSystemHasFoldableV d xs (denseGroupSurvivorsEV (denseCoveredCsOf d xs) xs (doms.map Prod.snd))) = true
      · rw [if_pos hgate]
        exact denseFoldOutV_correct bs d xs doms hgd isInput
      · rw [if_neg (by simpa using hgate)]; exact DensePassCorrect_refl isInput d bs
    · rw [if_neg hp]; exact DensePassCorrect_refl isInput d bs

theorem denseFoldStepWithV_covered (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (xs : List VarId) (es : List (DenseExpr p)) :
    (denseFoldStepWithV d xs es).CoveredBy reg := by
  unfold denseFoldStepWithV
  split
  · exact hcov
  · rename_i doms _
    by_cases hp : (doms.map (fun yd => yd.2.length)).prod ≤ 256
    · rw [if_pos hp]
      by_cases hgate : (1 ≤ (denseGroupSurvivorsEV es xs (doms.map Prod.snd)).length
          && denseSystemHasFoldableV d xs (denseGroupSurvivorsEV es xs (doms.map Prod.snd))) = true
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
      show DensePassCorrect isInput d
        (denseFoldLoopDirectV rest (denseFoldStepWithV d xs (denseCoveredCsOf d xs))) [] bs
      exact DensePassCorrect.trans (denseFoldStepWithV_correct bs isInput d xs) (ih _)

theorem denseFoldLoopDirectV_covered (reg : VarRegistry) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p),
      d.CoveredBy reg → (denseFoldLoopDirectV targets d).CoveredBy reg := by
  intro targets
  induction targets with
  | nil => intro d hcov; exact hcov
  | cons xs rest ih =>
      intro d hcov
      exact ih _ (denseFoldStepWithV_covered reg d hcov xs (denseCoveredCsOf d xs))

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
            then denseFoldOutV d xs
                (denseGroupSurvivorsEV (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs
                  (doms.map Prod.snd))
            else d)
           else d) := by
  simp only [denseFoldStepV]
  cases hgd : denseGroupDoms (denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs) xs with
  | none => rfl
  | some doms => simp only [apply_ite Prod.fst]

theorem denseFoldStepV_snd_idx (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : fidx.idx = denseCovBuild DenseExpr.vars d.algebraicConstraints) :
    (denseFoldStepV d fidx xs).2.idx
      = denseCovBuild DenseExpr.vars (denseFoldStepV d fidx xs).1.algebraicConstraints := by
  simp only [denseFoldStepV]; split
  · exact hidx
  · split_ifs <;> first | rfl | exact hidx

theorem denseFoldStepV_snd_arr (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (harr : fidx.arr = d.algebraicConstraints.toArray) :
    (denseFoldStepV d fidx xs).2.arr = (denseFoldStepV d fidx xs).1.algebraicConstraints.toArray := by
  simp only [denseFoldStepV]; split
  · exact harr
  · split_ifs <;> first | rfl | exact harr

/-- Under the index-synchronisation invariant, the covered set the index serves equals the direct
    covered set. -/
theorem denseFoldStepV_es_eq (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : fidx.idx = denseCovBuild DenseExpr.vars d.algebraicConstraints)
    (harr : fidx.arr = d.algebraicConstraints.toArray) :
    denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs = denseCoveredCsOf d xs := by
  rw [hidx, harr]
  exact denseCoveredIdx_eq_filter DenseExpr.vars d.algebraicConstraints (denseCoveredBy xs) xs
    (fun i _hi hQ => denseCoveredBy_shares_var xs d.algebraicConstraints[i] hQ)

theorem denseFoldStepV_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (hidx : fidx.idx = denseCovBuild DenseExpr.vars d.algebraicConstraints)
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
      · rw [if_pos hgate]
        exact denseFoldOutV_correct bs d xs doms hgd isInput
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
      · rw [if_pos hgate]; exact denseFoldOutV_covered reg d hcov xs _
      · rw [if_neg (by simpa using hgate)]; exact hcov
    · rw [if_neg hp]; exact hcov

theorem denseFoldLoopV_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool) :
    ∀ (targets : List (List VarId)) (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p),
      fidx.idx = denseCovBuild DenseExpr.vars d.algebraicConstraints →
      fidx.arr = d.algebraicConstraints.toArray →
      DensePassCorrect isInput d (denseFoldLoopV targets d fidx) [] bs := by
  intro targets
  induction targets with
  | nil => intro d fidx _ _; exact DensePassCorrect_refl isInput d bs
  | cons xs rest ih =>
      intro d fidx hidx harr
      show DensePassCorrect isInput d
        (denseFoldLoopV rest (denseFoldStepV d fidx xs).1 (denseFoldStepV d fidx xs).2) [] bs
      refine DensePassCorrect.trans (denseFoldStepV_correct bs isInput d fidx xs hidx harr)
        (ih _ _ ?_ ?_)
      · exact denseFoldStepV_snd_idx d fidx xs hidx
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
      exact denseFoldLoopV_correct bs isInput (denseTargetsV d) d (DenseFoldIdx.mk' d) rfl rfl
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
    `DensePassCorrect.lift` (through `ofNative`) on the native `DensePassCorrect` proof — no
    commutation with the reference pass, no `decode` in a discharged obligation. -/
def denseDomainFoldPassV (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofNative
    (fun _ _ d => denseDomainFoldFV pw d)
    (fun _ _ _ => [])
    (fun reg _ _ d hcov => denseDomainFoldFV_covered pw reg d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseDomainFoldFV_correct pw bs reg.isInput d)

end ApcOptimizer.Dense
