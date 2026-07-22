import ApcOptimizer.Implementation.OptimizerPasses.BoxRewrite
import ApcOptimizer.Implementation.OptimizerPasses.FlagFoldDropsProof

set_option autoImplicit false

/-! # Correctness for dense box-certified multilinear rewriting — flagFold's `boxRewrite` sub-pass

`DensePassCorrect` for the dense `boxRewrite` transform (`Dense/BoxRewriteNative.lean`), lifted to
the audited `Variable` spec through `DenseVerifiedPassW.of` (`Dense/Bridge.lean`). NO WIRING here —
`boxRewrite` is the second sub-pass of the scheduled `flagFold` composite
(`fxSubstPass → boxRewritePass → boxTautoDropPass → pointwiseDupDropPass`); the chain assembly lives
elsewhere. This file delivers the correctness proof plus the `DenseVerifiedPassW` value
`denseBoxRewritePass`, ready for chain assembly.

## Proof shape

`boxRewritePass` is a constraint-**and-bus-map** pass: every over-bound algebraic constraint, bus
multiplicity, and payload expression is replaced by its certified multilinear reduction. Crucially,
the reduction itself (`denseReduceExpr`/`densePolyOf`/…) carries **no** correctness proof — the
runtime certificate `denseBrCert` re-verifies pointwise, so the candidate `e'` is treated
*opaquely* and NO polynomial-semantics evaluation lemma is required. The box justification rides on
the single-variable constraints (the `denseFindDomainAlg` sources), which are never rewritten (they
fail the `≥ 2`-distinct-variable certificate guard) and survive verbatim into the output. So
`out.satisfies ↔ d.satisfies` on the SAME environment, side effects agree (rewrites are
eval-preserving on any assignment zeroing the singles), and admissibility is unchanged —
`DensePassCorrect.ofEnvEq`.

The correctness chain over `VarId → ZMod p` (`denseBrCert_sound → denseBrRw_sound/denseBrRw_vars/
denseBrRw_singleVar → denseBrBi_eval → boxRewrite_denseCorrect`) reuses
`denseFindDomainAlg_sound`/`mem_denseAssignments`/`denseEnvOfFast_map`/`DenseExpr.eval_congr` (finite
domain box), `DenseExpr.eval_substF`/`denseEnvF` (partial evaluation), `denseLinearize_eval`/
`DenseLinExpr.norm_eval` (affine-form semantics), and `List.mergeSort_perm` (the `canonEq`
permutation, keyed `VarId.index` densely — the two sorts only canonicalise a *multiset* comparison,
so the exact key is irrelevant to soundness, which only needs the two lists sorted by the SAME
total order).

## Degree

`boxRewrite` intermediates legitimately exceed the degree bound (its whole point is to rewrite
syntactically over-bound expressions back within bound), and the scheduled composite wraps the ENTIRE
`flagFold` chain under a single `guardDegree`. Accordingly this pass value carries NO degree guard of
its own: `DenseVerifiedPassW.of` produces a `DenseVerifiedPassW` with the spec `PassCorrect`-on-decode
discharged via the lift and NO `DenseRespectsDeg` obligation attached (that is the separate
`of_respectsDeg` theorem, only invoked when a pass is individually `guardDegree`-wrapped — as this
one is NOT). The composite assembly guards the whole chain. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Partial-evaluation point map is the identity on its own restriction -/

/-- `denseEnvF` over a point map is the identity when the point is the environment's own
    restriction. -/
theorem denseEnvF_ptFun_self (doms : List (VarId × List (ZMod p))) (denv : VarId → ZMod p) :
    denseEnvF (densePtFun (doms.map (fun vd => (vd.1, denv vd.1)))) denv = denv := by
  funext v
  unfold denseEnvF densePtFun
  by_cases hin : (doms.map (fun vd => (vd.1, denv vd.1))).any (fun t => t.1 == v) = true
  · rw [if_pos hin]
    show denseEnvOfFast (doms.map (fun vd => (vd.1, denv vd.1))) v = denv v
    refine denseEnvOfFast_map doms denv v ?_
    obtain ⟨t, ht, htv⟩ := List.any_eq_true.1 hin
    obtain ⟨vd, hvd, rfl⟩ := List.mem_map.1 ht
    have : vd.1 = v := eq_of_beq htv
    rw [← this]
    exact List.mem_map.2 ⟨vd, hvd, rfl⟩
  · rw [if_neg hin]

/-! ## The certificate is sound -/

/-- **Certificate soundness:** on every point of the joint small-domain box both expressions
    partially evaluate to the same affine form, so they agree on every assignment zeroing the
    single-variable constraints. The candidate `e'` is opaque; only the certificate is trusted. -/
theorem denseBrCert_sound [Fact p.Prime] (singles : List (DenseExpr p)) (e e' : DenseExpr p)
    (h : denseBrCert singles e e' = true) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval denv = 0) : e.eval denv = e'.eval denv := by
  unfold denseBrCert at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨_h2, ⟨⟨_hcover, _hcap⟩, hall⟩⟩ := h
  set boxed := ((e.vars ++ e'.vars).eraseDups.filter (fun v =>
    match denseFindDomainAlg singles v with
    | some d => d.length ≤ 2
    | none => false)) with hboxed
  set doms := (boxed.filterMap (fun v =>
    (denseFindDomainAlg singles v).map (fun d => (v, d)))) with hdoms
  have hmemdoms : ∀ vd ∈ doms, denv vd.1 ∈ vd.2 := by
    intro vd hvd
    rw [hdoms] at hvd
    obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
    cases hfd : denseFindDomainAlg singles v with
    | none => rw [hfd] at hvd'; simp at hvd'
    | some d =>
      rw [hfd] at hvd'
      simp only [Option.map_some, Option.some.injEq] at hvd'
      obtain rfl := hvd'.symm
      exact denseFindDomainAlg_sound denv singles v d hfd hdom
  have hpt := mem_denseAssignments doms denv hmemdoms
  have hcond := List.all_eq_true.mp hall _ hpt
  cases hl1 : denseLinearize (e.substF (densePtFun (doms.map (fun vd => (vd.1, denv vd.1))))) with
  | none => rw [hl1] at hcond; simp at hcond
  | some l1 =>
    cases hl2 : denseLinearize (e'.substF (densePtFun (doms.map (fun vd => (vd.1, denv vd.1))))) with
    | none => rw [hl1, hl2] at hcond; simp at hcond
    | some l2 =>
      rw [hl1, hl2] at hcond
      unfold denseCanonEq at hcond
      rw [Bool.and_eq_true] at hcond
      obtain ⟨hconst, hterms⟩ := hcond
      have hs1 : (e.substF (densePtFun (doms.map (fun vd => (vd.1, denv vd.1))))).eval denv
          = e.eval denv := by
        rw [DenseExpr.eval_substF, denseEnvF_ptFun_self]
      have hs2 : (e'.substF (densePtFun (doms.map (fun vd => (vd.1, denv vd.1))))).eval denv
          = e'.eval denv := by
        rw [DenseExpr.eval_substF, denseEnvF_ptFun_self]
      have hsum : ((l1.norm.terms.map (fun t => t.2 * denv t.1)).sum)
          = ((l2.norm.terms.map (fun t => t.2 * denv t.1)).sum) := by
        have hp1 : List.Perm (l1.norm.terms.map (fun t => t.2 * denv t.1))
            ((l1.norm.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))).map
              (fun t => t.2 * denv t.1)) :=
          ((List.mergeSort_perm l1.norm.terms _).symm).map _
        have hp2 : List.Perm ((l2.norm.terms.mergeSort
              (fun a b => decide (a.1.index ≤ b.1.index))).map (fun t => t.2 * denv t.1))
            (l2.norm.terms.map (fun t => t.2 * denv t.1)) :=
          (List.mergeSort_perm l2.norm.terms _).map _
        rw [hp1.sum_eq, eq_of_beq hterms, hp2.sum_eq]
      have hev : l1.norm.eval denv = l2.norm.eval denv := by
        show l1.norm.const + _ = l2.norm.const + _
        rw [eq_of_beq hconst, hsum]
      rw [← hs1, ← hs2, denseLinearize_eval _ l1 hl1 denv, denseLinearize_eval _ l2 hl2 denv,
          ← DenseLinExpr.norm_eval l1 denv, ← DenseLinExpr.norm_eval l2 denv]
      exact hev

/-! ## Per-expression rewrite lemmas -/

/-- **Per-expression rewrite soundness:** rewriting preserves evaluation on every assignment
    zeroing the single-variable constraints. -/
theorem denseBrRw_sound [Fact p.Prime] (singles : List (DenseExpr p)) (bound : Nat)
    (e : DenseExpr p) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval denv = 0) :
    (denseBrRw singles bound e).eval denv = e.eval denv := by
  simp only [denseBrRw]
  split_ifs with hd
  · rfl
  · split
    next e' _heq =>
      split_ifs with hok
      · rw [Bool.and_eq_true, Bool.and_eq_true] at hok
        exact (denseBrCert_sound singles e e' hok.2 denv hdom).symm
      · rfl
    next _heq => rfl

/-- **Per-expression rewrite variable subset:** the rewrite introduces no variable. -/
theorem denseBrRw_vars (singles : List (DenseExpr p)) (bound : Nat) (e : DenseExpr p) :
    ∀ v ∈ (denseBrRw singles bound e).vars, v ∈ e.vars := by
  intro v hv
  simp only [denseBrRw] at hv
  split_ifs at hv with hd
  · exact hv
  · split at hv
    next e' _heq =>
      split_ifs at hv with hok
      · rw [Bool.and_eq_true, Bool.and_eq_true] at hok
        exact of_decide_eq_true (List.all_eq_true.mp hok.1.2 v hv)
      · exact hv
    next _heq => exact hv

/-- A single-variable expression is never rewritten (the certificate's ≥ 2-variables guard), so the
    domain sources survive verbatim. -/
theorem denseBrRw_singleVar (singles : List (DenseExpr p)) (bound : Nat) (c : DenseExpr p)
    (hs : c.vars.eraseDups.length ≤ 1) : denseBrRw singles bound c = c := by
  have hcert : ∀ e' : DenseExpr p, denseBrCert singles c e' = false := by
    intro e'
    unfold denseBrCert
    have h2 : (2 ≤ c.vars.eraseDups.length : Bool) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [h2, Bool.false_and]
  simp only [denseBrRw]
  split_ifs with hd
  · rfl
  · split
    next e' _heq =>
      rw [hcert e', Bool.and_false, if_neg (by simp)]
    next _heq => rfl

/-! ## Per-interaction rewrite lemmas -/

/-- **Per-interaction rewrite eval:** the rewritten interaction evaluates to the same message on
    every assignment zeroing the single-variable constraints. -/
theorem denseBrBi_eval [Fact p.Prime] (singles : List (DenseExpr p)) (db : DegreeBound)
    (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval denv = 0) :
    denseBIEval (denseBrBi singles db bi) denv = denseBIEval bi denv := by
  unfold denseBrBi denseBIEval
  simp only [BusInteraction.mk.injEq]
  refine ⟨trivial, denseBrRw_sound singles _ _ denv hdom, ?_⟩
  rw [List.map_map]
  exact List.map_congr_left (fun e _ => denseBrRw_sound singles _ e denv hdom)

/-- The rewritten interaction carries only input variables (`denseBrRw_vars` lifted through
    `denseBrBi`). -/
theorem denseBrBi_vars (singles : List (DenseExpr p)) (db : DegreeBound)
    (bi : BusInteraction (DenseExpr p)) :
    ∀ i ∈ denseBIVars (denseBrBi singles db bi), i ∈ denseBIVars bi := by
  intro i hi
  simp only [denseBIVars, denseBrBi, List.mem_append, List.mem_flatMap] at hi ⊢
  rcases hi with hm | ⟨e', he', hie⟩
  · exact Or.inl (denseBrRw_vars singles _ _ i hm)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact Or.inr ⟨e, he, denseBrRw_vars singles _ e i hie⟩

/-! ## Coverage preservation -/

/-- Coverage is preserved: rewrites introduce no variable, so every leaf of the output is a leaf of
    the input, and the registry covers those. -/
theorem DenseConstraintSystem.boxRewrite_covered {reg : VarRegistry}
    {d : DenseConstraintSystem p} (b : DegreeBound) (hc : d.CoveredBy reg) :
    (d.boxRewrite b).CoveredBy reg := by
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 he
    intro i hi
    exact hc.1 c hcm i (denseBrRw_vars _ _ c i hi)
  · obtain ⟨bi0, hbim, rfl⟩ := List.mem_map.1 hbi
    obtain ⟨hmc, hpc⟩ := hc.2 bi0 hbim
    refine ⟨fun i hi => hmc i (denseBrRw_vars _ _ bi0.multiplicity i hi), fun e he => ?_⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact fun i hi => hpc e0 he0 i (denseBrRw_vars _ _ e0 i hi)

/-! ## Pass correctness -/

/-- **Box-rewrite correctness.** Every rewritten expression evaluates equally to the original on
    every assignment zeroing the (never-rewritten) single-variable constraints, so satisfaction is
    preserved on the SAME environment and side effects / admissibility are unchanged. -/
theorem DenseConstraintSystem.boxRewrite_denseCorrect [Fact p.Prime]
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (isInput : VarId → Bool)
    (b : DegreeBound) :
    DensePassCorrect isInput d (d.boxRewrite b) [] bs := by
  -- single-variable domain sources survive verbatim
  have hsingle : ∀ c ∈ denseSingleVarCs d.algebraicConstraints,
      c ∈ (d.boxRewrite b).algebraicConstraints := by
    intro c hc
    have hmem := List.mem_of_mem_filter hc
    have hs : c.vars.eraseDups.length ≤ 1 := by
      have h1 := (List.mem_filter.1 hc).2
      rw [HashedDedup.hashedEraseDups_eq] at h1
      have h2 : c.vars.eraseDups.length = 1 := by simpa using h1
      omega
    exact List.mem_map.2 ⟨c, hmem, denseBrRw_singleVar _ _ c hs⟩
  have hdomOut : ∀ denv, (d.boxRewrite b).satisfies bs denv →
      ∀ c ∈ denseSingleVarCs d.algebraicConstraints, c.eval denv = 0 :=
    fun denv hsat c hc => hsat.1 c (hsingle c hc)
  have hdomIn : ∀ denv, d.satisfies bs denv →
      ∀ c ∈ denseSingleVarCs d.algebraicConstraints, c.eval denv = 0 :=
    fun denv hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  -- satisfaction equivalence on the SAME environment
  have hiff : ∀ denv, (d.boxRewrite b).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    constructor
    · intro hsat
      have hdom := hdomOut denv hsat
      refine ⟨fun c hc => ?_, fun bi hbim => ?_⟩
      · have h0 := hsat.1 _ (List.mem_map.2 ⟨c, hc, rfl⟩)
        rw [denseBrRw_sound _ _ c denv hdom] at h0
        exact h0
      · have h0 := hsat.2 _ (List.mem_map.2 ⟨bi, hbim, rfl⟩)
        rw [denseBrBi_eval _ _ bi denv hdom] at h0
        exact h0
    · intro hsat
      have hdom := hdomIn denv hsat
      refine ⟨fun c' hc' => ?_, fun bi' hbi' => ?_⟩
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
        rw [denseBrRw_sound _ _ c denv hdom]
        exact hsat.1 c hc
      · obtain ⟨bi, hbim, rfl⟩ := List.mem_map.1 hbi'
        show (denseBIEval (denseBrBi (denseSingleVarCs d.algebraicConstraints) b bi) denv).multiplicity
            ≠ 0 → _
        rw [denseBrBi_eval _ _ bi denv hdom]
        exact hsat.2 bi hbim
  -- side effects agree given the domain hypothesis
  have hside : ∀ denv, (∀ c ∈ denseSingleVarCs d.algebraicConstraints, c.eval denv = 0) →
      (d.boxRewrite b).sideEffects bs denv = d.sideEffects bs denv := by
    intro denv hdom
    unfold DenseConstraintSystem.sideEffects
    rw [show (d.boxRewrite b).busInteractions
          = d.busInteractions.map (denseBrBi (denseSingleVarCs d.algebraicConstraints) b) from rfl,
        filter_map_busId_comm d.busInteractions
          (denseBrBi (denseSingleVarCs d.algebraicConstraints) b) bs (fun _ => rfl), List.map_map]
    refine List.map_congr_left (fun bi _ => ?_)
    simp only [Function.comp_apply,
      denseBrBi_eval (denseSingleVarCs d.algebraicConstraints) b bi denv hdom]
  -- admissibility agrees given the domain hypothesis
  have hadmEq : ∀ denv, (∀ c ∈ denseSingleVarCs d.algebraicConstraints, c.eval denv = 0) →
      ((d.boxRewrite b).admissible bs denv ↔ d.admissible bs denv) := by
    intro denv hdom
    unfold DenseConstraintSystem.admissible
    have hmap : (d.boxRewrite b).busInteractions.map (fun bi => denseBIEval bi denv)
        = d.busInteractions.map (fun bi => denseBIEval bi denv) := by
      rw [show (d.boxRewrite b).busInteractions
            = d.busInteractions.map (denseBrBi (denseSingleVarCs d.algebraicConstraints) b) from rfl,
          List.map_map]
      refine List.map_congr_left (fun bi _ => ?_)
      simp only [Function.comp_apply]
      exact denseBrBi_eval (denseSingleVarCs d.algebraicConstraints) b bi denv hdom
    rw [hmap]
  refine DensePassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  · -- soundness
    intro denv hsat
    refine ⟨denv, (hiff denv).1 hsat, ?_⟩
    rw [hside denv (hdomOut denv hsat)]
    exact BusState.equiv_refl _
  · -- invariant preservation
    intro hgi denv hsat bi hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
    show (denseBIEval (denseBrBi (denseSingleVarCs d.algebraicConstraints) b bi0) denv).multiplicity
        ≠ 0 → bs.breaksInvariant
          (denseBIEval (denseBrBi (denseSingleVarCs d.algebraicConstraints) b bi0) denv) = false
    rw [denseBrBi_eval _ _ bi0 denv (hdomOut denv hsat)]
    exact hgi denv ((hiff denv).1 hsat) bi0 hbi0
  · -- output occurrences are input occurrences
    intro i hi
    simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi
    rcases hi with ⟨e', he', hie⟩ | ⟨bi', hbi', hib⟩
    · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 he'
      exact DenseConstraintSystem.mem_occ_of_constraint hcm (denseBrRw_vars _ _ c i hie)
    · obtain ⟨bi, hbim, rfl⟩ := List.mem_map.1 hbi'
      exact DenseConstraintSystem.mem_occ_of_bi hbim (denseBrBi_vars _ _ bi i hib)
  · -- completeness (same env; admissibility/side effects unchanged)
    intro denv hadm hsat
    have hdom := hdomIn denv hsat
    refine ⟨(hiff denv).2 hsat, (hadmEq denv hdom).2 hadm, ?_⟩
    rw [hside denv hdom]
    exact BusState.equiv_refl _

/-! ## The dense box-rewrite pass -/

/-- The box-rewrite transform is covered. -/
theorem denseBoxRewriteF_covered (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseBoxRewriteF pw b bs d).CoveredBy reg := by
  unfold denseBoxRewriteF
  split_ifs with hp
  · exact DenseConstraintSystem.boxRewrite_covered b hcov
  · exact hcov

/-- The box-rewrite transform is `DensePassCorrect`. -/
theorem denseBoxRewriteF_correct (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (d : DenseConstraintSystem p) (_hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseBoxRewriteF pw b bs d) [] bs := by
  unfold denseBoxRewriteF
  split_ifs with hp
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    exact DenseConstraintSystem.boxRewrite_denseCorrect d bs reg.isInput b
  · exact dpcRefl reg.isInput d bs

/-- **The dense box-rewrite pass** (second sub-pass of the flagFold composite). Fact-free —
    the `of` transform ignores `facts`. Carries NO degree guard: the whole `flagFold` chain is
    wrapped under one `guardDegree` (box-rewrite intermediates legitimately exceed the bound).
    Ready for chain assembly. -/
def denseBoxRewritePass (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (fun bs _ d => denseBoxRewriteF pw b bs d) (fun _ _ _ => [])
    (fun reg bs _ d hcov => denseBoxRewriteF_covered pw b reg bs d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d hcov => denseBoxRewriteF_correct pw b reg bs d hcov)

end ApcOptimizer.Dense
