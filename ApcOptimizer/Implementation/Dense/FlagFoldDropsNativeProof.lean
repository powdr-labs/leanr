import ApcOptimizer.Implementation.Dense.FlagFoldDropsNative
import ApcOptimizer.Implementation.Dense.FlagUnifyNativeProof

set_option autoImplicit false

/-! # Native soundness for the dense flagFold drop sub-passes (Task 3, busUnify cluster, chunk
    S3 — prover)

Native `DensePassCorrect` for the two flagFold drop transforms
(`Dense/FlagFoldDropsNative.lean`), lifted to the audited `Variable` spec through
`DenseVerifiedPassW.ofNative` (`Dense/Bridge.lean`). NO WIRING here — the scheduled `flagFold`
label is a four-sub-pass composite (`fxSubstPass → boxRewritePass → boxTautoDropPass →
pointwiseDupDropPass`); only parts B/C exist densely so far, and the selector swap happens in a
later chunk (S5) once all four are ready. This file delivers the two proofs plus their
`DenseVerifiedPassW` values, ready for chain assembly.

## Part B: box-tautology replacement (`denseBoxTautoDropF`)

A constraint-**map** pass: each multi-variable constraint that vanishes on its variables' proven
finite-domain box is replaced by the literal `0`; bus interactions untouched. The box justification
rides on the single-variable constraints (the `denseFindDomainAlg` sources), which are never
replaced (they fail the `≥ 2` distinct-variable guard) and survive verbatim into the output. So
`out.satisfies ↔ d.satisfies` on the SAME environment, and side effects/admissibility are
unchanged (bus interactions identical) — `DensePassCorrect.ofEnvEq`. Native re-derivation of the
spec `ConstraintSystem.boxTautoReplace_correct` chain over `VarId → ZMod p` (reusing
`denseFindDomainAlg_sound`/`mem_denseAssignments`/`denseEnvOfFast_map`/`DenseExpr.eval_congr`).

## Part C: pointwise-duplicate stateless-check removal (`densePointwiseDupDropF`)

A bus-**filter** pass dropping stateless interactions whose message is pointwise equal to a
retained one on the box. The dropped interaction is accepted under every assignment satisfying the
FILTERED system, because its first-of-class earlier twin is provably kept and evaluates equally —
the depth-1 `densePdFirst_keep` rule, fed to a native `DensePassCorrect.denseFilterBusEntailed`
(the native mirror of `ConstraintSystem.filterBusEntailed_correct`). The certificate soundness
chain `denseBoxAgree_sound → denseSlotEqCert_sound → denseMsgEqCert_sound` is a native
re-derivation of the spec `boxAgree_sound/slotEqCert_sound/msgEqCert_sound`. The pass is stated
over an arbitrary prefilter `fast` (instantiated at runtime with `densePdFastKeep` over
`densePdDropSet`), so the mutable sweep carries no proof — dropping more is always sound — and the
`densePdFastKeep`/`densePdDropSet` loop is NOT reasoned about, exactly as the spec never reasons
about `pdDropSet` beyond `pdFastKeep = pdKeep`-equivalence (here: never needed, the certified
`densePdKeep` disjunct re-verifies every flagged drop).

## Fact-free `ofNative` wrapping

Both spec passes are `VerifiedPass p` (no `BusFacts`); the dense transforms drop `facts` entirely.
`DenseVerifiedPassW.ofNative` expects a `(bs) (facts) (d)` transform, so each is wrapped
`fun bs _ d => denseXxxF pw bs d`, ignoring `facts` — the same shape `denseConstantFoldPass` uses
for its `bs`/`facts`-ignoring transform. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part B: box-tautology replacement -/

/-- `denseBtKeep` implies its certificate (mirrors `btKeep_cert`). -/
theorem denseBtKeep_cert {singles : List (DenseExpr p)}
    {domOf : VarId → Option (List (ZMod p))} {c : DenseExpr p}
    (h : denseBtKeep singles domOf c = true) : denseBtCert singles c = true := by
  unfold denseBtKeep at h
  rw [Bool.and_eq_true] at h
  exact h.2

/-- A false certificate falsifies `denseBtKeep` (mirrors `btKeep_of_cert_false`). -/
theorem denseBtKeep_of_cert_false {singles : List (DenseExpr p)}
    {domOf : VarId → Option (List (ZMod p))} {c : DenseExpr p}
    (h : denseBtCert singles c = false) : denseBtKeep singles domOf c = false := by
  unfold denseBtKeep
  rw [h, Bool.and_false]

/-- A single-variable constraint is never replaced (it fails the `≥ 2` guard), so it survives
    verbatim into the output — the box justification stands on the output's own satisfaction.
    Native mirror of `singleVar_mem_boxTautoReplace`. -/
theorem denseSingleVar_mem_boxTautoReplace (d : DenseConstraintSystem p)
    (domOf : VarId → Option (List (ZMod p))) (c : DenseExpr p)
    (hc : c ∈ d.algebraicConstraints) (hs : (c.vars.eraseDups.length == 1) = true) :
    c ∈ (d.boxTautoReplaceWith (denseSingleVarCs d.algebraicConstraints)
      domOf).algebraicConstraints := by
  have hcf : denseBtCert (denseSingleVarCs d.algebraicConstraints) c = false := by
    unfold denseBtCert
    have h1 : ¬ (2 ≤ c.vars.eraseDups.length) := by
      have := of_decide_eq_true hs
      omega
    simp [h1]
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  rw [denseBtKeep_of_cert_false hcf]
  simp

/-- **Native box-tautology replacement correctness.** Every replaced constraint is a tautology over
    its variables' finite-domain box, justified from the (never-replaced) single-variable
    constraints, so the map preserves satisfaction on the same environment and leaves bus
    effects/admissibility untouched. Native mirror of `ConstraintSystem.boxTautoReplace_correct`
    for an arbitrary domain oracle. -/
theorem DenseConstraintSystem.boxTautoReplace_denseCorrect [Fact p.Prime]
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (isInput : VarId → Bool)
    (domOf : VarId → Option (List (ZMod p))) :
    DensePassCorrect isInput d
      (d.boxTautoReplaceWith (denseSingleVarCs d.algebraicConstraints) domOf) [] bs := by
  -- Every constraint whose certificate holds is zero under any assignment satisfying the output.
  have hzero : ∀ denv, (d.boxTautoReplaceWith (denseSingleVarCs d.algebraicConstraints)
      domOf).satisfies bs denv →
      ∀ c ∈ d.algebraicConstraints,
        denseBtCert (denseSingleVarCs d.algebraicConstraints) c = true → c.eval denv = 0 := by
    intro denv hsat c _hc hcert
    unfold denseBtCert at hcert
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcert
    obtain ⟨_h2, ⟨⟨hcover, _hcap⟩, hall⟩⟩ := hcert
    have hcover' := of_decide_eq_true hcover
    have hdom : ∀ c' ∈ denseSingleVarCs d.algebraicConstraints, c'.eval denv = 0 := by
      intro c' hc'
      have hmem := List.mem_of_mem_filter hc'
      have hsingle : (c'.vars.eraseDups.length == 1) = true := by
        have h := (List.mem_filter.1 hc').2
        rwa [HashedDedup.hashedEraseDups_eq] at h
      exact hsat.1 c' (denseSingleVar_mem_boxTautoReplace d domOf c' hmem hsingle)
    have hmemdoms : ∀ vd ∈ c.vars.eraseDups.filterMap (fun v =>
        (denseFindDomainAlg (denseSingleVarCs d.algebraicConstraints) v).map (fun dm => (v, dm))),
        denv vd.1 ∈ vd.2 := by
      intro vd hvd
      obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
      cases hfd : denseFindDomainAlg (denseSingleVarCs d.algebraicConstraints) v with
      | none => rw [hfd] at hvd'; simp at hvd'
      | some dm =>
          rw [hfd] at hvd'
          simp only [Option.map_some, Option.some.injEq] at hvd'
          obtain rfl := hvd'.symm
          exact denseFindDomainAlg_sound denv (denseSingleVarCs d.algebraicConstraints) v dm hfd hdom
    have hpt := mem_denseAssignments (c.vars.eraseDups.filterMap (fun v =>
      (denseFindDomainAlg (denseSingleVarCs d.algebraicConstraints) v).map (fun dm => (v, dm))))
      denv hmemdoms
    have hptz := of_decide_eq_true (List.all_eq_true.mp hall _ hpt)
    have hagree : c.eval (denseEnvOfFast ((c.vars.eraseDups.filterMap (fun v =>
        (denseFindDomainAlg (denseSingleVarCs d.algebraicConstraints) v).map
          (fun dm => (v, dm)))).map (fun vd => (vd.1, denv vd.1)))) = c.eval denv := by
      refine DenseExpr.eval_congr c _ denv (fun v hv => ?_)
      refine denseEnvOfFast_map _ denv v ?_
      rw [show ((c.vars.eraseDups.filterMap (fun v =>
        (denseFindDomainAlg (denseSingleVarCs d.algebraicConstraints) v).map
          (fun dm => (v, dm)))).map Prod.fst) = c.vars.eraseDups from hcover']
      exact List.mem_eraseDups.2 hv
    rw [← hagree]; exact hptz
  -- Satisfaction equivalence on the SAME environment.
  have hiff : ∀ denv, (d.boxTautoReplaceWith (denseSingleVarCs d.algebraicConstraints)
      domOf).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    constructor
    · intro hsat
      refine ⟨fun c hc => ?_, hsat.2⟩
      by_cases hcond : denseBtKeep (denseSingleVarCs d.algebraicConstraints) domOf c = true
      · exact hzero denv hsat c hc (denseBtKeep_cert hcond)
      · have h0 := hsat.1 _ (List.mem_map.2 ⟨c, hc, rfl⟩)
        rw [if_neg hcond] at h0
        exact h0
    · intro hsat
      refine ⟨fun c' hc' => ?_, hsat.2⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      by_cases hcond : denseBtKeep (denseSingleVarCs d.algebraicConstraints) domOf c = true
      · rw [if_pos hcond]; rfl
      · rw [if_neg hcond]; exact hsat.1 c hc
  refine DensePassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  · -- soundness (bus interactions identical ⇒ side effects equal)
    intro denv hsat
    exact ⟨denv, (hiff denv).1 hsat, BusState.equiv_refl _⟩
  · -- invariant preservation
    intro hgi denv hsat bi hbi
    exact hgi denv ((hiff denv).1 hsat) bi hbi
  · -- output occurrences are input occurrences (const 0 has none; bus untouched)
    intro i hi
    simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi
    rcases hi with ⟨c', hc', hic⟩ | ⟨bi, hbi, hib⟩
    · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hc'
      by_cases hcond : denseBtKeep (denseSingleVarCs d.algebraicConstraints) domOf c = true
      · rw [if_pos hcond] at hic; simp [DenseExpr.vars] at hic
      · rw [if_neg hcond] at hic
        exact DenseConstraintSystem.mem_occ_of_constraint hcm hic
    · exact DenseConstraintSystem.mem_occ_of_bi hbi hib
  · -- completeness (same env; admissibility/side effects unchanged)
    intro denv hadm hsat
    exact ⟨(hiff denv).2 hsat, hadm, BusState.equiv_refl _⟩

/-- Coverage is preserved: replaced constraints are `const 0` (no variables) or original (covered);
    bus interactions unchanged. -/
theorem DenseConstraintSystem.boxTautoReplaceWith_covered {reg : VarRegistry}
    {d : DenseConstraintSystem p} (singles : List (DenseExpr p))
    (domOf : VarId → Option (List (ZMod p))) (hc : d.CoveredBy reg) :
    (d.boxTautoReplaceWith singles domOf).CoveredBy reg := by
  refine ⟨fun e he => ?_, fun bi hbi => hc.2 bi hbi⟩
  simp only [DenseConstraintSystem.boxTautoReplaceWith] at he
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 he
  by_cases hcond : denseBtKeep singles domOf c = true
  · rw [if_pos hcond]; intro i hi; simp [DenseExpr.vars] at hi
  · rw [if_neg hcond]; exact hc.1 c hcm

/-- The part-B transform is covered. -/
theorem denseBoxTautoDropF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseBoxTautoDropF pw bs d).CoveredBy reg := by
  unfold denseBoxTautoDropF
  split_ifs with hp
  · exact DenseConstraintSystem.boxTautoReplaceWith_covered _ _ hcov
  · exact hcov

/-- The part-B transform is `DensePassCorrect` (native). -/
theorem denseBoxTautoDropF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (_hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseBoxTautoDropF pw bs d) [] bs := by
  unfold denseBoxTautoDropF
  split_ifs with hp
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    exact DenseConstraintSystem.boxTautoReplace_denseCorrect d bs reg.isInput _
  · exact dpcRefl reg.isInput d bs

/-- **The native dense box-tautology drop pass** (part B of the flagFold composite). Fact-free —
    the `ofNative` transform ignores `facts`. Ready for S5 chain assembly. -/
def denseBoxTautoDropPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofNative (fun bs _ d => denseBoxTautoDropF pw bs d) (fun _ _ _ => [])
    (fun reg bs _ d hcov => denseBoxTautoDropF_covered pw reg bs d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d hcov => denseBoxTautoDropF_correct pw reg bs d hcov)

/-! ## Part C: pointwise-duplicate stateless-check removal -/

/-- **Joint-box agreement soundness** (mirrors `boxAgree_sound`): two expressions agreeing at every
    point of their offset variables' proven finite-domain box agree on every assignment zeroing the
    single-variable constraints. -/
theorem denseBoxAgree_sound [Fact p.Prime] (singles : List (DenseExpr p)) (R R' : DenseExpr p)
    (h : denseBoxAgree singles R R' = true) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval denv = 0) : R.eval denv = R'.eval denv := by
  unfold denseBoxAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hcover, _hcap⟩, hall⟩ := h
  have hmemdoms : ∀ vd ∈ (R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (denseFindDomainAlg singles v).map (fun dm => (v, dm))), denv vd.1 ∈ vd.2 := by
    intro vd hvd
    obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
    cases hfd : denseFindDomainAlg singles v with
    | none => rw [hfd] at hvd'; simp at hvd'
    | some dm =>
        rw [hfd] at hvd'
        simp only [Option.map_some, Option.some.injEq] at hvd'
        obtain rfl := hvd'.symm
        exact denseFindDomainAlg_sound denv singles v dm hfd hdom
  have hpt := mem_denseAssignments ((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
    (denseFindDomainAlg singles v).map (fun dm => (v, dm)))) denv hmemdoms
  have hagree : ∀ v, v ∈ (R.vars ++ R'.vars).eraseDups →
      denseEnvOfFast (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
        (denseFindDomainAlg singles v).map (fun dm => (v, dm)))).map
          (fun vd => (vd.1, denv vd.1))) v = denv v := by
    intro v hv
    refine denseEnvOfFast_map _ denv v ?_
    rw [show (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (denseFindDomainAlg singles v).map (fun dm => (v, dm)))).map Prod.fst)
      = (R.vars ++ R'.vars).eraseDups from hcover]
    exact hv
  have hRR := of_decide_eq_true (List.all_eq_true.mp hall _ hpt)
  have hRa : R.eval (denseEnvOfFast (((R.vars ++ R'.vars).eraseDups.filterMap
      (fun v => (denseFindDomainAlg singles v).map (fun dm => (v, dm)))).map
        (fun vd => (vd.1, denv vd.1)))) = R.eval denv :=
    DenseExpr.eval_congr R _ denv (fun v hv =>
      hagree v (List.mem_eraseDups.2 (List.mem_append_left _ hv)))
  have hRa' : R'.eval (denseEnvOfFast (((R.vars ++ R'.vars).eraseDups.filterMap
      (fun v => (denseFindDomainAlg singles v).map (fun dm => (v, dm)))).map
        (fun vd => (vd.1, denv vd.1)))) = R'.eval denv :=
    DenseExpr.eval_congr R' _ denv (fun v hv =>
      hagree v (List.mem_eraseDups.2 (List.mem_append_right _ hv)))
  rw [← hRa, ← hRa', hRR]

/-- **Slot-pair certificate soundness** (mirrors `slotEqCert_sound`): syntactically equal, or the
    same-carrier same-coefficient decomposition whose offsets agree on the box. -/
theorem denseSlotEqCert_sound [Fact p.Prime] (singles : List (DenseExpr p)) (e e' : DenseExpr p)
    (h : denseSlotEqCert singles e e' = true) (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval denv = 0) : e.eval denv = e'.eval denv := by
  unfold denseSlotEqCert at h
  rw [Bool.or_eq_true] at h
  rcases h with heq | hany
  · rw [eq_of_beq heq]
  · obtain ⟨x, _hx, hx⟩ := List.any_eq_true.1 hany
    rw [Bool.and_eq_true] at hx
    obtain ⟨_hm, hx⟩ := hx
    cases hsX : e.splitAt x with
    | none => rw [hsX] at hx; simp at hx
    | some kR =>
        obtain ⟨k, R⟩ := kR
        cases hsY : e'.splitAt x with
        | none => rw [hsX, hsY] at hx; simp at hx
        | some kR' =>
            obtain ⟨k2, R'⟩ := kR'
            simp only [hsX, hsY, Bool.and_eq_true] at hx
            obtain ⟨hk2, hba⟩ := hx
            rw [DenseExpr.splitAt_eval x e k R hsX denv,
                DenseExpr.splitAt_eval x e' k2 R' hsY denv, eq_of_beq hk2,
                denseBoxAgree_sound singles R R' hba denv hdom]

/-- **Full-message certificate soundness** (mirrors `msgEqCert_sound`): same bus, same constant
    multiplicity, pointwise-equal payloads ⇒ the two interactions evaluate to the same message. -/
theorem denseMsgEqCert_sound [Fact p.Prime] (singles : List (DenseExpr p))
    (bi bi' : BusInteraction (DenseExpr p)) (h : denseMsgEqCert singles bi bi' = true)
    (denv : VarId → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval denv = 0) : denseBIEval bi denv = denseBIEval bi' denv := by
  unfold denseMsgEqCert at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hbus, hmult⟩, hlen⟩, hslots⟩ := h
  have hmm : bi.multiplicity.eval denv = bi'.multiplicity.eval denv := by
    cases hm : bi.multiplicity.constValue? with
    | none => rw [hm] at hmult; simp at hmult
    | some m =>
        cases hm' : bi'.multiplicity.constValue? with
        | none => rw [hm, hm'] at hmult; simp at hmult
        | some m' =>
            rw [hm, hm'] at hmult
            rw [bi.multiplicity.constValue?_sound m hm denv,
                bi'.multiplicity.constValue?_sound m' hm' denv, eq_of_beq hmult]
  have hpay : bi.payload.map (fun e => e.eval denv)
      = bi'.payload.map (fun e => e.eval denv) := by
    have hlen' : bi.payload.length = bi'.payload.length := by simpa using hlen
    refine List.ext_getElem (by simpa) (fun i h1 h2 => ?_)
    have hi1 : i < bi.payload.length := by simpa using h1
    have hi2 : i < bi'.payload.length := by simpa using h2
    have hz : (bi.payload[i]'hi1, bi'.payload[i]'hi2) ∈ bi.payload.zip bi'.payload := by
      have hzi : (bi.payload.zip bi'.payload)[i]'(by rw [List.length_zip]; omega)
          = (bi.payload[i]'hi1, bi'.payload[i]'hi2) := by
        simp [List.getElem_zip]
      rw [← hzi]
      exact List.getElem_mem _
    have hcert := List.all_eq_true.mp hslots _ hz
    simp only [List.getElem_map]
    exact denseSlotEqCert_sound singles _ _ hcert denv hdom
  show denseBIEval bi denv = denseBIEval bi' denv
  unfold denseBIEval
  rw [eq_of_beq hbus, hmm, hpay]

/-- A first-of-class interaction is always kept — the depth-1 justification for `densePdKeep`.
    Native mirror of `pdFirst_keep`. -/
theorem densePdFirst_keep (bs : BusSemantics p) (singles : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (b : BusInteraction (DenseExpr p))
    (h : densePdFirst bs singles bis b = true) : densePdKeep bs singles bis b = true := by
  unfold densePdKeep
  rw [Bool.or_eq_true]
  right
  unfold densePdFirst at h
  cases hidx : bis.findIdx? (fun x => x == b) with
  | none => simp
  | some i =>
      rw [hidx] at h
      simp only
      rw [Bool.not_eq_true']
      by_contra hany
      have hany' : ((bis.take i).any (fun b' => !bs.isStateful b'.busId
          && denseMsgEqCert singles b' b && densePdFirst bs singles bis b')) = true := by
        by_cases hh : ((bis.take i).any (fun b' => !bs.isStateful b'.busId
            && denseMsgEqCert singles b' b && densePdFirst bs singles bis b')) = true
        · exact hh
        · exact absurd (by simpa using hh) hany
      obtain ⟨b'', hb''mem, hb''⟩ := List.any_eq_true.1 hany'
      rw [Bool.and_eq_true, Bool.and_eq_true] at hb''
      obtain ⟨⟨hnst, hcert⟩, _⟩ := hb''
      have hall := List.all_eq_true.mp h b'' hb''mem
      rw [Bool.or_eq_true] at hall
      rcases hall with hst | hnc
      · rw [Bool.not_eq_true'] at hnst
        rw [hnst] at hst
        exact absurd hst (by simp)
      · rw [Bool.not_eq_true'] at hnc
        rw [hcert] at hnc
        exact absurd hnc (by simp)

/-- Filtered bus interactions carry only input occurrences. Native mirror of
    `filterBus_vars_subset`. -/
theorem DenseConstraintSystem.filterBus_occ_subset (d : DenseConstraintSystem p)
    (keep : BusInteraction (DenseExpr p) → Bool) :
    ∀ i ∈ (d.filterBus keep).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.filterBus, List.mem_append,
    List.mem_flatMap] at hi ⊢
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · exact Or.inl ⟨c, hc, hic⟩
  · exact Or.inr ⟨bi, List.mem_of_mem_filter hbi, hib⟩

/-- **Native "drop entailed stateless interactions" correctness.** Dropping bus interactions that
    are (a) stateless and (b) accepted under every assignment satisfying the FILTERED system is
    equivalence- and invariant-preserving. Native mirror of
    `ConstraintSystem.filterBusEntailed_correct` over `VarId → ZMod p`. -/
theorem DensePassCorrect.denseFilterBusEntailed (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (isInput : VarId → Bool) (keep : BusInteraction (DenseExpr p) → Bool)
    (hstateless : ∀ bi ∈ d.busInteractions, keep bi = false → bs.isStateful bi.busId = false)
    (hok : ∀ bi ∈ d.busInteractions, keep bi = false → ∀ denv,
      (d.filterBus keep).satisfies bs denv →
      (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    DensePassCorrect isInput d (d.filterBus keep) [] bs := by
  have hiff : ∀ denv, (d.filterBus keep).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    simp only [DenseConstraintSystem.satisfies]
    constructor
    · intro hsat
      obtain ⟨hc, hb⟩ := hsat
      refine ⟨hc, fun bi hbimem => ?_⟩
      by_cases hk : keep bi = true
      · exact hb bi (List.mem_filter.2 ⟨hbimem, hk⟩)
      · intro hm
        exact hok bi hbimem (by simpa using hk) denv ⟨hc, hb⟩ hm
    · rintro ⟨hc, hb⟩
      exact ⟨hc, fun bi hbimem => hb bi (List.mem_of_mem_filter hbimem)⟩
  have hfilter : ∀ (bis : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ bis, keep bi = false → bs.isStateful bi.busId = false) →
      (bis.filter keep).filter (fun bi => bs.isStateful bi.busId)
        = bis.filter (fun bi => bs.isStateful bi.busId) := by
    intro bis
    induction bis with
    | nil => intro _; rfl
    | cons bi rest ih =>
        intro hall
        have hrest := ih (fun b hb hkf => hall b (List.mem_cons_of_mem _ hb) hkf)
        by_cases hk : keep bi = true
        · rw [List.filter_cons_of_pos hk]
          by_cases hst : bs.isStateful bi.busId = true
          · rw [List.filter_cons_of_pos (by simpa using hst),
                List.filter_cons_of_pos (by simpa using hst), hrest]
          · rw [List.filter_cons_of_neg (by simpa using hst),
                List.filter_cons_of_neg (by simpa using hst), hrest]
        · have hst : bs.isStateful bi.busId = false :=
            hall bi (List.mem_cons_self ..) (by simpa using hk)
          rw [List.filter_cons_of_neg hk,
              List.filter_cons_of_neg (by simp [hst]), hrest]
  have hside : ∀ denv, (d.filterBus keep).sideEffects bs denv = d.sideEffects bs denv := by
    intro denv
    simp only [DenseConstraintSystem.sideEffects, DenseConstraintSystem.filterBus]
    rw [hfilter d.busInteractions hstateless]
  have hadmfilter : ∀ (denv : VarId → ZMod p) (bis : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ bis, keep bi = false → bs.isStateful bi.busId = false) →
      ((bis.filter keep).map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
        = (bis.map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
    intro denv bis
    induction bis with
    | nil => intro _; rfl
    | cons bi rest ih =>
        intro hall
        have hrest := ih (fun b hb hkf => hall b (List.mem_cons_of_mem _ hb) hkf)
        by_cases hk : keep bi = true
        · rw [List.filter_cons_of_pos hk]
          simp only [List.map_cons, List.filter_cons, hrest]
        · have hbusId : (denseBIEval bi denv).busId = bi.busId := rfl
          have hst : bs.isStateful bi.busId = false :=
            hall bi (List.mem_cons_self ..) (by simpa using hk)
          have hPfalse : (decide ((denseBIEval bi denv).multiplicity ≠ 0)
              && bs.isStateful (denseBIEval bi denv).busId) = false := by
            rw [hbusId, hst, Bool.and_false]
          rw [List.filter_cons_of_neg (by simpa using hk), List.map_cons]
          simp only [List.filter_cons, hPfalse, Bool.false_eq_true, if_false]
          exact hrest
  have hadm : ∀ denv, (d.filterBus keep).admissible bs denv ↔ d.admissible bs denv := by
    intro denv
    unfold DenseConstraintSystem.admissible
    simp only [DenseConstraintSystem.filterBus]
    rw [hadmfilter denv d.busInteractions hstateless]
  refine DensePassCorrect.ofEnvEq ?_ ?_ (d.filterBus_occ_subset keep) ?_
  · intro denv hsat
    exact ⟨denv, (hiff denv).1 hsat, by rw [hside denv]; exact BusState.equiv_refl _⟩
  · intro hinv denv hsat bi hbi
    have hbimem : bi ∈ d.busInteractions :=
      List.mem_of_mem_filter (show bi ∈ d.busInteractions.filter keep from hbi)
    exact hinv denv ((hiff denv).1 hsat) bi hbimem
  · intro denv hadmd hsat
    exact ⟨(hiff denv).2 hsat, (hadm denv).2 hadmd, by rw [hside denv]; exact BusState.equiv_refl _⟩

/-- **Native pointwise-duplicate drop correctness.** Stated over an arbitrary prefilter `fast`: a
    drop requires `densePdKeep … = false` (the certified condition), and keeping more is always
    sound. The certified twin justifying a drop is provably kept (`densePdFirst_keep`) and evaluates
    equally (`denseMsgEqCert_sound`). Native mirror of `ConstraintSystem.pointwiseDupDrop_correct`. -/
theorem DensePassCorrect.densePointwiseDupDrop [Fact p.Prime]
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (isInput : VarId → Bool)
    (fast : BusInteraction (DenseExpr p) → Bool) :
    DensePassCorrect isInput d
      (d.filterBus (fun bi => fast bi
        || densePdKeep bs (denseSingleVarCs d.algebraicConstraints) d.busInteractions bi)) [] bs := by
  refine DensePassCorrect.denseFilterBusEntailed d bs isInput _ ?_ ?_
  · intro bi _ hkf
    rw [Bool.or_eq_false_iff] at hkf
    have hkf' := hkf.2
    unfold densePdKeep at hkf'
    rw [Bool.or_eq_false_iff] at hkf'
    simpa using hkf'.1
  · intro bi hbimem hkf denv hsat hm
    rw [Bool.or_eq_false_iff] at hkf
    have hkf' := hkf.2
    unfold densePdKeep at hkf'
    rw [Bool.or_eq_false_iff] at hkf'
    obtain ⟨_hst, hmatch⟩ := hkf'
    cases hidx : d.busInteractions.findIdx? (fun x => x == bi) with
    | none => rw [hidx] at hmatch; simp at hmatch
    | some i =>
        rw [hidx] at hmatch
        simp only [Bool.not_eq_false'] at hmatch
        obtain ⟨b, hbmem, hb⟩ := List.any_eq_true.1 hmatch
        rw [Bool.and_eq_true, Bool.and_eq_true] at hb
        obtain ⟨⟨hnst, hcert⟩, hfirst⟩ := hb
        have hbcs : b ∈ d.busInteractions := List.mem_of_mem_take hbmem
        have hbkeep : densePdKeep bs (denseSingleVarCs d.algebraicConstraints)
            d.busInteractions b = true :=
          densePdFirst_keep bs (denseSingleVarCs d.algebraicConstraints) d.busInteractions b hfirst
        have hbout : b ∈ (d.filterBus (fun bi => fast bi
            || densePdKeep bs (denseSingleVarCs d.algebraicConstraints)
              d.busInteractions bi)).busInteractions :=
          List.mem_filter.2 ⟨hbcs, by simp [hbkeep]⟩
        have hdom : ∀ c ∈ denseSingleVarCs d.algebraicConstraints, c.eval denv = 0 := by
          intro c hc
          exact hsat.1 c (List.mem_of_mem_filter hc)
        have heq : denseBIEval b denv = denseBIEval bi denv :=
          denseMsgEqCert_sound (denseSingleVarCs d.algebraicConstraints) b bi hcert denv hdom
        have hob := hsat.2 b hbout
        rw [heq] at hob
        exact hob hm

/-- The part-C transform is covered (bus filter keeps a subset; constraints untouched). -/
theorem densePointwiseDupDropF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (densePointwiseDupDropF pw bs d).CoveredBy reg := by
  unfold densePointwiseDupDropF
  split_ifs with hp
  · exact DenseConstraintSystem.filterBus_covered hcov
  · exact hcov

/-- The part-C transform is `DensePassCorrect` (native). -/
theorem densePointwiseDupDropF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (_hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (densePointwiseDupDropF pw bs d) [] bs := by
  unfold densePointwiseDupDropF
  split_ifs with hp
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    exact DensePassCorrect.densePointwiseDupDrop d bs reg.isInput
      (densePdFastKeep (densePdDropSet bs (denseSingleVarCs d.algebraicConstraints)
        d.busInteractions))
  · exact dpcRefl reg.isInput d bs

/-- **The native dense pointwise-duplicate drop pass** (part C of the flagFold composite). Fact-free
    — the `ofNative` transform ignores `facts`. Ready for S5 chain assembly. -/
def densePointwiseDupDropPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofNative (fun bs _ d => densePointwiseDupDropF pw bs d) (fun _ _ _ => [])
    (fun reg bs _ d hcov => densePointwiseDupDropF_covered pw reg bs d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d hcov => densePointwiseDupDropF_correct pw reg bs d hcov)

end ApcOptimizer.Dense
