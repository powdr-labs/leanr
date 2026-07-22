import ApcOptimizer.Implementation.OptimizerPasses.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Entailed-check rewriting: correctness skeleton and pass builders

The reusable `DensePassCorrect` results every "append entailed constraints (and drop the
now-entailed checks)" pass instantiates:

- `DensePassCorrect.denseAddConstraints` / `DensePassCorrect.denseFilterBusEntailed` — the two
  primitive steps;
- `DenseVerifiedPassW.ofAddConstraints` — an append-only pass from an emitted-constraint list
  and its containment/entailment obligations;
- `DenseCheckRule` / `DenseVerifiedPassW.ofCheckRules` — an append-and-drop pass from
  recognizers whose acceptance is exactly the vanishing of the emitted constraint. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Adding constraints that every admissible satisfying assignment already fulfils (and introduce no
    new occurring variable) is `DensePassCorrect`; reusable by every "append entailed equalities"
    pass. -/
theorem DensePassCorrect.denseAddConstraints {isInput : VarId → Bool} (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (new : List (DenseExpr p))
    (hnv : ∀ c ∈ new, ∀ z ∈ c.vars, z ∈ d.occ)
    (H : ∀ denv, d.admissible bs denv → d.satisfies bs denv → ∀ c ∈ new, c.eval denv = 0) :
    DensePassCorrect isInput d
      { d with algebraicConstraints := d.algebraicConstraints ++ new } [] bs := by
  set out : DenseConstraintSystem p :=
    { d with algebraicConstraints := d.algebraicConstraints ++ new } with hout
  have hfwd : ∀ denv, out.satisfies bs denv → d.satisfies bs denv := by
    rintro denv ⟨hc, hb⟩
    exact ⟨fun c hcm => hc c (List.mem_append_left _ hcm), hb⟩
  have hoccsub : ∀ i ∈ out.occ, i ∈ d.occ := by
    intro i hi
    have hi2 : i ∈ (d.algebraicConstraints ++ new).flatMap DenseExpr.vars
        ++ d.busInteractions.flatMap denseBIVars := hi
    rw [List.mem_append, List.mem_flatMap, List.mem_flatMap] at hi2
    rcases hi2 with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
    · rcases List.mem_append.1 hc with h | h
      · exact DenseConstraintSystem.mem_occ_of_constraint h hic
      · exact hnv c h i hic
    · exact DenseConstraintSystem.mem_occ_of_bi hbi hib
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- soundness
    intro denv hsat
    exact ⟨denv, hfwd denv hsat, BusState.equiv_refl _⟩
  · -- invariant preservation
    intro hgi denv hsat bi hbi
    exact hgi denv (hfwd denv hsat) bi hbi
  · -- no new powdr-ID column
    intro i hi _; exact hoccsub i hi
  · -- completeness, witness `denv`
    intro denv hadm hsat
    have hout_sat : out.satisfies bs denv := by
      refine ⟨fun c hcm => ?_, hsat.2⟩
      rcases List.mem_append.1 hcm with h | h
      · exact hsat.1 c h
      · exact H denv hadm hsat c h
    refine ⟨denv, hout_sat, hadm, BusState.equiv_refl _, fun _ _ => rfl, ?_⟩
    intro inputVarIds _ i hi _
    show i ∈ d.occ ∧ denv i = denv i
    exact ⟨hoccsub i hi, rfl⟩

/-- Filtered bus interactions carry only input occurrences. -/
theorem DenseConstraintSystem.filterBus_occ_subset (d : DenseConstraintSystem p)
    (keep : BusInteraction (DenseExpr p) → Bool) :
    ∀ i ∈ (d.filterBus keep).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.filterBus, List.mem_append,
    List.mem_flatMap] at hi ⊢
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · exact Or.inl ⟨c, hc, hic⟩
  · exact Or.inr ⟨bi, List.mem_of_mem_filter hbi, hib⟩

/-- Dropping bus interactions that are (a) stateless and (b) accepted under every assignment
    satisfying the filtered system is equivalence- and invariant-preserving. -/
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

/-! ## The append-only pass builder -/

/-- Build a pass appending system-entailed constraints: the obligations are variable containment
    (`hvars`) and entailment on admissible satisfying assignments (`hsound`). -/
def DenseVerifiedPassW.ofAddConstraints
    (news : (bs : BusSemantics p) → BusFacts p bs → DenseConstraintSystem p → List (DenseExpr p))
    (hvars : ∀ (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p),
      ∀ c ∈ news bs facts d, ∀ z ∈ c.vars, z ∈ d.occ)
    (hsound : ∀ (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
      (denv : VarId → ZMod p), d.admissible bs denv → d.satisfies bs denv →
      ∀ c ∈ news bs facts d, c.eval denv = 0) :
    DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d =>
      { d with algebraicConstraints := d.algebraicConstraints ++ news bs facts d })
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => by
      refine ⟨fun e he => ?_, hcov.2⟩
      rcases List.mem_append.1 he with h | h
      · exact hcov.1 e h
      · intro i hi
        exact DenseConstraintSystem.occ_valid hcov i (hvars bs facts d e h i hi))
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => DensePassCorrect.denseAddConstraints d bs (news bs facts d)
      (hvars bs facts d) (hsound bs facts d))

/-! ## Check-rule passes -/

/-- A stateless-check recognizer bundled with its soundness: a recognized interaction always
    fires (unit multiplicity), lives on a stateless bus, emits a constraint over its own
    variables, and is accepted exactly when that constraint vanishes. -/
structure DenseCheckRule (p : ℕ) (bs : BusSemantics p) where
  recognize : BusInteraction (DenseExpr p) → Option (DenseExpr p)
  multOne : ∀ bi e, recognize bi = some e → bi.multiplicity = DenseExpr.const 1
  stateless : ∀ bi e, recognize bi = some e → bs.isStateful bi.busId = false
  vars : ∀ bi e, recognize bi = some e → ∀ z ∈ e.vars, z ∈ denseBIVars bi
  violates_iff : ∀ bi e, recognize bi = some e → ∀ denv : VarId → ZMod p,
    (bs.violatesConstraint (denseBIEval bi denv) = false ↔ e.eval denv = 0)

/-- Every emitted constraint comes from some recognizer firing on some listed interaction. -/
theorem denseGroupEmit_mem {recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p))}
    {bis : List (BusInteraction (DenseExpr p))} {c : DenseExpr p}
    (hc : c ∈ denseGroupEmit recs bis) : ∃ r ∈ recs, ∃ bi ∈ bis, r bi = some c := by
  induction recs generalizing bis with
  | nil => simp [denseGroupEmit] at hc
  | cons r rest ih =>
    rw [denseGroupEmit] at hc
    rcases List.mem_append.1 hc with h | h
    · obtain ⟨bi, hbi, hr⟩ := List.mem_filterMap.1 h
      exact ⟨r, List.mem_cons_self .., bi, hbi, hr⟩
    · obtain ⟨r', hr', bi, hbi, hfire⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', bi, List.mem_of_mem_filter hbi, hfire⟩

/-- An interaction some recognizer matches contributes its first match to the emitted list. -/
theorem denseGroupEmit_first {recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p))}
    {bis : List (BusInteraction (DenseExpr p))} {bi : BusInteraction (DenseExpr p)}
    (hbi : bi ∈ bis) (hfire : recs.all (fun r => (r bi).isNone) = false) :
    ∃ r ∈ recs, ∃ e, r bi = some e ∧ e ∈ denseGroupEmit recs bis := by
  induction recs generalizing bis with
  | nil => simp at hfire
  | cons r rest ih =>
    rw [denseGroupEmit]
    cases hopt : r bi with
    | some e =>
      exact ⟨r, List.mem_cons_self .., e, hopt,
        List.mem_append_left _ (List.mem_filterMap.2 ⟨bi, hbi, hopt⟩)⟩
    | none =>
      have hrest : rest.all (fun r => (r bi).isNone) = false := by
        simpa [List.all_cons, hopt] using hfire
      have hbi' : bi ∈ bis.filter (fun b => (r b).isNone) :=
        List.mem_filter.2 ⟨hbi, by simp [hopt]⟩
      obtain ⟨r', hr', e, he, hmem⟩ := ih hbi' hrest
      exact ⟨r', List.mem_cons_of_mem _ hr', e, he, List.mem_append_right _ hmem⟩

theorem denseCheckRewriteF_covered {bs : BusSemantics p} (rules : List (DenseCheckRule p bs))
    (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseCheckRewriteF (rules.map (·.recognize)) d).CoveredBy reg := by
  refine DenseConstraintSystem.filterBus_covered ⟨fun e he => ?_, hcov.2⟩
  rcases List.mem_append.1 he with h | h
  · exact hcov.1 e h
  · obtain ⟨r, hr, bi, hbi, hfire⟩ := denseGroupEmit_mem h
    obtain ⟨rule, -, rfl⟩ := List.mem_map.1 hr
    intro i hi
    exact DenseConstraintSystem.occ_valid hcov i
      (DenseConstraintSystem.mem_occ_of_bi hbi (rule.vars bi e hfire i hi))

theorem denseCheckRewriteF_correct {bs : BusSemantics p} (rules : List (DenseCheckRule p bs))
    (isInput : VarId → Bool) (d : DenseConstraintSystem p) (h1ne : (1 : ZMod p) ≠ 0) :
    DensePassCorrect isInput d (denseCheckRewriteF (rules.map (·.recognize)) d) [] bs := by
  have hadd : DensePassCorrect isInput d
      { d with algebraicConstraints :=
          d.algebraicConstraints ++ denseGroupEmit (rules.map (·.recognize)) d.busInteractions }
      [] bs := by
    refine DensePassCorrect.denseAddConstraints d bs _ ?_ ?_
    · intro c hc z hz
      obtain ⟨r, hr, bi, hbi, hfire⟩ := denseGroupEmit_mem hc
      obtain ⟨rule, -, rfl⟩ := List.mem_map.1 hr
      exact DenseConstraintSystem.mem_occ_of_bi hbi (rule.vars bi c hfire z hz)
    · intro denv _ hsat c hc
      obtain ⟨r, hr, bi, hbi, hfire⟩ := denseGroupEmit_mem hc
      obtain ⟨rule, -, rfl⟩ := List.mem_map.1 hr
      have hmult : (denseBIEval bi denv).multiplicity ≠ 0 := by
        show bi.multiplicity.eval denv ≠ 0
        rw [rule.multOne bi c hfire]
        simpa using h1ne
      exact (rule.violates_iff bi c hfire denv).mp (hsat.2 bi hbi hmult)
  refine DensePassCorrect.trans hadd ?_
  refine DensePassCorrect.denseFilterBusEntailed _ bs isInput
    (fun bi => (rules.map (·.recognize)).all (fun r => (r bi).isNone)) ?_ ?_
  · intro bi hbimem hkf
    obtain ⟨r, hr, e, he, -⟩ := denseGroupEmit_first hbimem hkf
    obtain ⟨rule, -, rfl⟩ := List.mem_map.1 hr
    exact rule.stateless bi e he
  · intro bi hbimem hkf denv hsatf _
    obtain ⟨r, hr, e, he, hmem⟩ := denseGroupEmit_first hbimem hkf
    obtain ⟨rule, -, rfl⟩ := List.mem_map.1 hr
    exact (rule.violates_iff bi e he denv).mpr
      (hsatf.1 e (List.mem_append_right _ hmem))

/-- Build an append-and-drop pass from check rules (a function of the semantics and facts, so
    recognizers can consult `BusFacts` and prime witnesses); gated on `(1 : ZMod p) ≠ 0`. -/
def DenseVerifiedPassW.ofCheckRules
    (rules : (bs : BusSemantics p) → BusFacts p bs → List (DenseCheckRule p bs)) :
    DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d =>
      if (1 : ZMod p) ≠ 0 then denseCheckRewriteF ((rules bs facts).map (·.recognize)) d else d)
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => by
      dsimp only
      split
      · exact denseCheckRewriteF_covered (rules bs facts) reg d hcov
      · exact hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => by
      dsimp only
      split
      next h => exact denseCheckRewriteF_correct (rules bs facts) reg.isInput d h
      next => exact DensePassCorrect.refl reg.isInput d bs)

end ApcOptimizer.Dense
