import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.FlagFoldDropsProof

set_option autoImplicit false

/-! # Native soundness for the dense drop passes (Task 3, equivalence pile)

Native `DensePassCorrect` proofs — over `VarId → ZMod p` environments, with no dependency on the
reference `Variable` passes — for the three dense drop passes previously built by `ofTransform`:

* `denseTrivialConstraintDropPass` — drop algebraic constraints whose fold is literal `0`;
* `denseZeroMultBusDropPass` — drop bus interactions whose multiplicity folds to `0`;
* `denseTautoBusDropPass` — drop stateless interactions with an accepted constant message.

The runtime transforms are unchanged (they still live in `DropPasses.lean`); only the correctness
argument moves from "decode the dense filter to the spec filter, inherit the spec `PassCorrect`" to a
direct native argument, lifted once to the audited `Variable` spec by `DenseVerifiedPassW.of`.

The reusable core is `DensePassCorrect.denseFilterConstraintsEntailed` (native mirror of
`ConstraintSystem.filterConstraints_correct`) for constraint drops, and — for the two bus drops —
`DensePassCorrect.denseFilterBusEntailed` (already in `FlagFoldDropsProof.lean`, reused directly by
`tautoBus`) plus a fresh `DensePassCorrect.denseFilterBusZeroMult` (native mirror of
`ConstraintSystem.filterBus_correct`) whose net-multiplicity and admissibility invariance are proved
by `denseMultiplicitySum_filterBus` and the disjunctive `DenseConstraintSystem.admissible_filterBus`
(`multiplicity = 0 ∨ stateless`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Occurrence subset for `filterConstraints` -/

/-- Filtered algebraic constraints carry only input occurrences. Native mirror of
    `ConstraintSystem.filterConstraints_vars_subset` (companion to
    `FlagFoldDropsProof`'s `filterBus_occ_subset`). -/
theorem DenseConstraintSystem.filterConstraints_occ_subset (d : DenseConstraintSystem p)
    (keep : DenseExpr p → Bool) : ∀ i ∈ (d.filterConstraints keep).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.filterConstraints, List.mem_append,
    List.mem_flatMap] at hi ⊢
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · exact Or.inl ⟨c, List.mem_of_mem_filter hc, hic⟩
  · exact Or.inr ⟨bi, hbi, hib⟩

/-! ## Reusable core: dropping identically-zero constraints -/

/-- **Native trivial-constraint removal correctness.** Dropping algebraic constraints that are
    identically zero (under every dense assignment) is equivalence- and invariant-preserving; bus
    interactions are untouched so side effects and admissibility are literally unchanged. Native
    mirror of `ConstraintSystem.filterConstraints_correct` over `VarId → ZMod p`. -/
theorem DensePassCorrect.denseFilterConstraintsEntailed (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (isInput : VarId → Bool) (keep : DenseExpr p → Bool)
    (h : ∀ c ∈ d.algebraicConstraints, keep c = false → ∀ denv, c.eval denv = 0) :
    DensePassCorrect isInput d (d.filterConstraints keep) [] bs := by
  have hiff : ∀ denv, (d.filterConstraints keep).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    simp only [DenseConstraintSystem.satisfies, DenseConstraintSystem.filterConstraints]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨fun c hcmem => ?_, hb⟩
      by_cases hk : keep c = true
      · exact hc c (List.mem_filter.2 ⟨hcmem, hk⟩)
      · exact h c hcmem (by simpa using hk) denv
    · rintro ⟨hc, hb⟩
      exact ⟨fun c hcmem => hc c (List.mem_filter.1 hcmem).1, hb⟩
  have hside : ∀ denv, (d.filterConstraints keep).sideEffects bs denv = d.sideEffects bs denv :=
    fun _ => rfl
  refine DensePassCorrect.ofEnvEq ?_ ?_ (d.filterConstraints_occ_subset keep) ?_
  · intro denv hsat
    exact ⟨denv, (hiff denv).1 hsat, by rw [hside denv]; exact BusState.equiv_refl _⟩
  · intro hinv denv hsat bi hbi
    exact hinv denv ((hiff denv).1 hsat) bi hbi
  · intro denv hadmd hsat
    exact ⟨(hiff denv).2 hsat, hadmd, by rw [hside denv]; exact BusState.equiv_refl _⟩

/-- Native mirror of `Expression.isConstZero_sound`: the const-zero test is sound (only `const 0`
    passes it), so a passing dense expression evaluates to `0` under every assignment. -/
theorem DenseExpr.isConstZero_sound (e : DenseExpr p) (h : e.isConstZero = true)
    (denv : VarId → ZMod p) : e.eval denv = 0 := by
  cases e <;> simp_all [DenseExpr.isConstZero, DenseExpr.eval]

/-- **The native dense trivial-constraint drop pass.** Fact-free — the `of` transform ignores
    `facts`. Runtime transform unchanged from the `ofTransform` version in `DropPasses.lean`. -/
def denseTrivialConstraintDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => d.filterConstraints (fun c => !c.fold.isConstZero))
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov => DenseConstraintSystem.filterConstraints_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ =>
      DensePassCorrect.denseFilterConstraintsEntailed d bs reg.isInput
        (fun c => !c.fold.isConstZero) (by
          intro c _ hkf denv
          have hz : c.fold.isConstZero = true := by simpa using hkf
          rw [← c.fold_eval denv]
          exact DenseExpr.isConstZero_sound c.fold hz denv))

/-! ## Zero-multiplicity bus removal -/

/-- Net multiplicity is unchanged by dropping bus interactions whose evaluated multiplicity is `0`:
    such an interaction contributes `0` to every message's net multiplicity, so the two bus states
    are `≈`-equal. Native mirror of `multiplicitySum_filterBus`. -/
theorem denseMultiplicitySum_filterBus (bs : BusSemantics p) (denv : VarId → ZMod p)
    (keep : BusInteraction (DenseExpr p) → Bool) (message : BusMessage p)
    (bis : List (BusInteraction (DenseExpr p)))
    (h0 : ∀ bi ∈ bis, keep bi = false → (denseBIEval bi denv).multiplicity = 0) :
    multiplicitySum message
      ((bis.filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := denseBIEval bi denv; ((m.busId, m.payload), m.multiplicity)))
    = multiplicitySum message
      (((bis.filter keep).filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := denseBIEval bi denv; ((m.busId, m.payload), m.multiplicity))) := by
  induction bis with
  | nil => rfl
  | cons bi rest ih =>
      have hrest : ∀ b ∈ rest, keep b = false → (denseBIEval b denv).multiplicity = 0 :=
        fun b hb => h0 b (List.mem_cons_of_mem _ hb)
      by_cases hkeep : keep bi = true
      · by_cases hstate : bs.isStateful bi.busId = true
        · rw [List.filter_cons_of_pos (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_pos hkeep,
              List.filter_cons_of_pos (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate]
          simp only [List.map_cons, multiplicitySum, ih hrest]
        · rw [List.filter_cons_of_neg (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_pos hkeep,
              List.filter_cons_of_neg (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate]
          exact ih hrest
      · have hbi0 : (denseBIEval bi denv).multiplicity = 0 :=
          h0 bi (List.mem_cons_self ..) (by simpa using hkeep)
        by_cases hstate : bs.isStateful bi.busId = true
        · rw [List.filter_cons_of_pos (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_neg hkeep]
          simp only [List.map_cons, multiplicitySum, hbi0, ite_self, zero_add]
          exact ih hrest
        · rw [List.filter_cons_of_neg (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_neg hkeep]
          exact ih hrest

/-- Dropping interactions that are (under `denv`) either inactive (multiplicity `0`) or on a
    stateless bus preserves `admissible`: `admissible` only inspects the active *stateful* evaluated
    messages, which such a drop leaves unchanged. Native mirror of
    `ConstraintSystem.admissible_filterBus` (the disjunctive form used by both the zero-multiplicity
    and tautology drops). -/
theorem DenseConstraintSystem.admissible_filterBus (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (keep : BusInteraction (DenseExpr p) → Bool) (denv : VarId → ZMod p)
    (h : ∀ bi ∈ d.busInteractions, keep bi = false →
        (denseBIEval bi denv).multiplicity = 0 ∨ bs.isStateful bi.busId = false) :
    (d.filterBus keep).admissible bs denv ↔ d.admissible bs denv := by
  unfold DenseConstraintSystem.admissible
  simp only [DenseConstraintSystem.filterBus]
  have key : ∀ (L : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ L, keep bi = false →
        (denseBIEval bi denv).multiplicity = 0 ∨ bs.isStateful bi.busId = false) →
      ((L.filter keep).map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
        = (L.map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons bi rest ih =>
      intro hL
      have hrest := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
      by_cases hk : keep bi = true
      · rw [List.filter_cons_of_pos hk]
        simp only [List.map_cons, List.filter_cons, hrest]
      · have hbusId : (denseBIEval bi denv).busId = bi.busId := rfl
        have hPfalse : (decide ((denseBIEval bi denv).multiplicity ≠ 0)
            && bs.isStateful (denseBIEval bi denv).busId) = false := by
          rcases hL bi (List.mem_cons_self ..) (by simpa using hk) with hz | hst
          · simp [hz]
          · rw [hbusId, hst, Bool.and_false]
        rw [List.filter_cons_of_neg (by simpa using hk), List.map_cons]
        simp only [List.filter_cons, hPfalse, Bool.false_eq_true, if_false]
        exact hrest
  rw [key d.busInteractions h]

/-- **Native zero-multiplicity bus removal correctness.** Dropping bus interactions whose evaluated
    multiplicity is identically `0` is equivalence- and invariant-preserving: their
    `violatesConstraint` obligation is vacuous, and a `0`-multiplicity stateful entry adds `0` to
    every net multiplicity. Sound for arbitrary bus semantics — the spec's unused `(1 : ZMod p) ≠ 0`
    hypothesis is omitted. Native mirror of `ConstraintSystem.filterBus_correct`. -/
theorem DensePassCorrect.denseFilterBusZeroMult (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (isInput : VarId → Bool) (keep : BusInteraction (DenseExpr p) → Bool)
    (h : ∀ bi ∈ d.busInteractions, keep bi = false → ∀ denv,
      (denseBIEval bi denv).multiplicity = 0) :
    DensePassCorrect isInput d (d.filterBus keep) [] bs := by
  have hiff : ∀ denv, (d.filterBus keep).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    simp only [DenseConstraintSystem.satisfies, DenseConstraintSystem.filterBus]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨hc, fun bi hbimem => ?_⟩
      by_cases hk : keep bi = true
      · exact hb bi (List.mem_filter.2 ⟨hbimem, hk⟩)
      · intro hne; exact absurd (h bi hbimem (by simpa using hk) denv) hne
    · rintro ⟨hc, hb⟩
      exact ⟨hc, fun bi hbimem => hb bi (List.mem_filter.1 hbimem).1⟩
  have hside : ∀ denv, d.sideEffects bs denv ≈ (d.filterBus keep).sideEffects bs denv := by
    intro denv message
    simp only [DenseConstraintSystem.sideEffects, DenseConstraintSystem.filterBus]
    exact denseMultiplicitySum_filterBus bs denv keep message d.busInteractions
      (fun bi hbi hkf => h bi hbi hkf denv)
  refine DensePassCorrect.ofEnvEq ?_ ?_ (d.filterBus_occ_subset keep) ?_
  · intro denv hsat
    exact ⟨denv, (hiff denv).1 hsat, BusState.equiv_symm (hside denv)⟩
  · intro hinv denv hsat bi hbi
    have hbimem : bi ∈ d.busInteractions :=
      List.mem_of_mem_filter (show bi ∈ d.busInteractions.filter keep from hbi)
    exact hinv denv ((hiff denv).1 hsat) bi hbimem
  · intro denv hadmd hsat
    exact ⟨(hiff denv).2 hsat,
      (d.admissible_filterBus bs keep denv (fun bi hbi hkf => Or.inl (h bi hbi hkf denv))).2 hadmd,
      hside denv⟩

/-- **The native dense zero-multiplicity bus drop pass.** Keeps the runtime `ite` gate exactly as in
    `DropPasses.lean`: in the degenerate `1 = 0` ring the pass is the identity (`refl`), else it drops
    zero-multiplicity interactions. Fact-free. -/
def denseZeroMultBusDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d =>
      if (1 : ZMod p) = 0 then d
      else d.filterBus (fun bi => !bi.multiplicity.fold.isConstZero))
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov => by
      split_ifs with hp1
      · exact hcov
      · exact DenseConstraintSystem.filterBus_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => by
      split_ifs with hp1
      · exact DensePassCorrect.refl reg.isInput d bs
      · refine DensePassCorrect.denseFilterBusZeroMult d bs reg.isInput
          (fun bi => !bi.multiplicity.fold.isConstZero) ?_
        intro bi _ hkf denv
        have hz : bi.multiplicity.fold.isConstZero = true := by simpa using hkf
        show bi.multiplicity.eval denv = 0
        rw [← bi.multiplicity.fold_eval denv]
        exact DenseExpr.isConstZero_sound bi.multiplicity.fold hz denv)

/-! ## Tautology-lookup removal -/

/-- The constant value of a dense expression is its actual value under every assignment (the fold is
    a literal). Native mirror of `Expression.constValue?_sound` (file-local to avoid clashing with the
    `DomainBatchProof` copy). -/
private theorem denseConstValue?_sound (e : DenseExpr p) (c : ZMod p)
    (h : e.constValue? = some c) (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  unfold DenseExpr.constValue? at h
  cases hf : e.fold with
  | const n => rw [hf] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | var j => rw [hf] at h; simp at h
  | add a b => rw [hf] at h; simp at h
  | mul a b => rw [hf] at h; simp at h

/-- A dense payload's constant values are its actual values under every assignment. Native mirror of
    `constValues?_sound`. -/
theorem denseConstValues?_sound (es : List (DenseExpr p)) (vs : List (ZMod p))
    (h : denseConstValues? es = some vs) (denv : VarId → ZMod p) :
    es.map (fun e => e.eval denv) = vs := by
  induction es generalizing vs with
  | nil => simp only [denseConstValues?, Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    rw [denseConstValues?] at h
    cases hv : e.constValue? with
    | none => rw [hv] at h; exact absurd h (by simp)
    | some v =>
      cases hvs : denseConstValues? rest with
      | none => rw [hv, hvs] at h; exact absurd h (by simp)
      | some vs' =>
        rw [hv, hvs] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [denseConstValue?_sound e v hv denv, ih vs' hvs]

/-- A dense interaction's constant message equals its evaluated message under every assignment (the
    multiplicity and all payload entries fold to constants). Native mirror of
    `BusInteraction.constMessage?_sound`. -/
theorem denseConstMessage?_sound (bi : BusInteraction (DenseExpr p))
    (msg : BusInteraction (ZMod p)) (h : denseConstMessage? bi = some msg)
    (denv : VarId → ZMod p) : denseBIEval bi denv = msg := by
  unfold denseConstMessage? at h
  cases hm : bi.multiplicity.constValue? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
    cases hvs : denseConstValues? bi.payload with
    | none => rw [hm, hvs] at h; exact absurd h (by simp)
    | some vs =>
      rw [hm, hvs] at h
      simp only [Option.some.injEq] at h
      subst h
      simp [denseBIEval, denseConstValue?_sound bi.multiplicity m hm denv,
            denseConstValues?_sound bi.payload vs hvs denv]

/-- **The native dense tautology-lookup drop pass.** Dropping a stateless interaction whose constant
    message the bus accepts is sound under every assignment (the acceptance is unconditional — a
    strictly stronger fact than `denseFilterBusEntailed` needs). Fact-free. -/
def denseTautoBusDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs _ d => d.filterBus (fun bi => !denseIsTautoLookup bs bi))
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov => DenseConstraintSystem.filterBus_covered hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => by
      refine DensePassCorrect.denseFilterBusEntailed d bs reg.isInput
        (fun bi => !denseIsTautoLookup bs bi) ?_ ?_
      · intro bi _ hkf
        have htauto : denseIsTautoLookup bs bi = true := by simpa using hkf
        simp only [denseIsTautoLookup, Bool.and_eq_true] at htauto
        simpa using htauto.1
      · intro bi _ hkf denv _ _
        have htauto : denseIsTautoLookup bs bi = true := by simpa using hkf
        simp only [denseIsTautoLookup, Bool.and_eq_true] at htauto
        have hmsg := htauto.2
        cases hcm : denseConstMessage? bi with
        | none => rw [hcm] at hmsg; exact absurd hmsg (by simp)
        | some msg =>
          rw [hcm] at hmsg
          rw [denseConstMessage?_sound bi msg hcm denv]
          simpa using hmsg)

end ApcOptimizer.Dense
