import ApcOptimizer.Implementation.OptimizerPasses.Pass

set_option autoImplicit false

/-! # Dense correctness and the central lift bridge

Passes are proved correct over dense environments `VarId → ZMod p` and connected to the audited
`Variable`-level spec once, at the optimizer boundary. This module defines the dense semantics
(evaluation, satisfaction, admissibility, side effects, refinement), `DensePassCorrect` (the dense
analogue of `PassCorrect`, parameterised by `isInput : VarId → Bool`), the lift theorem
`DensePassCorrect.lift`, and the pass builders `DenseVerifiedPassW.of` / `.ofExtending`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense computation methods -/

def DenseComputationMethod.eval : DenseComputationMethod p → (VarId → ZMod p) → ZMod p
  | .const c, _ => c
  | .quotientOrZero num den, denv =>
      if den.eval denv = 0 then 0 else (den.eval denv)⁻¹ * num.eval denv
  | .ifEqZero cond thenM elseM, denv =>
      if cond.eval denv = 0 then thenM.eval denv else elseM.eval denv

def DenseComputationMethod.vars : DenseComputationMethod p → List VarId
  | .const _ => []
  | .quotientOrZero num den => num.vars ++ den.vars
  | .ifEqZero cond thenM elseM => cond.vars ++ thenM.vars ++ elseM.vars

/-- The dense computation method `dd` uses for `i`: the **last** one listed. -/
def DenseDerivations.methodFor : DenseDerivations p → VarId → Option (DenseComputationMethod p)
  | [], _ => none
  | (u, cm) :: rest, v =>
      (DenseDerivations.methodFor rest v).orElse (fun _ => if u = v then some cm else none)

/-! ## Dense semantics over `VarId → ZMod p` environments -/

def denseBIEval (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p) :
    BusInteraction (ZMod p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.eval denv,
    payload := bi.payload.map (fun e => e.eval denv) }

/-- Dense side effects: the stateful-bus messages sent. -/
def DenseConstraintSystem.sideEffects (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (denv : VarId → ZMod p) : BusState p :=
  d.busInteractions.filter (fun bi => bs.isStateful bi.busId)
    |>.map (fun bi =>
      let m := denseBIEval bi denv
      ((m.busId, m.payload), m.multiplicity))

/-- Dense satisfaction: all constraints vanish and every fired bus message is unconstrained. -/
def DenseConstraintSystem.satisfies (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (denv : VarId → ZMod p) : Prop :=
  (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) ∧
  (∀ bi ∈ d.busInteractions,
    let message := denseBIEval bi denv
    message.multiplicity ≠ 0 → bs.violatesConstraint message = false)

/-- Dense admissibility: the fired stateful-bus messages satisfy the bus admissibility predicate. -/
def DenseConstraintSystem.admissible (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (denv : VarId → ZMod p) : Prop :=
  bs.admissible ((d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
    (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))

/-- Every fired bus message on a satisfying assignment breaks no invariant. -/
def DenseConstraintSystem.guaranteesInvariants (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    Prop :=
  ∀ denv, d.satisfies bs denv → ∀ bi ∈ d.busInteractions,
    let message := denseBIEval bi denv
    message.multiplicity ≠ 0 → bs.breaksInvariant message = false

/-- Every satisfying assignment has a matching one for `other` with equivalent side effects. -/
def DenseConstraintSystem.implies (self other : DenseConstraintSystem p) (bs : BusSemantics p) :
    Prop :=
  ∀ denv, self.satisfies bs denv →
    ∃ denv', other.satisfies bs denv' ∧
      self.sideEffects bs denv ≈ other.sideEffects bs denv'

/-! ## `occ` membership helpers -/

theorem DenseConstraintSystem.mem_occ_of_constraint {d : DenseConstraintSystem p} {c : DenseExpr p}
    {i : VarId} (hc : c ∈ d.algebraicConstraints) (hi : i ∈ c.vars) : i ∈ d.occ := by
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨c, hc, hi⟩

theorem DenseConstraintSystem.mem_occ_of_bi {d : DenseConstraintSystem p}
    {bi : BusInteraction (DenseExpr p)} {i : VarId} (hbi : bi ∈ d.busInteractions)
    (hi : i ∈ denseBIVars bi) : i ∈ d.occ := by
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨bi, hbi, hi⟩

/-! ## Dense congruence: a semantics depends only on the variables that occur -/

/-- Dense expression evaluation depends only on the variables that occur. -/
private theorem denseExprEvalCongr (e : DenseExpr p) (denv1 denv2 : VarId → ZMod p)
    (h : ∀ i ∈ e.vars, denv1 i = denv2 i) : e.eval denv1 = e.eval denv2 := by
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

theorem denseBIEval_congr (bi : BusInteraction (DenseExpr p)) (denv1 denv2 : VarId → ZMod p)
    (h : ∀ i ∈ denseBIVars bi, denv1 i = denv2 i) : denseBIEval bi denv1 = denseBIEval bi denv2 := by
  have hmult : bi.multiplicity.eval denv1 = bi.multiplicity.eval denv2 :=
    denseExprEvalCongr bi.multiplicity denv1 denv2 (fun i hi => h i (by simp [denseBIVars, hi]))
  have hpay : bi.payload.map (fun e => e.eval denv1) = bi.payload.map (fun e => e.eval denv2) := by
    refine List.map_congr_left (fun e he => denseExprEvalCongr e denv1 denv2 (fun i hi => h i ?_))
    simp only [denseBIVars, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hi⟩
  simp only [denseBIEval, hmult, hpay]

theorem DenseConstraintSystem.satisfies_congr {d : DenseConstraintSystem p} {bs : BusSemantics p}
    {denv1 denv2 : VarId → ZMod p} (h : ∀ i ∈ d.occ, denv1 i = denv2 i) :
    d.satisfies bs denv1 ↔ d.satisfies bs denv2 := by
  have imp : ∀ e1 e2 : VarId → ZMod p, (∀ i ∈ d.occ, e1 i = e2 i) →
      d.satisfies bs e1 → d.satisfies bs e2 := by
    intro e1 e2 hh hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · rw [← denseExprEvalCongr c e1 e2
        (fun i hi => hh i (DenseConstraintSystem.mem_occ_of_constraint hc hi))]
      exact hsat.1 c hc
    · have hbe : denseBIEval bi e1 = denseBIEval bi e2 :=
        denseBIEval_congr bi e1 e2 (fun i hi => hh i (DenseConstraintSystem.mem_occ_of_bi hbi hi))
      show (denseBIEval bi e2).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi e2) = false
      rw [← hbe]
      exact hsat.2 bi hbi
  exact ⟨imp denv1 denv2 h, imp denv2 denv1 (fun i hi => (h i hi).symm)⟩

theorem DenseConstraintSystem.admissible_congr {d : DenseConstraintSystem p} {bs : BusSemantics p}
    {denv1 denv2 : VarId → ZMod p} (h : ∀ i ∈ d.occ, denv1 i = denv2 i) :
    d.admissible bs denv1 ↔ d.admissible bs denv2 := by
  have hmap : (d.busInteractions.map (fun bi => denseBIEval bi denv1))
      = (d.busInteractions.map (fun bi => denseBIEval bi denv2)) :=
    List.map_congr_left (fun bi hbi => denseBIEval_congr bi denv1 denv2
      (fun i hi => h i (DenseConstraintSystem.mem_occ_of_bi hbi hi)))
  unfold DenseConstraintSystem.admissible
  rw [hmap]

theorem DenseConstraintSystem.sideEffects_congr {d : DenseConstraintSystem p} {bs : BusSemantics p}
    {denv1 denv2 : VarId → ZMod p} (h : ∀ i ∈ d.occ, denv1 i = denv2 i) :
    d.sideEffects bs denv1 = d.sideEffects bs denv2 := by
  unfold DenseConstraintSystem.sideEffects
  refine List.map_congr_left (fun bi hbi => ?_)
  rw [denseBIEval_congr bi denv1 denv2
    (fun i hi => h i (DenseConstraintSystem.mem_occ_of_bi (List.mem_of_mem_filter hbi) hi))]

/-- Filtering the *stateful* interactions commutes with any bus-interaction map that preserves
    `busId`. -/
theorem filter_map_busId_comm (l : List (BusInteraction (DenseExpr p)))
    (f : BusInteraction (DenseExpr p) → BusInteraction (DenseExpr p)) (bs : BusSemantics p)
    (hf : ∀ bi, (f bi).busId = bi.busId) :
    (l.map f).filter (fun bi => bs.isStateful bi.busId)
      = (l.filter (fun bi => bs.isStateful bi.busId)).map f := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      by_cases hb : bs.isStateful b.busId = true
      · rw [if_pos hb, if_pos (show bs.isStateful (f b).busId = true by rw [hf]; exact hb),
            List.map_cons, ih]
      · rw [if_neg hb, if_neg (show ¬ bs.isStateful (f b).busId = true by rw [hf]; exact hb), ih]

/-! ## Environment transfer: extend a dense env to a spec env -/

/-- Whether a `VarId` resolves to a powdr-ID column. -/
def VarRegistry.isInput (reg : VarRegistry) (i : VarId) : Bool := (reg.resolve i).powdrId?.isSome

/-- Extend a dense environment to a spec environment: registered variables read their dense value,
    everything else falls back to `E`. The fallback keeps unregistered powdr columns fixed, as the
    spec completeness clause requires. -/
def VarRegistry.extendEnv (reg : VarRegistry) (denv : VarId → ZMod p) (E : Variable → ZMod p) :
    Variable → ZMod p :=
  fun v => match reg.idOf? v with
    | some i => denv i
    | none => E v

theorem VarRegistry.extendEnv_resolve (reg : VarRegistry) (denv : VarId → ZMod p)
    (E : Variable → ZMod p) {i : VarId} (hi : reg.Valid i) :
    reg.extendEnv denv E (reg.resolve i) = denv i := by
  simp only [VarRegistry.extendEnv, reg.idOf_resolve hi]

theorem VarRegistry.extendEnv_unregistered (reg : VarRegistry) (denv : VarId → ZMod p)
    (E : Variable → ZMod p) {v : Variable} (h : reg.idOf? v = none) :
    reg.extendEnv denv E v = E v := by
  simp only [VarRegistry.extendEnv, h]

/-- A `VarId` that resolves to a powdr column is valid (invalid IDs resolve to the metadata-free
    default). -/
theorem VarRegistry.isInput_valid {reg : VarRegistry} {i : VarId} (h : reg.isInput i = true) :
    reg.Valid i := by
  by_contra hv
  have hnone : reg.byId[i.index]? = none := Array.getElem?_eq_none (Nat.not_lt.mp hv)
  rw [VarRegistry.isInput, VarRegistry.resolve, hnone, Option.getD_none] at h
  exact absurd h (by decide)

/-! ## Decode correspondence: a spec semantics on a decoded object under `E` equals the dense
    semantics under `E ∘ resolve` -/

theorem VarRegistry.decodeBI_eval (reg : VarRegistry) (bi : BusInteraction (DenseExpr p))
    (E : Variable → ZMod p) :
    (reg.decodeBI bi).eval E = denseBIEval bi (fun i => E (reg.resolve i)) := by
  simp only [VarRegistry.decodeBI, BusInteraction.eval, denseBIEval, reg.decodeExpr_eval,
    List.map_map, Function.comp_def]

theorem VarRegistry.decodeCS_satisfies (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (E : Variable → ZMod p) :
    (reg.decodeCS d).satisfies bs E ↔ d.satisfies bs (fun i => E (reg.resolve i)) := by
  simp only [ConstraintSystem.satisfies, DenseConstraintSystem.satisfies, VarRegistry.decodeCS,
    List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · have := h1 (reg.decodeExpr c) c hc rfl
      rwa [reg.decodeExpr_eval] at this
    · have := h2 (reg.decodeBI bi) bi hbi rfl
      rwa [reg.decodeBI_eval] at this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro c c0 hc0 rfl
      rw [reg.decodeExpr_eval]; exact h1 c0 hc0
    · rintro bi bi0 hbi0 rfl
      rw [reg.decodeBI_eval]; exact h2 bi0 hbi0

theorem VarRegistry.decodeCS_admissible (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (E : Variable → ZMod p) :
    (reg.decodeCS d).admissible bs E ↔ d.admissible bs (fun i => E (reg.resolve i)) := by
  have hlist : (((reg.decodeCS d).busInteractions.map (fun bi => bi.eval E)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
      = ((d.busInteractions.map (fun bi => denseBIEval bi (fun i => E (reg.resolve i)))).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := by
    congr 1
    show (d.busInteractions.map reg.decodeBI).map (fun bi => bi.eval E) = _
    rw [List.map_map]
    refine List.map_congr_left (fun bi _ => ?_)
    simp only [Function.comp_apply]
    exact reg.decodeBI_eval bi E
  have hAeq : (reg.decodeCS d).admissible bs E = d.admissible bs (fun i => E (reg.resolve i)) := by
    unfold ConstraintSystem.admissible DenseConstraintSystem.admissible
    rw [hlist]
  exact iff_of_eq hAeq

/-- Filtering the *stateful* interactions commutes with decoding (decode preserves `busId`). -/
theorem VarRegistry.decodeBI_filter_comm (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) :
    ((d.busInteractions.map reg.decodeBI).filter (fun bi => bs.isStateful bi.busId))
      = (d.busInteractions.filter (fun bi => bs.isStateful bi.busId)).map reg.decodeBI := by
  induction d.busInteractions with
  | nil => rfl
  | cons b rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      by_cases hb : bs.isStateful b.busId = true
      · rw [if_pos hb, if_pos (show bs.isStateful (reg.decodeBI b).busId = true from hb),
            List.map_cons, ih]
      · rw [if_neg hb, if_neg (show ¬ bs.isStateful (reg.decodeBI b).busId = true from hb), ih]

theorem VarRegistry.decodeCS_sideEffects (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (E : Variable → ZMod p) :
    (reg.decodeCS d).sideEffects bs E = d.sideEffects bs (fun i => E (reg.resolve i)) := by
  simp only [ConstraintSystem.sideEffects, DenseConstraintSystem.sideEffects, VarRegistry.decodeCS]
  rw [reg.decodeBI_filter_comm d bs, List.map_map]
  refine List.map_congr_left (fun bi _ => ?_)
  simp only [Function.comp_apply, reg.decodeBI_eval]

theorem VarRegistry.decodeCS_guaranteesInvariants (reg : VarRegistry) {d : DenseConstraintSystem p}
    (bs : BusSemantics p) (hc : d.CoveredBy reg) :
    (reg.decodeCS d).guaranteesInvariants bs ↔ d.guaranteesInvariants bs := by
  unfold ConstraintSystem.guaranteesInvariants DenseConstraintSystem.guaranteesInvariants
  constructor
  · -- decode → dense (needs coverage, to transport a dense env to a spec one)
    intro hgi denv hsat bi hbi
    show (denseBIEval bi denv).multiplicity ≠ 0 → bs.breaksInvariant (denseBIEval bi denv) = false
    intro hne
    have hsatE : (reg.decodeCS d).satisfies bs (reg.extendEnv denv (fun _ => 0)) := by
      rw [reg.decodeCS_satisfies]
      refine (DenseConstraintSystem.satisfies_congr (fun i hi => ?_)).mpr hsat
      exact reg.extendEnv_resolve denv (fun _ => 0) (DenseConstraintSystem.occ_valid hc i hi)
    have hbe : (reg.decodeBI bi).eval (reg.extendEnv denv (fun _ => 0)) = denseBIEval bi denv := by
      rw [reg.decodeBI_eval]
      exact denseBIEval_congr bi _ _ (fun i hi =>
        reg.extendEnv_resolve denv (fun _ => 0)
          (DenseConstraintSystem.occ_valid hc i (DenseConstraintSystem.mem_occ_of_bi hbi hi)))
    have hmem : reg.decodeBI bi ∈ (reg.decodeCS d).busInteractions := by
      simp only [VarRegistry.decodeCS]; exact List.mem_map_of_mem hbi
    have hconc := hgi (reg.extendEnv denv (fun _ => 0)) hsatE (reg.decodeBI bi) hmem
    rw [hbe] at hconc
    exact hconc hne
  · -- dense → decode (no coverage needed)
    intro hgi E hsat bi' hbi'
    simp only [VarRegistry.decodeCS, List.mem_map] at hbi'
    obtain ⟨bi, hbi, rfl⟩ := hbi'
    show ((reg.decodeBI bi).eval E).multiplicity ≠ 0
      → bs.breaksInvariant ((reg.decodeBI bi).eval E) = false
    rw [reg.decodeBI_eval]
    rw [reg.decodeCS_satisfies] at hsat
    exact fun hne => hgi _ hsat bi hbi hne

theorem VarRegistry.decodeCM_eval (reg : VarRegistry) (cm : DenseComputationMethod p)
    (E : Variable → ZMod p) :
    (reg.decodeCM cm).eval E = cm.eval (fun i => E (reg.resolve i)) := by
  induction cm with
  | const c => rfl
  | quotientOrZero num den =>
      simp only [VarRegistry.decodeCM, ComputationMethod.eval, DenseComputationMethod.eval,
        reg.decodeExpr_eval]
  | ifEqZero cond thenM elseM iht ihe =>
      simp only [VarRegistry.decodeCM, ComputationMethod.eval, DenseComputationMethod.eval,
        reg.decodeExpr_eval, iht, ihe]

theorem VarRegistry.decodeCM_vars (reg : VarRegistry) (cm : DenseComputationMethod p) :
    (reg.decodeCM cm).vars = cm.vars.map reg.resolve := by
  induction cm with
  | const c => rfl
  | quotientOrZero num den =>
      simp only [VarRegistry.decodeCM, ComputationMethod.vars, DenseComputationMethod.vars,
        reg.decodeExpr_vars, List.map_append]
  | ifEqZero cond thenM elseM iht ihe =>
      simp only [VarRegistry.decodeCM, ComputationMethod.vars, DenseComputationMethod.vars,
        reg.decodeExpr_vars, iht, ihe, List.map_append]

/-- Decoding `methodFor`: for a valid ID, the decoded derivations' method for its resolved variable
    is the dense method, decoded. -/
theorem VarRegistry.decodeDerivs_methodFor (reg : VarRegistry) {dd : DenseDerivations p}
    (hc : dd.CoveredBy reg) {i : VarId} (hi : reg.Valid i) :
    Derivations.methodFor (reg.decodeDerivs dd) (reg.resolve i)
      = (DenseDerivations.methodFor dd i).map reg.decodeCM := by
  induction dd with
  | nil => rfl
  | cons hd rest ih =>
      obtain ⟨u, cm⟩ := hd
      have hu : reg.Valid u := (hc (u, cm) (List.mem_cons_self ..)).1
      have hrest : DenseDerivations.CoveredBy reg rest :=
        fun x hx => hc x (List.mem_cons_of_mem _ hx)
      have hcons : reg.decodeDerivs ((u, cm) :: rest)
          = (reg.resolve u, reg.decodeCM cm) :: reg.decodeDerivs rest := rfl
      rw [hcons, Derivations.methodFor, DenseDerivations.methodFor, ih hrest]
      cases hM : DenseDerivations.methodFor rest i with
      | some m => rfl
      | none =>
          show (if reg.resolve u = reg.resolve i then some (reg.decodeCM cm) else none)
            = Option.map reg.decodeCM (if u = i then some cm else none)
          by_cases huv : u = i
          · subst huv; simp
          · have hne : reg.resolve u ≠ reg.resolve i := fun h => huv (reg.resolve_inj hu hi h)
            simp [hne, huv]

theorem VarRegistry.mem_decodeCS_vars (reg : VarRegistry) (d : DenseConstraintSystem p)
    {v : Variable} : v ∈ (reg.decodeCS d).vars ↔ ∃ i ∈ d.occ, reg.resolve i = v := by
  rw [show (reg.decodeCS d).vars = d.occ.map reg.resolve from reg.decodeCS_occ d, List.mem_map]

/-! ## `DensePassCorrect`: the dense analogue of `PassCorrect`

`isInput : VarId → Bool` marks the powdr-ID columns (the lift instantiates it with `reg.isInput`).
`DenseOutReconstructs` states the reconstruction obligation for a pass's output. -/

/-- The reconstruction obligation for a pass's output. -/
def DenseOutReconstructs (isInput : VarId → Bool) (inputVarIds : List VarId)
    (d out : DenseConstraintSystem p) (dd : DenseDerivations p) (denv denv' : VarId → ZMod p) :
    Prop :=
  ∀ i ∈ out.occ, isInput i = false →
    match DenseDerivations.methodFor dd i with
    | some dcm =>
        (∀ j ∈ dcm.vars, isInput j = true) ∧ (∀ j ∈ dcm.vars, j ∈ inputVarIds) ∧
          dcm.eval denv' = denv' i
    | none => i ∈ d.occ ∧ denv' i = denv i

/-- The per-pass correctness obligation over dense environments: the dense analogue of
    `PassCorrect`. Fully `Variable`-free and decode-free; all evidence is `Prop` (erases). -/
def DensePassCorrect (isInput : VarId → Bool) (d out : DenseConstraintSystem p)
    (dd : DenseDerivations p) (bs : BusSemantics p) : Prop :=
  out.implies d bs ∧
  (d.guaranteesInvariants bs → out.guaranteesInvariants bs) ∧
  (∀ i ∈ out.occ, isInput i = true → i ∈ d.occ) ∧
  (∀ denv, d.admissible bs denv → d.satisfies bs denv →
    ∃ denv', out.satisfies bs denv' ∧ out.admissible bs denv' ∧
      d.sideEffects bs denv ≈ out.sideEffects bs denv' ∧
      (∀ i, isInput i = true → denv' i = denv i) ∧
      (∀ inputVarIds, (∀ i ∈ d.occ, isInput i = true → i ∈ inputVarIds) →
        DenseOutReconstructs isInput inputVarIds d out dd denv denv'))

/-! ## Spec-level helpers -/

private theorem specExpr_eval_congr (e : Expression p) (e1 e2 : Variable → ZMod p)
    (h : ∀ v ∈ e.vars, e1 v = e2 v) : e.eval e1 = e.eval e2 := by
  induction e with
  | const n => rfl
  | var x => exact h x (by simp [Expression.vars])
  | add a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun v hv => h v (by simp [Expression.vars, hv])),
          ihb (fun v hv => h v (by simp [Expression.vars, hv]))]
  | mul a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun v hv => h v (by simp [Expression.vars, hv])),
          ihb (fun v hv => h v (by simp [Expression.vars, hv]))]

private theorem specCM_eval_congr (cm : ComputationMethod p) (e1 e2 : Variable → ZMod p)
    (h : ∀ v ∈ cm.vars, e1 v = e2 v) : cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => rfl
  | quotientOrZero num den =>
      have hn : num.eval e1 = num.eval e2 :=
        specExpr_eval_congr num _ _ (fun v hv => h v (List.mem_append_left _ hv))
      have hd : den.eval e1 = den.eval e2 :=
        specExpr_eval_congr den _ _ (fun v hv => h v (List.mem_append_right _ hv))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      have hc : cond.eval e1 = cond.eval e2 :=
        specExpr_eval_congr cond _ _ (fun v hv => h v (by
          simp only [ComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hv)))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, iht (fun v hv => h v (by
            simp only [ComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hv))),
          ihe (fun v hv => h v (by
            simp only [ComputationMethod.vars, List.mem_append]; exact Or.inr hv))]

private theorem specDCM_eval_congr (cm : DenseComputationMethod p) (e1 e2 : VarId → ZMod p)
    (h : ∀ i ∈ cm.vars, e1 i = e2 i) : cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => rfl
  | quotientOrZero num den =>
      have hn : num.eval e1 = num.eval e2 :=
        denseExprEvalCongr num _ _ (fun i hi => h i (List.mem_append_left _ hi))
      have hd : den.eval e1 = den.eval e2 :=
        denseExprEvalCongr den _ _ (fun i hi => h i (List.mem_append_right _ hi))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      have hc : cond.eval e1 = cond.eval e2 :=
        denseExprEvalCongr cond _ _ (fun i hi => h i (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hi)))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, iht (fun i hi => h i (by
            simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hi))),
          ihe (fun i hi => h i (by
            simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inr hi))]

private theorem specMethodFor_append (a b : Derivations p) (v : Variable) :
    Derivations.methodFor (a ++ b) v
      = (Derivations.methodFor b v).orElse (fun _ => Derivations.methodFor a v) := by
  induction a with
  | nil => simp only [List.nil_append]; cases Derivations.methodFor b v <;> rfl
  | cons hd rest ih =>
      obtain ⟨u, cm⟩ := hd
      simp only [List.cons_append, Derivations.methodFor, ih]
      cases Derivations.methodFor b v <;> rfl

/-! ## Dense composition: `refl` and `andThen`

The dense analogues of `PassCorrect.refl`/`PassCorrect.andThen`, over `VarId → ZMod p`. `andThen`
concatenates derivations (`dd1 ++ dd2`); with both sides `[]` it composes fixpoint loops. -/

/-- `methodFor` over an append: the second list wins, falling back to the first. -/
theorem DenseDerivations.methodFor_append (a b : DenseDerivations p) (v : VarId) :
    DenseDerivations.methodFor (a ++ b) v
      = (DenseDerivations.methodFor b v).orElse (fun _ => DenseDerivations.methodFor a v) := by
  induction a with
  | nil => simp only [List.nil_append]; cases DenseDerivations.methodFor b v <;> rfl
  | cons hd rest ih =>
      obtain ⟨u, cm⟩ := hd
      simp only [List.cons_append, DenseDerivations.methodFor, ih]
      cases DenseDerivations.methodFor b v <;> rfl

/-- Reflexivity: the identity transform (same system, no new derivations) is correct. -/
theorem DensePassCorrect.refl (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) : DensePassCorrect isInput d d [] bs := by
  refine ⟨fun denv hsat => ⟨denv, hsat, BusState.equiv_refl _⟩, _root_.id, fun i hi _ => hi, ?_⟩
  intro denv hadm hsat
  refine ⟨denv, hsat, hadm, BusState.equiv_refl _, fun _ _ => rfl, ?_⟩
  intro inputVarIds _ i hi _
  exact ⟨hi, rfl⟩

/-- Sequential composition: correctness `d → mid` (derivations `dd1`) and `mid → out` (`dd2`) give
    `d → out` with `dd1 ++ dd2`, composing all four `DensePassCorrect` clauses across the middle
    system. -/
theorem DensePassCorrect.andThen {isInput : VarId → Bool} {d mid out : DenseConstraintSystem p}
    {dd1 dd2 : DenseDerivations p} {bs : BusSemantics p}
    (hf : DensePassCorrect isInput d mid dd1 bs) (hg : DensePassCorrect isInput mid out dd2 bs) :
    DensePassCorrect isInput d out (dd1 ++ dd2) bs := by
  obtain ⟨hs12, hi12, hv12, hc12⟩ := hf
  obtain ⟨hs23, hi23, hv23, hc23⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Soundness: `out.implies d`.
    intro denv hsat3
    obtain ⟨e1, hsat2, hse23⟩ := hs23 denv hsat3
    obtain ⟨e0, hsat1, hse12⟩ := hs12 e1 hsat2
    exact ⟨e0, hsat1, BusState.equiv_trans hse23 hse12⟩
  · -- Invariant preservation.
    intro h; exact hi23 (hi12 h)
  · -- No new powdr-ID column.
    intro i hi3 hii; exact hv12 i (hv23 i hi3 hii) hii
  · -- Completeness with derivations.
    intro denv hadm1 hsat1
    obtain ⟨e1, hsat2, hadm2, hse12, hii12, hrec12⟩ := hc12 denv hadm1 hsat1
    obtain ⟨e2, hsat3, hadm3, hse23, hii23, hrec23⟩ := hc23 e1 hadm2 hsat2
    refine ⟨e2, hsat3, hadm3, BusState.equiv_trans hse12 hse23, ?_, ?_⟩
    · intro i hii; rw [hii23 i hii, hii12 i hii]
    · -- Reconstruction over `dd1 ++ dd2`.
      intro inputVarIds hcov1
      have hmidIn : ∀ i ∈ mid.occ, isInput i = true → i ∈ inputVarIds :=
        fun i hi hii => hcov1 i (hv12 i hi hii) hii
      have R23 := hrec23 inputVarIds hmidIn
      have R12 := hrec12 inputVarIds hcov1
      intro i hiout hisF
      have B23 := R23 i hiout hisF
      -- Case on the composite method (reduces the goal match); relate to `dd2`/`dd1` via append.
      cases hmapp : DenseDerivations.methodFor (dd1 ++ dd2) i with
      | some dcm =>
          cases hm2 : DenseDerivations.methodFor dd2 i with
          | some dcm2 =>
              have happ : DenseDerivations.methodFor (dd1 ++ dd2) i = some dcm2 := by
                rw [DenseDerivations.methodFor_append, hm2, Option.orElse_some]
              rw [hmapp, Option.some.injEq] at happ
              rw [hm2] at B23
              rw [happ]; exact B23
          | none =>
              have happ : DenseDerivations.methodFor (dd1 ++ dd2) i
                  = DenseDerivations.methodFor dd1 i := by
                rw [DenseDerivations.methodFor_append, hm2, Option.orElse_none]
              rw [hmapp] at happ
              rw [hm2] at B23
              obtain ⟨himid, he2e1⟩ := B23
              have B12 := R12 i himid hisF
              rw [← happ] at B12
              obtain ⟨hjIn, hjInIds, hEval1⟩ := B12
              refine ⟨hjIn, hjInIds, ?_⟩
              rw [specDCM_eval_congr dcm e2 e1 (fun j hj => hii23 j (hjIn j hj)), hEval1, he2e1]
      | none =>
          cases hm2 : DenseDerivations.methodFor dd2 i with
          | some dcm2 =>
              have happ : DenseDerivations.methodFor (dd1 ++ dd2) i = some dcm2 := by
                rw [DenseDerivations.methodFor_append, hm2, Option.orElse_some]
              rw [hmapp] at happ
              exact absurd happ (by simp)
          | none =>
              have happ : DenseDerivations.methodFor (dd1 ++ dd2) i
                  = DenseDerivations.methodFor dd1 i := by
                rw [DenseDerivations.methodFor_append, hm2, Option.orElse_none]
              rw [hmapp] at happ
              rw [hm2] at B23
              obtain ⟨himid, he2e1⟩ := B23
              have B12 := R12 i himid hisF
              rw [← happ] at B12
              obtain ⟨hiD, he1denv⟩ := B12
              exact ⟨hiD, by rw [he2e1, he1denv]⟩

/-! ## `DensePassCorrect` shortcuts (env'=env, and composition) -/

/-- The env'=env correctness shape: the completeness witness is the input assignment and it
    introduces no variable. -/
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

/-- `DensePassCorrect` composes (derivations empty on both sides); `PassCorrect.andThen`
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

/-! ### Sanity check: the composition lemmas type-check

Erased `example`s: a drop-shaped step chained after `refl`, and the general `andThen`. -/

private def keepAllBus (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { d with busInteractions := d.busInteractions.filter (fun _ => true) }

private theorem keepAllBus_eq (d : DenseConstraintSystem p) : keepAllBus d = d := by
  obtain ⟨ac, bi⟩ := d
  simp only [keepAllBus, List.filter_true]

private theorem keepAllBus_correct (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) : DensePassCorrect isInput d (keepAllBus d) [] bs := by
  rw [keepAllBus_eq]; exact DensePassCorrect.refl isInput d bs

/-- `refl` chained with a drop-shaped filter step through `andThen`. -/
private example (isInput : VarId → Bool) (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    DensePassCorrect isInput d (keepAllBus d) [] bs :=
  (DensePassCorrect.refl isInput d bs).andThen (keepAllBus_correct isInput d bs)

/-- The general `andThen` composes any two steps, concatenating their derivations. -/
private example (isInput : VarId → Bool) (d mid out : DenseConstraintSystem p)
    (dd1 dd2 : DenseDerivations p) (bs : BusSemantics p)
    (h1 : DensePassCorrect isInput d mid dd1 bs) (h2 : DensePassCorrect isInput mid out dd2 bs) :
    DensePassCorrect isInput d out (dd1 ++ dd2) bs :=
  h1.andThen h2

/-! ## The lift theorem -/

/-- **Lift.** Under the registry coverage invariants, a `DensePassCorrect` (with `isInput`
    instantiated as "resolves to a powdr column") implies the spec `PassCorrect` for the decoded
    input/output/derivations. This is the one place representation correspondence is discharged. -/
theorem DensePassCorrect.lift {reg : VarRegistry} {d out : DenseConstraintSystem p}
    {dd : DenseDerivations p} {bs : BusSemantics p}
    (hcd : d.CoveredBy reg) (hco : out.CoveredBy reg) (hdd : dd.CoveredBy reg)
    (h : DensePassCorrect reg.isInput d out dd bs) :
    PassCorrect (reg.decodeCS d) (reg.decodeCS out) (reg.decodeDerivs dd) bs := by
  obtain ⟨hSound, hInv, hVars, hComp⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Soundness: `(decode out).implies (decode d)`.
    intro E hsatE
    rw [reg.decodeCS_satisfies] at hsatE
    obtain ⟨denv', hsatd', hse⟩ := hSound _ hsatE
    refine ⟨reg.extendEnv denv' E, ?_, ?_⟩
    · rw [reg.decodeCS_satisfies]
      refine (DenseConstraintSystem.satisfies_congr (fun i hi => ?_)).mpr hsatd'
      exact reg.extendEnv_resolve denv' E (DenseConstraintSystem.occ_valid hcd i hi)
    · rw [reg.decodeCS_sideEffects, reg.decodeCS_sideEffects,
        DenseConstraintSystem.sideEffects_congr (d := d) (fun i hi =>
          reg.extendEnv_resolve denv' E (DenseConstraintSystem.occ_valid hcd i hi))]
      exact hse
  · -- Invariant preservation.
    intro hgiIn
    rw [reg.decodeCS_guaranteesInvariants bs hco]
    exact hInv ((reg.decodeCS_guaranteesInvariants bs hcd).mp hgiIn)
  · -- No new powdr-ID column.
    intro v hv hpow
    rw [reg.mem_decodeCS_vars] at hv ⊢
    obtain ⟨i, hi, rfl⟩ := hv
    have hisT : reg.isInput i = true := by simpa [VarRegistry.isInput] using hpow
    exact ⟨i, hVars i hi hisT, rfl⟩
  · -- Completeness with derivations.
    intro E hadmE hsatE
    rw [reg.decodeCS_admissible] at hadmE
    rw [reg.decodeCS_satisfies] at hsatE
    obtain ⟨denv', hsat', hadm', hse, hc4, hrec⟩ := hComp _ hadmE hsatE
    set env' := reg.extendEnv denv' E with henv'
    -- powdr-ID columns are preserved by `env'`.
    have hpw4 : ∀ w : Variable, w.powdrId?.isSome = true → env' w = E w := by
      intro w hw
      cases hidof : reg.idOf? w with
      | none => rw [henv', reg.extendEnv_unregistered denv' E hidof]
      | some i =>
          have hres : reg.resolve i = w := reg.resolve_idOf hidof
          have hvi : reg.Valid i := reg.valid_of_idOf hidof
          have hii : reg.isInput i = true := by
            simp only [VarRegistry.isInput, hres]; exact hw
          rw [henv',
            show reg.extendEnv denv' E w = denv' i from by simp only [VarRegistry.extendEnv, hidof]]
          rw [hc4 i hii]
          show E (reg.resolve i) = E w
          rw [hres]
    refine ⟨env', ?_, ?_, ?_, ?_, ?_⟩
    · rw [reg.decodeCS_satisfies]
      refine (DenseConstraintSystem.satisfies_congr (fun i hi => ?_)).mpr hsat'
      exact reg.extendEnv_resolve denv' E (DenseConstraintSystem.occ_valid hco i hi)
    · rw [reg.decodeCS_admissible]
      refine (DenseConstraintSystem.admissible_congr (fun i hi => ?_)).mpr hadm'
      exact reg.extendEnv_resolve denv' E (DenseConstraintSystem.occ_valid hco i hi)
    · rw [reg.decodeCS_sideEffects, reg.decodeCS_sideEffects,
        DenseConstraintSystem.sideEffects_congr (d := out) (fun i hi =>
          reg.extendEnv_resolve denv' E (DenseConstraintSystem.occ_valid hco i hi))]
      exact hse
    · intro v hpow; exact hpw4 v hpow
    · -- Reconstruction.
      intro inputVars hpowIn dsIn hrecIn
      set inputVarIds := inputVars.filterMap reg.idOf? with hIVI
      have hpowD : ∀ i ∈ d.occ, reg.isInput i = true → i ∈ inputVarIds := by
        intro i hi hisT
        have hvi : reg.Valid i := DenseConstraintSystem.occ_valid hcd i hi
        have hvmem : reg.resolve i ∈ (reg.decodeCS d).vars :=
          (reg.mem_decodeCS_vars d).mpr ⟨i, hi, rfl⟩
        have hpow : (reg.resolve i).powdrId?.isSome := by simpa [VarRegistry.isInput] using hisT
        have hin : reg.resolve i ∈ inputVars := hpowIn _ hvmem hpow
        rw [hIVI, List.mem_filterMap]
        exact ⟨reg.resolve i, hin, reg.idOf_resolve hvi⟩
      have hrecOut := hrec inputVarIds hpowD
      intro v hvout hvnone
      rw [reg.mem_decodeCS_vars] at hvout
      obtain ⟨i, hiout, rfl⟩ := hvout
      have hvi : reg.Valid i := DenseConstraintSystem.occ_valid hco i hiout
      have hisF : reg.isInput i = false := by
        simp only [VarRegistry.isInput, hvnone]; rfl
      have hbranch := hrecOut i hiout hisF
      -- decoded local method for `resolve i`.
      have hlocal : Derivations.methodFor (reg.decodeDerivs dd) (reg.resolve i)
          = (DenseDerivations.methodFor dd i).map reg.decodeCM :=
        reg.decodeDerivs_methodFor hdd hvi
      have hMF : Derivations.methodFor (dsIn ++ reg.decodeDerivs dd) (reg.resolve i)
          = ((DenseDerivations.methodFor dd i).map reg.decodeCM).orElse
              (fun _ => Derivations.methodFor dsIn (reg.resolve i)) := by
        rw [specMethodFor_append, hlocal]
      cases hdcm : DenseDerivations.methodFor dd i with
      | some dcm =>
          rw [hdcm] at hbranch
          obtain ⟨hjIn, hjInIds, hEval⟩ := hbranch
          refine ⟨reg.decodeCM dcm, ?_, ?_, ?_, ?_⟩
          · rw [hMF, hdcm]; rfl
          · intro x hx
            rw [reg.decodeCM_vars, List.mem_map] at hx
            obtain ⟨j, hj, rfl⟩ := hx
            simpa [VarRegistry.isInput] using hjIn j hj
          · intro x hx
            rw [reg.decodeCM_vars, List.mem_map] at hx
            obtain ⟨j, hj, rfl⟩ := hx
            have hjm := hjInIds j hj
            rw [hIVI, List.mem_filterMap] at hjm
            obtain ⟨w, hw, hidof⟩ := hjm
            rw [reg.resolve_idOf hidof]; exact hw
          · -- value: `(decodeCM dcm).eval env' = env' (resolve i)`.
            rw [reg.decodeCM_eval]
            have hagree : ∀ j ∈ dcm.vars, env' (reg.resolve j) = denv' j := by
              intro j hj
              exact reg.extendEnv_resolve denv' E (reg.isInput_valid (hjIn j hj))
            rw [specDCM_eval_congr dcm _ denv' hagree, hEval, henv',
              reg.extendEnv_resolve denv' E hvi]
      | none =>
          rw [hdcm] at hbranch
          obtain ⟨hiD, hpres⟩ := hbranch
          have hvmem : reg.resolve i ∈ (reg.decodeCS d).vars :=
            (reg.mem_decodeCS_vars d).mpr ⟨i, hiD, rfl⟩
          obtain ⟨cm, hmeth, hcmpow, hcmin, hcmeval⟩ := hrecIn (reg.resolve i) hvmem hvnone
          refine ⟨cm, ?_, hcmpow, hcmin, ?_⟩
          · rw [hMF, hdcm]; simpa using hmeth
          · -- value: `cm.eval env' = env' (resolve i)`.
            rw [specCM_eval_congr cm env' E (fun x hx => hpw4 x (hcmpow x hx)), hcmeval, henv',
              reg.extendEnv_resolve denv' E hvi, hpres]

/-! ## The dense-pass builder -/

/-- Build a `DenseVerifiedPassW` from a registry-preserving dense transform, its coverage
    preservation, and a `DensePassCorrect` proof (discharged via `DensePassCorrect.lift`).
    Fresh-variable passes use `ofExtending`. -/
def DenseVerifiedPassW.of
    (denseF : (bs : BusSemantics p) → BusFacts p bs → DenseConstraintSystem p →
      DenseConstraintSystem p)
    (denseDerivsF : (bs : BusSemantics p) → BusFacts p bs → DenseConstraintSystem p →
      DenseDerivations p)
    (hcov : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg → (denseF bs facts d).CoveredBy reg)
    (hdcov : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg → (denseDerivsF bs facts d).CoveredBy reg)
    (hcorrect : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg →
      DensePassCorrect reg.isInput d (denseF bs facts d) (denseDerivsF bs facts d) bs) :
    DenseVerifiedPassW p :=
  fun reg d hcovd bs facts =>
    { reg' := reg
      out := denseF bs facts d
      derivs := denseDerivsF bs facts d
      ext := VarRegistry.Extends.refl reg
      covered := hcov reg bs facts d hcovd
      dcovered := hdcov reg bs facts d hcovd
      correct := DensePassCorrect.lift hcovd (hcov reg bs facts d hcovd)
        (hdcov reg bs facts d hcovd) (hcorrect reg bs facts d hcovd) }

/-- `of` respects the degree bound whenever its dense output stays within bound. -/
theorem DenseVerifiedPassW.of_respectsDeg {b : DegreeBound}
    {denseF : (bs : BusSemantics p) → BusFacts p bs → DenseConstraintSystem p →
      DenseConstraintSystem p}
    {denseDerivsF : (bs : BusSemantics p) → BusFacts p bs → DenseConstraintSystem p →
      DenseDerivations p}
    {hcov hdcov hcorrect}
    (hdeg : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg →
      (reg.decodeCS d).withinDegree b → (reg.decodeCS (denseF bs facts d)).withinDegree b) :
    DenseRespectsDeg b (of denseF denseDerivsF hcov hdcov hcorrect) := by
  intro reg d hcovd bs facts hin
  exact hdeg reg bs facts d hcovd hin

/-! ## The registry-extending dense-pass builder

`ofExtending` is the sibling of `of` for fresh-variable passes: the transform returns the extended
registry, and `DensePassCorrect` is stated at the extended registry's `isInput`. -/

/-- Constraint-system coverage is preserved by a registry extension. -/
theorem denseCS_coveredBy_mono {r r' : VarRegistry} (h : r.Extends r')
    {d : DenseConstraintSystem p} (hc : d.CoveredBy r) : d.CoveredBy r' := by
  obtain ⟨hac, hbi⟩ := hc
  refine ⟨fun e he => (hac e he).mono h, fun bi hbimem => ?_⟩
  obtain ⟨hm, hp⟩ := hbi bi hbimem
  exact ⟨hm.mono h, fun e he => (hp e he).mono h⟩

/-- Build a `DenseVerifiedPassW` from a registry-extending dense transform (the sibling of `of` for
    fresh-variable passes). The `transform` returns the extended registry, output, and derivations;
    the obligations are extension (`hext`), coverage there (`hcov`/`hdcov`), and a
    `DensePassCorrect` proof at the extended registry's `isInput` (`hcorrect`). -/
def DenseVerifiedPassW.ofExtending
    (transform : VarRegistry → (bs : BusSemantics p) → BusFacts p bs → DenseConstraintSystem p →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p)
    (hext : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg → reg.Extends (transform reg bs facts d).1)
    (hcov : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg →
      (transform reg bs facts d).2.1.CoveredBy (transform reg bs facts d).1)
    (hdcov : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg →
      (transform reg bs facts d).2.2.CoveredBy (transform reg bs facts d).1)
    (hcorrect : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg →
      DensePassCorrect (transform reg bs facts d).1.isInput d
        (transform reg bs facts d).2.1 (transform reg bs facts d).2.2 bs) :
    DenseVerifiedPassW p :=
  fun reg d hcovd bs facts =>
    let t := transform reg bs facts d
    have hext' : reg.Extends t.1 := hext reg bs facts d hcovd
    have hcov' : t.2.1.CoveredBy t.1 := hcov reg bs facts d hcovd
    have hdcov' : t.2.2.CoveredBy t.1 := hdcov reg bs facts d hcovd
    have hcorrect' : DensePassCorrect t.1.isInput d t.2.1 t.2.2 bs := hcorrect reg bs facts d hcovd
    { reg' := t.1
      out := t.2.1
      derivs := t.2.2
      ext := hext'
      covered := hcov'
      dcovered := hdcov'
      correct := by
        have hcovd' : d.CoveredBy t.1 := denseCS_coveredBy_mono hext' hcovd
        have hlift := DensePassCorrect.lift hcovd' hcov' hdcov' hcorrect'
        rwa [hext'.decodeCS_eq hcovd] at hlift }

/-- `ofExtending` respects the degree bound whenever its dense output stays within bound. -/
theorem DenseVerifiedPassW.ofExtending_respectsDeg {b : DegreeBound}
    {transform : VarRegistry → (bs : BusSemantics p) → BusFacts p bs → DenseConstraintSystem p →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p}
    {hext hcov hdcov hcorrect}
    (hdeg : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p), d.CoveredBy reg →
      (reg.decodeCS d).withinDegree b →
      ((transform reg bs facts d).1.decodeCS (transform reg bs facts d).2.1).withinDegree b) :
    DenseRespectsDeg b (ofExtending transform hext hcov hdcov hcorrect) := by
  intro reg d hcovd bs facts hin
  exact hdeg reg bs facts d hcovd hin

/-! ### Sanity check: a trivial registry-minting stub composes through the builder -/

/-- A trivial registry-minting stub (register one fresh `Variable`, keep the system) composing
    through `ofExtending`; an erased `example` witnessing the extending builder type-checks. -/
private example (v : Variable) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofExtending
    (fun reg _ _ d => ((reg.register v).1, d, []))
    (fun reg _ _ _ _ => VarRegistry.register_extends reg v)
    (fun reg _ _ _ hcov => denseCS_coveredBy_mono (VarRegistry.register_extends reg v) hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => DensePassCorrect.refl (reg.register v).1.isInput d bs)

end ApcOptimizer.Dense
