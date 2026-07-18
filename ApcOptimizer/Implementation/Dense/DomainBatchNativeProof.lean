import ApcOptimizer.Implementation.Dense.DomainBatchNative
import ApcOptimizer.Implementation.Dense.Bridge

set_option autoImplicit false

/-! # Native correctness for the value-only dense `domainBatch` (Task 3)

This module proves `DensePassCorrect` for the value-only rebuild of `domainBatch`
(`Dense/DomainBatchNative.lean`) **natively** over dense environments `VarId → ZMod p`, with no
commutation to the spec pass and no decode in the discharged obligations. The spec pass's own
`PassCorrect` proof (`OptimizerPasses/DomainBatch.lean`) is only the roadmap: its argument structure
is mirrored here over the native dense semantics of `Dense/Bridge.lean`.

The pass output is `applyσ dσ d` — a batch substitution of forced *constants* into `d`. The proof has
two native halves:

* a native simultaneous-substitution correctness lemma (`substF_denseCorrect`): substituting an
  *entailed* map of constants yields `DensePassCorrect` (mirrors `ConstraintSystem.substF_correct`);
* a native entailment for the collected forced map (`denseDomainBatchσV`): every forced pair
  `(i, .const c)` satisfies `denv i = c` for every satisfying `denv`, established through native
  domain-table soundness (`rootsIn` roots, fact-bounded payload slots) and a native value-only
  box-scan certificate over the fixed-length candidate mask. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Native simultaneous substitution semantics -/

/-- The dense environment with every mapped `VarId` rebound to its solution's value (mirrors
    `envF`). -/
def denseEnvF (df : VarId → Option (DenseExpr p)) (denv : VarId → ZMod p) : VarId → ZMod p :=
  fun j => match df j with | some t => t.eval denv | none => denv j

theorem DenseExpr.eval_substF (e : DenseExpr p) (df : VarId → Option (DenseExpr p))
    (denv : VarId → ZMod p) : (e.substF df).eval denv = e.eval (denseEnvF df denv) := by
  induction e with
  | const n => rfl
  | var j =>
      show (match df j with | some t => t | none => DenseExpr.var j).eval denv = denseEnvF df denv j
      unfold denseEnvF
      cases df j <;> rfl
  | add a b iha ihb => simp only [DenseExpr.substF, DenseExpr.eval, iha, ihb]
  | mul a b iha ihb => simp only [DenseExpr.substF, DenseExpr.eval, iha, ihb]

/-- If every mapped pair is respected by `denv`, rebinding changes nothing (mirrors `envF_eq_self`). -/
theorem denseEnvF_eq_self (df : VarId → Option (DenseExpr p)) (denv : VarId → ZMod p)
    (H : ∀ j t, df j = some t → denv j = t.eval denv) : denseEnvF df denv = denv := by
  funext j
  unfold denseEnvF
  cases hj : df j with
  | none => rfl
  | some t => exact (H j t hj).symm

theorem denseBIEval_substF (bi : BusInteraction (DenseExpr p)) (df : VarId → Option (DenseExpr p))
    (denv : VarId → ZMod p) :
    denseBIEval (denseBIsubstF bi df) denv = denseBIEval bi (denseEnvF df denv) := by
  simp only [denseBIsubstF, denseBIEval, DenseExpr.eval_substF, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, DenseExpr.eval_substF]

theorem DenseConstraintSystem.satisfies_substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (denv : VarId → ZMod p) :
    (d.substF df).satisfies bs denv ↔ d.satisfies bs (denseEnvF df denv) := by
  simp only [DenseConstraintSystem.satisfies, DenseConstraintSystem.substF]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c0 hc0 => ?_, fun bi0 hbi0 => ?_⟩
    · have := hc _ (List.mem_map.2 ⟨c0, hc0, rfl⟩)
      rwa [DenseExpr.eval_substF] at this
    · have := hb _ (List.mem_map.2 ⟨bi0, hbi0, rfl⟩)
      rwa [denseBIEval_substF] at this
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hc' => ?_, fun bi hbi' => ?_⟩
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
      rw [DenseExpr.eval_substF]; exact hc c0 hc0
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
      rw [denseBIEval_substF]; exact hb bi0 hbi0

theorem DenseConstraintSystem.admissible_substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (denv : VarId → ZMod p) :
    (d.substF df).admissible bs denv ↔ d.admissible bs (denseEnvF df denv) := by
  unfold DenseConstraintSystem.admissible
  have hmap : (d.substF df).busInteractions.map (fun bi => denseBIEval bi denv)
      = d.busInteractions.map (fun bi => denseBIEval bi (denseEnvF df denv)) := by
    simp only [DenseConstraintSystem.substF, List.map_map]
    exact List.map_congr_left (fun bi _ => denseBIEval_substF bi df denv)
  rw [hmap]

theorem DenseConstraintSystem.sideEffects_substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (denv : VarId → ZMod p) :
    (d.substF df).sideEffects bs denv = d.sideEffects bs (denseEnvF df denv) := by
  unfold DenseConstraintSystem.sideEffects DenseConstraintSystem.substF
  rw [show (fun bi : BusInteraction (DenseExpr p) => bs.isStateful bi.busId) =
        (fun bi => bs.isStateful bi.busId) from rfl]
  rw [filter_map_busId_comm d.busInteractions (fun bi => denseBIsubstF bi df) bs (fun _ => rfl),
    List.map_map]
  refine List.map_congr_left (fun bi _ => ?_)
  simp only [Function.comp_apply, denseBIEval_substF]

/-- Substitution by an entailed map of constants introduces no new occurrence. -/
theorem DenseConstraintSystem.substF_occ_subset (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p))
    (hfv : ∀ (j : VarId) (t : DenseExpr p), df j = some t → ∀ z ∈ t.vars, z ∈ d.occ) :
    ∀ i ∈ (d.substF df).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.substF, List.mem_append,
    List.mem_flatMap] at hi
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    rcases DenseExpr.substF_vars df c0 i hic with h | ⟨j, hj, t, hft, hit⟩
    · exact DenseConstraintSystem.mem_occ_of_constraint hc0 h
    · exact hfv j t hft i hit
  · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
    simp only [denseBIsubstF, denseBIVars, List.mem_append, List.mem_flatMap] at hib
    rcases hib with hm | ⟨e, he, hie⟩
    · rcases DenseExpr.substF_vars df bi0.multiplicity i hm with h | ⟨j, hj, t, hft, hit⟩
      · exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
          simp only [denseBIVars, List.mem_append]; exact Or.inl h)
      · exact hfv j t hft i hit
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      rcases DenseExpr.substF_vars df e0 i hie with h | ⟨j, hj, t, hft, hit⟩
      · exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
          simp only [denseBIVars, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨e0, he0, h⟩)
      · exact hfv j t hft i hit

/-- **Native simultaneous-substitution correctness.** If every satisfying assignment of `d` forces
    `denv j = t.eval denv` for each mapped pair `df j = some t`, and every solution mentions only
    `d`'s occurring variables, then substituting the whole map at once satisfies `DensePassCorrect`
    (no derivations). The native mirror of `ConstraintSystem.substF_correct`. -/
theorem DenseConstraintSystem.substF_denseCorrect (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (isInput : VarId → Bool)
    (H : ∀ denv, d.satisfies bs denv → ∀ j t, df j = some t → denv j = t.eval denv)
    (hfv : ∀ (j : VarId) (t : DenseExpr p), df j = some t → ∀ z ∈ t.vars, z ∈ d.occ) :
    DensePassCorrect isInput d (d.substF df) [] bs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- soundness: `(d.substF df).implies d`
    intro denv hsat
    refine ⟨denseEnvF df denv, (d.satisfies_substF df bs denv).1 hsat, ?_⟩
    rw [d.sideEffects_substF df bs denv]
    exact BusState.equiv_refl _
  · -- invariant preservation
    intro hinv denv hsat bi hbi
    have hsatd : d.satisfies bs (denseEnvF df denv) := (d.satisfies_substF df bs denv).1 hsat
    simp only [DenseConstraintSystem.substF, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    show (denseBIEval (denseBIsubstF bi0 df) denv).multiplicity ≠ 0 →
      bs.breaksInvariant (denseBIEval (denseBIsubstF bi0 df) denv) = false
    rw [denseBIEval_substF]
    exact hinv (denseEnvF df denv) hsatd bi0 hbi0
  · -- no new occurrence at all (hence none introduced at an input column)
    intro i hi _
    exact d.substF_occ_subset df hfv i hi
  · -- completeness with derivations
    intro denv hadm hsat
    have henv : denseEnvF df denv = denv := denseEnvF_eq_self df denv (H denv hsat)
    refine ⟨denv, ?_, ?_, ?_, fun _ _ => rfl, ?_⟩
    · rw [d.satisfies_substF df bs denv, henv]; exact hsat
    · rw [d.admissible_substF df bs denv, henv]; exact hadm
    · rw [d.sideEffects_substF df bs denv, henv]; exact BusState.equiv_refl _
    · -- reconstruction: no derivations, and out.occ ⊆ d.occ, denv' = denv
      intro inputVarIds _
      unfold DenseOutReconstructs
      intro i hi _
      show i ∈ d.occ ∧ denv i = denv i
      exact ⟨d.substF_occ_subset df hfv i hi, rfl⟩

/-! ## Native affine-form evaluation (mirrors `LinExpr.add_eval`/`scale_eval`/`linearize_eval`) -/

theorem DenseLinExpr.add_eval (a b : DenseLinExpr p) (denv : VarId → ZMod p) :
    (a.add b).eval denv = a.eval denv + b.eval denv := by
  simp only [DenseLinExpr.add, DenseLinExpr.eval, List.map_append, List.sum_append]
  ring

theorem DenseLinExpr.scale_eval (k : ZMod p) (a : DenseLinExpr p) (denv : VarId → ZMod p) :
    (a.scale k).eval denv = k * a.eval denv := by
  simp only [DenseLinExpr.scale, DenseLinExpr.eval, List.map_map, mul_add]
  congr 1
  induction a.terms with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih, Function.comp_apply]; ring

theorem denseLinearize_eval (e : DenseExpr p) (l : DenseLinExpr p) (h : denseLinearize e = some l)
    (denv : VarId → ZMod p) : e.eval denv = l.eval denv := by
  induction e generalizing l with
  | const n =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      simp [DenseLinExpr.eval, DenseExpr.eval]
  | var i =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      simp [DenseLinExpr.eval, DenseExpr.eval]
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          rw [DenseExpr.eval, iha la hla, ihb lb hlb, DenseLinExpr.add_eval]
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          have hae : a.eval denv = la.eval denv := iha la hla
          have hbe : b.eval denv = lb.eval denv := ihb lb hlb
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            have hc : la.eval denv = la.const := by
              simp only [DenseLinExpr.eval, List.isEmpty_iff.1 h1, List.map_nil, List.sum_nil,
                add_zero]
            rw [DenseExpr.eval, hae, hbe, DenseLinExpr.scale_eval, hc]
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              have hc : lb.eval denv = lb.const := by
                simp only [DenseLinExpr.eval, List.isEmpty_iff.1 h2, List.map_nil, List.sum_nil,
                  add_zero]
              rw [DenseExpr.eval, hae, hbe, DenseLinExpr.scale_eval, hc, mul_comm]
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-! ## Native term-merge / normalize evaluation (mirrors `mergeTerms_eval`/`LinExpr.norm_eval`) -/

theorem denseAddCoeff_eval (v : VarId) (c : ZMod p) (ts : List (VarId × ZMod p))
    (denv : VarId → ZMod p) :
    ((denseAddCoeff v c ts).map (fun t => t.2 * denv t.1)).sum
      = c * denv v + (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts with
  | nil => simp [denseAddCoeff]
  | cons t rest ih =>
      simp only [denseAddCoeff]
      split
      · next h => subst h; simp only [List.map_cons, List.sum_cons]; ring
      · simp only [List.map_cons, List.sum_cons, ih]; ring

theorem denseFoldAddCoeff_eval (denv : VarId → ZMod p) (ts acc : List (VarId × ZMod p)) :
    ((ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) acc).map (fun t => t.2 * denv t.1)).sum
      = (acc.map (fun t => t.2 * denv t.1)).sum + (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, denseAddCoeff_eval]
      ring

theorem denseMergeTerms_eval (ts : List (VarId × ZMod p)) (denv : VarId → ZMod p) :
    ((denseMergeTerms ts).map (fun t => t.2 * denv t.1)).sum
      = (ts.map (fun t => t.2 * denv t.1)).sum := by
  simp [denseMergeTerms, denseFoldAddCoeff_eval]

theorem denseDropZero_eval (ts : List (VarId × ZMod p)) (denv : VarId → ZMod p) :
    ((ts.filter (fun t => t.2 ≠ 0)).map (fun t => t.2 * denv t.1)).sum
      = (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons, h]
        simp
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
            List.map_cons, List.sum_cons]

theorem DenseLinExpr.norm_eval (l : DenseLinExpr p) (denv : VarId → ZMod p) :
    l.norm.eval denv = l.eval denv := by
  simp only [DenseLinExpr.norm, DenseLinExpr.eval, denseDropZero_eval, denseMergeTerms_eval]

/-! ## Native root soundness (mirrors `rootsOfTerms_sound`/`affineRootsIn_sound`/`rootsIn_sound`) -/

theorem denseRootsOfTerms_sound [Fact p.Prime] (i : VarId) (c : ZMod p)
    (ts : List (VarId × ZMod p)) (roots : List (ZMod p))
    (h : denseRootsOfTerms i c ts = some roots) (denv : VarId → ZMod p)
    (hsum : c + (ts.map (fun t => t.2 * denv t.1)).sum = 0) : denv i ∈ roots := by
  rcases ts with _ | ⟨⟨j, a⟩, _ | ⟨t2, rest⟩⟩
  · simp only [denseRootsOfTerms] at h
    split_ifs at h with hc
    exact absurd (by simpa using hsum) hc
  · simp only [denseRootsOfTerms] at h
    split_ifs at h with hcond
    obtain ⟨rfl, ha, hr⟩ := hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
    have hxy : a * denv j + c = 0 := by linear_combination hsum
    have hcancel : a * denv j = a * (-(a⁻¹ * c)) := by
      rw [eq_neg_of_add_eq_zero_left hxy, ← eq_neg_of_add_eq_zero_left hr]
    simpa using mul_left_cancel₀ ha hcancel
  · exact absurd h (by simp [denseRootsOfTerms])

theorem denseAffineRootsIn_sound [Fact p.Prime] (i : VarId) (e : DenseExpr p)
    (roots : List (ZMod p)) (h : denseAffineRootsIn i e = some roots)
    (denv : VarId → ZMod p) (he : e.eval denv = 0) : denv i ∈ roots := by
  simp only [denseAffineRootsIn, Option.bind_eq_some_iff] at h
  obtain ⟨l, hlin, hroot⟩ := h
  have heval : l.norm.const + (l.norm.terms.map (fun t => t.2 * denv t.1)).sum = 0 := by
    have h1 : l.norm.eval denv = 0 := by
      rw [DenseLinExpr.norm_eval, ← denseLinearize_eval e l hlin]; exact he
    simpa [DenseLinExpr.eval] using h1
  exact denseRootsOfTerms_sound i l.norm.const l.norm.terms roots hroot denv heval

theorem denseRootsIn_sound [Fact p.Prime] (i : VarId) (e : DenseExpr p) (roots : List (ZMod p))
    (h : denseRootsIn i e = some roots) (denv : VarId → ZMod p) (he : e.eval denv = 0) :
    denv i ∈ roots := by
  induction e generalizing roots with
  | const n => exact denseAffineRootsIn_sound i _ roots h denv he
  | var y => exact denseAffineRootsIn_sound i _ roots h denv he
  | add a b _ _ => exact denseAffineRootsIn_sound i _ roots h denv he
  | mul a b iha ihb =>
    rw [denseRootsIn] at h
    split at h
    · rename_i r haff
      simp only [Option.some.injEq] at h
      subst h
      exact denseAffineRootsIn_sound i _ _ haff denv he
    · rename_i haff
      split at h
      · rename_i ra rb hra hrb
        simp only [Option.some.injEq] at h
        subst h
        have he' : a.eval denv * b.eval denv = 0 := he
        rcases mul_eq_zero.mp he' with hz | hz
        · exact List.mem_append.2 (Or.inl (iha ra hra hz))
        · exact List.mem_append.2 (Or.inr (ihb rb hrb hz))
      all_goals exact absurd h (by simp)

/-! ## Native constant / fact soundness -/

theorem DenseExpr.constValue?_sound (e : DenseExpr p) (c : ZMod p) (h : e.constValue? = some c)
    (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  unfold DenseExpr.constValue? at h
  cases hf : e.fold with
  | const n => rw [hf] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | var j => rw [hf] at h; simp at h
  | add a b => rw [hf] at h; simp at h
  | mul a b => rw [hf] at h; simp at h

theorem denseIsVarOf_sound (i : VarId) (e : DenseExpr p) (h : denseIsVarOf i e = true) :
    e = DenseExpr.var i := by
  cases e with
  | var j => simp only [denseIsVarOf, decide_eq_true_eq] at h; rw [h]
  | const n => simp [denseIsVarOf] at h
  | add a b => simp [denseIsVarOf] at h
  | mul a b => simp [denseIsVarOf] at h

theorem denseVarSlot_sound (i : VarId) (payload : List (DenseExpr p)) (slot : Nat)
    (h : denseVarSlot i payload = some slot) : payload[slot]? = some (.var i) := by
  induction payload generalizing slot with
  | nil => exact absurd h (by simp [denseVarSlot])
  | cons e rest ih =>
    rw [denseVarSlot] at h
    split_ifs at h with hv
    · simp only [Option.some.injEq] at h
      subst h
      simpa using denseIsVarOf_sound i e hv
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨s, hs, rfl⟩ := h
      simpa using ih s hs

theorem denseMatches_evalPattern (payload : List (DenseExpr p)) (denv : VarId → ZMod p) :
    Matches (payload.map (fun e => e.eval denv)) (payload.map DenseExpr.constValue?) := by
  refine ⟨by simp, ?_⟩
  intro slot c hc
  rw [List.getElem?_map] at hc
  rw [List.getElem?_map]
  cases he : payload[slot]? with
  | none => rw [he] at hc; simp at hc
  | some e =>
      rw [he] at hc
      simp only [Option.map_some, Option.some.injEq] at hc ⊢
      exact e.constValue?_sound c hc denv

theorem denseInteractionBound_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) (bound : Nat)
    (h : denseInteractionBound bs facts bi i = some bound) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (denv i).val < bound := by
  unfold denseInteractionBound at h
  split at h
  · exact absurd h (by simp)
  · rename_i mval hm
    split_ifs at h with hmz
    split at h
    · exact absurd h (by simp)
    · rename_i slot hslot
      have hmeval : (denseBIEval bi denv).multiplicity = mval :=
        bi.multiplicity.constValue?_sound mval hm denv
      have hviol : bs.violatesConstraint (denseBIEval bi denv) = false := by
        apply hob; rw [hmeval]; exact hmz
      have hgete : bi.payload[slot]? = some (.var i) := denseVarSlot_sound i bi.payload slot hslot
      have hget : (denseBIEval bi denv).payload[slot]? = some (denv i) := by
        show (bi.payload.map (fun e => e.eval denv))[slot]? = some (denv i)
        rw [List.getElem?_map, hgete]
        rfl
      rw [← hmeval] at h
      exact facts.slotBound_sound (denseBIEval bi denv)
        (bi.payload.map DenseExpr.constValue?) slot bound (denv i) h
        (denseMatches_evalPattern bi.payload denv) hviol hget

theorem denseInteractionDomainF_sound [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) (dm : FiniteDomain p)
    (h : denseInteractionDomainF bs facts bi i = some dm) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    denv i ∈ dm.toList := by
  unfold denseInteractionDomainF at h
  split at h
  · exact absurd h (by simp)
  · rename_i bound hB
    split_ifs at h with hcap
    simp only [Option.some.injEq] at h
    subst h
    show denv i ∈ (List.range bound).map (Nat.cast : Nat → ZMod p)
    exact mem_range_cast (denv i) bound
      (denseInteractionBound_sound bs facts bi i bound hB denv hob)

/-! ## Native domain-table soundness -/

/-- Native soundness of a dense domain table at a fixed environment: every stored domain contains the
    environment's value for its variable. -/
def DenseTableSoundAt (denv : VarId → ZMod p) (T : DenseDomainTable p) : Prop :=
  ∀ i dm, T.map[i]? = some dm → denv i ∈ dm.toList

theorem DenseTableSoundAt.empty (denv : VarId → ZMod p) :
    DenseTableSoundAt denv (DenseDomainTable.empty : DenseDomainTable p) := by
  intro i dm h
  simp only [DenseDomainTable.empty, Std.HashMap.getElem?_empty] at h
  exact absurd h (by simp)

theorem DenseDomainTable.insertEntry_soundAt {denv : VarId → ZMod p} {T : DenseDomainTable p}
    {i0 : VarId} {d0 : FiniteDomain p} (hd : denv i0 ∈ d0.toList) (hT : DenseTableSoundAt denv T) :
    DenseTableSoundAt denv (T.insertEntry i0 d0) := by
  intro i dm hi
  rw [DenseDomainTable.insertEntry_map] at hi
  split_ifs at hi with hkeep
  · rw [Std.HashMap.getElem?_insert] at hi
    by_cases hii : i0 = i
    · rw [if_pos (by simpa using hii)] at hi
      simp only [Option.some.injEq] at hi
      subst hii; subst hi; exact hd
    · rw [if_neg (by simpa using hii)] at hi
      exact hT i dm hi
  · exact hT i dm hi

theorem denseAddConstraintVars_soundAt [Fact p.Prime] {denv : VarId → ZMod p} (c : DenseExpr p)
    (hc0 : c.eval denv = 0) :
    ∀ (xs : List VarId) (T : DenseDomainTable p), DenseTableSoundAt denv T →
      DenseTableSoundAt denv (denseAddConstraintVars c xs T) := by
  intro xs
  induction xs with
  | nil => intro T hT; exact hT
  | cons i is ih =>
      intro T hT
      unfold denseAddConstraintVars
      split
      · rename_i d hr
        exact ih _ (DenseDomainTable.insertEntry_soundAt
          (d0 := .explicit d) (denseRootsIn_sound i c d hr denv hc0) hT)
      · exact ih _ hT

theorem denseAddConstraintDoms_soundAt [Fact p.Prime] {denv : VarId → ZMod p} :
    ∀ (dcs : List (DenseExpr p)), (∀ c ∈ dcs, c.eval denv = 0) →
      ∀ (T : DenseDomainTable p), DenseTableSoundAt denv T →
        DenseTableSoundAt denv (denseAddConstraintDoms dcs T) := by
  intro dcs
  induction dcs with
  | nil => intro _ T hT; exact hT
  | cons c rest ih =>
      intro hcs T hT
      have hc0 : c.eval denv = 0 := hcs c (List.mem_cons_self ..)
      have hrest : ∀ c' ∈ rest, c'.eval denv = 0 := fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
      unfold denseAddConstraintDoms
      apply ih hrest
      split
      · exact denseAddConstraintVars_soundAt c hc0 c.vars.dedup T hT
      · exact hT

theorem denseAddBusVars_soundAt [NeZero p] {denv : VarId → ZMod p} (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    ∀ (xs : List VarId) (T : DenseDomainTable p), DenseTableSoundAt denv T →
      DenseTableSoundAt denv (denseAddBusVars bs facts bi xs T) := by
  intro xs
  induction xs with
  | nil => intro T hT; exact hT
  | cons i is ih =>
      intro T hT
      unfold denseAddBusVars
      split
      · rename_i dm hr
        exact ih _ (DenseDomainTable.insertEntry_soundAt
          (denseInteractionDomainF_sound bs facts bi i dm hr denv hob) hT)
      · exact ih _ hT

theorem denseAddBusDoms_soundAt [NeZero p] {denv : VarId → ZMod p} (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    ∀ (dbis : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ dbis, (denseBIEval bi denv).multiplicity ≠ 0 →
        bs.violatesConstraint (denseBIEval bi denv) = false) →
      ∀ (T : DenseDomainTable p), DenseTableSoundAt denv T →
        DenseTableSoundAt denv (denseAddBusDoms bs facts dbis T) := by
  intro dbis
  induction dbis with
  | nil => intro _ T hT; exact hT
  | cons bi rest ih =>
      intro hob T hT
      have hbi : (denseBIEval bi denv).multiplicity ≠ 0 →
          bs.violatesConstraint (denseBIEval bi denv) = false := hob bi (List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest, (denseBIEval b denv).multiplicity ≠ 0 →
          bs.violatesConstraint (denseBIEval b denv) = false :=
        fun b hb => hob b (List.mem_cons_of_mem _ hb)
      unfold denseAddBusDoms
      exact ih hrest _ (denseAddBusVars_soundAt bs facts bi hbi _ T hT)

/-- **Native domain-table soundness.** Building the domain table from a system `d` satisfied by
    `denv` yields a table every stored domain of which contains `denv`'s value for its variable. -/
theorem denseDomainTable_soundAt [Fact p.Prime] [NeZero p] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (denv : VarId → ZMod p)
    (hsat : d.satisfies bs denv) :
    DenseTableSoundAt denv
      (denseAddBusDoms bs facts d.busInteractions
        (denseAddConstraintDoms d.algebraicConstraints DenseDomainTable.empty)) := by
  apply denseAddBusDoms_soundAt bs facts d.busInteractions (fun bi hbi => hsat.2 bi hbi)
  exact denseAddConstraintDoms_soundAt d.algebraicConstraints (fun c hc => hsat.1 c hc)
    DenseDomainTable.empty (DenseTableSoundAt.empty denv)

/-! ## Value-only lazy enumeration = eager fold over the value-only assignment product -/

/-- All value-only assignments in the Cartesian product of the domains (mirrors `assignments`). -/
def assignmentsV : List (FiniteDomain p) → List (List (ZMod p))
  | [] => [[]]
  | d :: rest => (assignmentsV rest).flatMap (fun a => d.toList.map (fun v => v :: a))

/-- `denseBoxFoldV` streams exactly the eager fold over `assignmentsV` (mirrors `boxFold_eq`). -/
theorem denseBoxFoldV_eq {β : Type} (f : β → List (ZMod p) → β) (stop : β → Bool)
    (doms : List (FiniteDomain p)) (acc : β) :
    denseBoxFoldV f stop doms acc = foldlStop f stop (assignmentsV doms) acc := by
  induction doms generalizing f acc with
  | nil => simp only [denseBoxFoldV, assignmentsV, foldlStop]
  | cons d rest ih =>
    rw [denseBoxFoldV, ih]
    show foldlStop (fun acc' a => d.foldElts (fun acc'' v => f acc'' (v :: a)) stop acc') stop
        (assignmentsV rest) acc
      = foldlStop f stop (assignmentsV (d :: rest)) acc
    rw [show assignmentsV (d :: rest)
          = (assignmentsV rest).flatMap (fun a => d.toList.map (fun v => v :: a)) from rfl,
      ← foldlStop_flatMap f stop (fun a => d.toList.map (fun v => v :: a))]
    apply foldlStop_congr
    intro acc' a
    show d.foldElts (fun acc'' v => f acc'' (v :: a)) stop acc'
      = foldlStop f stop (d.toList.map (fun v => v :: a)) acc'
    rw [FiniteDomain.foldElts_eq, foldlStop_map]

/-- The restriction of a satisfying `denv` to a keyed domain list is one of the value-only enumerated
    assignments (mirrors `mem_assignments`). -/
theorem mem_assignmentsV (denv : VarId → ZMod p) :
    ∀ (fdoms : List (VarId × FiniteDomain p)), (∀ kd ∈ fdoms, denv kd.1 ∈ kd.2.toList) →
      (fdoms.map (fun kd => denv kd.1)) ∈ assignmentsV (fdoms.map Prod.snd) := by
  intro fdoms
  induction fdoms with
  | nil => intro _; simp [assignmentsV]
  | cons kd rest ih =>
    intro h
    simp only [List.map_cons, assignmentsV, List.mem_flatMap]
    refine ⟨rest.map (fun kd => denv kd.1),
      ih (fun kd' hkd' => h kd' (List.mem_cons_of_mem _ hkd')), ?_⟩
    exact List.mem_map.2 ⟨denv kd.1, h kd (List.mem_cons_self ..), rfl⟩

/-! ## The value-only scan as a plain (no-stop) fold, and its intersection certificate -/

/-- One value-only scan step from a *tracking* state (mirrors `denseScanStepV`'s `some` branch). -/
def denseStepSomeV (surv : List (ZMod p) → Bool) (cands : DenseCandsV p) (pt : List (ZMod p)) :
    DenseCandsV p :=
  if surv pt = true then
    cands.zipWith (fun c v => match c with | some cv => if cv = v then some cv else none | none => none) pt
  else cands

theorem denseScanStepV_some (surv : List (ZMod p) → Bool) (cands : DenseCandsV p)
    (pt : List (ZMod p)) : denseScanStepV surv (some cands) pt = some (denseStepSomeV surv cands pt) := by
  cases h : surv pt
  · simp [denseScanStepV, denseStepSomeV, h]
  · simp [denseScanStepV, denseStepSomeV, h]; rfl

theorem denseScanStepV_none_pos (surv : List (ZMod p) → Bool) (pt : List (ZMod p))
    (hs : surv pt = true) : denseScanStepV surv none pt = some (pt.map some) := by
  simp only [denseScanStepV, if_pos hs]

theorem denseScanStepV_none_neg (surv : List (ZMod p) → Bool) (pt : List (ZMod p))
    (hs : ¬ surv pt = true) : denseScanStepV surv none pt = none := by
  simp only [denseScanStepV, if_neg hs]

/-- The plain (no-stop) fold from a tracking state stays a tracking state. -/
theorem foldl_denseScanStep_some_eq (surv : List (ZMod p) → Bool) :
    ∀ (pts : List (List (ZMod p))) (cands : DenseCandsV p),
      pts.foldl (denseScanStepV surv) (some cands) = some (pts.foldl (denseStepSomeV surv) cands) := by
  intro pts
  induction pts with
  | nil => intro cands; rfl
  | cons pt rest ih => intro cands; rw [List.foldl_cons, List.foldl_cons, denseScanStepV_some, ih]

/-- One tracking step forces a `some c` slot to agree with the point (the intersection semantics). -/
theorem denseStepSomeV_getElem (surv : List (ZMod p) → Bool) (cands : DenseCandsV p)
    (pt : List (ZMod p)) (n : Nat) (c : ZMod p) (hs : surv pt = true)
    (h : (denseStepSomeV surv cands pt)[n]? = some (some c)) :
    cands[n]? = some (some c) ∧ pt[n]? = some c := by
  unfold denseStepSomeV at h
  rw [if_pos hs, List.getElem?_zipWith] at h
  cases hcn : cands[n]? with
  | none => rw [hcn] at h; simp at h
  | some a =>
    cases hpn : pt[n]? with
    | none => rw [hcn, hpn] at h; simp at h
    | some b =>
      rw [hcn, hpn] at h
      cases a with
      | none => simp at h
      | some cv =>
        simp only [Option.some.injEq] at h
        split_ifs at h with hcv
        simp only [Option.some.injEq] at h
        exact ⟨by rw [h], by rw [← hcv, h]⟩

/-- Intersection certificate for the plain fold from a tracking state. -/
theorem denseStepSomeV_forces (surv : List (ZMod p) → Bool) (n : Nat) (c : ZMod p) :
    ∀ (pts : List (List (ZMod p))) (cands : DenseCandsV p),
      (pts.foldl (denseStepSomeV surv) cands)[n]? = some (some c) →
      cands[n]? = some (some c) ∧ ∀ pt ∈ pts, surv pt = true → pt[n]? = some c := by
  intro pts
  induction pts with
  | nil => intro cands h; exact ⟨h, by simp⟩
  | cons pt rest ih =>
    intro cands h
    rw [List.foldl_cons] at h
    obtain ⟨hstep, hrest⟩ := ih (denseStepSomeV surv cands pt) h
    by_cases hs : surv pt = true
    · obtain ⟨hcands, hpt⟩ := denseStepSomeV_getElem surv cands pt n c hs hstep
      refine ⟨hcands, ?_⟩
      intro pt' hpt' hs'
      rcases List.mem_cons.1 hpt' with rfl | hpt'
      · exact hpt
      · exact hrest pt' hpt' hs'
    · have hstep' : denseStepSomeV surv cands pt = cands := by simp only [denseStepSomeV, if_neg hs]
      rw [hstep'] at hstep
      refine ⟨hstep, ?_⟩
      intro pt' hpt' hs'
      rcases List.mem_cons.1 hpt' with rfl | hpt'
      · exact absurd hs' hs
      · exact hrest pt' hpt' hs'

/-- Intersection certificate for the plain fold from the *searching* state `none`. -/
theorem foldl_denseScanStep_forces (surv : List (ZMod p) → Bool) (n : Nat) (c : ZMod p) :
    ∀ (pts : List (List (ZMod p))) (mask : DenseCandsV p),
      pts.foldl (denseScanStepV surv) none = some mask → mask[n]? = some (some c) →
      ∀ pt ∈ pts, surv pt = true → pt[n]? = some c := by
  intro pts
  induction pts with
  | nil => intro mask h; simp at h
  | cons pt rest ih =>
    intro mask h hmask
    rw [List.foldl_cons] at h
    by_cases hs : surv pt = true
    · rw [denseScanStepV_none_pos surv pt hs, foldl_denseScanStep_some_eq] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hback, hrest⟩ := denseStepSomeV_forces surv n c rest (pt.map some) hmask
      intro pt'' hpt'' hs''
      rcases List.mem_cons.1 hpt'' with rfl | hpt''
      · rw [List.getElem?_map, Option.map_eq_some_iff] at hback
        obtain ⟨b, hb, hbc⟩ := hback
        rw [hb]; exact hbc
      · exact hrest pt'' hpt'' hs''
    · rw [denseScanStepV_none_neg surv pt hs] at h
      intro pt'' hpt'' hs''
      rcases List.mem_cons.1 hpt'' with rfl | hpt''
      · exact absurd hs'' hs
      · exact ih mask h hmask pt'' hpt'' hs''

/-! ## Bridging the early-stop fold to the plain fold -/

theorem foldlStop_eq_foldl_or_stop {α β : Type} (f : β → α → β) (stop : β → Bool) :
    ∀ (l : List α) (acc : β),
      foldlStop f stop l acc = l.foldl f acc ∨ stop (foldlStop f stop l acc) = true := by
  intro l
  induction l with
  | nil => intro acc; exact Or.inl rfl
  | cons a rest ih =>
    intro acc
    by_cases hs : stop acc = true
    · right; rw [foldlStop_stopped f stop (a :: rest) acc hs]; exact hs
    · rw [foldlStop, if_neg hs, List.foldl_cons]; exact ih (f acc a)

/-- The early-stop scan from a tracking state is never `none`. -/
theorem foldlStop_denseScanStep_isSome (surv : List (ZMod p) → Bool) :
    ∀ (pts : List (List (ZMod p))) (cands : DenseCandsV p),
      (foldlStop (denseScanStepV surv) denseScanStopV pts (some cands)).isSome = true := by
  intro pts
  induction pts with
  | nil => intro cands; rfl
  | cons pt rest ih =>
    intro cands
    rw [foldlStop]
    by_cases hstop : denseScanStopV (some cands) = true
    · rw [if_pos hstop]; rfl
    · rw [if_neg hstop, denseScanStepV_some]; exact ih (denseStepSomeV surv cands pt)

/-- If the early-stop scan from the searching state returns `none`, no enumerated point survives. -/
theorem foldlStop_denseScanStep_none (surv : List (ZMod p) → Bool) :
    ∀ (pts : List (List (ZMod p))),
      foldlStop (denseScanStepV surv) denseScanStopV pts none = none → ∀ pt ∈ pts, surv pt = false := by
  intro pts
  induction pts with
  | nil => intro _ pt hpt; simp at hpt
  | cons pt rest ih =>
    intro h pt' hpt'
    rw [foldlStop, if_neg (by simp [denseScanStopV] : ¬ denseScanStopV (none : Option (DenseCandsV p)) = true)] at h
    by_cases hs : surv pt = true
    · exfalso
      rw [denseScanStepV_none_pos surv pt hs] at h
      have hsome := foldlStop_denseScanStep_isSome surv rest (pt.map some)
      rw [h] at hsome; simp at hsome
    · rw [denseScanStepV_none_neg surv pt hs] at h
      rcases List.mem_cons.1 hpt' with rfl | hpt'
      · exact Bool.eq_false_iff.mpr hs
      · exact ih h pt' hpt'

/-- **Value-only scan `none` case.** No point of the box survives the scanned predicate. -/
theorem denseScanBoxV_none_unsat (surv : List (ZMod p) → Bool) (doms : List (FiniteDomain p))
    (h : denseScanBoxV surv doms = none) : ∀ pt ∈ assignmentsV doms, surv pt = false := by
  rw [denseScanBoxV, denseBoxFoldV_eq] at h
  exact foldlStop_denseScanStep_none surv (assignmentsV doms) h

/-- **Value-only scan `some` case.** A `some c` in the returned mask is agreed on by every surviving
    enumerated point. -/
theorem denseScanBoxV_forces (surv : List (ZMod p) → Bool) (doms : List (FiniteDomain p))
    (mask : DenseCandsV p) (h : denseScanBoxV surv doms = some mask) (n : Nat) (c : ZMod p)
    (hmask : mask[n]? = some (some c)) :
    ∀ pt ∈ assignmentsV doms, surv pt = true → pt[n]? = some c := by
  rw [denseScanBoxV, denseBoxFoldV_eq] at h
  have hne : denseScanStopV (some mask) = false := by
    rw [denseScanStopV, Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have hmem : (some c : Option (ZMod p)) ∈ mask := List.mem_of_getElem? hmask
    have := hall (some c) hmem
    simp at this
  rcases foldlStop_eq_foldl_or_stop (denseScanStepV surv) denseScanStopV (assignmentsV doms) none with
    heq | hstop
  · rw [heq] at h
    exact foldl_denseScanStep_forces surv n c (assignmentsV doms) mask h hmask
  · rw [h, hne] at hstop; exact absurd hstop (by simp)

/-! ## Value-only compiled evaluation and restriction survival -/

/-- The value-only environment reads a key's value from the positionally-aligned point. -/
theorem denseEnvOfKeysV_map (denv : VarId → ZMod p) :
    ∀ (keys : List VarId) (y : VarId), y ∈ keys → denseEnvOfKeysV keys (keys.map denv) y = denv y := by
  intro keys
  induction keys with
  | nil => intro y hy; simp at hy
  | cons x rest ih =>
    intro y hy
    rw [List.map_cons]
    show denseEnvOfKeysV (x :: rest) (denv x :: rest.map denv) y = denv y
    rw [denseEnvOfKeysV]
    by_cases hyx : (y == x) = true
    · have hyx' : y = x := by simpa using hyx
      rw [if_pos hyx, hyx']
    · rw [if_neg hyx]
      rcases List.mem_cons.1 hy with rfl | hy'
      · simp at hyx
      · exact ih y hy'

/-- Positional lookup on a value-only point matches the keyed environment lookup. -/
theorem denseVarIx_lookupV_env (keys : List VarId) (pt : List (ZMod p)) (y : VarId) (idx : Nat)
    (h : denseVarIx keys y = some idx) :
    denseLookupIxV pt idx = denseEnvOfKeysV keys pt y := by
  induction keys generalizing pt idx with
  | nil => simp [denseVarIx] at h
  | cons x rest ih =>
    rw [denseVarIx] at h
    cases pt with
    | nil => rfl
    | cons v vs =>
      split_ifs at h with hyx
      · simp only [Option.some.injEq] at h; subst h
        show denseLookupIxV (v :: vs) 0 = denseEnvOfKeysV (x :: rest) (v :: vs) y
        rw [denseLookupIxV, denseEnvOfKeysV, if_pos hyx]
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        show denseLookupIxV (v :: vs) (j + 1) = denseEnvOfKeysV (x :: rest) (v :: vs) y
        rw [denseLookupIxV, denseEnvOfKeysV, if_neg hyx]
        exact ih vs j hj

/-- Compiled value-only evaluation agrees with the keyed-environment evaluation of the source. -/
theorem denseCompileE_evalV (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (e : DenseExpr p) (ic : IExpr p), denseCompileE keys e = some ic →
      denseIExprEvalWithV add mul pt ic = e.eval (denseEnvOfKeysV keys pt) := by
  intro e
  induction e with
  | const n => intro ic h; simp only [denseCompileE, Option.some.injEq] at h; subst h; rfl
  | var y =>
      intro ic h
      rw [denseCompileE, Option.map_eq_some_iff] at h
      obtain ⟨idx, hidx, rfl⟩ := h
      show denseIExprEvalWithV add mul pt (.ix idx) = denseEnvOfKeysV keys pt y
      rw [denseIExprEvalWithV]
      exact denseVarIx_lookupV_env keys pt y idx hidx
  | add a b iha ihb =>
      intro ic h
      cases ha : denseCompileE keys a with
      | none => rw [denseCompileE, ha] at h; simp at h
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [denseCompileE, ha, hb] at h; simp at h
        | some ib =>
          rw [denseCompileE, ha, hb] at h; simp only [Option.some.injEq] at h; subst h
          show denseIExprEvalWithV add mul pt (.add ia ib) = (a.add b).eval (denseEnvOfKeysV keys pt)
          rw [denseIExprEvalWithV, DenseExpr.eval, hadd, iha ia ha, ihb ib hb]
  | mul a b iha ihb =>
      intro ic h
      cases ha : denseCompileE keys a with
      | none => rw [denseCompileE, ha] at h; simp at h
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [denseCompileE, ha, hb] at h; simp at h
        | some ib =>
          rw [denseCompileE, ha, hb] at h; simp only [Option.some.injEq] at h; subst h
          show denseIExprEvalWithV add mul pt (.mul ia ib) = (a.mul b).eval (denseEnvOfKeysV keys pt)
          rw [denseIExprEvalWithV, DenseExpr.eval, hmul, iha ia ha, ihb ib hb]

/-- Compiled-list zero-check agrees with the source list's (value-only). -/
theorem denseCompileEs_allV (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (es : List (DenseExpr p)) (ces : List (IExpr p)), denseCompileEs keys es = some ces →
      ces.all (fun ie => isZero (denseIExprEvalWithV add mul pt ie))
        = es.all (fun e => decide (e.eval (denseEnvOfKeysV keys pt) = 0)) := by
  intro es
  induction es with
  | nil => intro ces h; rw [denseCompileEs] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    intro ces h
    cases he : denseCompileE keys e with
    | none => rw [denseCompileEs, he] at h; simp at h
    | some ie =>
      cases hr : denseCompileEs keys rest with
      | none => rw [denseCompileEs, he, hr] at h; simp at h
      | some irest =>
        rw [denseCompileEs, he, hr] at h; simp only [Option.some.injEq] at h; subst h
        rw [List.all_cons, List.all_cons, ih irest hr,
          denseCompileE_evalV add mul hadd hmul keys pt e ie he, hz]

/-- Compiled payload evaluation agrees with the fallback payload (value-only). -/
theorem denseCompileEs_mapV (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (es : List (DenseExpr p)) (ces : List (IExpr p)), denseCompileEs keys es = some ces →
      ces.map (fun ie => denseIExprEvalWithV add mul pt ie)
        = es.map (fun e => e.eval (denseEnvOfKeysV keys pt)) := by
  intro es
  induction es with
  | nil => intro ces h; rw [denseCompileEs] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    intro ces h
    cases he : denseCompileE keys e with
    | none => rw [denseCompileEs, he] at h; simp at h
    | some ie =>
      cases hr : denseCompileEs keys rest with
      | none => rw [denseCompileEs, he, hr] at h; simp at h
      | some irest =>
        rw [denseCompileEs, he, hr] at h; simp only [Option.some.injEq] at h; subst h
        rw [List.map_cons, List.map_cons, ih irest hr,
          denseCompileE_evalV add mul hadd hmul keys pt e ie he]

/-- Compiled interaction evaluation agrees with the fallback message (value-only). -/
theorem denseCompileBi_evalWithV (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (keys : List VarId) (pt : List (ZMod p)) (bi : BusInteraction (DenseExpr p)) (cbi : CBi p)
    (h : denseCompileBi keys bi = some cbi) :
    denseCBiEvalWithV add mul cbi pt
      = { busId := bi.busId,
          multiplicity := bi.multiplicity.eval (denseEnvOfKeysV keys pt),
          payload := bi.payload.map (fun e => e.eval (denseEnvOfKeysV keys pt)) } := by
  cases hm : denseCompileE keys bi.multiplicity with
  | none => rw [denseCompileBi, hm] at h; simp at h
  | some m =>
    cases hpl : denseCompileEs keys bi.payload with
    | none => rw [denseCompileBi, hm, hpl] at h; simp at h
    | some pl =>
      rw [denseCompileBi, hm, hpl] at h; simp only [Option.some.injEq] at h; subst h
      unfold denseCBiEvalWithV
      dsimp only
      rw [denseCompileE_evalV add mul hadd hmul keys pt bi.multiplicity m hm,
        denseCompileEs_mapV add mul hadd hmul keys pt bi.payload pl hpl]

/-- Compiled-list obligation check agrees with the source list's (value-only). -/
theorem denseCompileBis_allV (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p) (keys : List VarId)
    (pt : List (ZMod p)) :
    ∀ (bis : List (BusInteraction (DenseExpr p))) (cbis : List (CBi p)),
      denseCompileBis keys bis = some cbis →
      cbis.all (fun cbi => let v := denseCBiEvalWithV add mul cbi pt;
          isZero v.multiplicity || !bs.violatesConstraint v)
        = bis.all (fun bi =>
          let v : BusInteraction (ZMod p) :=
            { busId := bi.busId,
              multiplicity := bi.multiplicity.eval (denseEnvOfKeysV keys pt),
              payload := bi.payload.map (fun e => e.eval (denseEnvOfKeysV keys pt)) };
          decide (v.multiplicity = 0) || !bs.violatesConstraint v) := by
  intro bis
  induction bis with
  | nil => intro cbis h; rw [denseCompileBis] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | cons bi rest ih =>
    intro cbis h
    cases hb : denseCompileBi keys bi with
    | none => rw [denseCompileBis, hb] at h; simp at h
    | some cbi =>
      cases hr : denseCompileBis keys rest with
      | none => rw [denseCompileBis, hb, hr] at h; simp at h
      | some crest =>
        rw [denseCompileBis, hb, hr] at h; simp only [Option.some.injEq] at h; subst h
        rw [List.all_cons, List.all_cons, ih crest hr]
        simp only [denseCompileBi_evalWithV add mul hadd hmul keys pt bi cbi hb, hz]

/-- The value-only compiled survivor predicate under compile success agrees with the uncompiled one. -/
theorem denseSurvivesAllCWV_eq (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (ces : List (IExpr p))
    (cbis : List (CBi p)) (pt : List (ZMod p))
    (hce : denseCompileEs keys es = some ces) (hcb : denseCompileBis keys bis = some cbis) :
    denseSurvivesAllCWV add mul isZero bs ces cbis pt = denseSurvivesAllMV bs es bis keys pt := by
  unfold denseSurvivesAllCWV denseSurvivesAllMV
  congr 1
  · exact denseCompileEs_allV add mul hadd hmul isZero hz keys pt es ces hce
  · exact denseCompileBis_allV add mul hadd hmul isZero hz bs keys pt bis cbis hcb

/-- The value-only compiled survivor predicate agrees with the uncompiled one on every point. -/
theorem denseCompiledSurvV_eq (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (pt : List (ZMod p)) :
    denseCompiledSurvV bs es bis keys pt = denseSurvivesAllMV bs es bis keys pt := by
  unfold denseCompiledSurvV
  cases hce : denseCompileEs keys es with
  | none => rfl
  | some ces =>
    cases hcb : denseCompileBis keys bis with
    | none => rfl
    | some cbis =>
      exact denseSurvivesAllCWV_eq _ _ (fun _ _ => rfl) (fun _ _ => rfl) _ (fun _ => rfl)
        bs es bis keys ces cbis pt hce hcb

/-- The restriction of a satisfying `denv` survives the covered-item predicate (value-only). -/
theorem denseSurvivesAllMV_restriction (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (denv : VarId → ZMod p)
    (hes0 : ∀ e ∈ es, e.eval denv = 0)
    (hbi0 : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false)
    (hesk : ∀ e ∈ es, ∀ i ∈ e.vars, i ∈ keys)
    (hbik : ∀ bi ∈ bis, ∀ i ∈ denseBIVars bi, i ∈ keys) :
    denseSurvivesAllMV bs es bis keys (keys.map denv) = true := by
  unfold denseSurvivesAllMV
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro e he
    have hcongr : e.eval (denseEnvOfKeysV keys (keys.map denv)) = e.eval denv :=
      DenseExpr.eval_congr e _ _ (fun i hi => denseEnvOfKeysV_map denv keys i (hesk e he i hi))
    simp only [decide_eq_true_eq, hcongr]
    exact hes0 e he
  · rw [List.all_eq_true]
    intro bi hbi
    have hbe : denseBIEval bi (denseEnvOfKeysV keys (keys.map denv)) = denseBIEval bi denv :=
      denseBIEval_congr bi _ _ (fun i hi => denseEnvOfKeysV_map denv keys i (hbik bi hbi i hi))
    show (decide ((denseBIEval bi (denseEnvOfKeysV keys (keys.map denv))).multiplicity = 0)
      || !bs.violatesConstraint (denseBIEval bi (denseEnvOfKeysV keys (keys.map denv)))) = true
    rw [hbe]
    by_cases hm : (denseBIEval bi denv).multiplicity = 0
    · simp [hm]
    · have hd : decide ((denseBIEval bi denv).multiplicity = 0) = false := decide_eq_false hm
      rw [hd, Bool.false_or]
      simpa using hbi0 bi hbi hm

/-- The restriction survives the compiled survivor predicate (value-only). -/
theorem denseCompiledSurvV_restriction (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (denv : VarId → ZMod p)
    (hes0 : ∀ e ∈ es, e.eval denv = 0)
    (hbi0 : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false)
    (hesk : ∀ e ∈ es, ∀ i ∈ e.vars, i ∈ keys)
    (hbik : ∀ bi ∈ bis, ∀ i ∈ denseBIVars bi, i ∈ keys) :
    denseCompiledSurvV bs es bis keys (keys.map denv) = true := by
  rw [denseCompiledSurvV_eq]
  exact denseSurvivesAllMV_restriction bs es bis keys denv hes0 hbi0 hesk hbik

/-! ## `forcedOver` entailment (value-only) -/

/-- The dense domain table's `doms` entries are individually present in the table. -/
theorem DenseDomainTable.doms_getElem (T : DenseDomainTable p) :
    ∀ (xs : List VarId) (fdoms : List (VarId × FiniteDomain p)),
      T.doms xs = some fdoms → ∀ kd ∈ fdoms, T.map[kd.1]? = some kd.2 := by
  intro xs
  induction xs with
  | nil =>
      intro fdoms h kd hkd
      simp only [DenseDomainTable.doms, Option.some.injEq] at h; subst h; simp at hkd
  | cons x rest ih =>
    intro fdoms h kd hkd
    rw [DenseDomainTable.doms] at h
    cases hd : T.map[x]? with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some dm =>
      cases hr : T.doms rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some ds' =>
        rw [hd, hr] at h; simp only [Option.some.injEq] at h; subst h
        rcases List.mem_cons.1 hkd with rfl | hkd'
        · exact hd
        · exact ih ds' hr kd hkd'

/-- A pair produced by `(keys.zip cands).filterMap (·.2.map …)` sits at a common index with a
    `some`-masked candidate. -/
theorem mem_zip_filterMap {α : Type} (keys : List α) (cands : DenseCandsV p) (f : α × ZMod p)
    (hf : f ∈ (keys.zip cands).filterMap (fun xc => xc.2.map (fun c => (xc.1, c)))) :
    ∃ n : ℕ, keys[n]? = some f.1 ∧ cands[n]? = some (some f.2) := by
  induction keys generalizing cands with
  | nil => simp at hf
  | cons k ks ih =>
    cases cands with
    | nil => simp at hf
    | cons oc ocs =>
      rw [List.zip_cons_cons, List.filterMap_cons] at hf
      cases hoc : oc with
      | none =>
          rw [hoc] at hf
          simp only [Option.map_none] at hf
          obtain ⟨n, hn1, hn2⟩ := ih ocs hf
          exact ⟨n + 1, by simpa using hn1, by simpa using hn2⟩
      | some c =>
          rw [hoc] at hf
          simp only [Option.map_some] at hf
          rcases List.mem_cons.1 hf with rfl | hf'
          · exact ⟨0, rfl, rfl⟩
          · obtain ⟨n, hn1, hn2⟩ := ih ocs hf'
            exact ⟨n + 1, by simpa using hn1, by simpa using hn2⟩

/-- **Value-only `forcedOver` entailment.** Every forced pair `(x, c)` is entailed by `denv`, given
    the domain table is sound at `denv` and the covered items evaluate/oblige correctly. -/
theorem denseForcedOverV_entails (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p) (xs : List VarId) (denv : VarId → ZMod p)
    (hTs : DenseTableSoundAt denv T)
    (hes : ∀ e ∈ denseCoveredIdxUnord fidx.activeIdx fidx.arrActive (fun c => c.varsInF xs) xs,
      e.eval denv = 0 ∧ ∀ i ∈ e.vars, i ∈ xs)
    (hbis : ∀ bi ∈ denseCoveredIdxUnord fidx.bisIdx fidx.arrBis
        (fun bi => denseBIVarsInF xs bi && !bs.isStateful bi.busId) xs,
      ((denseBIEval bi denv).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi denv) = false)
        ∧ ∀ i ∈ denseBIVars bi, i ∈ xs) :
    ∀ f ∈ denseForcedOverV bs facts T fidx xs, denv f.1 = f.2 := by
  unfold denseForcedOverV
  cases hdoms : T.doms xs with
  | none => intro f hf; simp at hf
  | some fdoms =>
    have hkeys : fdoms.map Prod.fst = xs := DenseDomainTable.doms_fst T xs fdoms hdoms
    have hmem : ∀ kd ∈ fdoms, denv kd.1 ∈ kd.2.toList :=
      fun kd hkd => hTs kd.1 kd.2 (DenseDomainTable.doms_getElem T xs fdoms hdoms kd hkd)
    have hinbox : (fdoms.map Prod.fst).map denv ∈ assignmentsV (fdoms.map Prod.snd) := by
      rw [List.map_map]; exact mem_assignmentsV denv fdoms hmem
    dsimp only
    split_ifs with hbox hwork
    · have hsurv : denseCompiledSurvV bs
          (denseCoveredIdxUnord fidx.activeIdx fidx.arrActive (fun c => c.varsInF xs) xs)
          (denseCoveredIdxUnord fidx.bisIdx fidx.arrBis
            (fun bi => denseBIVarsInF xs bi && !bs.isStateful bi.busId) xs)
          (fdoms.map Prod.fst) ((fdoms.map Prod.fst).map denv) = true := by
        apply denseCompiledSurvV_restriction
        · exact fun e he => (hes e he).1
        · exact fun bi hbi => (hbis bi hbi).1
        · intro e he i hi; rw [hkeys]; exact (hes e he).2 i hi
        · intro bi hbi i hi; rw [hkeys]; exact (hbis bi hbi).2 i hi
      cases hscan : denseScanBoxV (denseCompiledSurvV bs
          (denseCoveredIdxUnord fidx.activeIdx fidx.arrActive (fun c => c.varsInF xs) xs)
          (denseCoveredIdxUnord fidx.bisIdx fidx.arrBis
            (fun bi => denseBIVarsInF xs bi && !bs.isStateful bi.busId) xs)
          (fdoms.map Prod.fst)) (fdoms.map Prod.snd) with
      | none =>
          intro f hf
          have hcontra := denseScanBoxV_none_unsat _ _ hscan _ hinbox
          rw [hcontra] at hsurv; exact absurd hsurv (by simp)
      | some cands =>
          intro f hf
          obtain ⟨n, hn1, hn2⟩ := mem_zip_filterMap (fdoms.map Prod.fst) cands f hf
          have hforce := denseScanBoxV_forces _ _ cands hscan n f.2 hn2 _ hinbox hsurv
          rw [List.getElem?_map, hn1] at hforce
          simp only [Option.map_some, Option.some.injEq] at hforce
          exact hforce
    · intro f hf; simp at hf
    · intro f hf; simp at hf

/-! ## Covered-item variable membership helpers -/

theorem denseContainsFast_mem (xs : List VarId) (y : VarId) (h : denseContainsFast xs y = true) :
    y ∈ xs := by
  induction xs with
  | nil => simp [denseContainsFast] at h
  | cons x rest ih =>
    rw [denseContainsFast, Bool.or_eq_true] at h
    rcases h with h | h
    · have : y = x := by simpa using h
      exact this ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem denseExpr_varsInF_mem (xs : List VarId) :
    ∀ (e : DenseExpr p), e.varsInF xs = true → ∀ i ∈ e.vars, i ∈ xs := by
  intro e
  induction e with
  | const n => intro _ i hi; simp [DenseExpr.vars] at hi
  | var y =>
      intro h i hi
      simp only [DenseExpr.vars, List.mem_singleton] at hi
      rw [hi]; exact denseContainsFast_mem xs y h
  | add a b iha ihb =>
      intro h i hi
      rw [DenseExpr.varsInF, Bool.and_eq_true] at h
      simp only [DenseExpr.vars, List.mem_append] at hi
      rcases hi with hi | hi
      · exact iha h.1 i hi
      · exact ihb h.2 i hi
  | mul a b iha ihb =>
      intro h i hi
      rw [DenseExpr.varsInF, Bool.and_eq_true] at h
      simp only [DenseExpr.vars, List.mem_append] at hi
      rcases hi with hi | hi
      · exact iha h.1 i hi
      · exact ihb h.2 i hi

theorem denseBIVarsInF_mem (xs : List VarId) (bi : BusInteraction (DenseExpr p))
    (h : denseBIVarsInF xs bi = true) : ∀ i ∈ denseBIVars bi, i ∈ xs := by
  rw [denseBIVarsInF, Bool.and_eq_true] at h
  intro i hi
  simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hi
  rcases hi with hi | ⟨e, he, hie⟩
  · exact denseExpr_varsInF_mem xs bi.multiplicity h.1 i hi
  · exact denseExpr_varsInF_mem xs e (List.all_eq_true.1 h.2 e he) i hie

/-! ## The entailment invariant on the collected solution map -/

/-- A `(i, t)` solution pair is entailed by `d`: its variables occur in `d`, and every satisfying
    assignment forces `denv i = t.eval denv`. -/
def EntailedPair (d : DenseConstraintSystem p) (bs : BusSemantics p) (i : VarId) (t : DenseExpr p) :
    Prop :=
  (∀ z ∈ t.vars, z ∈ d.occ) ∧ (∀ denv, d.satisfies bs denv → denv i = t.eval denv)

/-- Every entry of a solution map is entailed. -/
def EntailedMap (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (m : Std.HashMap VarId (DenseExpr p)) : Prop :=
  ∀ i t, m[i]? = some t → EntailedPair d bs i t

theorem EntailedMap_foldl_insert (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    ∀ (pairs : List (VarId × DenseExpr p)) (m : Std.HashMap VarId (DenseExpr p)),
      EntailedMap d bs m → (∀ pr ∈ pairs, EntailedPair d bs pr.1 pr.2) →
      EntailedMap d bs (pairs.foldl (fun m p => m.insert p.1 p.2) m) := by
  intro pairs
  induction pairs with
  | nil => intro m hm _; exact hm
  | cons pr rest ih =>
    intro m hm hpairs
    apply ih
    · intro i t hit
      rw [Std.HashMap.getElem?_insert] at hit
      by_cases hii : pr.1 = i
      · rw [if_pos (by simpa using hii)] at hit
        simp only [Option.some.injEq] at hit; subst hii; subst hit
        exact hpairs pr (List.mem_cons_self ..)
      · rw [if_neg (by simpa using hii)] at hit
        exact hm i t hit
    · exact fun pr' hpr' => hpairs pr' (List.mem_cons_of_mem _ hpr')

/-- The value-only `collectForced` fold preserves the entailment invariant. -/
theorem denseCollectForcedV_entailed (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) (T : DenseDomainTable p) (fidx : DenseForcedIdx p)
    (d : DenseConstraintSystem p)
    (hforced : ∀ xs, ∀ f ∈ denseForcedOverV bs facts T fidx xs, ∀ denv,
      d.satisfies bs denv → denv f.1 = f.2) :
    ∀ (targets : List (List VarId)) (seen : Std.HashSet String) (dσ : DenseSolved p),
      EntailedMap d bs dσ.map →
      EntailedMap d bs (denseCollectForcedV bs facts reg T fidx targets seen dσ).map := by
  intro targets
  induction targets with
  | nil => intro seen dσ h; exact h
  | cons xs rest ih =>
    intro seen dσ h
    simp only [denseCollectForcedV]
    split_ifs with hseen
    · exact ih _ _ h
    · apply ih
      rw [DenseSolved.insertAll_map]
      apply EntailedMap_foldl_insert d bs _ dσ.map h
      intro pr hpr
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hpr
      refine ⟨fun z hz => by simp [DenseExpr.vars] at hz, fun denv hsat => ?_⟩
      show denv f.1 = (DenseExpr.const f.2).eval denv
      rw [DenseExpr.eval]
      exact hforced xs f hf denv hsat

/-! ## Reflexive (identity) native correctness -/

theorem DensePassCorrect_refl (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) : DensePassCorrect isInput d d [] bs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro denv hsat; exact ⟨denv, hsat, BusState.equiv_refl _⟩
  · intro hinv; exact hinv
  · intro i hi _; exact hi
  · intro denv hadm hsat
    refine ⟨denv, hsat, hadm, BusState.equiv_refl _, fun _ _ => rfl, ?_⟩
    intro inputVarIds _
    unfold DenseOutReconstructs
    intro i hi _
    show i ∈ d.occ ∧ denv i = denv i
    exact ⟨hi, rfl⟩

/-! ## The σ-map of the value-only pass is entailed -/

/-- The domain table built by `denseDomainBatchσV`. -/
def dbT (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseDomainTable p :=
  denseAddBusDoms bs facts d.busInteractions
    (denseAddConstraintDoms d.algebraicConstraints DenseDomainTable.empty)

/-- The non-redundant active-constraint set built by `denseDomainBatchσV`. -/
def dbActiveCs (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  d.algebraicConstraints.filter (fun c => !denseConstraintRedundantV (dbT bs facts d) c)

/-- The target list built by `denseDomainBatchσV`. -/
def dbTargets (d : DenseConstraintSystem p) : List (List VarId) :=
  d.algebraicConstraints.map (fun e => e.vars.dedup) ++
    d.busInteractions.map (fun bi => (denseBIVars bi).dedup)

/-- The inverted index built by `denseDomainBatchσV`. -/
def dbFidx (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseForcedIdx p :=
  { csIdx := denseCovBuild DenseExpr.vars d.algebraicConstraints,
    arrCs := d.algebraicConstraints.toArray,
    bisIdx := denseCovBuild denseBIVars d.busInteractions,
    arrBis := d.busInteractions.toArray,
    activeIdx := denseCovBuild DenseExpr.vars (dbActiveCs bs facts d),
    arrActive := (dbActiveCs bs facts d).toArray }

theorem denseDomainBatchσV_eq (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseDomainBatchσV reg bs facts d
      = denseCollectForcedV bs facts reg (dbT bs facts d) (dbFidx bs facts d) (dbTargets d) ∅
          DenseSolved.empty := rfl

theorem denseDomainBatchσV_entailed [Fact p.Prime] [NeZero p] (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    EntailedMap d bs (denseDomainBatchσV reg bs facts d).map := by
  rw [denseDomainBatchσV_eq]
  refine denseCollectForcedV_entailed bs facts reg (dbT bs facts d) (dbFidx bs facts d) d
    ?hforced (dbTargets d) ∅ DenseSolved.empty ?hbase
  case hbase =>
    intro i t h
    rw [DenseSolved.empty, Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)
  case hforced =>
    intro xs f hf denv hsat
    refine denseForcedOverV_entails bs facts (dbT bs facts d) (dbFidx bs facts d) xs denv
      ?_ ?_ ?_ f hf
    · exact denseDomainTable_soundAt bs facts d denv hsat
    · intro e he
      obtain ⟨hmem, hQ⟩ := denseCoveredIdxUnord_mem_of_eq (dbFidx bs facts d).activeIdx
        (dbActiveCs bs facts d) (dbFidx bs facts d).arrActive rfl (fun c => c.varsInF xs) xs he
      exact ⟨hsat.1 e (List.mem_of_mem_filter hmem), denseExpr_varsInF_mem xs e hQ⟩
    · intro bi hbi
      obtain ⟨hmem, hQ⟩ := denseCoveredIdxUnord_mem_of_eq (dbFidx bs facts d).bisIdx
        d.busInteractions (dbFidx bs facts d).arrBis rfl
        (fun bi => denseBIVarsInF xs bi && !bs.isStateful bi.busId) xs hbi
      rw [Bool.and_eq_true] at hQ
      exact ⟨hsat.2 bi hmem, denseBIVarsInF_mem xs bi hQ.1⟩

/-! ## The native value-only domain-batch pass -/

theorem denseDomainBatchTransformV_covered (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    (denseDomainBatchTransformV pw reg bs facts d).CoveredBy reg := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show denseDomainBatchTransformV pw reg bs facts d = applyσ (denseDomainBatchσV reg bs facts d) d
        from by simp only [denseDomainBatchTransformV, if_pos hpB], applyσ]
    by_cases he : (denseDomainBatchσV reg bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact hcov
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_covered hcov (fun i _ t ht z hz => ?_)
      exact DenseConstraintSystem.occ_valid hcov z
        ((denseDomainBatchσV_entailed reg bs facts d i t ht).1 z hz)
  · rw [show denseDomainBatchTransformV pw reg bs facts d = d
        from by simp only [denseDomainBatchTransformV, if_neg hpB]]
    exact hcov

theorem denseDomainBatchTransformV_correct (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseDomainBatchTransformV pw reg bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show denseDomainBatchTransformV pw reg bs facts d = applyσ (denseDomainBatchσV reg bs facts d) d
        from by simp only [denseDomainBatchTransformV, if_pos hpB], applyσ]
    by_cases he : (denseDomainBatchσV reg bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact DensePassCorrect_refl reg.isInput d bs
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_denseCorrect d (denseDomainBatchσV reg bs facts d).fn bs
        reg.isInput (fun denv hsat j t hjt => ?_) (fun j t hjt z hz => ?_)
      · exact (denseDomainBatchσV_entailed reg bs facts d j t hjt).2 denv hsat
      · exact (denseDomainBatchσV_entailed reg bs facts d j t hjt).1 z hz
  · rw [show denseDomainBatchTransformV pw reg bs facts d = d
        from by simp only [denseDomainBatchTransformV, if_neg hpB]]
    exact DensePassCorrect_refl reg.isInput d bs

/-- **The native value-only dense domain-batch pass.** Threads `reg`/`pw`, connects to the audited
    spec via `DensePassCorrect.lift` on the native `DensePassCorrect` proof (no commutation with the
    reference pass). -/
def denseDomainBatchPassV (pw : PrimeWitness p) : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := denseDomainBatchTransformV pw reg bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := denseDomainBatchTransformV_covered pw reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := DensePassCorrect.lift hcov
      (denseDomainBatchTransformV_covered pw reg bs facts d hcov) (by intro x hx; simp at hx)
      (denseDomainBatchTransformV_correct pw reg bs facts d) }

end ApcOptimizer.Dense
