import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchRuntime
import ApcOptimizer.Implementation.OptimizerPasses.Bridge
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Correctness for the value-only dense `domainBatch`

Proves `DensePassCorrect` for `denseDomainBatchTransformV`. The output is `applyσ dσ d`, a batch
substitution of forced constants; the proof combines a simultaneous-substitution correctness lemma
(`substF_denseCorrect`) with an entailment for the collected forced map (`denseDomainBatchσV_entailed`),
the latter via domain-table soundness and a value-only box-scan certificate. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Simultaneous substitution semantics -/

/-- The dense environment with every mapped `VarId` rebound to its solution's value. -/
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

/-- If every mapped pair is respected by `denv`, rebinding changes nothing. -/
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

/-- **Simultaneous-substitution correctness.** If every satisfying assignment of `d` forces
    `denv j = t.eval denv` for each mapped pair `df j = some t`, and every solution mentions only
    `d`'s occurring variables, then substituting the whole map at once satisfies `DensePassCorrect`
    (no derivations). -/
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

/-! ## Root soundness

The affine-form eval-preservation lemmas used here live in `Dense/Affine.lean` and
`Dense/Normalize.lean`. -/

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

/-! ## Constant / fact soundness -/

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
  grind [denseInteractionDomainF, FiniteDomain.toList, denseInteractionBound_sound, mem_range_cast]

/-! ## Domain-table soundness -/

/-- Soundness of a dense domain table at a fixed environment: every stored domain contains the
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

/-- **Domain-table soundness.** Building the domain table from a system `d` satisfied by
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

/-- All value-only assignments in the Cartesian product of the domains. -/
def assignmentsV : List (FiniteDomain p) → List (List (ZMod p))
  | [] => [[]]
  | d :: rest => (assignmentsV rest).flatMap (fun a => d.toList.map (fun v => v :: a))

/-- `denseBoxFoldV` streams exactly the eager fold over `assignmentsV`. -/
theorem denseBoxFoldV_eq {β : Type} (ops : DenseZModOps p)
    (f : β → List (ZMod p) → β) (stop : β → Bool)
    (doms : List (FiniteDomain p)) (acc : β) :
    denseBoxFoldV ops f stop doms acc = foldlStop f stop (assignmentsV doms) acc := by
  induction doms generalizing f acc with
  | nil => simp only [denseBoxFoldV, assignmentsV, foldlStop]
  | cons d rest ih =>
    rw [denseBoxFoldV, ih]
    show foldlStop (fun acc' a =>
        d.foldElts ops.zero (fun v => ops.add v ops.one)
          (fun acc'' v => f acc'' (v :: a)) stop acc') stop (assignmentsV rest) acc
      = foldlStop f stop (assignmentsV (d :: rest)) acc
    rw [show assignmentsV (d :: rest)
          = (assignmentsV rest).flatMap (fun a => d.toList.map (fun v => v :: a)) from rfl,
      ← foldlStop_flatMap f stop (fun a => d.toList.map (fun v => v :: a))]
    apply foldlStop_congr
    intro acc' a
    show d.foldElts ops.zero (fun v => ops.add v ops.one)
        (fun acc'' v => f acc'' (v :: a)) stop acc'
      = foldlStop f stop (d.toList.map (fun v => v :: a)) acc'
    rw [FiniteDomain.foldElts_eq ops.zero (fun v => ops.add v ops.one) ops.zero_eq
      (fun v => by simp only; rw [ops.add_eq, ops.one_eq]), foldlStop_map]

/-- The restriction of a satisfying `denv` to a keyed domain list is one of the value-only
    enumerated assignments. -/
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

/-- One value-only scan step from a *tracking* state (`denseScanStepV`'s `some` branch). -/
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
    denseLookupIxV 0 pt idx = denseEnvOfKeysV keys pt y := by
  induction keys generalizing pt idx with
  | nil => simp [denseVarIx] at h
  | cons x rest ih =>
    rw [denseVarIx] at h
    cases pt with
    | nil => rfl
    | cons v vs =>
      split_ifs at h with hyx
      · simp only [Option.some.injEq] at h; subst h
        show denseLookupIxV 0 (v :: vs) 0 = denseEnvOfKeysV (x :: rest) (v :: vs) y
        rw [denseLookupIxV, denseEnvOfKeysV, if_pos hyx]
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        show denseLookupIxV 0 (v :: vs) (j + 1) = denseEnvOfKeysV (x :: rest) (v :: vs) y
        rw [denseLookupIxV, denseEnvOfKeysV, if_neg hyx]
        exact ih vs j hj

/-- Compiled value-only evaluation agrees with the keyed-environment evaluation of the source. -/
theorem denseCompileE_evalV (ops : DenseZModOps p) (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (e : DenseExpr p) (ic : IExpr p), denseCompileE keys e = some ic →
      denseIExprEvalWithV ops pt ic = e.eval (denseEnvOfKeysV keys pt) := by
  intro e
  induction e with
  | const n => intro ic h; simp only [denseCompileE, Option.some.injEq] at h; subst h; rfl
  | var y =>
      intro ic h
      rw [denseCompileE, Option.map_eq_some_iff] at h
      obtain ⟨idx, hidx, rfl⟩ := h
      show denseIExprEvalWithV ops pt (.ix idx) = denseEnvOfKeysV keys pt y
      rw [denseIExprEvalWithV]
      rw [ops.zero_eq]
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
          show denseIExprEvalWithV ops pt (.add ia ib) = (a.add b).eval (denseEnvOfKeysV keys pt)
          rw [denseIExprEvalWithV, DenseExpr.eval, ops.add_eq, iha ia ha, ihb ib hb]
  | mul a b iha ihb =>
      intro ic h
      cases ha : denseCompileE keys a with
      | none => rw [denseCompileE, ha] at h; simp at h
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [denseCompileE, ha, hb] at h; simp at h
        | some ib =>
          rw [denseCompileE, ha, hb] at h; simp only [Option.some.injEq] at h; subst h
          show denseIExprEvalWithV ops pt (.mul ia ib) = (a.mul b).eval (denseEnvOfKeysV keys pt)
          rw [denseIExprEvalWithV, DenseExpr.eval, ops.mul_eq, iha ia ha, ihb ib hb]

/-- Compiled-list zero-check agrees with the source list's (value-only). -/
theorem denseCompileEs_allV (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (es : List (DenseExpr p)) (ces : List (IExpr p)), denseCompileEs keys es = some ces →
      ces.all (fun ie => isZero (denseIExprEvalWithV ops pt ie))
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
          denseCompileE_evalV ops keys pt e ie he, hz]

/-- Compiled payload evaluation agrees with the fallback payload (value-only). -/
theorem denseCompileEs_mapV (ops : DenseZModOps p) (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (es : List (DenseExpr p)) (ces : List (IExpr p)), denseCompileEs keys es = some ces →
      ces.map (fun ie => denseIExprEvalWithV ops pt ie)
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
          denseCompileE_evalV ops keys pt e ie he]

private theorem denseByteXorSpec_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (op.eval denv = spec.xorOp →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            (r.eval denv).val = Nat.xor (o1.eval denv).val (o2.eval denv).val)) ∧
    (op.eval denv = spec.pairOp →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            r.eval denv = 0)) := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
  have hdecEv : spec.decode (denseBIEval bi denv).payload =
      some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]
    rfl
  exact hsound (denseBIEval bi denv).payload (op.eval denv) (o1.eval denv) (o2.eval denv)
    (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

private theorem denseByteBoolSound_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (∀ oop, spec.orOp = some oop → op.eval denv = oop →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            (r.eval denv).val = Nat.lor (o1.eval denv).val (o2.eval denv).val)) ∧
    (∀ aop, spec.andOp = some aop → op.eval denv = aop →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            (r.eval denv).val = Nat.land (o1.eval denv).val (o2.eval denv).val)) := by
  have hdecEv : spec.decode (denseBIEval bi denv).payload =
      some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]
    rfl
  exact facts.byteBoolSound bi.busId spec hspec (denseBIEval bi denv).payload (op.eval denv)
    (o1.eval denv) (o2.eval denv) (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

private theorem denseNotBoolEqDecide (b : Bool) (P : Prop) [Decidable P]
    (h : b = false ↔ P) : (!b) = decide P := by
  cases b <;> simp_all

private instance denseBytePredKindHoldsDecidable (kind : DenseBytePredKind) (a b r : ZMod p) :
    Decidable (kind.Holds a b r) := by
  cases kind <;> simp [DenseBytePredKind.Holds] <;> infer_instance

theorem denseBytePredRelationV_eq (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (kind : DenseBytePredKind) (a b r : ZMod p) :
    denseBytePredRelationV isZero kind a b r = decide (kind.Holds a b r) := by
  cases kind <;> simp [denseBytePredRelationV, DenseBytePredKind.Holds, hz]

private theorem denseVarRangePred_eval (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (keys : List VarId) (pt : List (ZMod p)) (bi : BusInteraction (DenseExpr p))
    (x width : DenseExpr p) (mult ix iwidth : IExpr p)
    (hpay : bi.payload = [x, width]) (hfact : facts.varRangeBus bi.busId = true)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (hx : denseCompileE keys x = some ix) (hw : denseCompileE keys width = some iwidth) :
    denseCBiPredEvalV ops isZero bs pt (.varRange mult ix iwidth)
      = denseBiObligationV bs bi keys pt := by
  let env := denseEnvOfKeysV keys pt
  have hme := denseCompileE_evalV ops keys pt bi.multiplicity mult hm
  have hxe := denseCompileE_evalV ops keys pt x ix hx
  have hwe := denseCompileE_evalV ops keys pt width iwidth hw
  have hiff := (facts.varRangeBus_sound bi.busId hfact).2
    (x.eval env) (width.eval env) (bi.multiplicity.eval env)
  have hb :
      (!bs.violatesConstraint
          { busId := bi.busId, multiplicity := bi.multiplicity.eval env,
            payload := [x.eval env, width.eval env] })
        = decide ((width.eval env).val ≤ 17 ∧ (x.eval env).val < 2 ^ (width.eval env).val) :=
    denseNotBoolEqDecide _ _ hiff
  simp only [denseCBiPredEvalV, denseBiObligationV, hme, hxe, hwe, hpay, List.map_cons,
    List.map_nil, hz]
  exact congrArg (fun tail => if decide (bi.multiplicity.eval env = 0) then true else tail) hb.symm

private theorem denseVarRangeConstPred_eval (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p))
    (bi : BusInteraction (DenseExpr p)) (x width : DenseExpr p) (widthValue : ZMod p)
    (mult ix : IExpr p) (hpay : bi.payload = [x, width])
    (hfact : facts.varRangeBus bi.busId = true)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (hx : denseCompileE keys x = some ix) (hw : width.constValue? = some widthValue)
    (hle : widthValue.val ≤ 17) :
    denseCBiPredEvalV ops isZero bs pt (.varRangeConst mult ix (2 ^ widthValue.val))
      = denseBiObligationV bs bi keys pt := by
  let env := denseEnvOfKeysV keys pt
  have hme := denseCompileE_evalV ops keys pt bi.multiplicity mult hm
  have hxe := denseCompileE_evalV ops keys pt x ix hx
  have hwe := width.constValue?_sound widthValue hw env
  have hiff := (facts.varRangeBus_sound bi.busId hfact).2
    (x.eval env) (width.eval env) (bi.multiplicity.eval env)
  have hiff' :
      bs.violatesConstraint
          { busId := bi.busId, multiplicity := bi.multiplicity.eval env,
            payload := [x.eval env, width.eval env] } = false
        ↔ (x.eval env).val < 2 ^ widthValue.val := by
    simpa [hwe, hle] using hiff
  have hb :
      (!bs.violatesConstraint
          { busId := bi.busId, multiplicity := bi.multiplicity.eval env,
            payload := [x.eval env, width.eval env] })
        = decide ((x.eval env).val < 2 ^ widthValue.val) :=
    denseNotBoolEqDecide _ _ hiff'
  simp only [denseCBiPredEvalV, denseBiObligationV, hme, hxe, hpay, List.map_cons,
    List.map_nil, hz]
  exact congrArg (fun tail => if decide (bi.multiplicity.eval env = 0) then true else tail) hb.symm

private theorem denseTupleRangePred_eval (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (keys : List VarId) (pt : List (ZMod p)) (bi : BusInteraction (DenseExpr p))
    (x y : DenseExpr p) (mult ix iy : IExpr p) (boundX boundY : Nat)
    (hpay : bi.payload = [x, y]) (hfact : facts.tupleRangeBus bi.busId = some (boundX, boundY))
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (hx : denseCompileE keys x = some ix) (hy : denseCompileE keys y = some iy) :
    denseCBiPredEvalV ops isZero bs pt (.tupleRange mult ix iy boundX boundY)
      = denseBiObligationV bs bi keys pt := by
  let env := denseEnvOfKeysV keys pt
  have hme := denseCompileE_evalV ops keys pt bi.multiplicity mult hm
  have hxe := denseCompileE_evalV ops keys pt x ix hx
  have hye := denseCompileE_evalV ops keys pt y iy hy
  have hiff := (facts.tupleRangeBus_sound bi.busId boundX boundY hfact).2.2
    (x.eval env) (y.eval env) (bi.multiplicity.eval env)
  have hb :
      (!bs.violatesConstraint
          { busId := bi.busId, multiplicity := bi.multiplicity.eval env,
            payload := [x.eval env, y.eval env] })
        = decide ((x.eval env).val < boundX ∧ (y.eval env).val < boundY) :=
    denseNotBoolEqDecide _ _ hiff
  simp only [denseCBiPredEvalV, denseBiObligationV, hme, hxe, hye, hpay, List.map_cons,
    List.map_nil, hz]
  exact congrArg (fun tail => if decide (bi.multiplicity.eval env = 0) then true else tail) hb.symm

private theorem denseFallbackPred_eval (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p) (keys : List VarId)
    (pt : List (ZMod p)) (bi : BusInteraction (DenseExpr p)) (mult : IExpr p)
    (payload : List (IExpr p)) (hm : denseCompileE keys bi.multiplicity = some mult)
    (hpl : denseCompileEs keys bi.payload = some payload) :
    denseCBiPredEvalV ops isZero bs pt (.fallback ⟨bi.busId, mult, payload⟩)
      = denseBiObligationV bs bi keys pt := by
  simp only [denseCBiPredEvalV, denseBiObligationV,
    denseCompileE_evalV ops keys pt bi.multiplicity mult hm,
    denseCompileEs_mapV ops keys pt bi.payload payload hpl, hz]

private theorem denseFixedRangePred_eval (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (keys : List VarId) (pt : List (ZMod p)) (bi : BusInteraction (DenseExpr p))
    (multValue : ZMod p) (e : DenseExpr p) (mult value : IExpr p) (slot bound : Nat)
    (hmv : bi.multiplicity.constValue? = some multValue) (hmv1 : multValue = 1)
    (hrange : facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?)
      = some (slot, bound))
    (hslot : bi.payload[slot]? = some e)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (he : denseCompileE keys e = some value) :
    denseCBiPredEvalV ops isZero bs pt (.fixedRange mult value bound)
      = denseBiObligationV bs bi keys pt := by
  let env := denseEnvOfKeysV keys pt
  let msg : BusInteraction (ZMod p) :=
    { busId := bi.busId,
      multiplicity := bi.multiplicity.eval env,
      payload := bi.payload.map (fun e => e.eval env) }
  have hme := denseCompileE_evalV ops keys pt bi.multiplicity mult hm
  have hee := denseCompileE_evalV ops keys pt e value he
  have hmone : msg.multiplicity = 1 := by
    dsimp only [msg]
    rw [bi.multiplicity.constValue?_sound multValue hmv env, hmv1]
  obtain ⟨_, hsound⟩ := facts.rangeCheckAt_sound bi.busId
    (bi.payload.map DenseExpr.constValue?) slot bound hrange
  obtain ⟨_, hiffAt⟩ := hsound msg rfl hmone (denseMatches_evalPattern bi.payload env)
  have hget : msg.payload[slot]? = some (e.eval env) := by
    dsimp only [msg]
    rw [List.getElem?_map, hslot]
    rfl
  have hiff := hiffAt (e.eval env) hget
  have hb : (!bs.violatesConstraint msg) = decide ((e.eval env).val < bound) :=
    denseNotBoolEqDecide _ _ hiff
  simp only [denseCBiPredEvalV, denseBiObligationV, hme, hee, hz]
  change (if decide (msg.multiplicity = 0) then true
    else decide ((e.eval env).val < bound)) =
      (if decide (msg.multiplicity = 0) then true else !bs.violatesConstraint msg)
  exact congrArg (fun tail => if decide (msg.multiplicity = 0) then true else tail) hb.symm

private theorem denseBytePred_eval (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p)
    (keys : List VarId) (pt : List (ZMod p)) (bi : BusInteraction (DenseExpr p))
    (mult : IExpr p) (o1 o2 result : DenseExpr p) (io1 io2 iresult : IExpr p)
    (bound : Nat) (kind : DenseBytePredKind)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (ho1 : denseCompileE keys o1 = some io1) (ho2 : denseCompileE keys o2 = some io2)
    (hresult : denseCompileE keys result = some iresult)
    (hiff : bs.violatesConstraint (denseBIEval bi (denseEnvOfKeysV keys pt)) = false ↔
      (o1.eval (denseEnvOfKeysV keys pt)).val < bound ∧
      (o2.eval (denseEnvOfKeysV keys pt)).val < bound ∧
      kind.Holds (o1.eval (denseEnvOfKeysV keys pt)) (o2.eval (denseEnvOfKeysV keys pt))
        (result.eval (denseEnvOfKeysV keys pt))) :
    denseCBiPredEvalV ops isZero bs pt (.byte mult io1 io2 iresult bound kind)
      = denseBiObligationV bs bi keys pt := by
  let env := denseEnvOfKeysV keys pt
  have hme := denseCompileE_evalV ops keys pt bi.multiplicity mult hm
  have h1e := denseCompileE_evalV ops keys pt o1 io1 ho1
  have h2e := denseCompileE_evalV ops keys pt o2 io2 ho2
  have hre := denseCompileE_evalV ops keys pt result iresult hresult
  have hb : (!bs.violatesConstraint (denseBIEval bi env)) = decide
      ((o1.eval env).val < bound ∧ (o2.eval env).val < bound ∧
        kind.Holds (o1.eval env) (o2.eval env) (result.eval env)) :=
    denseNotBoolEqDecide _ _ hiff
  simp only [denseCBiPredEvalV, denseBiObligationV, hme, h1e, h2e, hre, hz,
    denseBytePredRelationV_eq isZero hz]
  change (if decide ((denseBIEval bi env).multiplicity = 0) then true else
      decide ((o1.eval env).val < bound ∧ (o2.eval env).val < bound) &&
        decide (kind.Holds (o1.eval env) (o2.eval env) (result.eval env))) =
    (if decide ((denseBIEval bi env).multiplicity = 0) then true
      else !bs.violatesConstraint (denseBIEval bi env))
  rw [hb]
  by_cases hm0 : (denseBIEval bi env).multiplicity = 0 <;>
    by_cases h1 : (o1.eval env).val < bound <;>
    by_cases h2 : (o2.eval env).val < bound <;>
    by_cases hr : kind.Holds (o1.eval env) (o2.eval env) (result.eval env) <;>
    simp [hm0, h1, h2, hr]

private theorem denseCompileRangeCBiPredV_eval (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p))
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) (pred : DenseCBiPred p)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (h : denseCompileRangeCBiPredV facts keys bi mult = some pred) :
    denseCBiPredEvalV ops isZero bs pt pred = denseBiObligationV bs bi keys pt := by
  unfold denseCompileRangeCBiPredV at h
  cases hmv : bi.multiplicity.constValue? with
  | none => simp [hmv] at h
  | some multValue =>
    simp only [hmv] at h
    by_cases hm1 : multValue = 1
    · simp only [hm1, if_pos] at h
      cases hrange : facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
      | none => simp [hrange] at h
      | some sb =>
        obtain ⟨slot, bound⟩ := sb
        simp only [hrange] at h
        cases hslot : bi.payload[slot]? with
        | none => simp [hslot] at h
        | some e =>
          simp only [hslot] at h
          cases he : denseCompileE keys e with
          | none => simp [he] at h
          | some value =>
            simp only [he, Option.map_some, Option.some.injEq] at h
            subst pred
            exact denseFixedRangePred_eval ops isZero hz bs facts keys pt bi multValue e mult
              value slot bound hmv hm1 hrange hslot hm he
    · simp [hm1] at h

private theorem denseCompileByteCBiPredV_eval (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p))
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) (pred : DenseCBiPred p)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (h : denseCompileByteCBiPredV facts keys bi mult = some pred) :
    denseCBiPredEvalV ops isZero bs pt pred = denseBiObligationV bs bi keys pt := by
  unfold denseCompileByteCBiPredV at h
  cases hspec : facts.byteXorSpec bi.busId with
  | none => simp [hspec] at h
  | some spec =>
    simp only [hspec] at h
    cases hdec : spec.decode bi.payload with
    | none => simp [hdec] at h
    | some decoded =>
      obtain ⟨op, o1, o2, result⟩ := decoded
      simp only [hdec] at h
      cases hop : op.constValue? with
      | none => simp [hop] at h
      | some opValue =>
        simp only [hop] at h
        cases ho1 : denseCompileE keys o1 with
        | none => simp [ho1] at h
        | some io1 =>
          simp only [ho1] at h
          cases ho2 : denseCompileE keys o2 with
          | none => simp [ho2] at h
          | some io2 =>
            simp only [ho2] at h
            cases hresult : denseCompileE keys result with
            | none => simp [hresult] at h
            | some iresult =>
              simp only [hresult] at h
              let env := denseEnvOfKeysV keys pt
              have hopeval := op.constValue?_sound opValue hop env
              by_cases hxor : opValue = spec.xorOp
              · simp only [hxor, if_pos] at h
                simp only [Option.some.injEq] at h
                subst pred
                have hiff := (denseByteXorSpec_decode_iff bs facts spec bi hspec op o1 o2
                  result hdec env).1 (hopeval.trans hxor)
                exact denseBytePred_eval ops isZero hz bs keys pt bi mult o1 o2 result io1 io2
                  iresult spec.bound .xor hm ho1 ho2 hresult (by
                    simpa [DenseBytePredKind.Holds] using hiff)
              · simp only [hxor, if_false] at h
                by_cases hpair : opValue = spec.pairOp
                · simp only [hpair, if_pos] at h
                  simp only [Option.some.injEq] at h
                  subst pred
                  have hiff := (denseByteXorSpec_decode_iff bs facts spec bi hspec op o1 o2
                    result hdec env).2 (hopeval.trans hpair)
                  exact denseBytePred_eval ops isZero hz bs keys pt bi mult o1 o2 result io1 io2
                    iresult spec.bound .pair hm ho1 ho2 hresult (by
                      simpa [DenseBytePredKind.Holds] using hiff)
                · simp only [hpair, if_false] at h
                  cases hor : spec.orOp with
                  | some orOp =>
                    simp only [hor] at h
                    by_cases hopOr : opValue = orOp
                    · simp only [hopOr, if_pos] at h
                      simp only [Option.some.injEq] at h
                      subst pred
                      have hiff := (denseByteBoolSound_decode_iff bs facts spec bi hspec op o1 o2
                        result hdec env).1 orOp hor (hopeval.trans hopOr)
                      exact denseBytePred_eval ops isZero hz bs keys pt bi mult o1 o2 result io1
                        io2 iresult spec.bound .or hm ho1 ho2 hresult (by
                          simpa [DenseBytePredKind.Holds] using hiff)
                    · simp only [hopOr, if_false] at h
                      cases hand : spec.andOp with
                      | none => simp [hand] at h
                      | some andOp =>
                        simp only [hand] at h
                        by_cases hopAnd : opValue = andOp
                        · simp only [hopAnd, if_pos, Option.some.injEq] at h
                          subst pred
                          have hiff := (denseByteBoolSound_decode_iff bs facts spec bi hspec op o1
                            o2 result hdec env).2 andOp hand (hopeval.trans hopAnd)
                          exact denseBytePred_eval ops isZero hz bs keys pt bi mult o1 o2 result
                            io1 io2 iresult spec.bound .and hm ho1 ho2 hresult (by
                              simpa [DenseBytePredKind.Holds] using hiff)
                        · simp [hopAnd] at h
                  | none =>
                    simp only [hor] at h
                    cases hand : spec.andOp with
                    | none => simp [hand] at h
                    | some andOp =>
                      simp only [hand] at h
                      by_cases hopAnd : opValue = andOp
                      · simp only [hopAnd, if_pos, Option.some.injEq] at h
                        subst pred
                        have hiff := (denseByteBoolSound_decode_iff bs facts spec bi hspec op o1 o2
                          result hdec env).2 andOp hand (hopeval.trans hopAnd)
                        exact denseBytePred_eval ops isZero hz bs keys pt bi mult o1 o2 result io1
                          io2 iresult spec.bound .and hm ho1 ho2 hresult (by
                            simpa [DenseBytePredKind.Holds] using hiff)
                      · simp [hopAnd] at h

private theorem denseCompileOtherCBiPredV_eval (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p))
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) (pred : DenseCBiPred p)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (h : denseCompileOtherCBiPredV facts keys bi mult = some pred) :
    denseCBiPredEvalV ops isZero bs pt pred = denseBiObligationV bs bi keys pt := by
  unfold denseCompileOtherCBiPredV at h
  cases hrange : denseCompileRangeCBiPredV facts keys bi mult with
  | some rangePred =>
    simp only [hrange, Option.some.injEq] at h
    subst pred
    exact denseCompileRangeCBiPredV_eval ops isZero hz bs facts keys pt bi mult rangePred hm hrange
  | none =>
    simp only [hrange] at h
    cases hbyte : denseCompileByteCBiPredV facts keys bi mult with
    | some bytePred =>
      simp only [hbyte, Option.some.injEq] at h
      subst pred
      exact denseCompileByteCBiPredV_eval ops isZero hz bs facts keys pt bi mult bytePred hm hbyte
    | none =>
      simp only [hbyte] at h
      cases hpayload : denseCompileEs keys bi.payload with
      | none => simp [hpayload] at h
      | some payload =>
        simp only [hpayload, Option.map_some, Option.some.injEq] at h
        subst pred
        exact denseFallbackPred_eval ops isZero hz bs keys pt bi mult payload hm hpayload

private theorem denseCompilePairCBiPredV_eval (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p))
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) (x width : DenseExpr p)
    (pred : DenseCBiPred p) (hpay : bi.payload = [x, width])
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (h : denseCompilePairCBiPredV facts keys bi mult x width = some pred) :
    denseCBiPredEvalV ops isZero bs pt pred = denseBiObligationV bs bi keys pt := by
  unfold denseCompilePairCBiPredV at h
  cases hx : denseCompileE keys x with
  | none =>
    simp only [hx] at h
    exact denseCompileOtherCBiPredV_eval ops isZero hz bs facts keys pt bi mult pred hm h
  | some ix =>
    simp only [hx] at h
    cases hwidth : denseCompileE keys width with
    | none =>
      simp only [hwidth] at h
      exact denseCompileOtherCBiPredV_eval ops isZero hz bs facts keys pt bi mult pred hm h
    | some iwidth =>
      simp only [hwidth] at h
      by_cases hvar : facts.varRangeBus bi.busId = true
      · simp only [hvar, if_true] at h
        cases hwc : width.constValue? with
        | none =>
          simp only [hwc, Option.some.injEq] at h
          subst pred
          exact denseVarRangePred_eval ops isZero hz bs facts keys pt bi x width mult ix iwidth
            hpay hvar hm hx hwidth
        | some widthValue =>
          simp only [hwc] at h
          by_cases hle : widthValue.val ≤ 17
          · simp only [hle, if_true, Option.some.injEq] at h
            subst pred
            exact denseVarRangeConstPred_eval ops isZero hz bs facts keys pt bi x width
              widthValue mult ix hpay hvar hm hx hwc hle
          · simp only [hle, if_false, Option.some.injEq] at h
            subst pred
            exact denseVarRangePred_eval ops isZero hz bs facts keys pt bi x width mult ix iwidth
              hpay hvar hm hx hwidth
      · have hvarFalse : facts.varRangeBus bi.busId = false := Bool.eq_false_of_not_eq_true hvar
        simp only [hvarFalse, Bool.false_eq_true, if_false] at h
        cases htuple : facts.tupleRangeBus bi.busId with
        | none =>
          simp only [htuple] at h
          exact denseCompileOtherCBiPredV_eval ops isZero hz bs facts keys pt bi mult pred hm h
        | some bounds =>
          obtain ⟨boundX, boundY⟩ := bounds
          simp only [htuple, Option.some.injEq] at h
          subst pred
          exact denseTupleRangePred_eval ops isZero hz bs facts keys pt bi x width mult ix iwidth
            boundX boundY hpay htuple hm hx hwidth

private theorem denseCompilePayloadCBiPredV_eval (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p))
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) (payload : List (DenseExpr p))
    (pred : DenseCBiPred p) (hpay : bi.payload = payload)
    (hm : denseCompileE keys bi.multiplicity = some mult)
    (h : denseCompilePayloadCBiPredV facts keys bi mult payload = some pred) :
    denseCBiPredEvalV ops isZero bs pt pred = denseBiObligationV bs bi keys pt := by
  cases payload with
  | nil =>
    exact denseCompileOtherCBiPredV_eval ops isZero hz bs facts keys pt bi mult pred hm h
  | cons x rest =>
    cases rest with
    | nil =>
      exact denseCompileOtherCBiPredV_eval ops isZero hz bs facts keys pt bi mult pred hm h
    | cons width tail =>
      cases tail with
      | nil =>
        exact denseCompilePairCBiPredV_eval ops isZero hz bs facts keys pt bi mult x width pred
          hpay hm h
      | cons third tail =>
        exact denseCompileOtherCBiPredV_eval ops isZero hz bs facts keys pt bi mult pred hm h

private theorem denseCompileCBiPredV_eval (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p))
    (bi : BusInteraction (DenseExpr p)) (pred : DenseCBiPred p)
    (h : denseCompileCBiPredV facts keys bi = some pred) :
    denseCBiPredEvalV ops isZero bs pt pred = denseBiObligationV bs bi keys pt := by
  unfold denseCompileCBiPredV at h
  by_cases hnever : facts.neverViolates bi.busId = true
  · simp only [hnever, if_true, Option.some.injEq] at h
    subst pred
    have hnv := facts.neverViolates_sound (denseBIEval bi (denseEnvOfKeysV keys pt)) hnever
    unfold denseCBiPredEvalV denseBiObligationV
    change true = (if decide ((denseBIEval bi (denseEnvOfKeysV keys pt)).multiplicity = 0)
      then true else !bs.violatesConstraint (denseBIEval bi (denseEnvOfKeysV keys pt)))
    rw [hnv]
    simp
  · have hneverFalse : facts.neverViolates bi.busId = false := Bool.eq_false_of_not_eq_true hnever
    simp only [hneverFalse, Bool.false_eq_true, if_false] at h
    cases hm : denseCompileE keys bi.multiplicity with
    | none => simp [hm] at h
    | some mult =>
      simp only [hm] at h
      exact denseCompilePayloadCBiPredV_eval ops isZero hz bs facts keys pt bi mult bi.payload
        pred rfl hm h

private theorem denseCompileCBiPredsV_all (ops : DenseZModOps p)
    (isZero : ZMod p → Bool) (hz : ∀ v, isZero v = decide (v = 0))
    (bs : BusSemantics p) (facts : BusFacts p bs) (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (bis : List (BusInteraction (DenseExpr p))) (preds : List (DenseCBiPred p)),
      denseCompileCBiPredsV facts keys bis = some preds →
      preds.all (denseCBiPredEvalV ops isZero bs pt) =
        bis.all (fun bi => denseBiObligationV bs bi keys pt) := by
  intro bis
  induction bis with
  | nil =>
    intro preds h
    simp only [denseCompileCBiPredsV, Option.some.injEq] at h
    subst preds
    rfl
  | cons bi rest ih =>
    intro preds h
    cases hb : denseCompileCBiPredV facts keys bi with
    | none => simp [denseCompileCBiPredsV, hb] at h
    | some pred =>
      cases hr : denseCompileCBiPredsV facts keys rest with
      | none => simp [denseCompileCBiPredsV, hb, hr] at h
      | some restPreds =>
        simp only [denseCompileCBiPredsV, hb, hr, Option.some.injEq] at h
        subst preds
        rw [List.all_cons, List.all_cons,
          denseCompileCBiPredV_eval ops isZero hz bs facts keys pt bi pred hb,
          ih restPreds hr]

theorem denseSurvivesAllCWV_eq (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (hz : ∀ v, isZero v = decide (v = 0)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (es : List (DenseExpr p)) (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId)
    (ces : List (IExpr p)) (preds : List (DenseCBiPred p)) (pt : List (ZMod p))
    (hce : denseCompileEs keys es = some ces)
    (hcb : denseCompileCBiPredsV facts keys bis = some preds) :
    denseSurvivesAllCWV ops isZero bs ces preds pt = denseSurvivesAllMV bs es bis keys pt := by
  unfold denseSurvivesAllCWV denseSurvivesAllMV
  congr 1
  · exact denseCompileEs_allV ops isZero hz keys pt es ces hce
  · exact denseCompileCBiPredsV_all ops isZero hz bs facts keys pt bis preds hcb

theorem denseCompiledSurvV_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (es : List (DenseExpr p)) (bis : List (BusInteraction (DenseExpr p)))
    (keys : List VarId) (pt : List (ZMod p)) :
    (denseCompiledSurvV bs facts es bis keys).run pt = denseSurvivesAllMV bs es bis keys pt := by
  unfold denseCompiledSurvV
  cases hce : denseCompileEs keys es with
  | none => rfl
  | some ces =>
    cases hcb : denseCompileCBiPredsV facts keys bis with
    | none => rfl
    | some preds =>
      change denseSurvivesAllCWV denseZModOps (fun v => decide (v = denseZModOps.zero))
          bs ces preds pt = denseSurvivesAllMV bs es bis keys pt
      exact denseSurvivesAllCWV_eq denseZModOps _ (fun _ => rfl)
        bs facts es bis keys ces preds pt hce hcb

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
    unfold denseBiObligationV
    change (if decide ((denseBIEval bi (denseEnvOfKeysV keys (keys.map denv))).multiplicity = 0)
      then true
      else !bs.violatesConstraint (denseBIEval bi (denseEnvOfKeysV keys (keys.map denv)))) = true
    rw [hbe]
    by_cases hm : (denseBIEval bi denv).multiplicity = 0
    · simp [hm]
    · simp [hm, hbi0 bi hbi hm]

/-- The restriction survives the compiled survivor predicate (value-only). -/
theorem denseCompiledSurvV_restriction (bs : BusSemantics p) (facts : BusFacts p bs)
    (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (denv : VarId → ZMod p)
    (hes0 : ∀ e ∈ es, e.eval denv = 0)
    (hbi0 : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false)
    (hesk : ∀ e ∈ es, ∀ i ∈ e.vars, i ∈ keys)
    (hbik : ∀ bi ∈ bis, ∀ i ∈ denseBIVars bi, i ∈ keys) :
    (denseCompiledSurvV bs facts es bis keys).run (keys.map denv) = true := by
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

theorem denseDomainConstantValueV?_mem_eq (d : FiniteDomain p) (c x : ZMod p)
    (hc : denseDomainConstantValueV? d = some c) (hx : x ∈ d.toList) : x = c := by
  cases d with
  | explicit values =>
      cases values with
      | nil => simp [denseDomainConstantValueV?] at hc
      | cons v vs =>
          simp only [denseDomainConstantValueV?] at hc
          split at hc
          · rename_i hall
            simp only [Option.some.injEq] at hc
            subst c
            simp only [FiniteDomain.toList, List.mem_cons] at hx
            rcases hx with rfl | hx
            · rfl
            · have hdec := (List.all_eq_true.mp hall) x hx
              exact of_decide_eq_true hdec
          · simp at hc
  | range size =>
      simp only [denseDomainConstantValueV?] at hc
      split at hc
      · rename_i hsize
        subst size
        simp only [Option.some.injEq] at hc
        subst c
        simpa [FiniteDomain.toList] using hx
      · simp at hc

theorem denseConstantDomainsV_entails (fdoms : List (VarId × FiniteDomain p))
    (denv : VarId → ZMod p)
    (hmem : ∀ kd ∈ fdoms, denv kd.1 ∈ kd.2.toList) :
    ∀ f ∈ denseConstantDomainsV fdoms, denv f.1 = f.2 := by
  intro f hf
  obtain ⟨xd, hxd, hmap⟩ := List.mem_filterMap.1 hf
  cases hc : denseDomainConstantValueV? xd.2 with
  | none => rw [hc] at hmap; simp at hmap
  | some c =>
      rw [hc] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      subst f
      exact denseDomainConstantValueV?_mem_eq xd.2 c (denv xd.1) hc (hmem xd hxd)

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

theorem denseGatherConstraintAtV_active_mem (arr : Array (DenseConstraintPlan p))
    (xs : List VarId) (acc : DenseConstraintGatherV p) (i : Nat)
    (hacc : ∀ e ∈ acc.active, ∃ i, ∃ h : i < arr.size,
      arr[i].expr = e ∧ denseVarsInListF xs arr[i].vars = true ∧ arr[i].active = true) :
    ∀ e ∈ (denseGatherConstraintAtV arr xs acc i).active,
      ∃ i, ∃ h : i < arr.size,
        arr[i].expr = e ∧ denseVarsInListF xs arr[i].vars = true ∧ arr[i].active = true := by
  intro e he
  by_cases hi : i < arr.size
  · by_cases hvars : denseVarsInListF xs arr[i].vars = true
    · simp only [denseGatherConstraintAtV, hi, ↓reduceDIte, hvars, ↓reduceIte] at he
      by_cases hactive : arr[i].active = true
      · simp only [hactive, ↓reduceIte] at he
        rcases List.mem_cons.1 he with he | he
        · subst e; exact ⟨i, hi, rfl, hvars, hactive⟩
        · exact hacc e he
      · simp [hactive] at he
        exact hacc e he
    · apply hacc e
      simpa [denseGatherConstraintAtV, hi, hvars] using he
  · apply hacc e
    simpa [denseGatherConstraintAtV, hi] using he

theorem denseGatherConstraintArrayV_active_mem (arr : Array (DenseConstraintPlan p))
    (xs : List VarId) (positions : Array Nat) (acc : DenseConstraintGatherV p)
    (hacc : ∀ e ∈ acc.active, ∃ i, ∃ h : i < arr.size,
      arr[i].expr = e ∧ denseVarsInListF xs arr[i].vars = true ∧ arr[i].active = true) :
    ∀ e ∈ (denseGatherConstraintArrayV arr xs positions acc).active,
      ∃ i, ∃ h : i < arr.size,
        arr[i].expr = e ∧ denseVarsInListF xs arr[i].vars = true ∧ arr[i].active = true := by
  rw [denseGatherConstraintArrayV, ← Array.foldl_toList]
  induction positions.toList generalizing acc with
  | nil => simpa using hacc
  | cons i rest ih =>
      simp only [List.foldl_cons]
      exact ih (denseGatherConstraintAtV arr xs acc i)
        (denseGatherConstraintAtV_active_mem arr xs acc i hacc)

theorem denseGatherConstraintBucketsV_active_mem (arr : Array (DenseConstraintPlan p))
    (idx : DenseConstraintCovIndex) (xs vs : List VarId) (acc : DenseConstraintGatherV p)
    (hacc : ∀ e ∈ acc.active, ∃ i, ∃ h : i < arr.size,
      arr[i].expr = e ∧ denseVarsInListF xs arr[i].vars = true ∧ arr[i].active = true) :
    ∀ e ∈ (vs.foldl (fun acc v =>
        denseGatherConstraintArrayV arr xs (idx.buckets.getD v #[]) acc) acc).active,
      ∃ i, ∃ h : i < arr.size,
        arr[i].expr = e ∧ denseVarsInListF xs arr[i].vars = true ∧ arr[i].active = true := by
  induction vs generalizing acc with
  | nil => simpa using hacc
  | cons v rest ih =>
      simp only [List.foldl_cons]
      exact ih _ (denseGatherConstraintArrayV_active_mem arr xs _ acc hacc)

theorem denseGatherConstraintsV_active_mem (fidx : DenseForcedIdx p) (xs : List VarId)
    {e : DenseExpr p} (he : e ∈ (denseGatherConstraintsV fidx xs).active) :
    ∃ i, ∃ h : i < fidx.arrCs.size,
      fidx.arrCs[i].expr = e ∧ denseVarsInListF xs fidx.arrCs[i].vars = true ∧
        fidx.arrCs[i].active = true := by
  rw [denseGatherConstraintsV] at he
  apply denseGatherConstraintArrayV_active_mem fidx.arrCs xs fidx.csIdx.activeVarless _
    (denseGatherConstraintBucketsV_active_mem fidx.arrCs fidx.csIdx xs xs
      ⟨fidx.csIdx.inactiveVarlessCount, []⟩ (by simp)) e he

theorem denseGatherConstraintsV_plan_mem (fidx : DenseForcedIdx p)
    (plans : List (DenseConstraintPlan p)) (harr : fidx.arrCs = plans.toArray)
    (xs : List VarId) {e : DenseExpr p} (he : e ∈ (denseGatherConstraintsV fidx xs).active) :
    ∃ plan ∈ plans, plan.expr = e ∧ denseVarsInListF xs plan.vars = true ∧
      plan.active = true := by
  obtain ⟨i, hi, hie, hvars, hactive⟩ := denseGatherConstraintsV_active_mem fidx xs he
  let plan := fidx.arrCs[i]
  have hmemA : plan ∈ fidx.arrCs := by
    simp [plan]
  have hmem : plan ∈ plans := by
    rw [harr] at hmemA
    simpa using hmemA
  exact ⟨plan, hmem, by simpa [plan] using hie, by simpa [plan] using hvars,
    by simpa [plan] using hactive⟩

theorem denseGatherBusAtV_interactions_mem (arr : Array (DenseBusPlan p))
    (xs : List VarId) (acc : DenseBusGatherV p) (i : Nat)
    (hacc : ∀ bi ∈ acc.interactions, ∃ i, ∃ h : i < arr.size,
      arr[i].interaction = bi ∧ arr[i].usable = true ∧
        denseVarsInListF xs arr[i].vars = true) :
    ∀ bi ∈ (denseGatherBusAtV arr xs acc i).interactions,
      ∃ i, ∃ h : i < arr.size,
        arr[i].interaction = bi ∧ arr[i].usable = true ∧
          denseVarsInListF xs arr[i].vars = true := by
  intro bi hbi
  by_cases hi : i < arr.size
  · by_cases husable : arr[i].usable = true
    · by_cases hvars : denseVarsInListF xs arr[i].vars = true
      · simp only [denseGatherBusAtV, hi, ↓reduceDIte, husable, hvars, Bool.and_self,
          ↓reduceIte] at hbi
        rcases List.mem_cons.1 hbi with hbi | hbi
        · subst bi; exact ⟨i, hi, rfl, husable, hvars⟩
        · exact hacc bi hbi
      · apply hacc bi
        simpa [denseGatherBusAtV, hi, husable, hvars] using hbi
    · apply hacc bi
      simpa [denseGatherBusAtV, hi, husable] using hbi
  · apply hacc bi
    simpa [denseGatherBusAtV, hi] using hbi

theorem denseGatherBusArrayV_interactions_mem (arr : Array (DenseBusPlan p))
    (xs : List VarId) (positions : Array Nat) (acc : DenseBusGatherV p)
    (hacc : ∀ bi ∈ acc.interactions, ∃ i, ∃ h : i < arr.size,
      arr[i].interaction = bi ∧ arr[i].usable = true ∧
        denseVarsInListF xs arr[i].vars = true) :
    ∀ bi ∈ (denseGatherBusArrayV arr xs positions acc).interactions,
      ∃ i, ∃ h : i < arr.size,
        arr[i].interaction = bi ∧ arr[i].usable = true ∧
          denseVarsInListF xs arr[i].vars = true := by
  rw [denseGatherBusArrayV, ← Array.foldl_toList]
  induction positions.toList generalizing acc with
  | nil => simpa using hacc
  | cons i rest ih =>
      simp only [List.foldl_cons]
      exact ih (denseGatherBusAtV arr xs acc i)
        (denseGatherBusAtV_interactions_mem arr xs acc i hacc)

theorem denseGatherBusBucketsV_interactions_mem (arr : Array (DenseBusPlan p))
    (idx : DenseArrayCovIndex) (xs vs : List VarId) (acc : DenseBusGatherV p)
    (hacc : ∀ bi ∈ acc.interactions, ∃ i, ∃ h : i < arr.size,
      arr[i].interaction = bi ∧ arr[i].usable = true ∧
        denseVarsInListF xs arr[i].vars = true) :
    ∀ bi ∈ (vs.foldl (fun acc v =>
        denseGatherBusArrayV arr xs (idx.buckets.getD v #[]) acc) acc).interactions,
      ∃ i, ∃ h : i < arr.size,
        arr[i].interaction = bi ∧ arr[i].usable = true ∧
          denseVarsInListF xs arr[i].vars = true := by
  induction vs generalizing acc with
  | nil => simpa using hacc
  | cons v rest ih =>
      simp only [List.foldl_cons]
      exact ih _ (denseGatherBusArrayV_interactions_mem arr xs _ acc hacc)

theorem denseGatherBusesV_interactions_mem (fidx : DenseForcedIdx p) (xs : List VarId)
    {bi : BusInteraction (DenseExpr p)} (hbi : bi ∈ (denseGatherBusesV fidx xs).interactions) :
    ∃ i, ∃ h : i < fidx.arrBis.size,
      fidx.arrBis[i].interaction = bi ∧ fidx.arrBis[i].usable = true ∧
        denseVarsInListF xs fidx.arrBis[i].vars = true := by
  rw [denseGatherBusesV] at hbi
  apply denseGatherBusArrayV_interactions_mem fidx.arrBis xs fidx.bisIdx.varless _
    (denseGatherBusBucketsV_interactions_mem fidx.arrBis fidx.bisIdx xs xs
      ⟨0, false, true, []⟩ (by simp)) bi hbi

theorem denseGatherBusesV_plan_mem (fidx : DenseForcedIdx p) (plans : List (DenseBusPlan p))
    (harr : fidx.arrBis = plans.toArray) (xs : List VarId)
    {bi : BusInteraction (DenseExpr p)} (hbi : bi ∈ (denseGatherBusesV fidx xs).interactions) :
    ∃ plan ∈ plans, plan.interaction = bi ∧ plan.usable = true ∧
      denseVarsInListF xs plan.vars = true := by
  obtain ⟨i, hi, hbi', husable, hvars⟩ := denseGatherBusesV_interactions_mem fidx xs hbi
  let plan := fidx.arrBis[i]
  have hmemA : plan ∈ fidx.arrBis := by
    simp [plan]
  have hmem : plan ∈ plans := by
    rw [harr] at hmemA
    simpa using hmemA
  exact ⟨plan, hmem, by simpa [plan] using hbi', by simpa [plan] using husable,
    by simpa [plan] using hvars⟩

/-- **Value-only `forcedOver` entailment.** Every forced pair `(x, c)` is entailed by `denv`, given
    the domain table is sound at `denv` and the covered items evaluate/oblige correctly. -/
theorem denseForcedOverV_entails (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p) (xs : List VarId) (denv : VarId → ZMod p)
    (hTs : DenseTableSoundAt denv T)
    (hes : ∀ e ∈ (denseGatherConstraintsV fidx xs).active,
      e.eval denv = 0 ∧ ∀ i ∈ e.vars, i ∈ xs)
    (hbis : ∀ bi ∈ (denseGatherBusesV fidx xs).interactions,
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
    split_ifs with hbox hwork hfast
    · exact denseConstantDomainsV_entails fdoms denv hmem
    · have hsurv : (denseCompiledSurvV bs facts
          (denseGatherConstraintsV fidx xs).active
          (denseGatherBusesV fidx xs).interactions
          (fdoms.map Prod.fst)).run ((fdoms.map Prod.fst).map denv) = true := by
        apply denseCompiledSurvV_restriction
        · exact fun e he => (hes e he).1
        · exact fun bi hbi => (hbis bi hbi).1
        · intro e he i hi; rw [hkeys]; exact (hes e he).2 i hi
        · intro bi hbi i hi; rw [hkeys]; exact (hbis bi hbi).2 i hi
      cases hscan : denseScanBoxV (denseCompiledSurvV bs facts
          (denseGatherConstraintsV fidx xs).active
          (denseGatherBusesV fidx xs).interactions
          (fdoms.map Prod.fst)).run (fdoms.map Prod.snd) with
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

theorem denseVarsInListF_mem (xs vs : List VarId) (h : denseVarsInListF xs vs = true) :
    ∀ i ∈ vs, i ∈ xs := by
  induction vs with
  | nil => intro i hi; simp at hi
  | cons v rest ih =>
      rw [denseVarsInListF, Bool.and_eq_true] at h
      intro i hi
      rcases List.mem_cons.mp hi with hi | hi
      · subst i; exact denseContainsFast_mem xs _ h.1
      · exact ih h.2 i hi

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

/-- `(Task.spawn f).get` reduces to `f ()` definitionally (`Task` is a one-field structure filled
    with `fn ()`). -/
theorem get_spawn {α : Type} (f : Unit → α) : (Task.spawn f).get = f () := rfl

/-- The parallel and serial branches of `denseCollectForcedV` compute the same solution map, so the
    entailment invariant can be proved over the single serial fold over `denseDedupTargetsV`. -/
theorem denseCollectForcedV_eq_serial (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p) (parallel : Bool)
    (targets : List (List VarId)) (seen : Std.HashSet (List VarId)) (dσ0 : DenseSolved p) :
    denseCollectForcedV bs facts T fidx parallel targets seen dσ0
      = (denseDedupTargetsV targets seen).foldl
          (fun dσ xs => dσ.insertAll
            ((denseForcedOverV bs facts T fidx xs).map (fun f => (f.1, DenseExpr.const f.2)))) dσ0 := by
  simp only [denseCollectForcedV]
  split_ifs with hp
  · simp only [List.foldl_map, get_spawn]
  · rfl

/-- The `collectForced` fold preserves the entailment invariant (via
    `denseCollectForcedV_eq_serial`; `hforced` is stated for every variable set). -/
theorem denseCollectForcedV_entailed (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p)
    (d : DenseConstraintSystem p)
    (hforced : ∀ xs, ∀ f ∈ denseForcedOverV bs facts T fidx xs, ∀ denv,
      d.satisfies bs denv → denv f.1 = f.2) :
    ∀ (parallel : Bool) (targets : List (List VarId)) (seen : Std.HashSet (List VarId))
      (dσ : DenseSolved p),
      EntailedMap d bs dσ.map →
      EntailedMap d bs (denseCollectForcedV bs facts T fidx parallel targets seen dσ).map := by
  have hfold : ∀ (uniq : List (List VarId)) (dσ : DenseSolved p), EntailedMap d bs dσ.map →
      EntailedMap d bs (uniq.foldl (fun dσ xs => dσ.insertAll
        ((denseForcedOverV bs facts T fidx xs).map (fun f => (f.1, DenseExpr.const f.2)))) dσ).map := by
    intro uniq
    induction uniq with
    | nil => intro dσ h; exact h
    | cons xs rest ih =>
      intro dσ h
      rw [List.foldl_cons]
      apply ih
      rw [DenseSolved.insertAll_map]
      apply EntailedMap_foldl_insert d bs _ dσ.map h
      intro pr hpr
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hpr
      refine ⟨fun z hz => by simp [DenseExpr.vars] at hz, fun denv hsat => ?_⟩
      show denv f.1 = (DenseExpr.const f.2).eval denv
      rw [DenseExpr.eval]
      exact hforced xs f hf denv hsat
  intro parallel targets seen dσ h
  rw [denseCollectForcedV_eq_serial]
  exact hfold (denseDedupTargetsV targets seen) dσ h

/-! ## Reflexive (identity) correctness -/

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

def dbConstraintPlans (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseConstraintPlan p) :=
  denseConstraintPlansV (dbT bs facts d) d.algebraicConstraints

def dbBusPlans (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseBusPlan p) :=
  denseBusPlansV bs facts (dbT bs facts d) d.busInteractions

/-- The target list built by `denseDomainBatchσV`. -/
def dbTargets (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (List VarId) :=
  densePlanTargetsV (dbConstraintPlans bs facts d) (dbBusPlans bs facts d)

/-- The inverted index built by `denseDomainBatchσV`. -/
def dbFidx (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseForcedIdx p :=
  denseForcedIdxV (dbConstraintPlans bs facts d) (dbBusPlans bs facts d)

theorem denseDomainBatchσV_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseDomainBatchσV bs facts d
      = denseCollectForcedV bs facts (dbT bs facts d) (dbFidx bs facts d)
          (8192 ≤ d.algebraicConstraints.length) (dbTargets bs facts d) ∅ DenseSolved.empty := rfl

theorem denseDomainBatchσV_entailed [Fact p.Prime] [NeZero p]
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    EntailedMap d bs (denseDomainBatchσV bs facts d).map := by
  rw [denseDomainBatchσV_eq]
  refine denseCollectForcedV_entailed bs facts (dbT bs facts d) (dbFidx bs facts d) d
    ?hforced (8192 ≤ d.algebraicConstraints.length) (dbTargets bs facts d) ∅ DenseSolved.empty ?hbase
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
      obtain ⟨plan, hplan, hpe, hpvars, _⟩ := denseGatherConstraintsV_plan_mem
        (dbFidx bs facts d) (dbConstraintPlans bs facts d) rfl xs he
      rw [dbConstraintPlans, denseConstraintPlansV] at hplan
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hplan
      simp only at hpe hpvars
      subst e
      refine ⟨hsat.1 c hc, ?_⟩
      intro i hi
      apply denseVarsInListF_mem xs (HashedDedup.hashedDedup (hash ·) c.vars) hpvars i
      rw [HashedDedup.hashedDedup_eq]
      simpa using hi
    · intro bi hbi
      obtain ⟨plan, hplan, hpbi, _, hpvars⟩ := denseGatherBusesV_plan_mem
        (dbFidx bs facts d) (dbBusPlans bs facts d) rfl xs hbi
      rw [dbBusPlans, denseBusPlansV] at hplan
      obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.mp hplan
      simp only at hpbi hpvars
      subst bi
      refine ⟨hsat.2 bi0 hbi0, ?_⟩
      intro i hi
      apply denseVarsInListF_mem xs
        (HashedDedup.hashedDedup (hash ·) (denseBIVars bi0)) hpvars i
      rw [HashedDedup.hashedDedup_eq]
      simpa using hi

/-! ## The value-only domain-batch pass -/

theorem denseDomainBatchTransformV_covered (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    (denseDomainBatchTransformV pw bs facts d).CoveredBy reg := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show denseDomainBatchTransformV pw bs facts d = applyσ (denseDomainBatchσV bs facts d) d
        from by simp only [denseDomainBatchTransformV, if_pos hpB], applyσ]
    by_cases he : (denseDomainBatchσV bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact hcov
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_covered hcov (fun i _ t ht z hz => ?_)
      exact DenseConstraintSystem.occ_valid hcov z
        ((denseDomainBatchσV_entailed bs facts d i t ht).1 z hz)
  · rw [show denseDomainBatchTransformV pw bs facts d = d
        from by simp only [denseDomainBatchTransformV, if_neg hpB]]
    exact hcov

theorem denseDomainBatchTransformV_correct (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseDomainBatchTransformV pw bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show denseDomainBatchTransformV pw bs facts d = applyσ (denseDomainBatchσV bs facts d) d
        from by simp only [denseDomainBatchTransformV, if_pos hpB], applyσ]
    by_cases he : (denseDomainBatchσV bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact DensePassCorrect_refl reg.isInput d bs
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_denseCorrect d (denseDomainBatchσV bs facts d).fn bs
        reg.isInput (fun denv hsat j t hjt => ?_) (fun j t hjt z hz => ?_)
      · exact (denseDomainBatchσV_entailed bs facts d j t hjt).2 denv hsat
      · exact (denseDomainBatchσV_entailed bs facts d j t hjt).1 z hz
  · rw [show denseDomainBatchTransformV pw bs facts d = d
        from by simp only [denseDomainBatchTransformV, if_neg hpB]]
    exact DensePassCorrect_refl reg.isInput d bs

/-- The dense domain-batch pass (see `denseDomainBatchσV`). -/
def denseDomainBatchPassV (pw : PrimeWitness p) : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := denseDomainBatchTransformV pw bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := denseDomainBatchTransformV_covered pw reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := DensePassCorrect.lift hcov
      (denseDomainBatchTransformV_covered pw reg bs facts d hcov) (by intro x hx; simp at hx)
      (denseDomainBatchTransformV_correct pw reg bs facts d) }

end ApcOptimizer.Dense
