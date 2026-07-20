import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Native soundness of the dense fact-derived bounds map (Task 3)

Native, `VarId`-level soundness for the dense bounds map built by `denseBuild` (`DigitFold.lean`),
proved over dense environments `VarId → ZMod p` with no decode and no dependency on the reference
`BoundsMap` proof. This is the shared bounds-map fact consumed by both `digitFold` and `carryBranch`
(and, via the swap below, `hintCollapse`): a value bound `denv i < b` holds for every assignment
`denv` whose bus interactions are non-violating (the second half of dense satisfaction).

The argument mirrors the spec `BoundsMap.build`'s `sound` field (`MemoryUnify.lean`) and the
`probedSlotBoundAt_sound` / `interactionBound_sound` value bounds (`DomainProp.lean`), transliterated
onto `denseBIEval` and threaded through the build recursion as a fixed-`denv` invariant
`DenseBMSoundAt` — the value-level `DomainBatchProof.DenseTableSoundAt` pattern. The per-interaction
`denseInteractionBound_sound` and the constant/pattern soundness lemmas are reused from
`DomainBatchProof.lean`; the probed-bound soundness (`denseProbedSlotBoundAt_sound`) is proved here as
the dense twin of `probedSlotBoundAt_sound`. -/

namespace ApcOptimizer.Dense

open DigitFold

variable {p : ℕ}

/-! ## Native probe-payload characterization (dense twin of `probeBase_eq_set`) -/

/-- With slot `i` a raw variable, slot `j` arbitrary, and every other slot a constant, the evaluated
    payload with slot `j` zeroed *is* the dense probe payload at `denv x`. Dense twin of
    `probeBase_eq_set` (`DomainProp.lean`). -/
theorem denseProbeBase_eq_set (payload : List (DenseExpr p)) (denv : VarId → ZMod p)
    (i j : Nat) (hij : i ≠ j) (x : VarId)
    (hi : payload[i]? = some (.var x))
    (hconst : ∀ k, k ≠ i → k ≠ j → ∀ e', payload[k]? = some e' → (DenseExpr.constValue? e').isSome) :
    ((payload.map (fun e => e.eval denv)).set j 0)
      = (denseProbeBase payload i (denv x)).set j 0 := by
  have hilen : i < payload.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hi
    exact absurd hi (by simp)
  apply List.ext_getElem?
  intro k
  by_cases hkj : k = j
  · subst hkj
    rw [List.getElem?_set, List.getElem?_set]
    simp [denseProbeBase]
  · rw [List.getElem?_set_ne (fun h => hkj h.symm), List.getElem?_set_ne (fun h => hkj h.symm)]
    by_cases hki : k = i
    · subst hki
      rw [List.getElem?_map, hi, denseProbeBase, List.getElem?_set, if_pos rfl]
      rw [List.length_map, if_pos hilen]
      rfl
    · rw [List.getElem?_map, denseProbeBase, List.getElem?_set_ne (fun h => hki h.symm),
        List.getElem?_map]
      cases hk : payload[k]? with
      | none => rfl
      | some e' =>
        have hcv := hconst k hki hkj e' hk
        obtain ⟨cv, hcveq⟩ := Option.isSome_iff_exists.1 hcv
        simp only [Option.map_some]
        rw [e'.constValue?_sound cv hcveq denv, hcveq]
        rfl

/-! ## Native probed-bound soundness (dense twin of `probedSlotBoundAt_sound`) -/

theorem denseProbedSlotBoundAt_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) (j : Nat) (bound : Nat)
    (h : denseProbedSlotBoundAt bs facts bi i j = some bound) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (denv i).val < bound := by
  unfold denseProbedSlotBoundAt at h
  split_ifs at h with hp0
  haveI : NeZero p := ⟨hp0⟩
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i mval hm
  split_ifs at h with hmz
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i s hslot
  split_ifs at h with hsj
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i B₀ hB
  split_ifs at h with hcap
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i f hf
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i e hj
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i l hlin
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i y c heq_terms
  split_ifs at h with hcond
  obtain ⟨hyi, hall⟩ := hcond
  rw [hyi] at heq_terms
  unfold capBound at h
  split_ifs at h with hbnd
  simp only [Option.some.injEq] at h
  subst h
  -- the obligation is active
  have hmeval : (denseBIEval bi denv).multiplicity = mval :=
    bi.multiplicity.constValue?_sound mval hm denv
  have hviol : bs.violatesConstraint (denseBIEval bi denv) = false := by
    apply hob; rw [hmeval]; exact hmz
  have hpat : Matches (denseBIEval bi denv).payload
      (bi.payload.map DenseExpr.constValue?) :=
    denseMatches_evalPattern bi.payload denv
  -- base bound for `i`
  have hgeti : bi.payload[s]? = some (.var i) := denseVarSlot_sound i bi.payload s hslot
  have hgetiE : (denseBIEval bi denv).payload[s]? = some (denv i) := by
    show (bi.payload.map (fun e' => e'.eval denv))[s]? = some (denv i)
    rw [List.getElem?_map, hgeti]
    rfl
  have hB' : facts.slotBound (denseBIEval bi denv).busId (denseBIEval bi denv).multiplicity
      (bi.payload.map DenseExpr.constValue?) s = some B₀ := by
    rw [hmeval]; exact hB
  have hbase : (denv i).val < B₀ :=
    facts.slotBound_sound (denseBIEval bi denv) (bi.payload.map DenseExpr.constValue?)
      s B₀ (denv i) hB' hpat hviol hgetiE
  -- functional dependence at slot `j`
  have hgetjE : (denseBIEval bi denv).payload[j]? = some (e.eval denv) := by
    show (bi.payload.map (fun e' => e'.eval denv))[j]? = some (e.eval denv)
    rw [List.getElem?_map, hj]
    rfl
  have hf' : facts.slotFun (denseBIEval bi denv).busId
      (bi.payload.map DenseExpr.constValue?) j = some f := hf
  have hfun : e.eval denv = f ((denseBIEval bi denv).payload.set j 0) :=
    facts.slotFun_sound (denseBIEval bi denv) (bi.payload.map DenseExpr.constValue?)
      j f (e.eval denv) hf' hpat hviol hgetjE
  -- the zeroed evaluated payload is the probe payload at `denv i`
  have hconst : ∀ k, k ≠ s → k ≠ j → ∀ e',
      bi.payload[k]? = some e' → (DenseExpr.constValue? e').isSome := by
    intro k hks hkj e' hk
    have hklen : k < bi.payload.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hk
      exact absurd hk (by simp)
    have := List.all_eq_true.1 hall k (List.mem_range.2 hklen)
    simp only [beq_iff_eq, Bool.or_eq_true] at this
    rcases this with (h' | h') | h'
    · exact absurd h' hks
    · exact absurd h' hkj
    · rw [hk] at h'
      simpa using h'
  have hpay : ((denseBIEval bi denv).payload).set j 0
      = (denseProbeBase bi.payload s (denv i)).set j 0 := by
    show ((bi.payload.map (fun e' => e'.eval denv)).set j 0)
        = (denseProbeBase bi.payload s (denv i)).set j 0
    exact denseProbeBase_eq_set bi.payload denv s j hsj i hgeti hconst
  -- the value equation `e = l.const + c·i`
  have heval : e.eval denv = l.const + c * denv i := by
    rw [denseLinearize_eval e l hlin denv]
    simp [DenseLinExpr.eval, heq_terms]
  -- the test passes at `v = (denv i).val`
  have hdenvi : (((denv i).val : ℕ) : ZMod p) = denv i :=
    ZMod.natCast_rightInverse (denv i)
  have htest : (f ((denseProbeBase bi.payload s (((denv i).val : ℕ) : ZMod p)).set j 0)
      == l.const + c * (((denv i).val : ℕ) : ZMod p)) = true := by
    rw [beq_iff_eq, hdenvi, ← hpay, ← hfun, heval]
  exact probeMax_lt _ B₀ (denv i).val hbase htest

/-! ## The fixed-`denv` build invariant and its induction -/

/-- Native soundness of a dense bounds map at a fixed environment: every stored bound is a strict
    upper bound on the environment's value for its variable (value-level, no decode). -/
def DenseBMSoundAt (denv : VarId → ZMod p) (T : Std.HashMap VarId Nat) : Prop :=
  ∀ i b, T[i]? = some b → (denv i).val < b

theorem DenseBMSoundAt.empty (denv : VarId → ZMod p) :
    DenseBMSoundAt denv (∅ : Std.HashMap VarId Nat) := by
  intro i b h
  rw [Std.HashMap.getElem?_empty] at h
  exact absurd h (by simp)

/-- Inserting a sound bound preserves the invariant (keeping the smaller bound is monotone). -/
theorem denseInsertEntry_soundAt {denv : VarId → ZMod p} {T : Std.HashMap VarId Nat}
    {i0 : VarId} {b0 : Nat} (hd : (denv i0).val < b0) (hT : DenseBMSoundAt denv T) :
    DenseBMSoundAt denv (denseInsertEntry T i0 b0) := by
  intro i b hi
  rw [show denseInsertEntry T i0 b0
        = (if (match T[i0]? with | some be => decide (b0 < be) | none => (true : Bool)) = true
            then T.insert i0 b0 else T) from rfl] at hi
  split_ifs at hi with hkeep
  · rw [Std.HashMap.getElem?_insert] at hi
    by_cases hii : i0 = i
    · rw [if_pos (by simpa using hii)] at hi
      simp only [Option.some.injEq] at hi
      subst hii; subst hi; exact hd
    · rw [if_neg (by simpa using hii)] at hi
      exact hT i b hi
  · exact hT i b hi

/-- `goCands` preserves the invariant (each candidate for a matching variable inserts a probed
    bound, sound by `denseProbedSlotBoundAt_sound`). -/
theorem denseGoCands_soundAt (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    ∀ (cl : List (VarId × Nat)) (T : Std.HashMap VarId Nat),
      DenseBMSoundAt denv T → DenseBMSoundAt denv (denseGoCands bs facts bi i cl T) := by
  intro cl
  induction cl with
  | nil => intro T hT; exact hT
  | cons c cl ih =>
      intro T hT
      obtain ⟨y, j⟩ := c
      unfold denseGoCands
      split
      · split
        · rename_i b hb
          exact ih _ (denseInsertEntry_soundAt
            (denseProbedSlotBoundAt_sound bs facts bi i j b hb denv hob) hT)
        · exact ih _ hT
      · exact ih _ hT

/-- `addVars` preserves the invariant (each raw variable inserts its interaction bound, sound by
    `denseInteractionBound_sound`, then its probed bounds via `goCands`). -/
theorem denseAddVars_soundAt (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) (cands : List (VarId × Nat)) :
    ∀ (xs : List VarId) (T : Std.HashMap VarId Nat),
      DenseBMSoundAt denv T → DenseBMSoundAt denv (denseAddVars bs facts bi cands xs T) := by
  intro xs
  induction xs with
  | nil => intro T hT; exact hT
  | cons i xs ih =>
      intro T hT
      have hT1 : DenseBMSoundAt denv (match denseInteractionBound bs facts bi i with
          | some b => denseInsertEntry T i b | none => T) := by
        split
        · rename_i bd hib
          exact denseInsertEntry_soundAt
            (denseInteractionBound_sound bs facts bi i bd hib denv hob) hT
        · exact hT
      exact ih _ (denseGoCands_soundAt bs facts bi i denv hob cands _ hT1)

/-- `addAll` preserves the invariant across every interaction. -/
theorem denseAddAll_soundAt (bs : BusSemantics p) (facts : BusFacts p bs) (denv : VarId → ZMod p) :
    ∀ (dbis : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ dbis, (denseBIEval bi denv).multiplicity ≠ 0 →
        bs.violatesConstraint (denseBIEval bi denv) = false) →
      ∀ (T : Std.HashMap VarId Nat), DenseBMSoundAt denv T →
        DenseBMSoundAt denv (denseAddAll bs facts dbis T) := by
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
      unfold denseAddAll
      exact ih hrest _ (denseAddVars_soundAt bs facts bi denv hbi (denseProbeCandidatesOf bi)
        (denseRawVarsOf bi) T hT)

/-! ## The native bounds-map soundness capstone -/

/-- **Native bounds-map soundness.** A bound stored by `denseBuild` for `i` is a strict upper bound
    on `denv i` for every assignment whose bus interactions are non-violating — the dense mirror of
    the spec `BoundsMap.build`'s carried `sound` field, proved value-level with no decode. -/
theorem denseBuild_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (i : VarId) (b : Nat)
    (hlk : (denseBuild bs facts bis)[i]? = some b) (denv : VarId → ZMod p)
    (hbus : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) : (denv i).val < b := by
  unfold denseBuild at hlk
  exact denseAddAll_soundAt bs facts denv bis hbus ∅ (DenseBMSoundAt.empty denv) i b hlk

end ApcOptimizer.Dense
