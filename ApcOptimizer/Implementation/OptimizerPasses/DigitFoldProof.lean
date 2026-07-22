import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Soundness of the dense fact-derived bounds map (`denseBuild`, `DigitFold.lean`): a value
bound `denv i < b` holds for every assignment whose bus interactions are non-violating. Threaded
through the build recursion as the fixed-`denv` invariant `DenseBMSoundAt`. -/

namespace ApcOptimizer.Dense

open DigitFold

variable {p : ℕ}

/-! ## Probe-payload characterization -/

/-- With slot `i` a raw variable, slot `j` arbitrary, and every other slot a constant, the evaluated
    payload with slot `j` zeroed *is* the dense probe payload at `denv x`. -/
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

/-! ## Probed-bound soundness -/

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

/-- At a fixed environment, every stored bound is a strict upper bound on the environment's
    value for its variable. -/
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

/-- `goCands` preserves the invariant (probed bounds sound by `denseProbedSlotBoundAt_sound`). -/
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

/-- `addVars` preserves the invariant (interaction bounds sound by `denseInteractionBound_sound`,
    then probed bounds via `goCands`). -/
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

/-! ## The bounds-map soundness capstone -/

/-- **Bounds-map soundness.** A bound stored by `denseBuild` for `i` is a strict upper bound
    on `denv i` for every assignment whose bus interactions are non-violating. -/
theorem denseBuild_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (i : VarId) (b : Nat)
    (hlk : (denseBuild bs facts bis)[i]? = some b) (denv : VarId → ZMod p)
    (hbus : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) : (denv i).val < b := by
  unfold denseBuild at hlk
  exact denseAddAll_soundAt bs facts denv bis hbus ∅ (DenseBMSoundAt.empty denv) i b hlk

/-! # Correctness of the dense digit-fold pass (`denseDigitFoldPass`, `DigitFold.lean`), reducing
the forced substitution to `DenseConstraintSystem.substF_denseCorrect` (`DomainBatchProof.lean`). -/

/-! ## Byte-pair recognizer soundness -/

/-- Acceptance of a recognized pair check bounds both operands below 256 (via the value-level
    `BusFacts.byteXorSpec_sound`). -/
theorem densePairByteOps?_bytes (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (x y : DenseExpr p)
    (h : densePairByteOps? bs facts bi = some (x, y))
    (h1 : (1 : ZMod p) ≠ 0) (denv : VarId → ZMod p)
    (hacc : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    (x.eval denv).val < 256 ∧ (y.eval denv).val < 256 := by
  unfold densePairByteOps? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i op o1 o2 r hdec
      split_ifs at h with hcond
      obtain ⟨hbound, hop, _, hm⟩ := hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmv : (denseBIEval bi denv).multiplicity = 1 := by
        show bi.multiplicity.eval denv = 1; rw [hm]; rfl
      have hviol : bs.violatesConstraint (denseBIEval bi denv) = false :=
        hacc (by rw [hmv]; simpa using h1)
      have hopEv : op.eval denv = spec.pairOp := by rw [hop]; rfl
      have hdecEv : spec.decode (denseBIEval bi denv).payload
          = some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
        show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
        rw [spec.decode_map, hdec]; rfl
      obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
      obtain ⟨hb1, hb2, _⟩ :=
        ((hsound (denseBIEval bi denv).payload (op.eval denv) (o1.eval denv) (o2.eval denv)
          (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv).2 hopEv).mp hviol
      rw [hbound] at hb1 hb2
      exact ⟨hb1, hb2⟩
    · exact absurd h (by simp)

/-! ## Ladder soundness chain -/

/-- A dense ladder's ZMod sum is the cast of its ℕ positional value (up to sign). -/
theorem denseIsLadder_sum [NeZero p] (pos : Bool) :
    ∀ (g : ℕ) (l : List (VarId × ZMod p)), denseIsLadder pos g l = true →
    ∀ (denv : VarId → ZMod p),
    (l.map (fun t => t.2 * denv t.1)).sum =
      signum pos * ((g * ladderVal (l.map (fun t => (denv t.1).val)) : ℕ) : ZMod p) := by
  intro g l
  induction l generalizing g with
  | nil => intro _ denv; simp [ladderVal]
  | cons t rest ih =>
    intro h denv
    obtain ⟨v, c⟩ := t
    simp only [denseIsLadder, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, hrest⟩ := h
    have hsum := ih (256 * g) hrest denv
    simp only [List.map_cons, List.sum_cons, hsum, ladderVal]
    have henv : denv v = (((denv v).val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse (denv v)).symm
    cases pos with
    | true =>
      have hcv : c = ((g : ℕ) : ZMod p) := by
        rw [← hc]; exact (ZMod.natCast_rightInverse c).symm
      rw [hcv, signum_true]
      conv_lhs => rw [henv]
      push_cast
      ring
    | false =>
      have hcv : -c = ((g : ℕ) : ZMod p) := by
        rw [← hc]; exact (ZMod.natCast_rightInverse (-c)).symm
      have hcv' : c = -((g : ℕ) : ZMod p) := by rw [← hcv]; ring
      rw [hcv', signum_false]
      conv_lhs => rw [henv]
      push_cast
      ring

/-- If the solution grid for a byte-checked dense ladder is the singleton `[ds]`, any satisfying
    assignment's digit vector is exactly `ds`. -/
theorem denseEnv_forced [NeZero p] (hp : 256 < p) (pos : Bool) (g : ℕ) (hg : 0 < g) (K : ZMod p)
    (l : List (VarId × ZMod p)) (hlad : denseIsLadder pos g l = true)
    (Bs : List ℕ) (hB : ∀ B ∈ Bs, B ≤ 256)
    (denv : VarId → ZMod p)
    (hbound : List.Forall₂ (fun (t : VarId × ZMod p) B => (denv t.1).val < B) l Bs)
    (hbyte : ((K + (l.map (fun t => t.2 * denv t.1)).sum).val) < 256)
    (ds : List ℕ)
    (hsol : solutions p (tval pos K) g Bs (g * ladderVal (Bs.map (· - 1))) = [ds]) :
    l.map (fun t => (denv t.1).val) = ds := by
  have hp0 : 0 < p := by omega
  have hxB : List.Forall₂ (· < ·) (l.map (fun t => (denv t.1).val)) Bs := by
    rw [List.forall₂_map_left_iff]
    exact hbound
  have hsum := denseIsLadder_sum pos g l hlad denv
  have hEvcast : (((K + (l.map (fun t => t.2 * denv t.1)).sum).val : ℕ) : ZMod p)
      = K + (l.map (fun t => t.2 * denv t.1)).sum :=
    ZMod.natCast_rightInverse _
  have hmod : (g * ladderVal (l.map (fun t => (denv t.1).val))) % p
      = tval pos K ((K + (l.map (fun t => t.2 * denv t.1)).sum).val) := by
    have hvalS : (((g * ladderVal (l.map (fun t => (denv t.1).val)) : ℕ)) : ZMod p).val
        = g * ladderVal (l.map (fun t => (denv t.1).val)) % p := by
      rw [ZMod.val_natCast]
    rw [← hvalS]
    unfold tval
    congr 1
    rw [hEvcast]
    cases pos with
    | true =>
      rw [hsum, signum_true, one_mul]
      simp
    | false =>
      rw [hsum, signum_false]
      simp only [Bool.false_eq_true, if_false]
      ring
  have hle : g * ladderVal (l.map (fun t => (denv t.1).val))
      ≤ g * ladderVal (Bs.map (· - 1)) :=
    Nat.mul_le_mul_left g (ladderVal_le_box _ Bs hxB)
  exact solutions_forced p (tval pos K) g Bs _ hp0 hg ds hsol _ hxB hB
    ((K + (l.map (fun t => t.2 * denv t.1)).sum).val) hbyte hmod hle

/-- Recognizing a dense ladder yields a permutation of the input terms with the leading coefficient
    positive and the ladder shape confirmed. -/
theorem denseTryLadder_spec (pos : Bool) (terms : List (VarId × ZMod p))
    (g : ℕ) (sorted : List (VarId × ZMod p))
    (h : denseTryLadder pos terms = some (g, sorted)) :
    terms.Perm sorted ∧ 0 < g ∧ denseIsLadder pos g sorted = true := by
  unfold denseTryLadder at h
  split at h
  · exact absurd h (by simp)
  · rename_i t rest hms
    split_ifs at h with hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hperm : (terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2)).Perm terms :=
      List.mergeSort_perm terms _
    rw [hms] at hperm
    exact ⟨hperm.symm, hcond.1, hcond.2⟩

/-- Bound lookup returns byte-sized (`≤ 256`) bounds paired to the terms in order. -/
theorem denseLookupBounds_spec (bounds : Std.HashMap VarId Nat) :
    ∀ (l : List (VarId × ZMod p)) (Bs : List ℕ), denseLookupBounds bounds l = some Bs →
    (∀ B ∈ Bs, B ≤ 256) ∧
      List.Forall₂ (fun (t : VarId × ZMod p) B => bounds[t.1]? = some B) l Bs := by
  intro l
  induction l with
  | nil =>
    intro Bs h
    simp only [denseLookupBounds, Option.some.injEq] at h
    subst h
    exact ⟨by simp, List.Forall₂.nil⟩
  | cons t rest ih =>
    intro Bs h
    obtain ⟨v, c⟩ := t
    simp only [denseLookupBounds] at h
    split at h
    · rename_i B hB
      split_ifs at h with hle
      obtain ⟨Bs', hBs', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h256, hall⟩ := ih Bs' hBs'
      refine ⟨?_, List.Forall₂.cons hB hall⟩
      intro B' hB'
      rcases List.mem_cons.1 hB' with rfl | hB'
      · exact hle
      · exact h256 B' hB'
    · exact absurd h (by simp)

/-- One sign interpretation forces the lowest-coefficient variable's value, using fact bounds valid
    at the assignment. -/
theorem denseAttemptLadder_sound [NeZero p] (hp : 256 < p) (bounds : Std.HashMap VarId Nat)
    (pos : Bool) (l : DenseLinExpr p) (v : VarId) (d : ℕ)
    (h : denseAttemptLadder pos bounds l = some (v, d))
    (denv : VarId → ZMod p)
    (hB : ∀ w bnd, bounds[w]? = some bnd → (denv w).val < bnd)
    (hbyte : (l.eval denv).val < 256) :
    denv v = (d : ZMod p) := by
  unfold denseAttemptLadder at h
  split at h
  · exact absurd h (by simp)
  · rename_i gs hladder
    split at h
    · exact absurd h (by simp)
    · rename_i Bs hbounds
      split at h
      · rename_i hsol'
        split at h
        · rename_i t htail d' dtail hsorted
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hperm, hg, hlad⟩ := denseTryLadder_spec pos l.terms gs.1 gs.2 hladder
          obtain ⟨h256, hbmap⟩ := denseLookupBounds_spec bounds gs.2 Bs hbounds
          have hbound : List.Forall₂ (fun (t : VarId × ZMod p) B => (denv t.1).val < B)
              gs.2 Bs :=
            hbmap.imp (fun {t} {B} hlk => hB t.1 B hlk)
          have hsumeq : (l.terms.map (fun t => t.2 * denv t.1)).sum
              = (gs.2.map (fun t => t.2 * denv t.1)).sum :=
            (hperm.map (fun t => t.2 * denv t.1)).sum_eq
          have hbyte' : ((l.const + (gs.2.map (fun t => t.2 * denv t.1)).sum).val) < 256 := by
            have hev : l.eval denv = l.const + (gs.2.map (fun t => t.2 * denv t.1)).sum := by
              rw [DenseLinExpr.eval, hsumeq]
            rwa [hev] at hbyte
          have hforced := denseEnv_forced hp pos gs.1 hg l.const gs.2 hlad Bs h256 denv hbound
            hbyte' (d' :: dtail) hsol'
          rw [hsorted] at hforced
          simp only [List.map_cons, List.cons.injEq] at hforced
          have hv : (denv t.1).val = d' := hforced.1
          rw [← hv]
          exact (ZMod.natCast_rightInverse (denv t.1)).symm
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- Solving one byte-checked operand forces the returned variable's value. -/
theorem denseSolveOperand_sound [NeZero p] (hp : 256 < p) (bounds : Std.HashMap VarId Nat)
    (E : DenseExpr p) (v : VarId) (d : ℕ)
    (h : denseSolveOperand bounds E = some (v, d))
    (denv : VarId → ZMod p)
    (hB : ∀ w bnd, bounds[w]? = some bnd → (denv w).val < bnd)
    (hbyte : (E.eval denv).val < 256) :
    denv v = (d : ZMod p) := by
  unfold denseSolveOperand at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    have hEl : E.eval denv = l.eval denv := denseLinearize_eval E l hlin denv
    rw [hEl] at hbyte
    split_ifs at h
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      subst h
      exact denseAttemptLadder_sound hp bounds true l v d hr denv hB hbyte
    · exact denseAttemptLadder_sound hp bounds false l v d h denv hB hbyte

/-! ## The scan entailment -/

/-- On a hit `(i, dd)`, every satisfying assignment forces `denv i = dd`; value bounds threaded as
    a fixed-`denv` hypothesis. -/
theorem denseFindFold_sound [NeZero p] (hp : 256 < p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bounds : Std.HashMap VarId Nat) (denv : VarId → ZMod p)
    (hB : ∀ w bnd, bounds[w]? = some bnd → (denv w).val < bnd) :
    ∀ (pending : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ pending, (denseBIEval bi denv).multiplicity ≠ 0 →
        bs.violatesConstraint (denseBIEval bi denv) = false) →
      ∀ i dd, denseFindFold bs facts bounds pending = some (i, dd) → denv i = (dd : ZMod p) := by
  intro pending
  induction pending with
  | nil => intro _ i dd h; simp [denseFindFold] at h
  | cons bi rest ih =>
      intro hpend i dd h
      have hacc := hpend bi (List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest, (denseBIEval b denv).multiplicity ≠ 0 →
          bs.violatesConstraint (denseBIEval b denv) = false :=
        fun b hb => hpend b (List.mem_cons_of_mem _ hb)
      have h1 : (1 : ZMod p) ≠ 0 := by
        haveI : Fact (1 < p) := ⟨by omega⟩
        exact one_ne_zero
      unfold denseFindFold at h
      cases hdp : densePairByteOps? bs facts bi with
      | none => rw [hdp] at h; dsimp only at h; exact ih hrest i dd h
      | some xy =>
          obtain ⟨x, y⟩ := xy
          rw [hdp] at h; dsimp only at h
          obtain ⟨hbx, hby⟩ := densePairByteOps?_bytes bs facts bi x y hdp h1 denv hacc
          cases hsx : denseSolveOperand bounds x with
          | some r =>
              rw [hsx] at h; dsimp only at h; simp only [Option.some.injEq] at h
              subst h
              exact denseSolveOperand_sound hp bounds x i dd hsx denv hB hbx
          | none =>
              rw [hsx] at h; dsimp only at h
              cases hsy : denseSolveOperand bounds y with
              | some r =>
                  rw [hsy] at h; dsimp only at h; simp only [Option.some.injEq] at h
                  subst h
                  exact denseSolveOperand_sound hp bounds y i dd hsy denv hB hby
              | none => rw [hsy] at h; dsimp only at h; exact ih hrest i dd h

/-- If `denseFindFold` over the fact-built bounds map fires `(i, dd)`, every satisfying assignment
    of `d` has `denv i = dd` (bounds validity from `denseBuild_sound`). -/
theorem denseDigitFoldFindFold_entails [NeZero p] (hp : 256 < p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (i : VarId) (dd : ℕ)
    (h : denseFindFold bs facts (denseBuild bs facts d.busInteractions) d.busInteractions
      = some (i, dd)) :
    ∀ denv, d.satisfies bs denv → denv i = (dd : ZMod p) := by
  intro denv hsat
  have hbus := hsat.2
  have hB : ∀ w bnd, (denseBuild bs facts d.busInteractions)[w]? = some bnd → (denv w).val < bnd :=
    fun w bnd hlk => denseBuild_sound bs facts d.busInteractions w bnd hlk denv hbus
  exact denseFindFold_sound hp bs facts _ denv hB d.busInteractions hbus i dd h

/-! ## Reducing the point substitution to `substF` -/

/-- `DenseExpr.subst i t` is the simultaneous substitution of the singleton map `i ↦ t`. -/
theorem DenseExpr.subst_eq_substF (e : DenseExpr p) (i : VarId) (t : DenseExpr p) :
    e.subst i t = e.substF (fun j => if j = i then some t else none) := by
  induction e with
  | const n => rfl
  | var j =>
      simp only [DenseExpr.subst, DenseExpr.substF]
      by_cases h : j = i
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
  | add a b iha ihb => simp only [DenseExpr.subst, DenseExpr.substF, iha, ihb]
  | mul a b iha ihb => simp only [DenseExpr.subst, DenseExpr.substF, iha, ihb]

/-- Bus-interaction point substitution is the singleton simultaneous substitution. -/
theorem denseBIsubst_eq_substF (bi : BusInteraction (DenseExpr p)) (i : VarId) (t : DenseExpr p) :
    denseBIsubst bi i t = denseBIsubstF bi (fun j => if j = i then some t else none) := by
  simp only [denseBIsubst, denseBIsubstF, DenseExpr.subst_eq_substF]

/-- System point substitution is the singleton simultaneous substitution. -/
theorem denseSubst_eq_substF (d : DenseConstraintSystem p) (i : VarId) (t : DenseExpr p) :
    d.subst i t = d.substF (fun j => if j = i then some t else none) := by
  simp only [DenseConstraintSystem.subst, DenseConstraintSystem.substF, DenseExpr.subst_eq_substF,
    denseBIsubst_eq_substF]

/-! ## The pass -/

/-- Coverage preservation: a constant substitution keeps every mentioned variable registered. -/
theorem denseDigitFoldF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseDigitFoldF bs facts d).CoveredBy reg := by
  unfold denseDigitFoldF
  by_cases hp : 256 < p
  · rw [if_pos hp]
    cases denseFindFold bs facts (denseBuild bs facts d.busInteractions) d.busInteractions with
    | none => exact hcov
    | some idd =>
        obtain ⟨i, dd⟩ := idd
        exact DenseConstraintSystem.subst_covered hcov (DenseExpr.coveredBy_const reg _)
  · rw [if_neg hp]; exact hcov

/-- Digit-fold correctness: the fired constant substitution preserves the satisfying set (forced
    digit via `denseDigitFoldFindFold_entails`), through `DenseConstraintSystem.substF_denseCorrect`;
    the no-fire and small-`p` branches are the identity. -/
theorem denseDigitFoldF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseDigitFoldF bs facts d) [] bs := by
  unfold denseDigitFoldF
  by_cases hp : 256 < p
  · rw [if_pos hp]
    haveI : NeZero p := ⟨by omega⟩
    cases hff : denseFindFold bs facts (denseBuild bs facts d.busInteractions)
        d.busInteractions with
    | none => exact DensePassCorrect.refl reg.isInput d bs
    | some idd =>
        obtain ⟨i, dd⟩ := idd
        show DensePassCorrect reg.isInput d (d.subst i (DenseExpr.const (dd : ZMod p))) [] bs
        rw [denseSubst_eq_substF d i (DenseExpr.const (dd : ZMod p))]
        refine DenseConstraintSystem.substF_denseCorrect d
          (fun j => if j = i then some (DenseExpr.const (dd : ZMod p)) else none) bs reg.isInput
          ?_ ?_
        · intro denv hsat j t hjt
          dsimp only at hjt
          by_cases hji : j = i
          · rw [if_pos hji] at hjt
            simp only [Option.some.injEq] at hjt
            rw [← hjt, hji]
            exact denseDigitFoldFindFold_entails hp bs facts d i dd hff denv hsat
          · rw [if_neg hji] at hjt; exact absurd hjt (by simp)
        · intro j t hjt z hz
          dsimp only at hjt
          by_cases hji : j = i
          · rw [if_pos hji] at hjt
            simp only [Option.some.injEq] at hjt
            rw [← hjt] at hz; simp [DenseExpr.vars] at hz
          · rw [if_neg hji] at hjt; exact absurd hjt (by simp)
  · rw [if_neg hp]; exact DensePassCorrect.refl reg.isInput d bs

/-- The dense bounded-payload digit fold pass; correctness via `denseDigitFoldF_correct`. -/
def denseDigitFoldPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    denseDigitFoldF
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseDigitFoldF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseDigitFoldF_correct reg bs facts d)

end ApcOptimizer.Dense
