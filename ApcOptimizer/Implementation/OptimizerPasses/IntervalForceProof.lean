import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.BusUnifyProof
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof

set_option autoImplicit false

/-! # Dense interval forcing: native proof and wiring (Task 3)

Native `DensePassCorrect` proof for the dense `intervalForce` transform (`IntervalForce.lean`),
lifted to the audited spec via `DenseVerifiedPassW.of`. No dependency on the reference
`IntervalForce.intervalForcePass` — the pass is a single-shot **append of entailed constraints**, so
its correctness rides on the reusable `DensePassCorrect.denseAddConstraints` (`BusUnifyProof.lean`)
once every appended seed is shown to evaluate to `0` on any satisfying dense assignment.

The seed soundness is a direct transliteration of the spec's integer-window argument
(`slotSeeds_sound`/`walk_sound`/`interactionSeeds_sound`/`allSeeds_sound`) to `DensePTerm`/`DenseExpr`
over `VarId → ZMod p`. The variable-type-independent `Int`/`ZMod` lemmas
(`IntervalForce.srep_cast`/`term_window`/`int_window`) are reused unqualified; the per-invocation
bounds index's soundness (dropped as a structure field in the dense `Std.HashMap VarId Nat` port) is
re-established here as an external fold invariant, discharged value-level by
`denseInteractionBound_sound` (`DomainBatchProof.lean`). -/

namespace ApcOptimizer.Dense

open IntervalForce

variable {p : ℕ}

/-! ## The integer value of a dense processed-term list (proof-side only) -/

/-- The integer value of a dense processed-term list under an assignment (mirrors `intEval`; not
    part of the runtime — used only to state the window lemmas). -/
def denseIntEval (denv : VarId → ZMod p) (pts : List DensePTerm) : Int :=
  (pts.map (fun t => t.sc * ((denv t.v).val : Int))).sum

theorem denseProcTerms_cast [NeZero p] (bnd : VarId → Option Nat)
    (terms : List (VarId × ZMod p)) (pts : List DensePTerm)
    (h : denseProcTerms bnd terms = some pts) (denv : VarId → ZMod p) :
    ((denseIntEval denv pts : Int) : ZMod p) = (terms.map (fun t => t.2 * denv t.1)).sum := by
  induction terms generalizing pts with
  | nil =>
    simp only [denseProcTerms, Option.some.injEq] at h
    subst h
    simp [denseIntEval]
  | cons t rest ih =>
    obtain ⟨v, c⟩ := t
    simp only [denseProcTerms] at h
    cases hb : bnd v with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some B =>
      cases hr : denseProcTerms bnd rest with
      | none => simp only [hb, hr] at h; exact absurd h (by simp)
      | some pts' =>
        simp only [hb, hr, Option.some.injEq] at h
        subst h
        have hstep : denseIntEval denv (⟨srep c, B, v⟩ :: pts')
            = srep c * ((denv v).val : Int) + denseIntEval denv pts' := by
          simp [denseIntEval]
        rw [hstep, Int.cast_add, Int.cast_mul, Int.cast_natCast, srep_cast,
          ZMod.natCast_val, ZMod.cast_id, ih pts' hr, List.map_cons, List.sum_cons]

theorem denseProcTerms_bounds (bnd : VarId → Option Nat)
    (terms : List (VarId × ZMod p)) (pts : List DensePTerm)
    (h : denseProcTerms bnd terms = some pts) (denv : VarId → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (denv v).val < b) :
    ∀ t ∈ pts, ((denv t.v).val : Int) < (t.bnd : Int) := by
  induction terms generalizing pts with
  | nil =>
    simp only [denseProcTerms, Option.some.injEq] at h
    subst h
    intro t ht
    exact absurd ht (by simp)
  | cons t0 rest ih =>
    obtain ⟨v, c⟩ := t0
    simp only [denseProcTerms] at h
    cases hb : bnd v with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some B =>
      cases hr : denseProcTerms bnd rest with
      | none => simp only [hb, hr] at h; exact absurd h (by simp)
      | some pts' =>
        simp only [hb, hr, Option.some.injEq] at h
        subst h
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact_mod_cast hbnd v B hb
        · exact ih pts' hr t ht'

theorem denseIntEval_window (denv : VarId → ZMod p) (pts : List DensePTerm)
    (hb : ∀ t ∈ pts, ((denv t.v).val : Int) < (t.bnd : Int)) :
    denseMinSum pts ≤ denseIntEval denv pts ∧ denseIntEval denv pts ≤ denseMaxSum pts := by
  induction pts with
  | nil => simp [denseIntEval, denseMinSum, denseMaxSum]
  | cons t rest ih =>
    have hrest := ih (fun t' ht' => hb t' (List.mem_cons_of_mem _ ht'))
    have ht := term_window t.sc ((denv t.v).val : Int) (t.bnd : Int)
      (Int.natCast_nonneg _) (hb t (List.mem_cons_self ..))
    simp only [denseIntEval, denseMinSum, denseMaxSum, List.map_cons, List.sum_cons] at *
    omega

/-! ## The seed walk -/

theorem densePairDiff_eval (v w : VarId) (denv : VarId → ZMod p) :
    (densePairDiff v w : DenseExpr p).eval denv = denv v - denv w := by
  unfold densePairDiff
  rw [denseEqExpr_eval]; rfl

theorem denseFindPartner_spec (g : Int) :
    ∀ (pts : List DensePTerm) (t : DensePTerm) (rest : List DensePTerm),
      denseFindPartner g pts = some (t, rest) → t.sc = g ∧ pts.Perm (t :: rest) := by
  intro pts
  induction pts with
  | nil => intro t rest h; exact absurd h (by simp [denseFindPartner])
  | cons t0 rest0 ih =>
    intro t rest h
    unfold denseFindPartner at h
    split_ifs at h with hsc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hsc, List.Perm.refl _⟩
    · cases hr : denseFindPartner g rest0 with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some tr =>
        obtain ⟨t', rest'⟩ := tr
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hg, hperm⟩ := ih t' rest' hr
        exact ⟨hg, (hperm.cons t0).trans (List.Perm.swap t' t0 rest')⟩

theorem denseIntEval_perm (denv : VarId → ZMod p) {l1 l2 : List DensePTerm} (h : l1.Perm l2) :
    denseIntEval denv l1 = denseIntEval denv l2 :=
  List.Perm.sum_eq (List.Perm.map _ h)

theorem denseWalk_sound [NeZero p] (B : Nat) (c0 : Int) (denv : VarId → ZMod p)
    (pts0 : List DensePTerm)
    (hbnds : ∀ t ∈ pts0, ((denv t.v).val : Int) < (t.bnd : Int))
    (hS0 : 0 ≤ c0 + denseIntEval denv pts0) (hSB : c0 + denseIntEval denv pts0 < (B : Int)) :
    ∀ (seen cur : List DensePTerm), (seen ++ cur).Perm pts0 →
      ∀ e ∈ denseWalk B c0 seen cur, e.eval denv = 0 := by
  intro seen cur
  induction cur generalizing seen with
  | nil => intro _ e he; exact absurd he (by simp [denseWalk])
  | cons t rest ih =>
    intro hperm e he
    have hperm' : (t :: (seen ++ rest)).Perm pts0 :=
      (List.perm_middle (a := t) (l₁ := seen) (l₂ := rest)).symm.trans hperm
    have hsplit : denseIntEval denv pts0
        = t.sc * ((denv t.v).val : Int) + denseIntEval denv (seen ++ rest) := by
      rw [← denseIntEval_perm denv hperm']
      simp [denseIntEval]
    have hbnds' : ∀ t' ∈ seen ++ rest, ((denv t'.v).val : Int) < (t'.bnd : Int) := fun t' ht' =>
      hbnds t' (hperm'.subset (List.mem_cons_of_mem _ ht'))
    have hbt : ((denv t.v).val : Int) < (t.bnd : Int) :=
      hbnds t (hperm'.subset (List.mem_cons_self ..))
    have hwother := denseIntEval_window denv (seen ++ rest) hbnds'
    unfold denseWalk at he
    simp only [List.mem_append] at he
    rcases he with (hz | hp) | hrec
    · -- zero arm
      split_ifs at hz with hcond
      swap
      · exact absurd hz (by simp)
      rw [List.mem_singleton] at hz
      subst hz
      show denv t.v = 0
      rw [← ZMod.val_eq_zero]
      by_contra hne
      have hd1 : (1 : Int) ≤ ((denv t.v).val : Int) := by
        have h1 : 1 ≤ (denv t.v).val := Nat.one_le_iff_ne_zero.mpr hne
        exact_mod_cast h1
      rcases hcond with ⟨hsc, hcnd⟩ | ⟨hsc, hcnd⟩
      · have hscd : t.sc ≤ t.sc * ((denv t.v).val : Int) :=
          le_mul_of_one_le_right (le_of_lt hsc) hd1
        generalize hX : t.sc * ((denv t.v).val : Int) = X at hsplit hscd
        omega
      · have hscd : t.sc * ((denv t.v).val : Int) ≤ t.sc := by
          have h1 : t.sc * ((denv t.v).val : Int) ≤ t.sc * 1 :=
            mul_le_mul_of_nonpos_left hd1 (le_of_lt hsc)
          rwa [mul_one] at h1
        generalize hX : t.sc * ((denv t.v).val : Int) = X at hsplit hscd
        omega
    · -- pair arm
      split_ifs at hp with hsc
      swap
      · exact absurd hp (by simp)
      cases hfp : denseFindPartner (-t.sc) (seen ++ rest) with
      | none => simp only [hfp] at hp; exact absurd hp (by simp)
      | some tr =>
        obtain ⟨t', others'⟩ := tr
        simp only [hfp] at hp
        split_ifs at hp with hcond
        swap
        · exact absurd hp (by simp)
        rw [List.mem_singleton] at hp
        subst hp
        obtain ⟨hc1, hc2, _hne⟩ := hcond
        obtain ⟨hg, hpp⟩ := denseFindPartner_spec (-t.sc) (seen ++ rest) t' others' hfp
        have hsplit2 : denseIntEval denv (seen ++ rest)
            = t'.sc * ((denv t'.v).val : Int) + denseIntEval denv others' := by
          rw [denseIntEval_perm denv hpp]
          simp [denseIntEval]
        have hbnds'' : ∀ u ∈ others', ((denv u.v).val : Int) < (u.bnd : Int) := fun u hu =>
          hbnds' u (hpp.symm.subset (List.mem_cons_of_mem _ hu))
        have hwother' := denseIntEval_window denv others' hbnds''
        have hcomb : denseIntEval denv pts0
            = t.sc * (((denv t.v).val : Int) - ((denv t'.v).val : Int)) + denseIntEval denv others' := by
          rw [hsplit, hsplit2, hg]
          ring
        show (densePairDiff t.v t'.v).eval denv = 0
        rw [densePairDiff_eval]
        have hveq : (denv t.v).val = (denv t'.v).val := by
          by_contra hnev
          rcases Nat.lt_or_ge (denv t.v).val (denv t'.v).val with hlt | hge
          · have hdlt : ((denv t.v).val : Int) - ((denv t'.v).val : Int) ≤ -1 := by
              have h1 : (denv t.v).val + 1 ≤ (denv t'.v).val := hlt
              have h2 : ((denv t.v).val : Int) + 1 ≤ ((denv t'.v).val : Int) := by exact_mod_cast h1
              omega
            have hXle : t.sc * (((denv t.v).val : Int) - ((denv t'.v).val : Int)) ≤ -t.sc := by
              have h1 : t.sc * (((denv t.v).val : Int) - ((denv t'.v).val : Int)) ≤ t.sc * (-1) :=
                mul_le_mul_of_nonneg_left hdlt (le_of_lt hsc)
              rwa [mul_neg_one] at h1
            generalize hX : t.sc * (((denv t.v).val : Int) - ((denv t'.v).val : Int)) = X
              at hcomb hXle
            omega
          · have hdgt : (1 : Int) ≤ ((denv t.v).val : Int) - ((denv t'.v).val : Int) := by
              have h1 : (denv t'.v).val + 1 ≤ (denv t.v).val := by omega
              have h2 : ((denv t'.v).val : Int) + 1 ≤ ((denv t.v).val : Int) := by exact_mod_cast h1
              omega
            have hXge : t.sc ≤ t.sc * (((denv t.v).val : Int) - ((denv t'.v).val : Int)) :=
              le_mul_of_one_le_right (le_of_lt hsc) hdgt
            generalize hX : t.sc * (((denv t.v).val : Int) - ((denv t'.v).val : Int)) = X
              at hcomb hXge
            omega
        rw [show denv t.v = denv t'.v from ZMod.val_injective p hveq, sub_self]
    · -- recursive call
      exact ih (t :: seen) (by simpa using hperm') e hrec

/-! ## Per-slot seeds -/

theorem denseSlotSeeds_sound (bnd : VarId → Option Nat) (B : Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (denv v).val < b)
    (hB : (e.eval denv).val < B) :
    ∀ s ∈ denseSlotSeeds bnd B e, s.eval denv = 0 := by
  intro s hs
  unfold denseSlotSeeds at hs
  split_ifs at hs with hp0
  · exact absurd hs (by simp)
  haveI : NeZero p := ⟨hp0⟩
  cases hl : denseLinearize e with
  | none => simp only [hl] at hs; exact absurd hs (by simp)
  | some l =>
    simp only [hl] at hs
    split_ifs at hs with hlen
    swap
    · exact absurd hs (by simp)
    cases hpt : denseProcTerms bnd l.norm.terms with
    | none => simp only [hpt] at hs; exact absurd hs (by simp)
    | some pts =>
      simp only [hpt] at hs
      split_ifs at hs with hwin
      swap
      · exact absurd hs (by simp)
      obtain ⟨hhi, hlo⟩ := hwin
      have hbnds : ∀ t ∈ pts, ((denv t.v).val : Int) < (t.bnd : Int) :=
        denseProcTerms_bounds bnd l.norm.terms pts hpt denv hbnd
      have hcast : (((srep l.norm.const + denseIntEval denv pts : Int)) : ZMod p) = e.eval denv := by
        push_cast
        rw [srep_cast, denseProcTerms_cast bnd l.norm.terms pts hpt denv,
          denseLinearize_eval e l hl denv, ← DenseLinExpr.norm_eval]
        rfl
      have hwindow := denseIntEval_window denv pts hbnds
      have hS := int_window (srep l.norm.const + denseIntEval denv pts) B (e.eval denv) hcast hB
        (by omega) (by omega)
      have hSB : srep l.norm.const + denseIntEval denv pts < (B : Int) := by
        rw [hS]; exact_mod_cast hB
      have hS0 : 0 ≤ srep l.norm.const + denseIntEval denv pts := by
        rw [hS]; exact Int.natCast_nonneg _
      exact denseWalk_sound B (srep l.norm.const) denv pts hbnds hS0 hSB [] pts (by simp) s hs

/-! ## The per-invocation bounds index soundness (external fold invariant) -/

/-- The witnessing invariant on the dense bounds map: every entry is produced by some member
    interaction's `denseInteractionBound` (native mirror of the dropped `BoundIdx.sound` field). -/
def DenseBoundIdxWitnessed {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (I : Std.HashMap VarId Nat) : Prop :=
  ∀ (x : VarId) (B : Nat), I[x]? = some B →
    ∃ bi ∈ bis, denseInteractionBound bs facts bi x = some B

theorem denseBoundIdxInsertVar_witnessed {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (I : Std.HashMap VarId Nat)
    (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ bis) (x : VarId)
    (hI : DenseBoundIdxWitnessed facts bis I) :
    DenseBoundIdxWitnessed facts bis (denseBoundIdxInsertVar bs facts I bi x) := by
  intro y B' h
  unfold denseBoundIdxInsertVar at h
  split at h
  · exact hI y B' h
  · rename_i B hb
    split_ifs at h with hg
    · rw [Std.HashMap.getElem?_insert] at h
      by_cases hxy : (x == y) = true
      · rw [if_pos hxy] at h
        simp only [Option.some.injEq] at h
        have hxy' : x = y := by simpa using hxy
        subst hxy'
        exact ⟨bi, hbi, h ▸ hb⟩
      · rw [if_neg hxy] at h
        exact hI y B' h
    · exact hI y B' h

theorem denseBoundIdxInsertVar_foldl_witnessed {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ bis)
    (xs : List VarId) :
    ∀ (I : Std.HashMap VarId Nat), DenseBoundIdxWitnessed facts bis I →
      DenseBoundIdxWitnessed facts bis
        (xs.foldl (fun I x => denseBoundIdxInsertVar bs facts I bi x) I) := by
  induction xs with
  | nil => intro I hI; exact hI
  | cons x rest ih =>
    intro I hI
    exact ih _ (denseBoundIdxInsertVar_witnessed facts bis I bi hbi x hI)

theorem denseBoundIdxAddBi_witnessed {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (I : Std.HashMap VarId Nat)
    (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ bis)
    (hI : DenseBoundIdxWitnessed facts bis I) :
    DenseBoundIdxWitnessed facts bis (denseBoundIdxAddBi bs facts I bi) := by
  unfold denseBoundIdxAddBi
  exact denseBoundIdxInsertVar_foldl_witnessed facts bis bi hbi _ I hI

theorem denseBoundIdxAddAll_witnessed {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (rest : List (BusInteraction (DenseExpr p))) :
    ∀ (I : Std.HashMap VarId Nat), (∀ bi ∈ rest, bi ∈ bis) →
      DenseBoundIdxWitnessed facts bis I →
      DenseBoundIdxWitnessed facts bis (denseBoundIdxAddAll bs facts I rest) := by
  induction rest with
  | nil => intro I _ hI; exact hI
  | cons bi rest' ih =>
    intro I hmem hI
    show DenseBoundIdxWitnessed facts bis (denseBoundIdxAddAll bs facts (denseBoundIdxAddBi bs facts I bi) rest')
    exact ih (denseBoundIdxAddBi bs facts I bi) (fun b hb => hmem b (List.mem_cons_of_mem _ hb))
      (denseBoundIdxAddBi_witnessed facts bis I bi (hmem bi (List.mem_cons_self ..)) hI)

theorem denseBoundIdxBuild_witnessed {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) :
    DenseBoundIdxWitnessed facts bis (denseBoundIdxBuild bs facts bis) := by
  unfold denseBoundIdxBuild
  refine denseBoundIdxAddAll_witnessed facts bis bis ∅ (fun _ h => h) ?_
  intro x B h
  rw [Std.HashMap.getElem?_empty] at h
  exact absurd h (by simp)

theorem denseBoundIdxBuild_lookup_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p)
    (hbus : ∀ bi ∈ d.busInteractions, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    ∀ v B, (denseBoundIdxBuild bs facts d.busInteractions)[v]? = some B → (denv v).val < B := by
  intro v B h
  obtain ⟨bi, hbi, hib⟩ := denseBoundIdxBuild_witnessed facts d.busInteractions v B h
  exact denseInteractionBound_sound bs facts bi v B hib denv (hbus bi hbi)

/-! ## Per-interaction and whole-system seed soundness -/

theorem denseInteractionSeeds_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bnd : VarId → Option Nat) (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (denv v).val < b)
    (hviol : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.violatesConstraint (denseBIEval bi denv) = false) :
    ∀ s ∈ denseInteractionSeeds bs facts bnd bi, s.eval denv = 0 := by
  intro s hs
  unfold denseInteractionSeeds at hs
  cases hmc : bi.multiplicity.constValue? with
  | none => simp only [hmc] at hs; exact absurd hs (by simp)
  | some mval =>
    simp only [hmc] at hs
    by_cases hmz : mval = 0
    · rw [if_pos hmz] at hs
      exact absurd hs (by simp)
    rw [if_neg hmz] at hs
    unfold denseInteractionSeedsGo at hs
    rw [List.mem_flatMap] at hs
    obtain ⟨i, _, hsi⟩ := hs
    cases hpe : bi.payload[i]? with
    | none => simp only [hpe] at hsi; exact absurd hsi (by simp)
    | some e =>
      cases hsb : facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
      | none => simp only [hpe, hsb] at hsi; exact absurd hsi (by simp)
      | some B =>
        simp only [hpe, hsb] at hsi
        have hmeval : (denseBIEval bi denv).multiplicity = mval :=
          bi.multiplicity.constValue?_sound mval hmc denv
        have hv : bs.violatesConstraint (denseBIEval bi denv) = false := by
          apply hviol
          rw [hmeval]
          exact hmz
        have hget : (denseBIEval bi denv).payload[i]? = some (e.eval denv) := by
          show (bi.payload.map (fun t => t.eval denv))[i]? = some (e.eval denv)
          rw [List.getElem?_map, hpe]
          rfl
        have hsb' : facts.slotBound (denseBIEval bi denv).busId (denseBIEval bi denv).multiplicity
            (bi.payload.map DenseExpr.constValue?) i = some B := by
          show facts.slotBound bi.busId (denseBIEval bi denv).multiplicity _ i = some B
          rw [hmeval]
          exact hsb
        have hbound : (e.eval denv).val < B :=
          facts.slotBound_sound (denseBIEval bi denv) (bi.payload.map DenseExpr.constValue?) i B
            (e.eval denv) hsb' (denseMatches_evalPattern bi.payload denv) hv hget
        exact denseSlotSeeds_sound bnd B e denv hbnd hbound s hsi

theorem denseAllSeeds_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bnd : VarId → Option Nat) (d : DenseConstraintSystem p) (denv : VarId → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (denv v).val < b)
    (hsat : d.satisfies bs denv) :
    ∀ s ∈ denseAllSeeds bs facts bnd d, s.eval denv = 0 := by
  intro s hs
  unfold denseAllSeeds at hs
  rw [HashedDedup.hashedEraseDups_eq] at hs
  rcases List.mem_append.1 (List.mem_eraseDups.1 hs) with h | h
  · obtain ⟨bi, hbi, hsi⟩ := List.mem_flatMap.1 h
    exact denseInteractionSeeds_sound facts bnd bi denv hbnd (hsat.2 bi hbi) s hsi
  · obtain ⟨c, hc, hsi⟩ := List.mem_flatMap.1 h
    by_cases hp0 : p = 0
    · exfalso
      unfold denseSlotSeeds at hsi
      rw [if_pos hp0] at hsi
      exact absurd hsi (by simp)
    · haveI : NeZero p := ⟨hp0⟩
      have hc0 : (c.eval denv).val < 1 := by
        rw [hsat.1 c hc, ZMod.val_zero]
        omega
      exact denseSlotSeeds_sound bnd 1 c denv hbnd hc0 s hsi

/-! ## The pass -/

/-- The appended list of entailed seeds (mirrors `denseIntervalForceF`'s internal `new`). -/
def denseIntervalForceNew (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let idx := denseBoundIdxBuild bs facts d.busInteractions
  let seeds := denseAllSeeds bs facts (fun v => idx[v]?) d
  let varSet : Std.HashSet VarId := Std.HashSet.ofList d.occ
  let csBuckets : Std.HashMap UInt64 (List (DenseExpr p)) :=
    d.algebraicConstraints.foldl (fun m c => m.insert c.bHash (c :: m.getD c.bHash [])) ∅
  (seeds.filter (fun e => e.vars.all (fun z => varSet.contains z))).filter
    (fun e => !(csBuckets.getD e.bHash []).contains e)

theorem denseIntervalForceF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseIntervalForceF bs facts d =
      if (denseIntervalForceNew bs facts d).isEmpty then d
      else { d with algebraicConstraints := d.algebraicConstraints ++ denseIntervalForceNew bs facts d } :=
  rfl

theorem denseIntervalForceNew_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseIntervalForceNew bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  have hp := (List.mem_filter.1 (List.mem_of_mem_filter hc)).2
  simp only [List.all_eq_true] at hp
  have hz' := hp z hz
  rw [Std.HashSet.contains_ofList] at hz'
  exact List.contains_iff_mem.mp hz'

theorem denseIntervalForceNew_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseIntervalForceNew bs facts d, c.eval denv = 0 := by
  intro c hc
  have hcseed : c ∈ denseAllSeeds bs facts
      (fun v => (denseBoundIdxBuild bs facts d.busInteractions)[v]?) d :=
    List.mem_of_mem_filter (List.mem_of_mem_filter hc)
  exact denseAllSeeds_sound facts (fun v => (denseBoundIdxBuild bs facts d.busInteractions)[v]?) d denv
    (fun v B hb => denseBoundIdxBuild_lookup_sound facts d denv (fun bi hbi => hsat.2 bi hbi) v B hb)
    hsat c hcseed

theorem denseIntervalForceF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseIntervalForceF bs facts d).CoveredBy reg := by
  rw [denseIntervalForceF_eq]
  split
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h' | h'
    · exact hcov.1 e h'
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i (denseIntervalForceNew_vars bs facts d e h' i hi)

theorem denseIntervalForceF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseIntervalForceF bs facts d) [] bs := by
  rw [denseIntervalForceF_eq]
  split
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseIntervalForceNew bs facts d)
      (denseIntervalForceNew_vars bs facts d)
      (fun denv _ hsat => denseIntervalForceNew_sound bs facts d denv hsat)

/-- **The native dense `intervalForce` pass.** Threads the original `facts` unchanged, connected to
    the audited spec via `DensePassCorrect.lift` (through `of`) — no reference-pass dependency. -/
def denseIntervalForcePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseIntervalForceF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseIntervalForceF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseIntervalForceF_correct reg bs facts d)

end ApcOptimizer.Dense
