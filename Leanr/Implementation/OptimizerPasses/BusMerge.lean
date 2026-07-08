import Leanr.Implementation.OptimizerPasses.Rewrite
import Leanr.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false

/-! # Stateless lookup merging

Replaces two *stateless* lookup interactions by a single one carrying exactly their combined
obligation, using the proven `BusFacts.mergeLookups` (e.g. two single-byte range checks packed into
one two-byte range check on the OpenVM bitwise bus). Because all three interactions are stateless,
this cannot touch `sideEffects` or the `admissible` filter (both range over active *stateful*
messages only), so soundness/completeness reduce to the obligation equivalence the fact provides:

* the merged interaction's `violatesConstraint` obligation holds iff both originals' do
  (`mergeLookups_sound`), so `satisfies` is preserved in both directions (the originals are active
  by the fact, unlocking their guards);
* the merged interaction is invariant-safe (`breaksInvariant = false`).

The pass drops *every* copy of the two originals and prepends the merged interaction — a net
reduction in bus interactions with no change to the variable set. Generic in the bus semantics: with
`BusFacts.trivial` (`mergeLookups = fun _ _ => none`) it is the identity. -/

variable {p : ℕ}

/-- Filtering out interactions that are all stateless leaves the *stateful* sublist unchanged. -/
theorem filterKeep_stateful (bs : BusSemantics p) (keep : BusInteraction (Expression p) → Bool)
    (L : List (BusInteraction (Expression p)))
    (h : ∀ b ∈ L, keep b = false → bs.isStateful b.busId = false) :
    (L.filter keep).filter (fun bi => bs.isStateful bi.busId)
      = L.filter (fun bi => bs.isStateful bi.busId) := by
  induction L with
  | nil => rfl
  | cons b rest ih =>
    have hrest := ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    by_cases hk : keep b = true
    · rw [List.filter_cons_of_pos hk]
      by_cases hst : bs.isStateful b.busId = true
      · rw [List.filter_cons_of_pos (by simpa using hst),
            List.filter_cons_of_pos (by simpa using hst), hrest]
      · rw [List.filter_cons_of_neg (by simpa using hst),
            List.filter_cons_of_neg (by simpa using hst), hrest]
    · have hst : bs.isStateful b.busId = false := h b (List.mem_cons_self ..) (by simpa using hk)
      rw [List.filter_cons_of_neg (by simpa using hk),
          List.filter_cons_of_neg (by simp [hst]), hrest]

/-- **Correctness of stateless lookup merging.** Given two stateless, active, invariant-safe
    interactions whose merged interaction `bi3` (also stateless, active, invariant-safe) has the
    conjoined obligation, replacing every copy of `bi1`/`bi2` by `bi3` is equivalence- and
    invariant-preserving. -/
theorem ConstraintSystem.mergeLookups_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (bi1 bi2 bi3 : BusInteraction (Expression p))
    (hmem1 : bi1 ∈ cs.busInteractions) (hmem2 : bi2 ∈ cs.busInteractions)
    (hs1 : bs.isStateful bi1.busId = false) (hs2 : bs.isStateful bi2.busId = false)
    (hs3 : bs.isStateful bi3.busId = false)
    (ha1 : ∀ env, (bi1.eval env).multiplicity ≠ 0) (ha2 : ∀ env, (bi2.eval env).multiplicity ≠ 0)
    (ha3 : ∀ env, (bi3.eval env).multiplicity ≠ 0)
    (hinv3 : ∀ env, bs.breaksInvariant (bi3.eval env) = false)
    (hobl : ∀ env, bs.violatesConstraint (bi3.eval env) = false ↔
      (bs.violatesConstraint (bi1.eval env) = false ∧ bs.violatesConstraint (bi2.eval env) = false)) :
    PassCorrect cs
      { cs with busInteractions :=
        bi3 :: cs.busInteractions.filter (fun b => decide (b ≠ bi1) && decide (b ≠ bi2)) } bs := by
  set keep : BusInteraction (Expression p) → Bool :=
    fun b => decide (b ≠ bi1) && decide (b ≠ bi2) with hkeep
  -- a dropped interaction is `bi1` or `bi2`
  have hdrop : ∀ b, keep b = false → b = bi1 ∨ b = bi2 := by
    intro b hb
    rw [hkeep] at hb
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_not] at hb
    exact hb
  have hdropStateless : ∀ b ∈ cs.busInteractions, keep b = false → bs.isStateful b.busId = false := by
    intro b _ hb; rcases hdrop b hb with rfl | rfl
    · exact hs1
    · exact hs2
  -- satisfies is preserved in both directions
  have hiff : ∀ env,
      ({ cs with busInteractions :=
        bi3 :: cs.busInteractions.filter keep } : ConstraintSystem p).satisfies bs env
        ↔ cs.satisfies bs env := by
    intro env
    simp only [ConstraintSystem.satisfies]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨hc, fun bi hbimem => ?_⟩
      by_cases hk : keep bi = true
      · exact hb bi (List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hbimem, hk⟩))
      · -- bi = bi1 or bi2: obligation follows from bi3's (in the output) via hobl
        have hb3 : bs.violatesConstraint (bi3.eval env) = false := by
          have := hb bi3 (List.mem_cons_self ..)
          exact this (ha3 env)
        obtain ⟨hv1, hv2⟩ := (hobl env).1 hb3
        rcases hdrop bi (by simpa using hk) with rfl | rfl
        · intro _; exact hv1
        · intro _; exact hv2
    · rintro ⟨hc, hb⟩
      refine ⟨hc, fun bi hbimem => ?_⟩
      rcases List.mem_cons.1 hbimem with rfl | hbi
      · -- bi3: obligation from bi1, bi2 (active in the input)
        intro _
        exact (hobl env).2 ⟨hb bi1 hmem1 (ha1 env), hb bi2 hmem2 (ha2 env)⟩
      · exact hb bi (List.mem_filter.1 hbi).1
  -- side effects are unchanged (all three are stateless)
  have hside : ∀ env,
      ({ cs with busInteractions :=
        bi3 :: cs.busInteractions.filter keep } : ConstraintSystem p).sideEffects bs env
        = cs.sideEffects bs env := by
    intro env
    simp only [ConstraintSystem.sideEffects]
    rw [List.filter_cons_of_neg (by simp [hs3]),
        filterKeep_stateful bs keep cs.busInteractions hdropStateless]
  -- admissibility is unchanged (all three are stateless)
  have hadm : ∀ env,
      ({ cs with busInteractions :=
        bi3 :: cs.busInteractions.filter keep } : ConstraintSystem p).admissible bs env
        ↔ cs.admissible bs env := by
    intro env
    have hbi3ns : bs.isStateful (bi3.eval env).busId = false := hs3
    have hfilt : ((bi3 :: cs.busInteractions.filter keep).map (fun bi => bi.eval env)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
        = ((cs.busInteractions.filter keep).map (fun bi => bi.eval env)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
      rw [List.map_cons, List.filter_cons_of_neg (by simp [hbi3ns])]
    have h1 : ({ cs with busInteractions :=
          bi3 :: cs.busInteractions.filter keep } : ConstraintSystem p).admissible bs env
        ↔ (cs.filterBus keep).admissible bs env :=
      Iff.of_eq (congrArg bs.admissible hfilt)
    rw [h1]
    exact cs.admissible_filterBus bs keep env
      (fun bi hbi hkf => Or.inr (hdropStateless bi hbi hkf))
  -- assemble
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro env hint hsat
    exact ⟨env, (hiff env).2 hsat, (hadm env).2 hint, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    rcases List.mem_cons.1 hbi with rfl | hbimem
    · exact fun _ => hinv3 env
    · exact hinv env ((hiff env).1 hsat) bi (List.mem_filter.1 hbimem).1

/-! ## The pass -/

/-- Scan for the first pair of interactions `merge` can combine: the earliest `bi1` with a later
    `bi2` such that `merge bi1 bi2` succeeds. Linear per starting position. -/
def findMergeable (merge : BusInteraction (Expression p) → BusInteraction (Expression p) →
      Option (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) →
    Option (BusInteraction (Expression p) × BusInteraction (Expression p) ×
      BusInteraction (Expression p))
  | [] => none
  | bi1 :: rest =>
    match rest.findSome? (fun bi2 => (merge bi1 bi2).map (fun bi3 => (bi2, bi3))) with
    | some (bi2, bi3) => some (bi1, bi2, bi3)
    | none => findMergeable merge rest

/-- The stateless lookup-merge pass: find a `mergeLookups`-mergeable pair and replace both with the
    merged interaction (dropping every copy of the two originals). Identity when no pair merges. -/
def mergeLookupPass : VerifiedPassW p := fun cs bs facts =>
  match findMergeable facts.mergeLookups cs.busInteractions with
  | some (bi1, bi2, bi3) =>
    if h : (bi1 ∈ cs.busInteractions ∧ bi2 ∈ cs.busInteractions)
        ∧ facts.mergeLookups bi1 bi2 = some bi3 then
      let ⟨hs1, hs2, hs3, ha1, ha2, ha3, hinv3, hobl⟩ := facts.mergeLookups_sound bi1 bi2 bi3 h.2
      ⟨{ cs with busInteractions :=
          bi3 :: cs.busInteractions.filter (fun b => decide (b ≠ bi1) && decide (b ≠ bi2)) },
       cs.mergeLookups_correct bs bi1 bi2 bi3 h.1.1 h.1.2 hs1 hs2 hs3 ha1 ha2 ha3 hinv3 hobl⟩
    else ⟨cs, cs.refines_refl bs, _root_.id⟩
  | none => ⟨cs, cs.refines_refl bs, _root_.id⟩

/-- The tuple-packing pass: pack a `mergeTupleLookups`-mergeable pair (e.g. a byte check and a range
    check) into one tuple range check. Runs before `mergeLookupPass` so tuple packing wins over
    byte-pairing the same byte check. Identity when no pair merges. -/
def mergeTuplePass : VerifiedPassW p := fun cs bs facts =>
  match findMergeable facts.mergeTupleLookups cs.busInteractions with
  | some (bi1, bi2, bi3) =>
    if h : (bi1 ∈ cs.busInteractions ∧ bi2 ∈ cs.busInteractions)
        ∧ facts.mergeTupleLookups bi1 bi2 = some bi3 then
      let ⟨hs1, hs2, hs3, ha1, ha2, ha3, hinv3, hobl⟩ :=
        facts.mergeTupleLookups_sound bi1 bi2 bi3 h.2
      ⟨{ cs with busInteractions :=
          bi3 :: cs.busInteractions.filter (fun b => decide (b ≠ bi1) && decide (b ≠ bi2)) },
       cs.mergeLookups_correct bs bi1 bi2 bi3 h.1.1 h.1.2 hs1 hs2 hs3 ha1 ha2 ha3 hinv3 hobl⟩
    else ⟨cs, cs.refines_refl bs, _root_.id⟩
  | none => ⟨cs, cs.refines_refl bs, _root_.id⟩
