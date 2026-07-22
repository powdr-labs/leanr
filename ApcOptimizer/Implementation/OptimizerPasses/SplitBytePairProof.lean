import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPackProof
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancel

set_option autoImplicit false

/-! # Native correctness of the dense byte-check pair splitting pass (Task 3)

Native, `VarId`-native `DensePassCorrect` proof for `denseSplitBytePairF`
(`OptimizerPasses/SplitBytePair.lean`), the dense transliteration of the reference
`SplitBytePair.splitBytePairPass`. No decode transport
into the reference `Variable` passes: every obligation is discharged over dense environments `VarId → ZMod p`.

## Why it is correct

Splitting a recognized packed pair check `denseMkBytePair spec busId a b` (multiplicity `1`, on a
`byteXorSpec` bus, decoding to `(pairOp, a, b, 0)`) into the two single-value checks
`[denseMkByteCheck spec busId a, denseMkByteCheck spec busId b]` carries the *identical* obligation
("both operands are bytes"): the proven pack/split law `denseMkBytePair_iff_singles`
(`ByteCheckPackProof.lean`, the inverse pack pass's precedent) ties acceptance of the pair form to
bytehood of both operands. Because these lookups are stateless, the stateful side effects and the
active∧stateful admissibility argument are untouched, so completeness rides on `env' = env`
(`DensePassCorrect.ofEnvEq`). The transform is variable- and constraint-neutral (`a`/`b` are already
payload entries of the replaced interaction).

## Reuse

* `denseMkBytePair_iff_singles`/`denseMkBytePair_eval`/`denseMkBytePair_operand_mem`/
  `denseMkBytePair_payload_vars`/`denseMem_biVars_of_payload` (`ByteCheckPackProof.lean`) and
  `denseMkByteCheck_eval`/`_breaks`/`_payload_vars` (`BusPairCancelCheckProof.lean`),
  `denseMkByteCheck_covered` (`BusPairCancel.lean`) — the same bus-fact lemma cluster the pack pass
  reasons about, mined rather than re-derived.
* `DensePassCorrect.ofEnvEq`/`.refl` and `DenseVerifiedPassW.of` (`Dense/Bridge.lean`) close
  the pass and lift it to the audited `Variable` spec once, at the optimizer boundary. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A recognizer hit pins the whole interaction: `bi` is exactly `denseMkBytePair spec busId a b`, on
    a `byteXorSpec` bus. Native mirror of `SplitBytePair.asBytePair_eq`
   . -/
theorem denseAsBytePair_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (busId : Nat) (spec : ByteXorSpec p) (a b : DenseExpr p)
    (h : denseAsBytePair bs facts bi = some (busId, spec, a, b)) :
    bi = denseMkBytePair spec busId a b ∧ facts.byteXorSpec busId = some spec := by
  obtain ⟨biBus, biMul, biPay⟩ := bi
  unfold denseAsBytePair at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec' hspec
    split at h
    · rename_i op o1 o2 r hdec
      split_ifs at h with hc
      obtain ⟨hm, hop, hr⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hpay : biPay = spec'.encode (DenseExpr.const spec'.pairOp) o1 o2 (DenseExpr.const 0) := by
        have he := spec'.decode_eq_encode biPay op o1 o2 r hdec
        rw [hop, hr] at he; exact he
      refine ⟨?_, hspec⟩
      have hm' : biMul = DenseExpr.const 1 := hm
      show ({ busId := biBus, multiplicity := biMul, payload := biPay } : BusInteraction (DenseExpr p))
        = denseMkBytePair spec' biBus o1 o2
      rw [hm', hpay]; rfl
    · exact absurd h (by simp)

/-- The obligation predicate appearing in dense `satisfies` (native mirror of the spec `P`). -/
private def denseP (bs : BusSemantics p) (denv : VarId → ZMod p)
    (bi : BusInteraction (DenseExpr p)) : Prop :=
  (denseBIEval bi denv).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi denv) = false

/-- `[x].filter q ++ ys.filter q = (x :: ys).filter q`. Native copy of the spec `filter_cons_append`. -/
private theorem filter_cons_append {α : Type} (q : α → Bool) (x : α) (ys : List α) :
    ([x].filter q) ++ ys.filter q = (x :: ys).filter q := by
  cases h : q x <;> simp [h]

/-- Per-interaction obligation equivalence: the split list carries the same obligation as `bi`.
    Native mirror of `SplitBytePair.splitOne_P`. -/
private theorem denseSplitOne_P (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p) :
    (∀ b ∈ denseSplitOne bs facts bi, denseP bs denv b) ↔ denseP bs denv bi := by
  unfold denseSplitOne
  cases hab : denseAsBytePair bs facts bi with
  | none => simp
  | some t =>
    obtain ⟨busId, spec, a, b⟩ := t
    obtain ⟨rfl, hspec⟩ := denseAsBytePair_eq bs facts bi busId spec a b hab
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have hsaP : denseP bs denv (denseMkByteCheck spec busId a) ↔
        bs.violatesConstraint (denseBIEval (denseMkByteCheck spec busId a) denv) = false := by
      unfold denseP
      have hmul : (denseBIEval (denseMkByteCheck spec busId a) denv).multiplicity = 1 := by
        rw [denseMkByteCheck_eval]
      exact ⟨fun h => h (by rw [hmul]; exact hp1), fun h _ => h⟩
    have hsbP : denseP bs denv (denseMkByteCheck spec busId b) ↔
        bs.violatesConstraint (denseBIEval (denseMkByteCheck spec busId b) denv) = false := by
      unfold denseP
      have hmul : (denseBIEval (denseMkByteCheck spec busId b) denv).multiplicity = 1 := by
        rw [denseMkByteCheck_eval]
      exact ⟨fun h => h (by rw [hmul]; exact hp1), fun h _ => h⟩
    have hpairP : denseP bs denv (denseMkBytePair spec busId a b) ↔
        bs.violatesConstraint (denseBIEval (denseMkBytePair spec busId a b) denv) = false := by
      unfold denseP
      have hmul : (denseBIEval (denseMkBytePair spec busId a b) denv).multiplicity = 1 := by
        rw [denseMkBytePair_eval]
      exact ⟨fun h => h (by rw [hmul]; exact hp1), fun h _ => h⟩
    rw [hsaP, hsbP, hpairP]
    exact (denseMkBytePair_iff_singles bs facts spec busId hspec a b denv).symm

/-- The bus-list-level obligation equivalence. Native mirror of `SplitBytePair.forall_P_flatMap`
   . -/
private theorem forall_denseP_flatMap (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (l : List (BusInteraction (DenseExpr p))) (denv : VarId → ZMod p) :
    (∀ b ∈ l.flatMap (denseSplitOne bs facts), denseP bs denv b) ↔
      (∀ b ∈ l, denseP bs denv b) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.flatMap_cons]
    simp only [List.mem_append, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      exact ⟨(denseSplitOne_P bs facts hp1 a denv).1 (fun b hb => h b (Or.inl hb)),
        ih.1 (fun b hb => h b (Or.inr hb))⟩
    · rintro ⟨ha, hrest⟩ b (hb | hb)
      · exact (denseSplitOne_P bs facts hp1 a denv).2 ha b hb
      · exact ih.2 hrest b hb

/-- Splitting a stateless byte-pair check yields only stateless interactions, so the
    stateful-filtered bus list is unchanged (per interaction). Native mirror of
    `SplitBytePair.splitOne_filter_stateful`. -/
private theorem denseSplitOne_filter_stateful (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    (denseSplitOne bs facts bi).filter (fun b => bs.isStateful b.busId)
      = [bi].filter (fun b => bs.isStateful b.busId) := by
  unfold denseSplitOne
  cases hab : denseAsBytePair bs facts bi with
  | none => rfl
  | some t =>
    obtain ⟨busId, spec, a, b⟩ := t
    obtain ⟨rfl, hspec⟩ := denseAsBytePair_eq bs facts bi busId spec a b hab
    have hst : bs.isStateful busId = false := (facts.byteXorSpec_sound busId spec hspec).1
    simp only [denseMkByteCheck, denseMkBytePair, List.filter_cons, List.filter_nil, hst,
      Bool.false_eq_true, if_false]

/-- The stateful-filtered bus list is invariant under the whole split. Native mirror of
    `SplitBytePair.filter_stateful_flatMap`. -/
private theorem filter_stateful_flatMap (bs : BusSemantics p) (facts : BusFacts p bs)
    (l : List (BusInteraction (DenseExpr p))) :
    (l.flatMap (denseSplitOne bs facts)).filter (fun b => bs.isStateful b.busId)
      = l.filter (fun b => bs.isStateful b.busId) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, List.filter_append, denseSplitOne_filter_stateful bs facts a, ih]
    exact filter_cons_append _ a rest

/-- The active∧stateful evaluated messages are invariant under the split (per interaction). Native
    mirror of `SplitBytePair.splitOne_map_filter`. -/
private theorem denseSplitOne_map_filter (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p) :
    ((denseSplitOne bs facts bi).map (fun b => denseBIEval b denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = ([bi].map (fun b => denseBIEval b denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
  unfold denseSplitOne
  cases hab : denseAsBytePair bs facts bi with
  | none => rfl
  | some t =>
    obtain ⟨busId, spec, a, b⟩ := t
    obtain ⟨rfl, hspec⟩ := denseAsBytePair_eq bs facts bi busId spec a b hab
    have hst : bs.isStateful busId = false := (facts.byteXorSpec_sound busId spec hspec).1
    simp only [denseMkByteCheck, denseMkBytePair, List.map_cons, List.map_nil, denseBIEval,
      List.filter_cons, List.filter_nil, hst, Bool.and_false, Bool.false_eq_true, if_false]

/-- The active∧stateful evaluated-message list is invariant under the whole split. Native mirror of
    `SplitBytePair.map_filter_flatMap`. -/
private theorem map_filter_flatMap (bs : BusSemantics p) (facts : BusFacts p bs)
    (l : List (BusInteraction (DenseExpr p))) (denv : VarId → ZMod p) :
    ((l.flatMap (denseSplitOne bs facts)).map (fun b => denseBIEval b denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = (l.map (fun b => denseBIEval b denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, List.map_append, List.filter_append,
      denseSplitOne_map_filter bs facts a denv, ih]
    simp only [List.map_cons, List.map_nil]
    exact filter_cons_append _ (denseBIEval a denv) (rest.map (fun b => denseBIEval b denv))

/-- Variables of a split interaction come from the original. Native mirror of
    `SplitBytePair.splitOne_vars`. -/
private theorem denseSplitOne_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi b : BusInteraction (DenseExpr p)) (hb : b ∈ denseSplitOne bs facts bi)
    {v : VarId} (hv : v ∈ denseBIVars b) : v ∈ denseBIVars bi := by
  cases hab : denseAsBytePair bs facts bi with
  | none => simp only [denseSplitOne, hab, List.mem_singleton] at hb; subst hb; exact hv
  | some t =>
    obtain ⟨busId, spec, a, b'⟩ := t
    simp only [denseSplitOne, hab] at hb
    obtain ⟨rfl, hspec⟩ := denseAsBytePair_eq bs facts bi busId spec a b' hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    obtain ⟨hma, hmb⟩ := denseMkBytePair_operand_mem spec busId a b'
    rcases hb with rfl | rfl
    · rw [denseBIVars, List.mem_append] at hv
      rcases hv with hm | hp
      · simp only [denseMkByteCheck, DenseExpr.vars, List.not_mem_nil] at hm
      · rw [List.mem_flatMap] at hp
        obtain ⟨pe, hpe, hx⟩ := hp
        exact denseMem_biVars_of_payload (denseMkBytePair spec busId a b') a hma
          (denseMkByteCheck_payload_vars spec busId a pe hpe hx)
    · rw [denseBIVars, List.mem_append] at hv
      rcases hv with hm | hp
      · simp only [denseMkByteCheck, DenseExpr.vars, List.not_mem_nil] at hm
      · rw [List.mem_flatMap] at hp
        obtain ⟨pe, hpe, hx⟩ := hp
        exact denseMem_biVars_of_payload (denseMkBytePair spec busId a b') b' hmb
          (denseMkByteCheck_payload_vars spec busId b' pe hpe hx)

/-- Every split interaction is either `bi` itself, or never breaks an invariant (a byte self-check).
    Native mirror of `SplitBytePair.splitOne_breaksInvariant`
   . -/
private theorem denseSplitOne_breaksInvariant (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi b : BusInteraction (DenseExpr p)) (hb : b ∈ denseSplitOne bs facts bi)
    (denv : VarId → ZMod p) :
    (b = bi) ∨ bs.breaksInvariant (denseBIEval b denv) = false := by
  cases hab : denseAsBytePair bs facts bi with
  | none => simp only [denseSplitOne, hab, List.mem_singleton] at hb; exact Or.inl hb
  | some t =>
    obtain ⟨busId, spec, a, b'⟩ := t
    simp only [denseSplitOne, hab] at hb
    obtain ⟨rfl, hspec⟩ := denseAsBytePair_eq bs facts bi busId spec a b' hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    refine Or.inr ?_
    rcases hb with rfl | rfl
    · exact denseMkByteCheck_breaks bs facts spec busId hspec a denv
    · exact denseMkByteCheck_breaks bs facts spec busId hspec b' denv

/-- Each split interaction is covered whenever the original is (`a`/`b` are payload entries). -/
private theorem denseSplitOne_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (hbi : denseBICovered reg bi)
    (b : BusInteraction (DenseExpr p)) (hb : b ∈ denseSplitOne bs facts bi) :
    denseBICovered reg b := by
  cases hab : denseAsBytePair bs facts bi with
  | none => simp only [denseSplitOne, hab, List.mem_singleton] at hb; subst hb; exact hbi
  | some t =>
    obtain ⟨busId, spec, a, b'⟩ := t
    simp only [denseSplitOne, hab] at hb
    obtain ⟨rfl, hspec⟩ := denseAsBytePair_eq bs facts bi busId spec a b' hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    obtain ⟨hma, hmb⟩ := denseMkBytePair_operand_mem spec busId a b'
    have ha : a.CoveredBy reg := hbi.2 a hma
    have hb2 : b'.CoveredBy reg := hbi.2 b' hmb
    rcases hb with rfl | rfl
    · exact denseMkByteCheck_covered reg spec busId a ha
    · exact denseMkByteCheck_covered reg spec busId b' hb2

/-- Native correctness of one full split (parameterised on the output system so the projections
    reduce by `rfl` at the call site). -/
private theorem denseSplitBytePair_correct_aux (isInput : VarId → Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (d out : DenseConstraintSystem p)
    (hac : out.algebraicConstraints = d.algebraicConstraints)
    (hbus : out.busInteractions = d.busInteractions.flatMap (denseSplitOne bs facts)) :
    DensePassCorrect isInput d out [] bs := by
  have hsatiff : ∀ denv, d.satisfies bs denv ↔ out.satisfies bs denv := by
    intro denv
    simp only [DenseConstraintSystem.satisfies, hac, hbus]
    constructor
    · rintro ⟨hc, hb⟩
      exact ⟨hc, (forall_denseP_flatMap bs facts hp1 d.busInteractions denv).2 hb⟩
    · rintro ⟨hc, hb⟩
      exact ⟨hc, (forall_denseP_flatMap bs facts hp1 d.busInteractions denv).1 hb⟩
  have hside : ∀ denv, d.sideEffects bs denv = out.sideEffects bs denv := by
    intro denv
    simp only [DenseConstraintSystem.sideEffects, hbus]
    rw [filter_stateful_flatMap bs facts d.busInteractions]
  have hadm : ∀ denv, d.admissible bs denv ↔ out.admissible bs denv := by
    intro denv
    unfold DenseConstraintSystem.admissible
    rw [hbus, map_filter_flatMap bs facts d.busInteractions denv]
  have hsub : ∀ i ∈ out.occ, i ∈ d.occ := by
    intro i hi
    rw [DenseConstraintSystem.occ, hac, hbus, List.mem_append] at hi
    rw [DenseConstraintSystem.occ, List.mem_append]
    rcases hi with hi | hi
    · exact Or.inl hi
    · rw [List.mem_flatMap] at hi
      obtain ⟨bi, hbi, hib⟩ := hi
      rw [List.mem_flatMap] at hbi
      obtain ⟨orig, horig, hbimem⟩ := hbi
      exact Or.inr (List.mem_flatMap.2 ⟨orig, horig, denseSplitOne_vars bs facts orig bi hbimem hib⟩)
  refine DensePassCorrect.ofEnvEq ?_ ?_ hsub ?_
  · intro denv hsat
    exact ⟨denv, (hsatiff denv).2 hsat, by rw [hside denv]; exact BusState.equiv_refl _⟩
  · intro hgi denv hsat bi hbi
    rw [hbus, List.mem_flatMap] at hbi
    obtain ⟨orig, horig, hbimem⟩ := hbi
    show (denseBIEval bi denv).multiplicity ≠ 0 → bs.breaksInvariant (denseBIEval bi denv) = false
    intro hne
    rcases denseSplitOne_breaksInvariant bs facts orig bi hbimem denv with heq | hbrk
    · rw [heq]; exact hgi denv ((hsatiff denv).2 hsat) orig horig (heq ▸ hne)
    · exact hbrk
  · intro denv hadmE hsat
    exact ⟨(hsatiff denv).1 hsat, (hadm denv).1 hadmE, by rw [hside denv]; exact BusState.equiv_refl _⟩

/-- Coverage is preserved by the split. -/
theorem denseSplitBytePairF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseSplitBytePairF bs facts d).CoveredBy reg := by
  unfold denseSplitBytePairF
  split
  · refine ⟨hcov.1, fun bi hbi => ?_⟩
    have hbi' : bi ∈ d.busInteractions.flatMap (denseSplitOne bs facts) := hbi
    obtain ⟨orig, horig, hbimem⟩ := List.mem_flatMap.1 hbi'
    exact denseSplitOne_covered reg bs facts orig (hcov.2 orig horig) bi hbimem
  · exact hcov

/-- Native `DensePassCorrect` of the whole split transform. -/
theorem denseSplitBytePairF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseSplitBytePairF bs facts d) [] bs := by
  unfold denseSplitBytePairF
  split
  next hp1 => exact denseSplitBytePair_correct_aux reg.isInput bs facts hp1 d _ rfl rfl
  next => exact DensePassCorrect.refl reg.isInput d bs

/-- The dense byte-check pair splitting pass. Registry-preserving (`a`/`b` are existing operands, no
    fresh variables): `of` over `denseSplitBytePairF`, lifted to the audited `Variable`
    `PassCorrect` once by `DensePassCorrect.lift`. Native proof — no dependency on the reference
    `splitBytePairPass`. -/
def denseSplitBytePairPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d => denseSplitBytePairF bs facts d)
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseSplitBytePairF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseSplitBytePairF_correct reg bs facts d)

end ApcOptimizer.Dense
