import ApcOptimizer.Implementation.OptimizerPasses.BytePack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # Byte-check pair splitting (`splitBytePairPass`)

The inverse of `bytePackPass` (`BytePack.lean`): explode every packed pair byte check
`[a, b, 0, 0]` on a `bytePairBus` back into the two single-value checks `[a, a, 0, 1]`,
`[b, b, 0, 1]`. Because the pair and the two singles impose the *identical* obligation ("both
operands are bytes") — the proven `bytePairBus` fact — the split is satisfaction-preserving, and
because these lookups are stateless it leaves every stateful side effect and the memory discipline
untouched. It is variable- and constraint-neutral; it *increases* the bus-interaction count on its
own, so it is never run to a fixpoint.

Its purpose is to unblock two downstream cleanups that a packed pair traps:

* **Duplicate byte-value elimination.** The same value is often byte-checked in several *different*
  pairs (a constant `0`, or a limb reused across rows). As `[0, b, 0, 0]` and `[0, c, 0, 0]` these
  are not syntactic duplicates, so `Dedup` cannot collapse them; as singles `[0, 0, 0, 1]` they are,
  and `Dedup` keeps one.
* **Operand-granular redundant-byte drop.** `RedundantByteDrop` drops a pair only when *both*
  operands are byte-justified elsewhere (memory-read words, constants). A pair mixing a
  memory-guaranteed byte with a freshly computed ALU result is kept, trapping the redundant half.
  Split into singles, the justified half is dropped and the other kept.

The intended pipeline placement is the coda: `… → busPairCancelLate → splitBytePair → dedupLate →
redundantByteDrop → bytePackLate → …`. `bytePackLate` re-packs the surviving singles, so a pair
with no redundant/duplicate operand is reconstructed unchanged (net zero), while trapped redundancy
is shed. The split transiently *increases* the bus count, so it must never run inside the
size-decreasing cleanup fixpoint.

The table equivalence is the same proven `BusFacts` fact (`bytePairBus`) `bytePackPass` uses; with
`BusFacts.trivial` (`bytePairBus = false`) this pass is a no-op. -/

namespace SplitBytePair

variable {p : ℕ}

/-- Recognize a packed pair byte check `[a, b, 0, 0]` (multiplicity `1`) on a bus that is both a
    `bytePairBus` and a `byteCheck` bus, returning `(busId, a, b)`. -/
def asBytePair {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Nat × Expression p × Expression p) :=
  if facts.bytePairBus bi.busId && facts.byteCheck bi.busId then
    match bi.multiplicity, bi.payload with
    | .const c, [a, b, .const z, .const op] =>
        if decide (c = 1) && decide (z = 0) && decide (op = 0) then some (bi.busId, a, b) else none
    | _, _ => none
  else none

/-- A recognizer hit pins the whole interaction: `bi` is exactly `byteCheck2 busId a b`, and both
    facts hold on `busId`. -/
theorem asBytePair_eq {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (busId : Nat) (a b : Expression p)
    (h : asBytePair facts bi = some (busId, a, b)) :
    bi = byteCheck2 busId a b ∧ facts.bytePairBus busId = true ∧ facts.byteCheck busId = true := by
  obtain ⟨biBus, biMul, biPay⟩ := bi
  unfold asBytePair at h
  simp only at h
  split at h
  · rename_i hbus
    rw [Bool.and_eq_true] at hbus
    split at h
    · rename_i c a' b' z op _
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, hbus.1, hbus.2⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The two shapes of `splitOne`, unfolded via the recognizer. -/
def splitOne {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : List (BusInteraction (Expression p)) :=
  match asBytePair facts bi with
  | some (busId, a, b) => [byteCheck1 busId a, byteCheck1 busId b]
  | none => [bi]

/-- `[x].filter p ++ ys.filter p = (x :: ys).filter p`. -/
private theorem filter_cons_append {α : Type} (q : α → Bool) (x : α) (ys : List α) :
    ([x].filter q) ++ ys.filter q = (x :: ys).filter q := by
  cases h : q x <;> simp [List.filter_cons, h]

/-- The obligation predicate that appears in `satisfies`. -/
private def P {bs : BusSemantics p} (env : Variable → ZMod p)
    (bi : BusInteraction (Expression p)) : Prop :=
  (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false

/-- Per-interaction obligation equivalence: the split list carries the same obligation as `bi`. -/
private theorem splitOne_P (bs : BusSemantics p) (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    (bi : BusInteraction (Expression p)) (env : Variable → ZMod p) :
    (∀ b ∈ splitOne facts bi, P (bs := bs) env b) ↔ P (bs := bs) env bi := by
  unfold splitOne
  cases hab : asBytePair facts bi with
  | none => simp
  | some t =>
    obtain ⟨busId, a, b⟩ := t
    obtain ⟨rfl, hbp, hbc⟩ := asBytePair_eq facts bi busId a b hab
    obtain ⟨_, _, hbicond⟩ := facts.bytePairBus_sound busId hbp
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have hsaP : P (bs := bs) env (byteCheck1 busId a) ↔
        bs.violatesConstraint ((byteCheck1 busId a).eval env) = false := by
      unfold P; rw [byteCheck1_eval]; exact ⟨fun h => h (by simpa using hp1), fun h _ => h⟩
    have hsbP : P (bs := bs) env (byteCheck1 busId b) ↔
        bs.violatesConstraint ((byteCheck1 busId b).eval env) = false := by
      unfold P; rw [byteCheck1_eval]; exact ⟨fun h => h (by simpa using hp1), fun h _ => h⟩
    have hpairP : P (bs := bs) env (byteCheck2 busId a b) ↔
        bs.violatesConstraint ((byteCheck2 busId a b).eval env) = false := by
      unfold P; rw [byteCheck2_eval]; exact ⟨fun h => h (by simpa using hp1), fun h _ => h⟩
    rw [hsaP, hsbP, hpairP, byteCheck1_eval, byteCheck1_eval, byteCheck2_eval]
    exact (hbicond (a.eval env) (b.eval env) 1).symm

/-- The bus-list-level obligation equivalence. -/
private theorem forall_P_flatMap (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (l : List (BusInteraction (Expression p)))
    (env : Variable → ZMod p) :
    (∀ b ∈ l.flatMap (splitOne facts), P (bs := bs) env b) ↔ (∀ b ∈ l, P (bs := bs) env b) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.flatMap_cons]
    simp only [List.mem_append, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      exact ⟨(splitOne_P bs facts hp1 a env).1 (fun b hb => h b (Or.inl hb)),
        ih.1 (fun b hb => h b (Or.inr hb))⟩
    · rintro ⟨ha, hrest⟩ b (hb | hb)
      · exact (splitOne_P bs facts hp1 a env).2 ha b hb
      · exact ih.2 hrest b hb

/-- Splitting a stateless byte-pair check yields only stateless interactions, so the
    stateful-filtered bus list is unchanged (per interaction). -/
private theorem splitOne_filter_stateful (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) :
    (splitOne facts bi).filter (fun b => bs.isStateful b.busId)
      = [bi].filter (fun b => bs.isStateful b.busId) := by
  unfold splitOne
  cases hab : asBytePair facts bi with
  | none => rfl
  | some t =>
    obtain ⟨busId, a, b⟩ := t
    obtain ⟨rfl, hbp, _⟩ := asBytePair_eq facts bi busId a b hab
    have hst : bs.isStateful busId = false := (facts.bytePairBus_sound busId hbp).1
    simp only [byteCheck1, byteCheck2, List.filter_cons, List.filter_nil, hst,
      Bool.false_eq_true, if_false]

/-- The stateful-filtered bus list is invariant under the whole split. -/
private theorem filter_stateful_flatMap (bs : BusSemantics p) (facts : BusFacts p bs)
    (l : List (BusInteraction (Expression p))) :
    (l.flatMap (splitOne facts)).filter (fun b => bs.isStateful b.busId)
      = l.filter (fun b => bs.isStateful b.busId) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, List.filter_append, splitOne_filter_stateful bs facts a, ih]
    exact filter_cons_append _ a rest

/-- The active∧stateful evaluated messages are invariant under the split (per interaction). -/
private theorem splitOne_map_filter (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (env : Variable → ZMod p) :
    ((splitOne facts bi).map (fun b => b.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = ([bi].map (fun b => b.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
  unfold splitOne
  cases hab : asBytePair facts bi with
  | none => rfl
  | some t =>
    obtain ⟨busId, a, b⟩ := t
    obtain ⟨rfl, hbp, _⟩ := asBytePair_eq facts bi busId a b hab
    have hst : bs.isStateful busId = false := (facts.bytePairBus_sound busId hbp).1
    simp only [byteCheck1, byteCheck2, List.map_cons, List.map_nil, BusInteraction.eval,
      List.filter_cons, List.filter_nil, hst, Bool.and_false, Bool.false_eq_true, if_false]

/-- The active∧stateful evaluated-message list is invariant under the whole split. -/
private theorem map_filter_flatMap (bs : BusSemantics p) (facts : BusFacts p bs)
    (l : List (BusInteraction (Expression p))) (env : Variable → ZMod p) :
    ((l.flatMap (splitOne facts)).map (fun b => b.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = (l.map (fun b => b.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, List.map_append, List.filter_append, splitOne_map_filter bs facts a env,
      ih]
    simp only [List.map_cons, List.map_nil]
    exact filter_cons_append _ (a.eval env) (rest.map (fun b => b.eval env))

/-- Variables of a split interaction come from the original. -/
private theorem splitOne_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi b : BusInteraction (Expression p)) (hb : b ∈ splitOne facts bi)
    (v : Variable) (hv : v ∈ b.multiplicity.vars ∨ ∃ e ∈ b.payload, v ∈ e.vars) :
    v ∈ bi.multiplicity.vars ∨ ∃ e ∈ bi.payload, v ∈ e.vars := by
  cases hab : asBytePair facts bi with
  | none => simp only [splitOne, hab, List.mem_singleton] at hb; subst hb; exact hv
  | some t =>
    obtain ⟨busId, a, b'⟩ := t
    simp only [splitOne, hab] at hb
    obtain ⟨rfl, _, _⟩ := asBytePair_eq facts bi busId a b' hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;>
      · simp only [byteCheck1, byteCheck2, Expression.vars, List.mem_cons, List.not_mem_nil,
          List.append_nil, List.nil_append, or_false, exists_eq_or_imp, exists_eq_left] at hv ⊢
        tauto

/-- Every split interaction is either `bi` itself, or never breaks an invariant (a byte self-check). -/
private theorem splitOne_breaksInvariant (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi b : BusInteraction (Expression p)) (hb : b ∈ splitOne facts bi)
    (env : Variable → ZMod p) :
    (b = bi) ∨ bs.breaksInvariant (b.eval env) = false := by
  cases hab : asBytePair facts bi with
  | none => simp only [splitOne, hab, List.mem_singleton] at hb; exact Or.inl hb
  | some t =>
    obtain ⟨busId, a, b'⟩ := t
    simp only [splitOne, hab] at hb
    obtain ⟨rfl, _, hbc⟩ := asBytePair_eq facts bi busId a b' hab
    obtain ⟨_, hbrk, _⟩ := facts.byteCheck_sound busId hbc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    refine Or.inr ?_
    rcases hb with rfl | rfl
    · rw [byteCheck1_eval]; exact hbrk (a.eval env)
    · rw [byteCheck1_eval]; exact hbrk (b'.eval env)

/-! ## The pass -/

/-- Split every packed pair byte check into two single-value checks. Correct by the `bytePairBus`
    fact (obligation-equivalent) and stateless (side effects, memory discipline, admissibility
    untouched). -/
def splitBytePairPass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    let out : ConstraintSystem p :=
      { cs with busInteractions := cs.busInteractions.flatMap (splitOne facts) }
    have hbus : out.busInteractions = cs.busInteractions.flatMap (splitOne facts) := rfl
    ⟨out, [], by
      have hsatiff : ∀ env, cs.satisfies bs env ↔ out.satisfies bs env := by
        intro env
        simp only [ConstraintSystem.satisfies, hbus]
        constructor
        · rintro ⟨hc, hb⟩
          exact ⟨hc, (forall_P_flatMap bs facts hp1 cs.busInteractions env).2 hb⟩
        · rintro ⟨hc, hb⟩
          exact ⟨hc, (forall_P_flatMap bs facts hp1 cs.busInteractions env).1 hb⟩
      have hside : ∀ env, cs.sideEffects bs env = out.sideEffects bs env := by
        intro env
        simp only [ConstraintSystem.sideEffects, hbus, filter_stateful_flatMap bs facts]
      have hadm : ∀ env, cs.admissible bs env ↔ out.admissible bs env := by
        intro env
        simp only [ConstraintSystem.admissible, hbus, map_filter_flatMap bs facts]
      have hsub : ∀ v ∈ out.vars, v ∈ cs.vars := by
        intro v hv
        rw [ConstraintSystem.mem_vars] at hv ⊢
        rcases hv with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hvbi⟩
        · exact Or.inl ⟨c, hc, hvc⟩
        · rw [hbus, List.mem_flatMap] at hbi
          obtain ⟨orig, horig, hbimem⟩ := hbi
          exact Or.inr ⟨orig, horig, splitOne_vars bs facts orig bi hbimem v hvbi⟩
      refine PassCorrect.ofEnvEq ?_ ?_ hsub ?_
      · intro env hsat
        exact ⟨env, (hsatiff env).2 hsat, by rw [← hside]; exact BusState.equiv_refl _⟩
      · intro hinv env hsat bi hbi
        rw [hbus, List.mem_flatMap] at hbi
        obtain ⟨orig, horig, hbimem⟩ := hbi
        show (bi.eval env).multiplicity ≠ 0 → bs.breaksInvariant (bi.eval env) = false
        intro hne
        rcases splitOne_breaksInvariant bs facts orig bi hbimem env with heq | hbrk
        · rw [heq]; exact hinv env ((hsatiff env).2 hsat) orig horig (heq ▸ hne)
        · exact hbrk
      · intro env hadmE hsat
        exact ⟨(hsatiff env).1 hsat, (hadm env).1 hadmE, by rw [← hside]; exact BusState.equiv_refl _⟩⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

end SplitBytePair
