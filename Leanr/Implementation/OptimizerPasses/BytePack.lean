import Leanr.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false
-- `simp`'s unused-argument linter mis-flags lemmas that enable a rewrite another lemma then
-- consumes (e.g. unfolding `Expression.vars` on a numeral); it is a style lint, not a soundness one.
set_option linter.unusedSimpArgs false

/-! # Byte-check packing (`bytePackPass`)

On a bitwise-style lookup bus (OpenVM's `BitwiseLookup`), a single value is byte-range-checked by the
self-XOR message `[e, e, 0, 1]` (op = 1: it asserts `e ⊕ e = 0`, which only forces both operands —
here the same `e` — to be bytes). Two such single-value checks pack into **one** pair check
`[e₁, e₂, 0, 0]` (op = 0: range-check both operands as bytes). The pair check imposes the *identical*
obligation — "both operands are bytes" — so replacing a pair of single checks with one pair check is
satisfaction-preserving. Because these lookups are **stateless**, the swap leaves every stateful side
effect and the memory discipline untouched: a pure bus-interaction win (variables and constraints
unchanged). This is exactly powdr's byte-check packing.

The table equivalence is a proven `BusFacts` fact (`bytePairBus`, discharged for OpenVM in
`Leanr/Implementation/OpenVmFacts.lean`); the pass here is VM-agnostic — with `BusFacts.trivial`
(`bytePairBus = false`) it is a no-op. One pair is packed per invocation; `iterateToFixpoint` drains
them (the bus length strictly drops by one each time). -/

variable {p : ℕ}

/-- Canonical single-value byte check `[e, e, 0, 1]` (multiplicity `1`). Constants are written with
    `Expression.const` rather than numeral sugar so the file needs no numeral-notation import. -/
def byteCheck1 (busId : Nat) (e : Expression p) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1, payload := [e, e, .const 0, .const 1] }

/-- Canonical packed pair byte check `[e₁, e₂, 0, 0]` (multiplicity `1`). -/
def byteCheck2 (busId : Nat) (e₁ e₂ : Expression p) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1, payload := [e₁, e₂, .const 0, .const 0] }

theorem byteCheck1_eval (busId : Nat) (e : Expression p) (env : Variable → ZMod p) :
    (byteCheck1 busId e).eval env
      = { busId := busId, multiplicity := 1, payload := [e.eval env, e.eval env, 0, 1] } := rfl

theorem byteCheck2_eval (busId : Nat) (e₁ e₂ : Expression p) (env : Variable → ZMod p) :
    (byteCheck2 busId e₁ e₂).eval env
      = { busId := busId, multiplicity := 1, payload := [e₁.eval env, e₂.eval env, 0, 0] } := rfl

/-! ## Correctness of one packing step -/

/-- Replacing a pair of single-value byte checks `A = [eA,eA,0,1]`, `B = [eB,eB,0,1]` (both on a
    `bytePairBus`) by the packed check `C = [eA,eB,0,0]` is `PassCorrect`: the fact makes `C`'s
    obligation equivalent to `A`'s and `B`'s together (same satisfying set), and all three are
    stateless so side effects and `admissible` are unchanged. No new variables, no derivations. -/
theorem mergeBytePair_correct (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (busId : Nat) (hbp : facts.bytePairBus busId = true)
    (pre mid post : List (BusInteraction (Expression p))) (eA eB : Expression p)
    (hsplit : cs.busInteractions
        = pre ++ byteCheck1 busId eA :: mid ++ byteCheck1 busId eB :: post) :
    PassCorrect cs
      { cs with busInteractions := pre ++ byteCheck2 busId eA eB :: mid ++ post } [] bs := by
  obtain ⟨hstate, hbrk, hbicond⟩ := facts.bytePairBus_sound busId hbp
  set out : ConstraintSystem p :=
    { cs with busInteractions := pre ++ byteCheck2 busId eA eB :: mid ++ post } with hout
  have houtb : out.busInteractions = pre ++ byteCheck2 busId eA eB :: mid ++ post := rfl
  -- all three interactions are stateless
  have hstA : bs.isStateful (byteCheck1 busId eA).busId = false := hstate
  have hstB : bs.isStateful (byteCheck1 busId eB).busId = false := hstate
  have hstC : bs.isStateful (byteCheck2 busId eA eB).busId = false := hstate
  -- per-env obligation equivalence: `P C ↔ P A ∧ P B`
  have hkey : ∀ env,
      (bs.violatesConstraint ((byteCheck2 busId eA eB).eval env) = false ↔
        bs.violatesConstraint ((byteCheck1 busId eA).eval env) = false ∧
          bs.violatesConstraint ((byteCheck1 busId eB).eval env) = false) := by
    intro env
    rw [byteCheck1_eval, byteCheck1_eval, byteCheck2_eval]
    exact hbicond (eA.eval env) (eB.eval env) 1
  -- the obligation predicate that appears in `satisfies`
  set P : (Variable → ZMod p) → BusInteraction (Expression p) → Prop :=
    fun env bi => (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false
    with hP
  have hPA : ∀ env, (P env (byteCheck1 busId eA) ↔
      bs.violatesConstraint ((byteCheck1 busId eA).eval env) = false) := by
    intro env
    simp only [hP, byteCheck1_eval]
    exact ⟨fun h => h hp1, fun h _ => h⟩
  have hPB : ∀ env, (P env (byteCheck1 busId eB) ↔
      bs.violatesConstraint ((byteCheck1 busId eB).eval env) = false) := by
    intro env
    simp only [hP, byteCheck1_eval]
    exact ⟨fun h => h hp1, fun h _ => h⟩
  have hPC : ∀ env, (P env (byteCheck2 busId eA eB) ↔
      bs.violatesConstraint ((byteCheck2 busId eA eB).eval env) = false) := by
    intro env
    simp only [hP, byteCheck2_eval]
    exact ⟨fun h => h hp1, fun h _ => h⟩
  -- satisfaction equivalence
  have hsatiff : ∀ env, cs.satisfies bs env ↔ out.satisfies bs env := by
    intro env
    have hbus : (∀ bi ∈ cs.busInteractions, P env bi) ↔
        (∀ bi ∈ out.busInteractions, P env bi) := by
      rw [hsplit, houtb]
      simp only [List.forall_mem_append, List.forall_mem_cons]
      have hc := hPC env; have ha := hPA env; have hb := hPB env
      have hk := hkey env
      tauto
    constructor
    · rintro ⟨hcons, hb⟩
      exact ⟨hcons, (hbus.1 (fun bi hbi => hb bi hbi))⟩
    · rintro ⟨hcons, hb⟩
      exact ⟨hcons, (hbus.2 (fun bi hbi => hb bi hbi))⟩
  -- the stateful-filtered interaction lists coincide (A, B, C are stateless)
  have hfilt : cs.busInteractions.filter (fun bi => bs.isStateful bi.busId)
      = out.busInteractions.filter (fun bi => bs.isStateful bi.busId) := by
    rw [hsplit, houtb]
    simp only [List.filter_append, List.filter_cons, hstA, hstB, hstC, Bool.false_eq_true,
      if_false]
  have hside : ∀ env, cs.sideEffects bs env = out.sideEffects bs env := by
    intro env
    simp only [ConstraintSystem.sideEffects, hfilt]
  -- the active∧stateful evaluated messages coincide too (A, B, C are stateless)
  have hadmarg : ∀ env,
      (cs.busInteractions.map (fun bi => bi.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = (out.busInteractions.map (fun bi => bi.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
    intro env
    rw [hsplit, houtb]
    simp only [List.map_append, List.map_cons, List.filter_append, List.filter_cons,
      byteCheck1_eval, byteCheck2_eval, hstate, Bool.and_false, Bool.false_eq_true, if_false]
  have hadm : ∀ env, cs.admissible bs env ↔ out.admissible bs env := by
    intro env
    simp only [ConstraintSystem.admissible, hadmarg]
  -- membership: `out`'s interactions come from `cs`'s payloads (C's vars come from eA/eB)
  have hsub : ∀ v ∈ out.vars, v ∈ cs.vars := by
    intro v hv
    rw [ConstraintSystem.mem_vars] at hv ⊢
    rcases hv with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hvbi⟩
    · exact Or.inl ⟨c, hc, hvc⟩
    · rw [houtb] at hbi
      simp only [List.mem_append, List.mem_cons] at hbi
      rcases hbi with (h | rfl | h) | h
      · exact Or.inr ⟨bi, by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto, hvbi⟩
      · -- `bi = C = byteCheck2 busId eA eB`; its vars come from eA or eB
        have hnil0 : (Expression.const (0 : ZMod p)).vars = [] := rfl
        have hab : v ∈ eA.vars ∨ v ∈ eB.vars := by
          rcases hvbi with hm | ⟨e, he, hve⟩
          · -- multiplicity `1` has no variables
            exact absurd hm (by
              rw [show (byteCheck2 busId eA eB).multiplicity.vars = [] from rfl]
              simp)
          · have he' : e = eA ∨ e = eB ∨ e = Expression.const (0 : ZMod p)
                ∨ e = Expression.const (0 : ZMod p) := by simpa [byteCheck2] using he
            rcases he' with rfl | rfl | rfl | rfl
            · exact Or.inl hve
            · exact Or.inr hve
            · exact absurd hve (by rw [hnil0]; simp)
            · exact absurd hve (by rw [hnil0]; simp)
        have hpayA : eA ∈ (byteCheck1 busId eA).payload := by
          show eA ∈ [eA, eA, Expression.const 0, Expression.const 1]; exact List.mem_cons_self ..
        have hpayB : eB ∈ (byteCheck1 busId eB).payload := by
          show eB ∈ [eB, eB, Expression.const 0, Expression.const 1]; exact List.mem_cons_self ..
        rcases hab with h | h
        · exact Or.inr ⟨byteCheck1 busId eA,
            by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto,
            Or.inr ⟨eA, hpayA, h⟩⟩
        · exact Or.inr ⟨byteCheck1 busId eB,
            by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto,
            Or.inr ⟨eB, hpayB, h⟩⟩
      · exact Or.inr ⟨bi, by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto, hvbi⟩
      · exact Or.inr ⟨bi, by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto, hvbi⟩
  refine PassCorrect.ofEnvEq ?_ ?_ hsub ?_
  · intro env hsat
    exact ⟨env, (hsatiff env).2 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    rw [houtb] at hbi
    simp only [List.mem_append, List.mem_cons] at hbi
    rcases hbi with (h | rfl | h) | h
    · exact hinv env ((hsatiff env).2 hsat) bi
        (by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto)
    · -- `bi = C`: a multiplicity-1 packed check never breaks an invariant
      show ((byteCheck2 busId eA eB).eval env).multiplicity ≠ 0 →
        bs.breaksInvariant ((byteCheck2 busId eA eB).eval env) = false
      intro _
      rw [byteCheck2_eval]; exact hbrk (eA.eval env) (eB.eval env)
    · exact hinv env ((hsatiff env).2 hsat) bi
        (by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto)
    · exact hinv env ((hsatiff env).2 hsat) bi
        (by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto)
  · intro env hadmE hsat
    exact ⟨(hsatiff env).1 hsat, (hadm env).1 hadmE, by rw [hside]; exact BusState.equiv_refl _⟩

/-! ## The pass: find and pack one pair per invocation -/

/-- If `bi` is a single-value byte check `[e, e, 0, 1]` (multiplicity `1`) on a `bytePairBus`,
    return the checked value `e`. All fields are checked structurally, so a hit means
    `bi = byteCheck1 bi.busId e`. -/
def matchByteCheck {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  if facts.bytePairBus bi.busId then
    match bi.multiplicity, bi.payload with
    | .const c, [e, e', z, op] =>
        if decide (c = 1) && decide (e = e') && decide (z = .const 0) && decide (op = .const 1)
        then some e else none
    | _, _ => none
  else none

/-- Scan for the next byte check on `busId`, returning the interior `mid`, its value `eB`, and the
    remainder `post`. -/
def findSecond {bs : BusSemantics p} (facts : BusFacts p bs) (busId : Nat) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    Option (List (BusInteraction (Expression p)) × Expression p ×
      List (BusInteraction (Expression p)))
  | _, [] => none
  | revMid, b :: rest =>
    match matchByteCheck facts b with
    | some eB => if decide (b.busId = busId) then some (revMid.reverse, eB, rest)
                 else findSecond facts busId (b :: revMid) rest
    | none => findSecond facts busId (b :: revMid) rest

/-- Fused scan for the first packable pair; the O(n) split-equation `decide` runs only for the
    chosen candidate (mirrors `busPairCancel`). -/
def findBytePackGo (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (revPre : List (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) → Option (PassResult cs bs)
  | [] => none
  | a :: rest =>
    match matchByteCheck facts a with
    | some eA =>
      match findSecond facts a.busId [] rest with
      | some (mid, eB, post) =>
        if hbp : facts.bytePairBus a.busId = true then
          if hsplit : cs.busInteractions
              = revPre.reverse ++ byteCheck1 a.busId eA :: mid ++ byteCheck1 a.busId eB :: post then
            some ⟨{ cs with busInteractions :=
                      revPre.reverse ++ byteCheck2 a.busId eA eB :: mid ++ post }, [],
                  mergeBytePair_correct cs bs facts hp1 a.busId hbp revPre.reverse mid post eA eB
                    hsplit⟩
          else findBytePackGo cs bs facts hp1 (a :: revPre) rest
        else findBytePackGo cs bs facts hp1 (a :: revPre) rest
      | none => findBytePackGo cs bs facts hp1 (a :: revPre) rest
    | none => findBytePackGo cs bs facts hp1 (a :: revPre) rest

/-- Pack one pair of single-value byte checks into a pair check. `iterateToFixpoint` drains all
    packable pairs (the bus length strictly decreases each step). -/
def bytePackPass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    match findBytePackGo cs bs facts hp1 [] cs.busInteractions with
    | some r => r
    | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
