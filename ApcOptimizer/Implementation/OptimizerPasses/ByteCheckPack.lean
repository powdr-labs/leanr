import ApcOptimizer.Implementation.OptimizerPasses.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus

set_option autoImplicit false

/-! # Generalized single-value byte-check packing (`byteCheckPackPass`)

On a bitwise-style lookup bus a single value is byte-range-checked in one of several multiplicity-1
encodings that all impose exactly "this value is a byte":

* the self-check `[x, x, 0, 1]` (`BusFacts.byteCheck`),
* the XOR-with-zero form `[x, 0, x, 1]` and its mirror `[0, x, x, 1]` (`BusFacts.xorZeroCheck`),
* the NOT (XOR-with-255) form `[x, 255, 255 − x, 1]` and its mirror `[255, x, 255 − x, 1]`
  (`BusFacts.xorComplCheck`, where the third slot normalizes to `255 − x`) — the shape
  `xorEqExtractPass` (C4b) + Gauss leave when a `255`-operand XOR's NOT-result is substituted.

Two such single-value checks — in *any* combination of these forms — pack into **one** pair check
`[eA, eB, 0, 0]` (`BusFacts.bytePairBus`), which imposes the identical obligation "both operands are
bytes". Because these lookups are stateless, the swap leaves every stateful side effect and the
memory discipline untouched: a pure bus-interaction win, variables and constraints unchanged. This
generalizes `bytePackPass` (which only recognized the canonical self-check `[x, x, 0, 1]`); the extra
mirror forms are exactly the ones OpenVM emits for keccak state limbs.

The correctness of one packing step is the *general* stateless two-for-one swap
`mergeStateless2_correct` (from `TupleRange.lean`): given that each replaced interaction's acceptance
is equivalent to its value being a byte (`svCheck?_sound`), and the pair check's acceptance is the
conjunction of both byte obligations (`bytePairBus` + `byteCheck`), the swap preserves the satisfying
set. No new correctness lemma is needed. VM-agnostic: with `BusFacts.trivial` every fact is `false`,
so `svCheck?` returns `none` and the pass is the identity. One pair is packed per invocation;
`iterateToFixpoint` drains them (the bus length strictly drops by one each time). -/

namespace ByteCheckPack

variable {p : ℕ}

/-! ## Recognizing the NOT-form complement -/

/-- `255 − e` as an expression. -/
def complExpr (e : Expression p) : Expression p := .add (.const 255) (.mul (.const (-1)) e)

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment? Decided by folding
    `b − (255 − a)` to a constant and checking it is `0`. Recognizes the third slot of the NOT-form
    byte check `[a, 255, 255 − a, 1]` that `xorEqExtractPass` (C4b) + Gauss leave on the bus. -/
def isByteCompl (a b : Expression p) : Bool :=
  (Expression.add b (.mul (.const (-1)) (complExpr a))).normalize.constValue? == some 0

theorem isByteCompl_sound (a b : Expression p) (h : isByteCompl a b = true)
    (env : Variable → ZMod p) : b.eval env = 255 - a.eval env := by
  unfold isByteCompl at h
  have hc : (Expression.add b (.mul (.const (-1)) (complExpr a))).normalize.constValue? = some 0 := by
    simpa using h
  have h0 : (Expression.add b (.mul (.const (-1)) (complExpr a))).eval env = 0 := by
    have := Expression.constValue?_sound _ (0 : ZMod p) hc env
    rwa [Expression.normalize_eval] at this
  simp only [complExpr, Expression.eval] at h0
  linear_combination h0

/-! ## Recognizing a single-value byte check in any encoding -/

/-- The value byte-checked by a multiplicity-1 single-value bitwise byte check: the self-check
    `[x, x, 0, 1]` (`byteCheck`), the two XOR-with-zero mirrors `[x, 0, x, 1]` / `[0, x, x, 1]`
    (`xorZeroCheck`), and the two NOT (XOR-with-255) forms `[x, 255, 255 − x, 1]` /
    `[255, x, 255 − x, 1]` (`xorComplCheck`) all return `some x`; `none` otherwise. -/
def svCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match bi.payload with
  | [e1, e2, e3, e4] =>
    if bi.multiplicity = Expression.const 1 ∧ e4 = Expression.const 1 then
      if facts.byteCheck bi.busId = true ∧ e1 = e2 ∧ e3 = Expression.const 0 then some e1
      else if facts.xorZeroCheck bi.busId = true ∧ e2 = Expression.const 0 ∧ e1 = e3 then some e1
      else if facts.xorZeroCheck bi.busId = true ∧ e1 = Expression.const 0 ∧ e2 = e3 then some e2
      else if facts.xorComplCheck bi.busId = true ∧ e2 = Expression.const 255 ∧ isByteCompl e1 e3 = true then some e1
      else if facts.xorComplCheck bi.busId = true ∧ e1 = Expression.const 255 ∧ isByteCompl e2 e3 = true then some e2
      else none
    else none
  | [e1, w] =>
    -- a bare width-8 variable-range check `[e, 8]` (mult 1) is a byte check; `256 < p` keeps
    -- the width constant's canonical value at `8` so the strengths agree exactly
    if bi.multiplicity = Expression.const 1 ∧ facts.varRangeBus bi.busId = true
        ∧ w = Expression.const 8 ∧ 256 < p then some e1
    else none
  | _ => none

/-- A membership helper for `BusInteraction.vars`: a variable of a payload expression is a variable
    of the interaction. -/
theorem mem_biVars_of_payload (bi : BusInteraction (Expression p)) (e : Expression p)
    (he : e ∈ bi.payload) {v : Variable} (hv : v ∈ e.vars) : v ∈ bi.vars := by
  rw [BusInteraction.vars]
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, hv⟩)

/-- A recognized single-value byte check is stateless, has multiplicity 1, its value is a payload
    entry, and its acceptance is exactly "the value is a byte". -/
theorem svCheck?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (e : Expression p) (h : svCheck? bs facts bi = some e) :
    bs.isStateful bi.busId = false ∧ bi.multiplicity = Expression.const 1 ∧ e ∈ bi.payload ∧
      (∀ env, bs.violatesConstraint (bi.eval env) = false ↔ (e.eval env).val < 256) := by
  unfold svCheck? at h
  split at h
  case h_3 => exact absurd h (by simp)
  case h_2 e1 w hpay =>
    split_ifs at h with hmo
    · obtain ⟨hm, hvr, hw, hple⟩ := hmo
      obtain rfl : e1 = e := by simpa using h
      refine ⟨(facts.varRangeBus_sound bi.busId hvr).1, hm, by rw [hpay]; simp, fun env => ?_⟩
      have heq : bi.eval env
          = BusInteraction.mk bi.busId 1 [e1.eval env, (8 : ZMod p)] := by
        unfold BusInteraction.eval
        rw [hm, hpay, hw]; simp [Expression.eval]
      rw [heq]
      have h8 : ((8 : ZMod p)).val = 8 := by
        have hc : ((8 : ℕ) : ZMod p) = (8 : ZMod p) := by norm_num
        rw [← hc]
        exact ZMod.val_natCast_of_lt (by omega)
      rw [(facts.varRangeBus_sound bi.busId hvr).2 (e1.eval env) (8 : ZMod p) 1, h8]
      constructor
      · rintro ⟨-, hlt⟩
        simpa using hlt
      · intro hlt
        exact ⟨by omega, by simpa using hlt⟩
  case h_1 e1 e2 e3 e4 hpay =>
    -- payload shape and multiplicity
    have hmem : ∀ x ∈ ([e1, e2, e3, e4] : List (Expression p)), x ∈ bi.payload := by
      intro x hx; rw [hpay]; exact hx
    split_ifs at h with hmo hA hB hC hD hE
    · -- self-check `[x, x, 0, 1]`
      obtain ⟨hm, he4⟩ := hmo; obtain ⟨hfact, he12, he3⟩ := hA
      obtain rfl : e1 = e := by simpa using h
      refine ⟨(facts.byteCheck_sound bi.busId hfact).1, hm, hmem e1 (by simp), fun env => ?_⟩
      have heq : bi.eval env
          = { busId := bi.busId, multiplicity := 1, payload := [e1.eval env, e1.eval env, 0, 1] } := by
        unfold BusInteraction.eval
        rw [hm, hpay, ← he12, he3, he4]; simp [Expression.eval]
      rw [heq]
      exact (facts.byteCheck_sound bi.busId hfact).2.2 (e1.eval env) 1
    · -- XOR-with-zero `[x, 0, x, 1]`
      obtain ⟨hm, he4⟩ := hmo; obtain ⟨hfact, he2, he13⟩ := hB
      obtain rfl : e1 = e := by simpa using h
      refine ⟨(facts.xorZeroCheck_sound bi.busId hfact).1, hm, hmem e1 (by simp), fun env => ?_⟩
      have heq : bi.eval env
          = { busId := bi.busId, multiplicity := 1, payload := [e1.eval env, 0, e1.eval env, 1] } := by
        unfold BusInteraction.eval
        rw [hm, hpay, he2, ← he13, he4]; simp [Expression.eval]
      rw [heq]
      exact ((facts.xorZeroCheck_sound bi.busId hfact).2.1 (e1.eval env) 1)
    · -- mirror XOR-with-zero `[0, x, x, 1]`
      obtain ⟨hm, he4⟩ := hmo; obtain ⟨hfact, he1, he23⟩ := hC
      obtain rfl : e2 = e := by simpa using h
      refine ⟨(facts.xorZeroCheck_sound bi.busId hfact).1, hm, hmem e2 (by simp), fun env => ?_⟩
      have heq : bi.eval env
          = { busId := bi.busId, multiplicity := 1, payload := [0, e2.eval env, e2.eval env, 1] } := by
        unfold BusInteraction.eval
        rw [hm, hpay, he1, ← he23, he4]; simp [Expression.eval]
      rw [heq]
      exact ((facts.xorZeroCheck_sound bi.busId hfact).2.2 (e2.eval env) 1)
    · -- NOT-form `[x, 255, 255 - x, 1]`
      obtain ⟨hm, he4⟩ := hmo; obtain ⟨hfact, he2, hcompl⟩ := hD
      obtain rfl : e1 = e := by simpa using h
      refine ⟨(facts.xorComplCheck_sound bi.busId hfact).1, hm, hmem e1 (by simp), fun env => ?_⟩
      have he3 : e3.eval env = 255 - e1.eval env := isByteCompl_sound e1 e3 hcompl env
      have heq : bi.eval env
          = { busId := bi.busId, multiplicity := 1,
              payload := [e1.eval env, 255, 255 - e1.eval env, 1] } := by
        unfold BusInteraction.eval
        rw [hm, hpay, he2, he4]; simp [Expression.eval, he3]
      rw [heq]
      exact ((facts.xorComplCheck_sound bi.busId hfact).2.1 (e1.eval env) 1)
    · -- mirror NOT-form `[255, x, 255 - x, 1]`
      obtain ⟨hm, he4⟩ := hmo; obtain ⟨hfact, he1, hcompl⟩ := hE
      obtain rfl : e2 = e := by simpa using h
      refine ⟨(facts.xorComplCheck_sound bi.busId hfact).1, hm, hmem e2 (by simp), fun env => ?_⟩
      have he3 : e3.eval env = 255 - e2.eval env := isByteCompl_sound e2 e3 hcompl env
      have heq : bi.eval env
          = { busId := bi.busId, multiplicity := 1,
              payload := [255, e2.eval env, 255 - e2.eval env, 1] } := by
        unfold BusInteraction.eval
        rw [hm, hpay, he1, he4]; simp [Expression.eval, he3]
      rw [heq]
      exact ((facts.xorComplCheck_sound bi.busId hfact).2.2 (e2.eval env) 1)

/-! ## Acceptance of a pair check -/

/-- A pair check `[x, y, 0, 0]` (multiplicity 1) on a `bytePairBus` that also carries `byteCheck` is
    accepted exactly when both operands are bytes. -/
theorem pairAccept (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat)
    (hbp : facts.bytePairBus busId = true) (hbc : facts.byteCheck busId = true) (x y : ZMod p) :
    bs.violatesConstraint { busId := busId, multiplicity := 1, payload := [x, y, 0, 0] } = false
      ↔ x.val < 256 ∧ y.val < 256 :=
  ((facts.bytePairBus_sound busId hbp).2.2 x y 1).trans
    (and_congr ((facts.byteCheck_sound busId hbc).2.2 x 1) ((facts.byteCheck_sound busId hbc).2.2 y 1))

/-! ## The pass: find and pack one pair per invocation -/

/-- Scan for the next single-value byte check on `busId`, returning the interior `mid`, the
    interaction `b`, its checked value `eB`, and the remainder `post`. -/
def findSecond (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    Option (List (BusInteraction (Expression p)) × BusInteraction (Expression p) ×
      Expression p × List (BusInteraction (Expression p)))
  | _, [] => none
  | revMid, b :: rest =>
    match svCheck? bs facts b with
    | some eB => if decide (b.busId = busId) then some (revMid.reverse, b, eB, rest)
                 else findSecond bs facts busId (b :: revMid) rest
    | none => findSecond bs facts busId (b :: revMid) rest

/-- If `findSecond` returns `(mid, b, eB, post)` then `b` is a recognized single-value byte check
    with value `eB`. -/
theorem findSecond_sound (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat) :
    ∀ (revMid rest : List (BusInteraction (Expression p)))
      (mid : List (BusInteraction (Expression p))) (b : BusInteraction (Expression p))
      (eB : Expression p) (post : List (BusInteraction (Expression p))),
      findSecond bs facts busId revMid rest = some (mid, b, eB, post) →
      svCheck? bs facts b = some eB := by
  intro revMid rest
  induction rest generalizing revMid with
  | nil => intro _ _ _ _ h; exact absurd h (by simp [findSecond])
  | cons c cs ih =>
    intro mid b eB post h
    rw [findSecond] at h
    cases hc : svCheck? bs facts c with
    | none => rw [hc] at h; exact ih (c :: revMid) mid b eB post h
    | some eC =>
      rw [hc] at h
      split_ifs at h with hbus
      · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hcb, hceb, _⟩ := h
        rw [← hcb, ← hceb]; exact hc
      · exact ih (c :: revMid) mid b eB post h

/-- The target bus for a packed pair: prefer the singles' own bus; otherwise any bus present in
    the system carrying both pair facts. Byte singles recognised on a variable-range bus must
    emit their pair on a bitwise-style bus, which this scan finds. -/
def pairBus? {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (preferred : Nat) : Option Nat :=
  (preferred :: cs.busInteractions.map (·.busId)).find? (fun id =>
    facts.bytePairBus id && facts.byteCheck id)

/-- Fused scan for the first packable pair; the O(n) split-equation `decide` runs only for the
    chosen candidate (mirrors `bytePackPass`). -/
def findGo (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (revPre : List (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) → Option (PassResult cs bs)
  | [] => none
  | a :: rest =>
    match ha : svCheck? bs facts a with
    | some eA =>
      match hfs : findSecond bs facts a.busId [] rest with
      | some (mid, b, eB, post) =>
        match pairBus? facts cs a.busId with
        | none => findGo cs bs facts hp1 (a :: revPre) rest
        | some tId =>
        if hbp : facts.bytePairBus tId = true then
          if hbc : facts.byteCheck tId = true then
            if hsplit : cs.busInteractions = revPre.reverse ++ a :: mid ++ b :: post then
              some ⟨{ cs with busInteractions :=
                        revPre.reverse ++ byteCheck2 tId eA eB :: mid ++ post }, [],
                    by
                      have hsb : svCheck? bs facts b = some eB :=
                        findSecond_sound bs facts a.busId [] rest mid b eB post hfs
                      have hsa := svCheck?_sound bs facts a eA ha
                      have hsbd := svCheck?_sound bs facts b eB hsb
                      refine mergeStateless2_correct cs bs hp1 a b (byteCheck2 tId eA eB)
                        hsa.1 hsbd.1 (facts.bytePairBus_sound tId hbp).1 hsa.2.1 hsbd.2.1 rfl
                        (fun env => ?_) (fun env => ?_)
                        (fun v hv => ?_) revPre.reverse mid post hsplit
                      · -- obligation equivalence
                        rw [byteCheck2_eval,
                          pairAccept bs facts tId hbp hbc (eA.eval env) (eB.eval env)]
                        exact and_congr (hsa.2.2.2 env).symm (hsbd.2.2.2 env).symm
                      · -- the pair check breaks no invariant
                        rw [byteCheck2_eval]
                        exact (facts.bytePairBus_sound tId hbp).2.1 (eA.eval env) (eB.eval env)
                      · -- the pair check's variables come from `a` and `b`
                        have hvab : v ∈ eA.vars ∨ v ∈ eB.vars := by
                          simp only [byteCheck2, BusInteraction.vars, Expression.vars,
                            List.flatMap_cons, List.flatMap_nil, List.append_nil,
                            List.nil_append, List.mem_append] at hv
                          tauto
                        rcases hvab with h | h
                        · exact Or.inl (mem_biVars_of_payload a eA hsa.2.2.1 h)
                        · exact Or.inr (mem_biVars_of_payload b eB hsbd.2.2.1 h)⟩
            else findGo cs bs facts hp1 (a :: revPre) rest
          else findGo cs bs facts hp1 (a :: revPre) rest
        else findGo cs bs facts hp1 (a :: revPre) rest
      | none => findGo cs bs facts hp1 (a :: revPre) rest
    | none => findGo cs bs facts hp1 (a :: revPre) rest

/-- Pack one pair of single-value byte checks (in any encoding) into a pair check.
    `iterateToFixpoint` drains all packable pairs (the bus length strictly decreases each step). -/
def byteCheckPackPass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    match findGo cs bs facts hp1 [] cs.busInteractions with
    | some r => r
    | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

end ByteCheckPack
