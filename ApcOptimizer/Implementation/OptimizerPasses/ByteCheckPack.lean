import ApcOptimizer.Implementation.OptimizerPasses.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus

set_option autoImplicit false

/-! # Generalized single-value byte-check packing (`byteCheckPackPass`)

On a byte-lookup bus a single value is byte-range-checked in one of several multiplicity-1 encodings
that all impose exactly "this value is a byte" — the self-check, the two XOR-with-zero mirrors, and
the two NOT (XOR-with-255) forms (the last shape `xorEqExtractPass` (C4b) + Gauss leave when a
`255`-operand XOR's NOT-result is substituted). All are recognized VM-neutrally through
`BusFacts.byteXorSpec` (decoded op `= xorOp`, byte bound `256`).

Two such single-value checks — in *any* combination of these forms — pack into **one** pair check
(`spec.encode pairOp`, i.e. OpenVM `[eA, eB, 0, 0]`), which imposes the identical obligation "both
operands are bytes". Because these lookups are stateless, the swap leaves every stateful side effect
and the memory discipline untouched: a pure bus-interaction win, variables and constraints unchanged.
This generalizes `bytePackPass` (which only recognized the canonical self-check); the extra mirror
forms are exactly the ones OpenVM emits for keccak state limbs.

The correctness of one packing step is the *general* stateless two-for-one swap
`mergeStateless2_correct` (from `TupleRange.lean`): given that each replaced interaction's acceptance
is equivalent to its value being a byte (`svCheck?_sound`), and the pair check's acceptance is the
conjunction of both byte obligations (`mkBytePair_accepted`), the swap preserves the satisfying set.
No new correctness lemma is needed. VM-agnostic: with `BusFacts.trivial` `byteXorSpec` is `none`, so
`svCheck?` returns `none` and the pass is the identity. One pair is packed per invocation;
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

/-- The value byte-checked by a multiplicity-1 single-value byte check, recognized through the
    VM-neutral `byteXorSpec` (byte bound `256`, decoded op `= xorOp`): the self-check (`o₁ = o₂`,
    `r = 0`), the two XOR-with-zero mirrors (`o₂ = 0, o₁ = r` / `o₁ = 0, o₂ = r`), and the two NOT
    (XOR-with-255) forms (`o₂ = 255, r = 255 − o₁` / `o₁ = 255, r = 255 − o₂`, when `256 ≤ p`) all
    return the checked operand; `none` otherwise. -/
def svCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | none => none
      | some (op, o1, o2, r) =>
        if bi.multiplicity = Expression.const 1 ∧ op = Expression.const spec.xorOp then
          if o1 = o2 ∧ r = Expression.const 0 then some o1
          else if o2 = Expression.const 0 ∧ o1 = r then some o1
          else if o1 = Expression.const 0 ∧ o2 = r then some o2
          else if decide (256 ≤ p) ∧ o2 = Expression.const 255 ∧ isByteCompl o1 r = true then some o1
          else if decide (256 ≤ p) ∧ o1 = Expression.const 255 ∧ isByteCompl o2 r = true then some o2
          else none
        else if bi.multiplicity = Expression.const 1 ∧
            spec.orOp.any (fun oop => op == Expression.const oop) = true then
          -- OR identity (`x | 0 = x`): the interaction is exactly a byte check on the survivor.
          if o2 = Expression.const 0 ∧ o1 = r then some o1
          else if o1 = Expression.const 0 ∧ o2 = r then some o2
          else none
        else none
    else none

/-- A membership helper for `BusInteraction.vars`: a variable of a payload expression is a variable
    of the interaction. -/
theorem mem_biVars_of_payload (bi : BusInteraction (Expression p)) (e : Expression p)
    (he : e ∈ bi.payload) {v : Variable} (hv : v ∈ e.vars) : v ∈ bi.vars := by
  rw [BusInteraction.vars]
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, hv⟩)

/-- `255 − a` with no wraparound is the byte complement, hence `a`'s XOR with `255`. -/
private theorem val_255_sub {p : ℕ} (hp : 256 ≤ p) (a : ZMod p) (ha : a.val < 256) :
    (255 - a).val = Nat.xor a.val 255 := by
  haveI : NeZero p := ⟨by omega⟩
  have hle : a.val ≤ 255 := by omega
  have ha' : a = ((a.val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse a).symm
  have hcast : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  have hval : (255 - a).val = 255 - a.val := by
    calc (255 - a).val
        = ((255 : ZMod p) - ((a.val : ℕ) : ZMod p)).val := by rw [← ha']
      _ = (((255 - a.val : ℕ) : ZMod p)).val := by rw [Nat.cast_sub hle, hcast]
      _ = 255 - a.val := ZMod.val_natCast_of_lt (by omega)
  rw [hval]; exact (nat_xor_255 _ ha).symm

/-- `(255 : ZMod p).val = 255` when `256 ≤ p`. -/
private theorem val_255 {p : ℕ} (hp : 256 ≤ p) : (255 : ZMod p).val = 255 := by
  have hc : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  rw [← hc, ZMod.val_natCast_of_lt (by omega)]

/-- A recognized single-value byte check is stateless, has multiplicity 1, its value is a payload
    entry, and its acceptance is exactly "the value is a byte". -/
theorem svCheck?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (e : Expression p) (h : svCheck? bs facts bi = some e) :
    bs.isStateful bi.busId = false ∧ bi.multiplicity = Expression.const 1 ∧ e ∈ bi.payload ∧
      (∀ env, bs.violatesConstraint (bi.eval env) = false ↔ (e.eval env).val < 256) := by
  unfold svCheck? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i hb
      have hbound : spec.bound = 256 := of_decide_eq_true hb
      split at h
      · exact absurd h (by simp)
      · rename_i op o1 o2 r hdec
        have hstateless := (facts.byteXorSpec_sound bi.busId spec hspec).1
        obtain ⟨hmemO1, hmemO2, _⟩ := spec.decode_mem bi.payload op o1 o2 r hdec
        have key := byteXorSpec_decode_iff bs facts spec bi hspec op o1 o2 r hdec
        split_ifs at h with hmo hA hB hC hD hE hor hOA hOB
        · -- self-check: o₁ = o₂, r = 0
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨he12, hr0⟩ := hA
          obtain rfl : o1 = e := by simpa using h
          refine ⟨hstateless, hm, hmemO1, fun env => ?_⟩
          have hopEv : op.eval env = spec.xorOp := by rw [hop]; rfl
          rw [(key env).1 hopEv, hbound]
          refine ⟨fun hh => hh.1, fun hh => ⟨hh, he12 ▸ hh, ?_⟩⟩
          rw [show r.eval env = 0 by rw [hr0]; rfl, ZMod.val_zero, ← he12]
          exact (Nat.xor_self _).symm
        · -- XOR-with-zero: o₂ = 0, o₁ = r
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hz, heq⟩ := hB
          obtain rfl : o1 = e := by simpa using h
          refine ⟨hstateless, hm, hmemO1, fun env => ?_⟩
          have hopEv : op.eval env = spec.xorOp := by rw [hop]; rfl
          rw [(key env).1 hopEv, hbound]
          refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_, ?_⟩⟩
          · rw [show o2.eval env = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
          · rw [show r.eval env = o1.eval env by rw [heq], show o2.eval env = 0 by rw [hz]; rfl,
              ZMod.val_zero]
            exact (Nat.xor_zero _).symm
        · -- mirror XOR-with-zero: o₁ = 0, o₂ = r
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hz, heq⟩ := hC
          obtain rfl : o2 = e := by simpa using h
          refine ⟨hstateless, hm, hmemO2, fun env => ?_⟩
          have hopEv : op.eval env = spec.xorOp := by rw [hop]; rfl
          rw [(key env).1 hopEv, hbound]
          refine ⟨fun hh => hh.2.1, fun hh => ⟨?_, hh, ?_⟩⟩
          · rw [show o1.eval env = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
          · rw [show r.eval env = o2.eval env by rw [heq], show o1.eval env = 0 by rw [hz]; rfl,
              ZMod.val_zero]
            exact (Nat.zero_xor _).symm
        · -- NOT-form: o₂ = 255, r = 255 − o₁
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hp, hz, hcompl⟩ := hD
          obtain rfl : o1 = e := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hp
          refine ⟨hstateless, hm, hmemO1, fun env => ?_⟩
          have hopEv : op.eval env = spec.xorOp := by rw [hop]; rfl
          have ho2 : o2.eval env = 255 := by rw [hz]; rfl
          have hr : r.eval env = 255 - o1.eval env := isByteCompl_sound o1 r hcompl env
          rw [(key env).1 hopEv, hbound]
          refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_, ?_⟩⟩
          · rw [ho2, val_255 hple]; omega
          · rw [hr, ho2, val_255 hple, val_255_sub hple _ hh]
        · -- mirror NOT-form: o₁ = 255, r = 255 − o₂
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hp, hz, hcompl⟩ := hE
          obtain rfl : o2 = e := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hp
          refine ⟨hstateless, hm, hmemO2, fun env => ?_⟩
          have hopEv : op.eval env = spec.xorOp := by rw [hop]; rfl
          have ho1 : o1.eval env = 255 := by rw [hz]; rfl
          have hr : r.eval env = 255 - o2.eval env := isByteCompl_sound o2 r hcompl env
          rw [(key env).1 hopEv, hbound]
          refine ⟨fun hh => hh.2.1, fun hh => ⟨?_, hh, ?_⟩⟩
          · rw [ho1, val_255 hple]; omega
          · rw [hr, ho1, val_255 hple, val_255_sub hple _ hh]; exact Nat.xor_comm _ _
        · -- OR identity: o₂ = 0, o₁ = r
          obtain ⟨hm, horAny⟩ := hor; obtain ⟨hz, heq⟩ := hOA
          obtain rfl : o1 = e := by simpa using h
          cases hoo : spec.orOp with
          | none => rw [hoo] at horAny; simp [Option.any] at horAny
          | some oop =>
            rw [hoo] at horAny
            simp only [Option.any, beq_iff_eq] at horAny
            refine ⟨hstateless, hm, hmemO1, fun env => ?_⟩
            have hopEv : op.eval env = oop := by rw [horAny]; rfl
            have keyOr := (byteBoolSound_decode_iff bs facts spec bi hspec op o1 o2 r hdec env).1
              oop hoo hopEv
            rw [keyOr, hbound]
            refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_, ?_⟩⟩
            · rw [show o2.eval env = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
            · rw [show r.eval env = o1.eval env by rw [heq],
                show o2.eval env = 0 by rw [hz]; rfl, ZMod.val_zero]
              simp
        · -- mirror OR identity: o₁ = 0, o₂ = r
          obtain ⟨hm, horAny⟩ := hor; obtain ⟨hz, heq⟩ := hOB
          obtain rfl : o2 = e := by simpa using h
          cases hoo : spec.orOp with
          | none => rw [hoo] at horAny; simp [Option.any] at horAny
          | some oop =>
            rw [hoo] at horAny
            simp only [Option.any, beq_iff_eq] at horAny
            refine ⟨hstateless, hm, hmemO2, fun env => ?_⟩
            have hopEv : op.eval env = oop := by rw [horAny]; rfl
            have keyOr := (byteBoolSound_decode_iff bs facts spec bi hspec op o1 o2 r hdec env).1
              oop hoo hopEv
            rw [keyOr, hbound]
            refine ⟨fun hh => hh.2.1, fun hh => ⟨?_, hh, ?_⟩⟩
            · rw [show o1.eval env = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
            · rw [show r.eval env = o2.eval env by rw [heq],
                show o1.eval env = 0 by rw [hz]; rfl, ZMod.val_zero]
              simp
    · exact absurd h (by simp)

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
        match hbx : facts.byteXorSpec a.busId with
        | some spec =>
          if hbound : spec.bound = 256 then
            if hsplit : cs.busInteractions = revPre.reverse ++ a :: mid ++ b :: post then
              some ⟨{ cs with busInteractions :=
                        revPre.reverse ++ mkBytePair spec a.busId eA eB :: mid ++ post }, [],
                    by
                      have hsb : svCheck? bs facts b = some eB :=
                        findSecond_sound bs facts a.busId [] rest mid b eB post hfs
                      have hsa := svCheck?_sound bs facts a eA ha
                      have hsbd := svCheck?_sound bs facts b eB hsb
                      refine mergeStateless2_correct cs bs hp1 a b (mkBytePair spec a.busId eA eB)
                        hsa.1 hsbd.1 hsa.1 hsa.2.1 hsbd.2.1 rfl (fun env => ?_) (fun env => ?_)
                        (fun v hv => ?_) revPre.reverse mid post hsplit
                      · -- obligation equivalence
                        rw [mkBytePair_accepted bs facts spec a.busId hbx eA eB env, hbound]
                        exact and_congr (hsa.2.2.2 env).symm (hsbd.2.2.2 env).symm
                      · -- the pair check breaks no invariant
                        exact mkBytePair_breaks bs facts spec a.busId hbx eA eB env
                      · -- the pair check's variables come from `a` and `b`
                        have hvab : v ∈ eA.vars ∨ v ∈ eB.vars := by
                          rw [BusInteraction.vars, List.mem_append] at hv
                          rcases hv with hm | hp
                          · simp only [mkBytePair, Expression.vars, List.not_mem_nil] at hm
                          · rw [List.mem_flatMap] at hp
                            obtain ⟨pe, hpe, hx⟩ := hp
                            exact mkBytePair_payload_vars spec a.busId eA eB pe hpe hx
                        rcases hvab with h | h
                        · exact Or.inl (mem_biVars_of_payload a eA hsa.2.2.1 h)
                        · exact Or.inr (mem_biVars_of_payload b eB hsbd.2.2.1 h)⟩
            else findGo cs bs facts hp1 (a :: revPre) rest
          else findGo cs bs facts hp1 (a :: revPre) rest
        | none => findGo cs bs facts hp1 (a :: revPre) rest
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
