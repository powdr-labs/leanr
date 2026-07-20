import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheckProof

set_option autoImplicit false

/-! # Native soundness of the dense `bytePack` recognizer and builders (Task 3, chunk BP-P1)

Native, `VarId`-native proofs for the recognizer and pair builder of the dense generalized
single-value byte-check packing pass (`OptimizerPasses/ByteCheckPack.lean`, impl chunk BP-I1).
These mirror the spec's `OldVariableBased/ByteCheckPack.lean` `_sound` lemmas and
`BytePack.lean`'s `mkBytePair_*` cluster, re-derived over dense environments `VarId → ZMod p`
with no decode dependency (`denseBIEval`, `DenseExpr.eval`, and value-level `BusFacts` application).

## Reuse

* `denseMkByteCheck` and its soundness (`denseMkByteCheck_eval`/`_accepted`/`_breaks`/
  `_payload_vars`, `BusPairCancelCheckProof.lean`) are reused verbatim: `denseMkBytePair`'s
  acceptance is routed through `denseMkBytePair_iff_singles` (the dense mirror of
  `mkBytePair_iff_singles`, `BytePack.lean:93`) so the merge key (chunk BP-P2) reuses
  `denseMkByteCheck_accepted` rather than re-deriving pair acceptance inline.
* `DenseExpr.normalize`/`DenseExpr.normalize_eval` (`Normalize.lean`) and
  `DenseExpr.constValue?`/`DenseExpr.constValue?_sound` (`DomainBatchProof.lean`) discharge
  `denseIsByteCompl_sound` exactly as `Expression`'s do for `isByteCompl_sound`.
* `ByteXorSpec.decode`/`encode` are payload-polymorphic (`{α : Type} → …`), so `spec.decode_map`
  applies to a dense payload mapped through `.eval` identically to the `Expression` case — this
  is the whole content of `denseByteXorSpec_decode_iff`/`denseByteBoolSound_decode_iff`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Emitted pair byte checks (`denseMkBytePair_*`, native mirrors of the `mkBytePair_*` lemmas) -/

/-- The evaluation of an emitted pair byte check. Native mirror of `mkBytePair_eval`
    (`BytePack.lean:35`). -/
theorem denseMkBytePair_eval (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p)
    (denv : VarId → ZMod p) :
    denseBIEval (denseMkBytePair spec busId e₁ e₂) denv
      = { busId := busId, multiplicity := 1,
          payload := spec.encode spec.pairOp (e₁.eval denv) (e₂.eval denv) 0 } := by
  simp only [denseMkBytePair, denseBIEval, spec.encode_map, DenseExpr.eval]

/-- An emitted pair byte check breaks no invariant. Native mirror of `mkBytePair_breaks`
    (`BytePack.lean:56`). -/
theorem denseMkBytePair_breaks (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : DenseExpr p) (denv : VarId → ZMod p) :
    bs.breaksInvariant (denseBIEval (denseMkBytePair spec busId e₁ e₂) denv) = false := by
  obtain ⟨_, hbreak, _⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkBytePair_eval]; exact hbreak _

/-- A pair byte check is accepted exactly when both operands are bytes. Native mirror of
    `mkBytePair_accepted` (`BytePack.lean:81`). -/
theorem denseMkBytePair_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : DenseExpr p) (denv : VarId → ZMod p) :
    bs.violatesConstraint (denseBIEval (denseMkBytePair spec busId e₁ e₂) denv) = false
      ↔ (e₁.eval denv).val < spec.bound ∧ (e₂.eval denv).val < spec.bound := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkBytePair_eval]
  have hdec : spec.decode (spec.encode spec.pairOp (e₁.eval denv) (e₂.eval denv) 0)
      = some (spec.pairOp, e₁.eval denv, e₂.eval denv, (0 : ZMod p)) := spec.decode_encode _ _ _ _
  rw [(hsound _ spec.pairOp _ _ 0 1 hdec).2 rfl]; simp

/-- A pair byte check is accepted exactly when both single-value checks are — the pack/split law.
    Native mirror of `mkBytePair_iff_singles` (`BytePack.lean:93`). -/
theorem denseMkBytePair_iff_singles (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : DenseExpr p) (denv : VarId → ZMod p) :
    bs.violatesConstraint (denseBIEval (denseMkBytePair spec busId e₁ e₂) denv) = false
      ↔ bs.violatesConstraint (denseBIEval (denseMkByteCheck spec busId e₁) denv) = false
        ∧ bs.violatesConstraint (denseBIEval (denseMkByteCheck spec busId e₂) denv) = false := by
  rw [denseMkBytePair_accepted bs facts spec busId hspec,
      denseMkByteCheck_accepted bs facts spec busId hspec,
      denseMkByteCheck_accepted bs facts spec busId hspec]

/-- The two operands of an emitted pair check are payload entries. Native mirror of
    `mkBytePair_operand_mem` (`BytePack.lean:165`). -/
theorem denseMkBytePair_operand_mem (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p) :
    e₁ ∈ (denseMkBytePair spec busId e₁ e₂).payload
      ∧ e₂ ∈ (denseMkBytePair spec busId e₁ e₂).payload := by
  have h := spec.decode_mem (denseMkBytePair spec busId e₁ e₂).payload
    (.const spec.pairOp) e₁ e₂ (.const 0) (spec.decode_encode _ _ _ _)
  exact ⟨h.1, h.2.1⟩

/-- An emitted pair check introduces no variable beyond its operands'. Native mirror of
    `mkBytePair_payload_vars` (`BytePack.lean:172`). -/
theorem denseMkBytePair_payload_vars (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p)
    {x : VarId} (pe : DenseExpr p) (hpe : pe ∈ (denseMkBytePair spec busId e₁ e₂).payload)
    (hx : x ∈ pe.vars) : x ∈ e₁.vars ∨ x ∈ e₂.vars := by
  simp only [denseMkBytePair] at hpe
  rcases spec.encode_mem _ _ _ _ pe hpe with h | h | h | h <;> rw [h] at hx
  · simp only [DenseExpr.vars, List.not_mem_nil] at hx
  · exact Or.inl hx
  · exact Or.inr hx
  · simp only [DenseExpr.vars, List.not_mem_nil] at hx

/-! ## Decoded-field acceptance characterizations (dense mirrors of `byte*_decode_iff`) -/

/-- Lift `byteXorSpec_sound` to a *symbolic* dense interaction whose payload decodes to
    `(op, o₁, o₂, r)`: acceptance of `denseBIEval bi denv` is characterized by the decoded fields'
    evaluations. Native mirror of `byteXorSpec_decode_iff` (`BytePack.lean:107`). -/
theorem denseByteXorSpec_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (op.eval denv = spec.xorOp →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound
            ∧ (r.eval denv).val = Nat.xor (o1.eval denv).val (o2.eval denv).val)) ∧
    (op.eval denv = spec.pairOp →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧ r.eval denv = 0)) := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
  have hdecEv : spec.decode (denseBIEval bi denv).payload
      = some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]; rfl
  exact hsound (denseBIEval bi denv).payload (op.eval denv) (o1.eval denv) (o2.eval denv)
    (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

/-- The `byteBoolSound` analog of `denseByteXorSpec_decode_iff`. Native mirror of
    `byteBoolSound_decode_iff` (`BytePack.lean:130`). -/
theorem denseByteBoolSound_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (∀ oop, spec.orOp = some oop → op.eval denv = oop →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound
            ∧ (r.eval denv).val = Nat.lor (o1.eval denv).val (o2.eval denv).val)) ∧
    (∀ aop, spec.andOp = some aop → op.eval denv = aop →
        (bs.violatesConstraint (denseBIEval bi denv) = false ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound
            ∧ (r.eval denv).val = Nat.land (o1.eval denv).val (o2.eval denv).val)) := by
  have hdecEv : spec.decode (denseBIEval bi denv).payload
      = some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]; rfl
  exact facts.byteBoolSound bi.busId spec hspec (denseBIEval bi denv).payload (op.eval denv)
    (o1.eval denv) (o2.eval denv) (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

/-! ## The NOT-form complement recognizer -/

/-- `255 − a` with no wraparound is the byte complement, hence `a`'s XOR with `255`. Copy of the
    spec's `val_255_sub` (`OldVariableBased/ByteCheckPack.lean:96`). -/
private theorem val_255_sub (hp : 256 ≤ p) (a : ZMod p) (ha : a.val < 256) :
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

/-- `(255 : ZMod p).val = 255` when `256 ≤ p`. Copy of the spec's `val_255`
    (`OldVariableBased/ByteCheckPack.lean:110`). -/
private theorem val_255 (hp : 256 ≤ p) : (255 : ZMod p).val = 255 := by
  have hc : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  rw [← hc, ZMod.val_natCast_of_lt (by omega)]

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment. Native mirror of
    `isByteCompl_sound` (`OldVariableBased/ByteCheckPack.lean:45`). -/
theorem denseIsByteCompl_sound (a b : DenseExpr p) (h : denseIsByteCompl a b = true)
    (denv : VarId → ZMod p) : b.eval denv = 255 - a.eval denv := by
  unfold denseIsByteCompl at h
  have hc : (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).normalize.constValue?
      = some 0 := by simpa using h
  have h0 : (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).eval denv = 0 := by
    have := DenseExpr.constValue?_sound _ (0 : ZMod p) hc denv
    rwa [DenseExpr.normalize_eval] at this
  simp only [denseComplExpr, DenseExpr.eval] at h0
  linear_combination h0

/-! ## Membership helper -/

/-- A variable of a payload expression is a variable of the dense interaction. Native mirror of
    `mem_biVars_of_payload` (`OldVariableBased/ByteCheckPack.lean:90`). -/
theorem denseMem_biVars_of_payload (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (he : e ∈ bi.payload) {v : VarId} (hv : v ∈ e.vars) : v ∈ denseBIVars bi := by
  rw [denseBIVars, List.mem_append]
  exact Or.inr (List.mem_flatMap.2 ⟨e, he, hv⟩)

/-! ## The single-value byte-check recognizer is sound -/

/-- A recognized single-value byte check is stateless, has multiplicity 1, its value is a payload
    entry, and its acceptance is exactly "the value is a byte". Native mirror of `svCheck?_sound`
    (`OldVariableBased/ByteCheckPack.lean:116`), same 7 branches. -/
theorem denseSvCheck?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (h : denseSvCheck? bs facts bi = some e) :
    bs.isStateful bi.busId = false ∧ bi.multiplicity = DenseExpr.const 1 ∧ e ∈ bi.payload ∧
      (∀ denv, bs.violatesConstraint (denseBIEval bi denv) = false ↔ (e.eval denv).val < 256) := by
  unfold denseSvCheck? at h
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
        have key := denseByteXorSpec_decode_iff bs facts spec bi hspec op o1 o2 r hdec
        split_ifs at h with hmo hA hB hC hD hE hor hOA hOB
        · -- self-check: o₁ = o₂, r = 0
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨he12, hr0⟩ := hA
          obtain rfl : o1 = e := by simpa using h
          refine ⟨hstateless, hm, hmemO1, fun denv => ?_⟩
          have hopEv : op.eval denv = spec.xorOp := by rw [hop]; rfl
          rw [(key denv).1 hopEv, hbound]
          refine ⟨fun hh => hh.1, fun hh => ⟨hh, he12 ▸ hh, ?_⟩⟩
          rw [show r.eval denv = 0 by rw [hr0]; rfl, ZMod.val_zero, ← he12]
          exact (Nat.xor_self _).symm
        · -- XOR-with-zero: o₂ = 0, o₁ = r
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hz, heq⟩ := hB
          obtain rfl : o1 = e := by simpa using h
          refine ⟨hstateless, hm, hmemO1, fun denv => ?_⟩
          have hopEv : op.eval denv = spec.xorOp := by rw [hop]; rfl
          rw [(key denv).1 hopEv, hbound]
          refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_, ?_⟩⟩
          · rw [show o2.eval denv = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
          · rw [show r.eval denv = o1.eval denv by rw [heq], show o2.eval denv = 0 by rw [hz]; rfl,
              ZMod.val_zero]
            exact (Nat.xor_zero _).symm
        · -- mirror XOR-with-zero: o₁ = 0, o₂ = r
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hz, heq⟩ := hC
          obtain rfl : o2 = e := by simpa using h
          refine ⟨hstateless, hm, hmemO2, fun denv => ?_⟩
          have hopEv : op.eval denv = spec.xorOp := by rw [hop]; rfl
          rw [(key denv).1 hopEv, hbound]
          refine ⟨fun hh => hh.2.1, fun hh => ⟨?_, hh, ?_⟩⟩
          · rw [show o1.eval denv = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
          · rw [show r.eval denv = o2.eval denv by rw [heq], show o1.eval denv = 0 by rw [hz]; rfl,
              ZMod.val_zero]
            exact (Nat.zero_xor _).symm
        · -- NOT-form: o₂ = 255, r = 255 − o₁
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hpp, hz, hcompl⟩ := hD
          obtain rfl : o1 = e := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hpp
          refine ⟨hstateless, hm, hmemO1, fun denv => ?_⟩
          have hopEv : op.eval denv = spec.xorOp := by rw [hop]; rfl
          have ho2 : o2.eval denv = 255 := by rw [hz]; rfl
          have hr : r.eval denv = 255 - o1.eval denv := denseIsByteCompl_sound o1 r hcompl denv
          rw [(key denv).1 hopEv, hbound]
          refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_, ?_⟩⟩
          · rw [ho2, val_255 hple]; omega
          · rw [hr, ho2, val_255 hple, val_255_sub hple _ hh]
        · -- mirror NOT-form: o₁ = 255, r = 255 − o₂
          obtain ⟨hm, hop⟩ := hmo; obtain ⟨hpp, hz, hcompl⟩ := hE
          obtain rfl : o2 = e := by simpa using h
          have hple : 256 ≤ p := of_decide_eq_true hpp
          refine ⟨hstateless, hm, hmemO2, fun denv => ?_⟩
          have hopEv : op.eval denv = spec.xorOp := by rw [hop]; rfl
          have ho1 : o1.eval denv = 255 := by rw [hz]; rfl
          have hr : r.eval denv = 255 - o2.eval denv := denseIsByteCompl_sound o2 r hcompl denv
          rw [(key denv).1 hopEv, hbound]
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
            refine ⟨hstateless, hm, hmemO1, fun denv => ?_⟩
            have hopEv : op.eval denv = oop := by rw [horAny]; rfl
            have keyOr := (denseByteBoolSound_decode_iff bs facts spec bi hspec op o1 o2 r hdec denv).1
              oop hoo hopEv
            rw [keyOr, hbound]
            refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_, ?_⟩⟩
            · rw [show o2.eval denv = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
            · rw [show r.eval denv = o1.eval denv by rw [heq],
                show o2.eval denv = 0 by rw [hz]; rfl, ZMod.val_zero]
              simp
        · -- mirror OR identity: o₁ = 0, o₂ = r
          obtain ⟨hm, horAny⟩ := hor; obtain ⟨hz, heq⟩ := hOB
          obtain rfl : o2 = e := by simpa using h
          cases hoo : spec.orOp with
          | none => rw [hoo] at horAny; simp [Option.any] at horAny
          | some oop =>
            rw [hoo] at horAny
            simp only [Option.any, beq_iff_eq] at horAny
            refine ⟨hstateless, hm, hmemO2, fun denv => ?_⟩
            have hopEv : op.eval denv = oop := by rw [horAny]; rfl
            have keyOr := (denseByteBoolSound_decode_iff bs facts spec bi hspec op o1 o2 r hdec denv).1
              oop hoo hopEv
            rw [keyOr, hbound]
            refine ⟨fun hh => hh.2.1, fun hh => ⟨?_, hh, ?_⟩⟩
            · rw [show o1.eval denv = 0 by rw [hz]; rfl, ZMod.val_zero]; omega
            · rw [show r.eval denv = o2.eval denv by rw [heq],
                show o1.eval denv = 0 by rw [hz]; rfl, ZMod.val_zero]
              simp
    · exact absurd h (by simp)

/-- If `denseFindSecond` returns `(mid, b, eB, post)` then `b` is a recognized single-value byte
    check with value `eB`. Native mirror of `findSecond_sound`
    (`OldVariableBased/ByteCheckPack.lean:244`). -/
theorem denseFindSecond_sound (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat) :
    ∀ (revMid rest : List (BusInteraction (DenseExpr p)))
      (mid : List (BusInteraction (DenseExpr p))) (b : BusInteraction (DenseExpr p))
      (eB : DenseExpr p) (post : List (BusInteraction (DenseExpr p))),
      denseFindSecond bs facts busId revMid rest = some (mid, b, eB, post) →
      denseSvCheck? bs facts b = some eB := by
  intro revMid rest
  induction rest generalizing revMid with
  | nil => intro _ _ _ _ h; exact absurd h (by simp [denseFindSecond])
  | cons c cs ih =>
    intro mid b eB post h
    rw [denseFindSecond] at h
    cases hc : denseSvCheck? bs facts c with
    | none => rw [hc] at h; exact ih (c :: revMid) mid b eB post h
    | some eC =>
      rw [hc] at h
      split_ifs at h with hbus
      · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hcb, hceb, _⟩ := h
        rw [← hcb, ← hceb]; exact hc
      · exact ih (c :: revMid) mid b eB post h

end ApcOptimizer.Dense
