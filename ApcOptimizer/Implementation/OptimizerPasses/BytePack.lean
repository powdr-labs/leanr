import ApcOptimizer.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false

/-! # VM-neutral byte-check builders

On a byte-lookup bus a single value is byte-range-checked by a self-XOR message (op `= xorOp`,
`e ⊕ e = 0`, forcing `e` to be a byte), and two such checks pack into one pair check (op `= pairOp`,
range-check both operands as bytes). Rather than hard-wire a VM's slot layout, the builders below
produce these messages through a `ByteXorSpec` (`spec.encode`), so a pass can emit a byte check
without knowing the layout — for OpenVM `mkByteCheck` is `[e, e, 0, 1]` and `mkBytePair` is
`[e₁, e₂, 0, 0]` definitionally. All soundness flows from `BusFacts.byteXorSpec_sound`. -/

variable {p : ℕ}

/-- Single-value byte check on `e`, emitted through `spec` (multiplicity `1`). -/
def mkByteCheck (spec : ByteXorSpec p) (busId : Nat) (e : Expression p) :
    BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.xorOp) e e (.const 0) }

/-- Packed pair byte check on `(e₁, e₂)`, emitted through `spec` (multiplicity `1`). -/
def mkBytePair (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : Expression p) :
    BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.pairOp) e₁ e₂ (.const 0) }

theorem mkByteCheck_eval (spec : ByteXorSpec p) (busId : Nat) (e : Expression p)
    (env : Variable → ZMod p) :
    (mkByteCheck spec busId e).eval env
      = { busId := busId, multiplicity := 1,
          payload := spec.encode spec.xorOp (e.eval env) (e.eval env) 0 } := by
  simp only [mkByteCheck, BusInteraction.eval, spec.encode_map, Expression.eval]

theorem mkBytePair_eval (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : Expression p)
    (env : Variable → ZMod p) :
    (mkBytePair spec busId e₁ e₂).eval env
      = { busId := busId, multiplicity := 1,
          payload := spec.encode spec.pairOp (e₁.eval env) (e₂.eval env) 0 } := by
  simp only [mkBytePair, BusInteraction.eval, spec.encode_map, Expression.eval]

/-- A byte check lives on a stateless bus. -/
theorem mkByteCheck_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec) :
    bs.isStateful busId = false := (facts.byteXorSpec_sound busId spec hspec).1

/-- An emitted single-value byte check breaks no invariant. -/
theorem mkByteCheck_breaks (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e : Expression p) (env : Variable → ZMod p) :
    bs.breaksInvariant ((mkByteCheck spec busId e).eval env) = false := by
  obtain ⟨_, hbreak, _⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [mkByteCheck_eval]; exact hbreak _

/-- An emitted pair byte check breaks no invariant. -/
theorem mkBytePair_breaks (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : Expression p) (env : Variable → ZMod p) :
    bs.breaksInvariant ((mkBytePair spec busId e₁ e₂).eval env) = false := by
  obtain ⟨_, hbreak, _⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [mkBytePair_eval]; exact hbreak _

/-- A single-value byte check is accepted exactly when its operand is a byte. -/
theorem mkByteCheck_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e : Expression p) (env : Variable → ZMod p) :
    bs.violatesConstraint ((mkByteCheck spec busId e).eval env) = false
      ↔ (e.eval env).val < spec.bound := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [mkByteCheck_eval]
  have hdec : spec.decode (spec.encode spec.xorOp (e.eval env) (e.eval env) 0)
      = some (spec.xorOp, e.eval env, e.eval env, (0 : ZMod p)) := spec.decode_encode _ _ _ _
  rw [(hsound _ spec.xorOp _ _ 0 1 hdec).1 rfl]
  have hx : (0 : ZMod p).val = Nat.xor (e.eval env).val (e.eval env).val := by
    rw [ZMod.val_zero]; exact (Nat.xor_self _).symm
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, h, hx⟩

/-- A pair byte check is accepted exactly when both operands are bytes. -/
theorem mkBytePair_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : Expression p) (env : Variable → ZMod p) :
    bs.violatesConstraint ((mkBytePair spec busId e₁ e₂).eval env) = false
      ↔ (e₁.eval env).val < spec.bound ∧ (e₂.eval env).val < spec.bound := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [mkBytePair_eval]
  have hdec : spec.decode (spec.encode spec.pairOp (e₁.eval env) (e₂.eval env) 0)
      = some (spec.pairOp, e₁.eval env, e₂.eval env, (0 : ZMod p)) := spec.decode_encode _ _ _ _
  rw [(hsound _ spec.pairOp _ _ 0 1 hdec).2 rfl]; simp

/-- A pair byte check is accepted exactly when both single-value checks are — the pack/split law. -/
theorem mkBytePair_iff_singles (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : Expression p) (env : Variable → ZMod p) :
    bs.violatesConstraint ((mkBytePair spec busId e₁ e₂).eval env) = false
      ↔ bs.violatesConstraint ((mkByteCheck spec busId e₁).eval env) = false
        ∧ bs.violatesConstraint ((mkByteCheck spec busId e₂).eval env) = false := by
  rw [mkBytePair_accepted bs facts spec busId hspec,
      mkByteCheck_accepted bs facts spec busId hspec,
      mkByteCheck_accepted bs facts spec busId hspec]

/-- Lift `byteXorSpec_sound` to a *symbolic* interaction whose payload decodes to `(op, o₁, o₂, r)`:
    acceptance of `bi.eval env` is characterized by the decoded fields' evaluations. This is the
    form the byte-check recognizers consume — they match `spec.decode` on the `Expression` payload,
    then read off the operand values. -/
theorem byteXorSpec_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (Expression p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : Expression p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (env : Variable → ZMod p) :
    (op.eval env = spec.xorOp →
        (bs.violatesConstraint (bi.eval env) = false ↔
          (o1.eval env).val < spec.bound ∧ (o2.eval env).val < spec.bound
            ∧ (r.eval env).val = Nat.xor (o1.eval env).val (o2.eval env).val)) ∧
    (op.eval env = spec.pairOp →
        (bs.violatesConstraint (bi.eval env) = false ↔
          (o1.eval env).val < spec.bound ∧ (o2.eval env).val < spec.bound ∧ r.eval env = 0)) := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
  have hdecEv : spec.decode (bi.eval env).payload
      = some (op.eval env, o1.eval env, o2.eval env, r.eval env) := by
    show spec.decode (bi.payload.map (fun e => e.eval env)) = _
    rw [spec.decode_map, hdec]; rfl
  exact hsound (bi.eval env).payload (op.eval env) (o1.eval env) (o2.eval env)
    (r.eval env) (bi.eval env).multiplicity hdecEv

/-- An emitted byte check introduces no variable beyond its operand's. -/
theorem mkByteCheck_payload_vars (spec : ByteXorSpec p) (busId : Nat) (e : Expression p)
    {x : Variable} (pe : Expression p) (hpe : pe ∈ (mkByteCheck spec busId e).payload)
    (hx : x ∈ pe.vars) : x ∈ e.vars := by
  simp only [mkByteCheck] at hpe
  rcases spec.encode_mem _ _ _ _ pe hpe with h | h | h | h <;> rw [h] at hx <;>
    first | exact hx | (simp only [Expression.vars, List.not_mem_nil] at hx)

/-- The operand of an emitted single-value byte check is a payload entry. -/
theorem mkByteCheck_operand_mem (spec : ByteXorSpec p) (busId : Nat) (e : Expression p) :
    e ∈ (mkByteCheck spec busId e).payload :=
  (spec.decode_mem (mkByteCheck spec busId e).payload
    (.const spec.xorOp) e e (.const 0) (spec.decode_encode _ _ _ _)).1

/-- The two operands of an emitted pair check are payload entries. -/
theorem mkBytePair_operand_mem (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : Expression p) :
    e₁ ∈ (mkBytePair spec busId e₁ e₂).payload ∧ e₂ ∈ (mkBytePair spec busId e₁ e₂).payload := by
  have h := spec.decode_mem (mkBytePair spec busId e₁ e₂).payload
    (.const spec.pairOp) e₁ e₂ (.const 0) (spec.decode_encode _ _ _ _)
  exact ⟨h.1, h.2.1⟩

/-- An emitted pair check introduces no variable beyond its operands'. -/
theorem mkBytePair_payload_vars (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : Expression p)
    {x : Variable} (pe : Expression p) (hpe : pe ∈ (mkBytePair spec busId e₁ e₂).payload)
    (hx : x ∈ pe.vars) : x ∈ e₁.vars ∨ x ∈ e₂.vars := by
  simp only [mkBytePair] at hpe
  rcases spec.encode_mem _ _ _ _ pe hpe with h | h | h | h <;> rw [h] at hx
  · simp only [Expression.vars, List.not_mem_nil] at hx
  · exact Or.inl hx
  · exact Or.inr hx
  · simp only [Expression.vars, List.not_mem_nil] at hx
