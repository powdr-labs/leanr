import ApcOptimizer.Implementation.BusFacts
import ApcOptimizer.Implementation.MemoryBusDrop
import ApcOptimizer.Sp1Semantics

set_option autoImplicit false

/-!
# Proven bus facts for the SP1 semantics

The `BusFacts` instance for `sp1BusSemantics` (see `ApcOptimizer/Implementation/BusFacts.lean` for
the design). The memory discipline is direction-parametric (`MemoryBusShape.direction`), so SP1's
reverse memory convention (`setNewMult = -1`) and its execution bridge (`setNewMult = 1`) reuse the
same machinery. Every claim is proven against the concrete `violates`, so none needs auditing.
Parameterized by the bus map (defaulting to `defaultBusMap`).
-/

namespace ApcOptimizer.SP1

variable {p : ℕ}

private def neverViolatesImpl (busMap : Nat → Option Sp1BusType) (busId : Nat) : Bool :=
  match busMap busId with
  | some .executionBridge => true
  | _ => false

private def slotFunImpl (busMap : Nat → Option Sp1BusType) (busId : Nat)
    (pattern : List (Option (ZMod p))) (outSlot : Nat) :
    Option (List (ZMod p) → ZMod p) :=
  match busMap busId, pattern, outSlot with
  -- Byte bus XOR (op 2): the result `a` (slot 1) is `b ^ c` (slots 2, 3).
  | some .byteLookup, [some op, _, _, _], 1 =>
      if op.val = 2 then
        some (fun payload =>
          match payload with
          | [_, _, b, c] => ((Nat.xor b.val c.val : Nat) : ZMod p)
          | _ => 0)
      else none
  | _, _, _ => none

private def slotBoundImpl (busMap : Nat → Option Sp1BusType) (busId : Nat) (mult : ZMod p)
    (pattern : List (Option (ZMod p))) (slot : Nat) : Option Nat :=
  match busMap busId, slot with
  -- The byte bus operands `b` (slot 2) and `c` (slot 3) are always bytes.
  | some .byteLookup, 2 => some 256
  | some .byteLookup, 3 => some 256
  -- An op-6 (`Range`) byte-bus message `[6, a, b, 0]` range-checks its result `a` (slot 1) to
  -- `a < 2^b`; with op (slot 0) and width `b` (slot 2) constant in the pattern, that bounds slot 1
  -- by `2^b`.
  | some .byteLookup, 1 =>
    match pattern[0]? with
    | some (some op) =>
      -- Non-range byte ops (`op ≤ 5`) return a byte; op-6 (`Range`) returns `< 2^w` (needs `w`).
      if op.val ≤ 5 then some 256
      else match pattern[2]? with
        | some (some w) => if op.val = 6 then some (2 ^ w.val) else none
        | _ => none
    | _ => none
  -- The four data limbs (slots 5–8) of a memory `getPrevious` (multiplicity `1`, ≥9-slot record)
  -- are 16-bit.
  | some .memory, 5 => if mult = 1 ∧ 9 ≤ pattern.length then some (2 ^ 16) else none
  | some .memory, 6 => if mult = 1 ∧ 9 ≤ pattern.length then some (2 ^ 16) else none
  | some .memory, 7 => if mult = 1 ∧ 9 ≤ pattern.length then some (2 ^ 16) else none
  | some .memory, 8 => if mult = 1 ∧ 9 ≤ pattern.length then some (2 ^ 16) else none
  | _, _ => none

private theorem payload_four {payload : List (ZMod p)} {p0 p1 p2 p3 : Option (ZMod p)}
    (h : Matches payload [p0, p1, p2, p3]) :
    ∃ a b c d, payload = [a, b, c, d] := by
  obtain ⟨hlen, _⟩ := h
  match payload, hlen with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- Every accepted byte-bus message is a 4-tuple `[op, a, b, c]` with byte operands `b`, `c`. -/
private theorem byte_operands (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .byteLookup)
    (hok : violates busMap m = false) :
    ∃ op a b c, m.payload = [op, a, b, c] ∧ b.val < 256 ∧ c.val < 256 := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus ⊢
  unfold violates at hok
  rw [hbus] at hok
  rcases payload with _ | ⟨op, _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩⟩ <;>
    dsimp only at hok
  · exact absurd hok (by simp)
  · exact absurd hok (by simp)
  · exact absurd hok (by simp)
  · exact absurd hok (by simp)
  · refine ⟨op, a, b, c, rfl, ?_, ?_⟩ <;>
      (split at hok <;>
        first
          | (simp only [isByte, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hok
             obtain ⟨⟨hb, hc⟩, _⟩ := hok
             omega)
          | simp_all)
  · exact absurd hok (by simp)

/-- An accepted op-6 (`Range`) byte-bus message `[6, a, b, c]` range-checks `a` to `a < 2^b`. -/
private theorem byte_op6_bound (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .byteLookup)
    (hok : violates busMap m = false)
    (op a b c : ZMod p) (hpay : m.payload = [op, a, b, c]) (hop : op.val = 6) :
    a.val < 2 ^ b.val := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hpay
  subst hpay
  unfold violates at hok
  rw [hbus] at hok
  dsimp only at hok
  simp only [hop] at hok
  rw [Bool.not_eq_false', Bool.and_eq_true] at hok
  exact of_decide_eq_true hok.2

/-- An accepted byte-bus message `[op, a, b, c]` with a non-range op (`op ≤ 5`) has a byte result
    `a < 256` (AND/OR/XOR of bytes, U8Range `a = 0`, LTU/MSB a bit). -/
private theorem byte_result_lt256 (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .byteLookup)
    (hok : violates busMap m = false)
    (op a b c : ZMod p) (hpay : m.payload = [op, a, b, c]) (hop : op.val ≤ 5) :
    a.val < 256 := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hpay
  subst hpay
  unfold violates at hok
  rw [hbus] at hok
  dsimp only at hok
  rcases (show op.val = 0 ∨ op.val = 1 ∨ op.val = 2 ∨ op.val = 3 ∨ op.val = 4 ∨ op.val = 5 by omega)
    with h | h | h | h | h | h
  · rw [h] at hok
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, isByte] at hok
    obtain ⟨⟨hb, _⟩, ha⟩ := hok
    rw [ha]; exact lt_of_le_of_lt Nat.and_le_left hb
  · rw [h] at hok
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, isByte] at hok
    obtain ⟨⟨hb, hc⟩, ha⟩ := hok
    rw [ha]; exact Nat.or_lt_two_pow (n := 8) hb hc
  · rw [h] at hok
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, isByte] at hok
    obtain ⟨⟨hb, hc⟩, ha⟩ := hok
    rw [ha]; exact Nat.xor_lt_two_pow (n := 8) hb hc
  · rw [h] at hok
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, isByte] at hok
    obtain ⟨_, ha⟩ := hok
    rw [ha]; omega
  · rw [h] at hok
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, isByte] at hok
    obtain ⟨_, ha⟩ := hok
    rw [ha]; split <;> omega
  · rw [h] at hok
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, isByte] at hok
    obtain ⟨⟨hb, _⟩, ha⟩ := hok
    rw [ha, Nat.shiftRight_eq_div_pow]
    have h128 : (2 : ℕ) ^ 7 = 128 := rfl
    rw [h128]; omega

/-- An op-6 `[6, a, b, c]` message with supported width (`b ≤ 16`) and `c = 0` is accepted iff
    `a < 2^b`. -/
private theorem byte_op6_iff (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .byteLookup)
    (op a b c : ZMod p) (hpay : m.payload = [op, a, b, c]) (hop : op.val = 6)
    (hw : b.val ≤ 16) (hc : c.val = 0) :
    violates busMap m = false ↔ a.val < 2 ^ b.val := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hpay
  subst hpay
  unfold violates
  rw [hbus]
  dsimp only
  simp only [hop, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨⟨hw, hc⟩, h⟩

/-- SP1's op-6 (`Range`) byte-bus check as a single-value range check: `[6, _, w, 0]` with `w ≤ 16`
    is accepted iff its result (slot 1) is `< 2^w`. -/
private def rangeCheckAtImpl (busMap : Nat → Option Sp1BusType) (busId : Nat)
    (pattern : List (Option (ZMod p))) : Option (Nat × Nat) :=
  match busMap busId, pattern with
  | some .byteLookup, [some op, _, some w, some c] =>
    if op.val = 6 ∧ w.val ≤ 16 ∧ c.val = 0 then some (1, 2 ^ w.val) else none
  | _, _ => none

/-- The fixed-zero cell of the SP1 memory bus: `x0` = address `(0, 0, 0)` at slots 2–4, data limbs
    at slots 5–8; `none` for non-memory buses. -/
private def zeroCellImpl (busMap : Nat → Option Sp1BusType) (busId : Nat) :
    Option (List (Nat × ZMod p) × List Nat) :=
  match busMap busId with
  | some .memory => some ([(2, 0), (3, 0), (4, 0)], [5, 6, 7, 8])
  | _ => none

/-- Byte-slot obligation for an SP1 memory-style pair cancellation: 16-bit data limbs (bound
    `2^16`) at slots 5–8. The execution bridge never violates; other buses claim nothing. -/
private def recvByteSlotsImpl (busMap : Nat → Option Sp1BusType) (busId : Nat)
    (_pattern : List (Option (ZMod p))) : Option (List Nat × Nat) :=
  match busMap busId with
  | some .memory => some ([5, 6, 7, 8], 2 ^ 16)
  | some .executionBridge => some ([], 256)
  | _ => none

/-- SP1 byte-bus payload `[op, a, b, c]` decodes to logical `(op, b, c, a)` (result `a` in slot 1,
    operands `b`, `c` in slots 2, 3). -/
def sp1ByteDecode {α : Type} : List α → Option (α × α × α × α)
  | [op, a, b, c] => some (op, b, c, a)
  | _ => none

theorem sp1ByteDecode_some {α : Type} {pl : List α} {o p1 p2 res : α} :
    sp1ByteDecode pl = some (o, p1, p2, res) ↔ pl = [o, res, p1, p2] := by
  constructor
  · intro h
    rcases pl with _ | ⟨w, _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨e, tl⟩⟩⟩⟩⟩ <;> simp_all [sp1ByteDecode]
  · intro h; subst h; rfl

theorem sp1ByteDecode_map {α β : Type} (f : α → β) (pl : List α) :
    sp1ByteDecode (pl.map f)
      = (sp1ByteDecode pl).map (fun t => (f t.1, f t.2.1, f t.2.2.1, f t.2.2.2)) := by
  rcases pl with _ | ⟨w, _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨e, tl⟩⟩⟩⟩⟩ <;> rfl

theorem sp1ByteDecode_mem {α : Type} (pl : List α) (op o1 o2 r : α)
    (h : sp1ByteDecode pl = some (op, o1, o2, r)) : o1 ∈ pl ∧ o2 ∈ pl ∧ r ∈ pl := by
  rw [sp1ByteDecode_some] at h; subst h; simp

/-- Emit an SP1 byte payload `[op, result, operand₁, operand₂]`, inverting `sp1ByteDecode`. -/
def sp1ByteEncode {α : Type} (op o1 o2 r : α) : List α := [op, r, o1, o2]

theorem sp1ByteDecode_encode {α : Type} (op o1 o2 r : α) :
    sp1ByteDecode (sp1ByteEncode op o1 o2 r) = some (op, o1, o2, r) := rfl

theorem sp1ByteDecode_eq_encode {α : Type} (pl : List α) (op o1 o2 r : α)
    (h : sp1ByteDecode pl = some (op, o1, o2, r)) : pl = sp1ByteEncode op o1 o2 r := by
  rw [sp1ByteDecode_some] at h; exact h

theorem sp1ByteEncode_map {α β : Type} (f : α → β) (op o1 o2 r : α) :
    (sp1ByteEncode op o1 o2 r).map f = sp1ByteEncode (f op) (f o1) (f o2) (f r) := rfl

theorem sp1ByteEncode_mem {α : Type} (op o1 o2 r x : α)
    (h : x ∈ sp1ByteEncode op o1 o2 r) : x = op ∨ x = o1 ∨ x = o2 ∨ x = r := by
  simp only [sp1ByteEncode, List.mem_cons, List.not_mem_nil, or_false] at h; tauto

/-- An execution-bridge message never violates. -/
private theorem execBridge_ok (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .executionBridge) :
    violates busMap m = false := by
  unfold violates
  rw [hbus]

/-- A bus with a declared last-write-wins shape (memory or execution bridge) is stateful. -/
theorem sp1_isStateful_of_memShape {p : ℕ} (busMap : Nat → Option Sp1BusType)
    (busId : Nat) (shape : MemoryBusShape) (h : memShapeOf busMap busId = some shape) :
    (sp1BusSemantics p busMap).isStateful busId = true := by
  show (match busMap busId with | some t => t.isStateful | none => false) = true
  unfold memShapeOf at h
  generalize busMap busId = o at h ⊢
  cases o with
  | none => simp at h
  | some t => cases t <;> simp_all [Sp1BusType.isStateful]

/-- The SP1 memory bus uses `direction := .sendThenReceive`, so its `setNewMult` reduces to `-1`
    (the reverse of OpenVM; the execution bridge instead uses `1`). -/
private theorem memShapeOf_memory_setNewMult {p : ℕ} (busMap : Nat → Option Sp1BusType)
    (busId : Nat) (shape : MemoryBusShape) (hbus : busMap busId = some .memory)
    (h : memShapeOf busMap busId = some shape) :
    (shape.setNewMult : ZMod p) = -1 := by
  unfold memShapeOf at h
  rw [hbus] at h
  obtain rfl := Option.some.inj h; rfl

/-- A memory message that is not a `getPrevious` (multiplicity ≠ 1) never violates. -/
private theorem memory_nonGetPrev_ok (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity ≠ 1) : violates busMap m = false := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hm
  unfold violates
  rw [hbus]
  rcases payload with _ | ⟨c0, _ | ⟨c1, _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2,
    _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [hm]

/-- A memory `getPrevious` (multiplicity 1) with 16-bit data limbs (slots 5–8) never violates. -/
private theorem memory_getPrev_ok (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = 1)
    (hslots : ∀ slot ∈ [5, 6, 7, 8], ∀ x : ZMod p, m.payload[slot]? = some x → x.val < 2 ^ 16) :
    violates busMap m = false := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hm hslots
  unfold violates
  rw [hbus]
  rcases payload with _ | ⟨c0, _ | ⟨c1, _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2,
    _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try rfl
  have h0 : d0.val < 65536 := hslots 5 (by simp) d0 rfl
  have h1 : d1.val < 65536 := hslots 6 (by simp) d1 rfl
  have h2 : d2.val < 65536 := hslots 7 (by simp) d2 rfl
  have h3 : d3.val < 65536 := hslots 8 (by simp) d3 rfl
  simp [is16Bit, hm, h0, h1, h2, h3]

/-- The four data limbs (slots 5–8) of an accepted memory `getPrevious` (multiplicity `1`, ≥9-slot
    record) are 16-bit (converse of `memory_getPrev_ok`). -/
private theorem memory_read_data (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = 1) (hok : violates busMap m = false) (hlen : 9 ≤ m.payload.length)
    (slot : Nat) (hs : slot = 5 ∨ slot = 6 ∨ slot = 7 ∨ slot = 8)
    (x : ZMod p) (hget : m.payload[slot]? = some x) : x.val < 2 ^ 16 := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hm hget hlen
  unfold violates at hok
  rw [hbus, hm] at hok
  rcases hs with rfl | rfl | rfl | rfl <;>
    (rcases payload with _ | ⟨c0, _ | ⟨c1, _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2,
      _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp_all [is16Bit, List.all_cons, List.all_nil])

/-- A memory `setNew` (multiplicity -1) never violates. -/
private theorem memory_setNew_ok [NeZero p] (busMap : Nat → Option Sp1BusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = -1) : violates busMap m = false := by
  by_cases hc : (1 : ZMod p) = -1
  · -- `p ∣ 2`: every value is `< 2 ≤ 2^16`, so the 16-bit test never fails.
    have hadd : (1 : ZMod p) + 1 = 0 := (congrArg (· + 1) hc).trans (neg_add_cancel 1)
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_ofNat, ← one_add_one_eq_two]; exact hadd
    have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
    have h16 : ∀ d : ZMod p, d.val < 65536 :=
      fun d => lt_of_lt_of_le (ZMod.val_lt d)
        (le_trans (Nat.le_of_dvd (by decide) hp2) (by decide))
    obtain ⟨bid, mult, payload⟩ := m
    simp only at hbus
    unfold violates
    rw [hbus]
    rcases payload with _ | ⟨c0, _ | ⟨c1, _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2,
      _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [is16Bit, h16]
  · exact memory_nonGetPrev_ok busMap m hbus (by rw [hm]; exact fun h => hc h.symm)

/-- The proven facts about `sp1BusSemantics`, for any bus map. -/
def sp1Facts (p : ℕ) [NeZero p]
    (busMap : Nat → Option Sp1BusType := defaultBusMap) :
    BusFacts p (sp1BusSemantics p busMap) :=
  { BusFacts.trivial (sp1BusSemantics p busMap) with
    slotBound := fun busId mult pattern slot => slotBoundImpl busMap busId mult pattern slot
    slotBound_sound := by
      intro m pattern slot bound x hfact hmatch hok hget
      have hok' : violates busMap m = false := hok
      unfold slotBoundImpl at hfact
      split at hfact
      · rename_i hbus
        simp only [Option.some.injEq] at hfact
        subst hfact
        obtain ⟨op, a, b, c, hpay, hb, hc⟩ := byte_operands busMap m hbus hok'
        have hxb : b = x := by rw [hpay] at hget; simpa using hget
        rw [← hxb]; exact hb
      · rename_i hbus
        simp only [Option.some.injEq] at hfact
        subst hfact
        obtain ⟨op, a, b, c, hpay, hb, hc⟩ := byte_operands busMap m hbus hok'
        have hxc : c = x := by rw [hpay] at hget; simpa using hget
        rw [← hxc]; exact hc
      · -- slot 1: a non-range byte op bounds its result `a` by `256`; op-6 by `2^w`.
        rename_i hbus
        obtain ⟨op, a, b, c, hpay, _, _⟩ := byte_operands busMap m hbus hok'
        have hax : a = x := by rw [hpay] at hget; simpa using hget
        rcases hp0 : pattern[0]? with _ | o0
        · rw [hp0] at hfact; simp at hfact
        · rcases o0 with _ | pop
          · rw [hp0] at hfact; simp at hfact
          · rw [hp0] at hfact
            dsimp only at hfact
            have hpop : op = pop := by
              have := hmatch.2 0 pop (by rw [hp0]); rw [hpay] at this; simpa using this
            by_cases hle : pop.val ≤ 5
            · rw [if_pos hle] at hfact
              simp only [Option.some.injEq] at hfact; subst hfact
              have hr := byte_result_lt256 busMap m hbus hok' op a b c hpay (by rw [hpop]; exact hle)
              rw [hax] at hr; exact hr
            · rw [if_neg hle] at hfact
              rcases hp2 : pattern[2]? with _ | o2
              · rw [hp2] at hfact; simp at hfact
              · rcases o2 with _ | pw
                · rw [hp2] at hfact; simp at hfact
                · rw [hp2] at hfact
                  dsimp only at hfact
                  split_ifs at hfact with hop6
                  · simp only [Option.some.injEq] at hfact; subst hfact
                    have hpw : b = pw := by
                      have := hmatch.2 2 pw (by rw [hp2]); rw [hpay] at this; simpa using this
                    have hb6 := byte_op6_bound busMap m hbus hok' op a b c hpay
                      (by rw [hpop]; exact hop6)
                    rw [hpw, hax] at hb6; exact hb6
      · -- memory data slot 5: a full-record read has 16-bit data
        rename_i hbus
        split_ifs at hfact with hm1
        obtain ⟨hm1', hlen⟩ := hm1
        simp only [Option.some.injEq] at hfact; subst hfact
        exact memory_read_data busMap m hbus hm1' hok' (by have h := hmatch.1; omega) 5
          (by tauto) x hget
      · -- memory data slot 6
        rename_i hbus
        split_ifs at hfact with hm1
        obtain ⟨hm1', hlen⟩ := hm1
        simp only [Option.some.injEq] at hfact; subst hfact
        exact memory_read_data busMap m hbus hm1' hok' (by have h := hmatch.1; omega) 6
          (by tauto) x hget
      · -- memory data slot 7
        rename_i hbus
        split_ifs at hfact with hm1
        obtain ⟨hm1', hlen⟩ := hm1
        simp only [Option.some.injEq] at hfact; subst hfact
        exact memory_read_data busMap m hbus hm1' hok' (by have h := hmatch.1; omega) 7
          (by tauto) x hget
      · -- memory data slot 8
        rename_i hbus
        split_ifs at hfact with hm1
        obtain ⟨hm1', hlen⟩ := hm1
        simp only [Option.some.injEq] at hfact; subst hfact
        exact memory_read_data busMap m hbus hm1' hok' (by have h := hmatch.1; omega) 8
          (by tauto) x hget
      · exact absurd hfact (by simp)
    slotFun := slotFunImpl busMap
    slotFun_sound := by
      intro m pattern outSlot f z hfact hmatch hok hget
      have hok' : violates busMap m = false := hok
      unfold slotFunImpl at hfact
      split at hfact
      · rename_i op w1 w2 w3 hbus
        split_ifs at hfact with hop
        simp only [Option.some.injEq] at hfact
        subst hfact
        obtain ⟨e0, e1, e2, e3, hpay⟩ := payload_four hmatch
        have h0 : e0 = op := by
          have := hmatch.2 0 op (by simp)
          rw [hpay] at this; simpa using this
        have hz : e1 = z := by rw [hpay] at hget; simpa using hget
        subst hz h0
        unfold violates at hok'
        rw [hbus, hpay] at hok'
        simp only [hop] at hok'
        rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
        have hxor : e1.val = Nat.xor e2.val e3.val := of_decide_eq_true hok'.2
        rw [hpay]
        show e1 = ((Nat.xor e2.val e3.val : Nat) : ZMod p)
        rw [← hxor]
        exact (ZMod.natCast_rightInverse e1).symm
      · exact absurd hfact (by simp)
    neverViolates := neverViolatesImpl busMap
    neverViolates_sound := by
      intro m h
      unfold neverViolatesImpl at h
      split at h
      · rename_i hbus; exact execBridge_ok busMap m hbus
      · exact absurd h (by simp)
    zeroCell := zeroCellImpl busMap
    zeroCell_sound := by
      intro msgs hadm busId addrReq dataSlots hfact m hm hbusId hmne haddr slot hslot v hget
      unfold zeroCellImpl at hfact
      split at hfact
      · rename_i hbus
        simp only [Option.some.injEq, Prod.mk.injEq] at hfact
        obtain ⟨rfl, rfl⟩ := hfact
        have hstateful : (sp1BusSemantics p busMap).isStateful m.busId = true := by
          show (match busMap m.busId with | some t => t.isStateful | none => false) = true
          rw [hbusId, hbus]; rfl
        have hmemBus : busMap m.busId = some .memory := by rw [hbusId]; exact hbus
        have hmfilt : m ∈ msgs.filter
            (fun m => decide (m.multiplicity ≠ 0) && (sp1BusSemantics p busMap).isStateful m.busId) := by
          rw [List.mem_filter]
          exact ⟨hm, by rw [hstateful, decide_eq_true hmne]; rfl⟩
        have h2 : m.payload[2]? = some 0 := haddr (2, 0) (by simp)
        have h3 : m.payload[3]? = some 0 := haddr (3, 0) (by simp)
        have h4 : m.payload[4]? = some 0 := haddr (4, 0) (by simp)
        have hz := hadm.2 m hmfilt hmemBus h2 h3 h4
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
        rcases hslot with rfl | rfl | rfl | rfl
        · rw [hget] at hz; exact Option.some.inj hz.1
        · rw [hget] at hz; exact Option.some.inj hz.2.1
        · rw [hget] at hz; exact Option.some.inj hz.2.2.1
        · rw [hget] at hz; exact Option.some.inj hz.2.2.2
      · exact absurd hfact (by simp)
    memShape := memShapeOf busMap
    memShape_stateful := fun busId shape hshape =>
      sp1_isStateful_of_memShape busMap busId shape hshape
    admissible_sound := by
      intro msgs hadm busId shape hshape
      have hstateful : (sp1BusSemantics p busMap).isStateful busId = true :=
        sp1_isStateful_of_memShape busMap busId shape hshape
      have hd := hadm.1 busId shape hshape
      have hlist : (msgs.filter (fun m => decide (m.multiplicity ≠ 0) &&
            (sp1BusSemantics p busMap).isStateful m.busId)).filter (fun m => m.busId = busId)
          = (msgs.filter (fun m => m.busId = busId)).filter
            (fun m => decide (m.multiplicity ≠ 0)) := by
        rw [List.filter_filter, List.filter_filter]
        apply List.filter_congr
        intro m _
        by_cases hb : m.busId = busId
        · rw [hb, hstateful]; simp
        · simp [hb]
      rwa [hlist] at hd
    admissible_dropPair := by
      intro hp1 busId shape hshape A B C S R hSbus hRbus _hSm _hRm haddrEq hcons hshield hadm_full
      obtain ⟨hdisc, hzero⟩ := hadm_full
      refine ⟨fun busId' shape' hshape' => ?_, ?_⟩
      · by_cases hbb : busId' = busId
        · subst busId'
          obtain rfl : shape = shape' := Option.some.inj (hshape.symm.trans hshape')
          have hgoal : (A ++ B ++ C).filter (fun m => m.busId = busId)
              = A.filter (fun m => m.busId = busId) ++ B.filter (fun m => m.busId = busId)
                ++ C.filter (fun m => m.busId = busId) := by
            simp only [List.filter_append]
          rw [hgoal]
          have hfull := hdisc busId shape hshape
          have hfiltFull : (A ++ S :: B ++ R :: C).filter (fun m => m.busId = busId)
              = A.filter (fun m => m.busId = busId) ++ S :: B.filter (fun m => m.busId = busId)
                ++ R :: C.filter (fun m => m.busId = busId) := by
            simp only [List.filter_append, List.filter_cons, hSbus, hRbus, decide_true, if_true]
          rw [hfiltFull] at hfull
          refine admissibleMemoryBus_dropPair shape hp1 _ _ _ S R hfull ?_ ?_ haddrEq
          · intro m hm hmne hmaddr
            rw [List.mem_filter] at hm
            exact hcons m hm.1 (of_decide_eq_true hm.2) hmne hmaddr
          · intro A₁' Sx A₂' hAsplit hSxne hSxaddr hSxmult
            obtain ⟨A₁, A₂, hAeq, _, hA₂filt⟩ :=
              filter_split (fun m => m.busId = busId) Sx A A₁' A₂' hAsplit
            have hSxbus : Sx.busId = busId := by
              have : Sx ∈ A.filter (fun m => m.busId = busId) := by
                rw [hAsplit]; exact List.mem_append_right A₁' (List.mem_cons_self ..)
              exact of_decide_eq_true (List.mem_filter.mp this).2
            obtain ⟨m, hmem, hmbus, hmne, hmaddr, hmmult⟩ :=
              hshield A₁ Sx A₂ hAeq hSxbus hSxne hSxaddr hSxmult
            refine ⟨m, ?_, hmne, hmaddr, hmmult⟩
            rw [← hA₂filt]; exact List.mem_filter.mpr ⟨hmem, by simp [hmbus]⟩
        · have hne : busId ≠ busId' := fun h => hbb h.symm
          have heq : (A ++ B ++ C).filter (fun m => m.busId = busId')
              = (A ++ S :: B ++ R :: C).filter (fun m => m.busId = busId') := by
            simp only [List.filter_append, List.filter_cons, hSbus, hRbus,
              decide_eq_false hne, Bool.false_eq_true, if_false]
          rw [heq]
          exact hdisc busId' shape' hshape'
      · intro m hm hbus hp2 hp3 hp4
        have hmem : m ∈ A ++ S :: B ++ R :: C := by
          rcases List.mem_append.mp hm with hAB | hC
          · rcases List.mem_append.mp hAB with hA | hB
            · exact List.mem_append_left _ (List.mem_append_left _ hA)
            · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ hB))
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hC)
        exact hzero m hmem hbus hp2 hp3 hp4
    -- SP1 memory limbs are 16-bit at slots 5–8; the execution bridge never violates.
    recvByteSlots := recvByteSlotsImpl busMap
    recvByteSlots_sound := by
      intro busId shape hmemshape pattern slots bound hfact m hbusId
      subst hbusId
      unfold recvByteSlotsImpl at hfact
      cases hbus : busMap m.busId with
      | none => rw [hbus] at hfact; simp at hfact
      | some bt =>
        cases bt with
        | executionBridge =>
          -- The execution bridge never violates at any multiplicity.
          rw [hbus] at hfact
          simp only [Option.some.injEq, Prod.mk.injEq] at hfact
          obtain ⟨rfl, rfl⟩ := hfact
          exact ⟨fun _ => execBridge_ok busMap m hbus, fun _ _ _ => execBridge_ok busMap m hbus⟩
        | memory =>
          have hw : (shape.setNewMult : ZMod p) = -1 :=
            memShapeOf_memory_setNewMult busMap m.busId shape hbus hmemshape
          simp only [hw, neg_neg]
          rw [hbus] at hfact
          simp only [Option.some.injEq, Prod.mk.injEq] at hfact
          obtain ⟨rfl, rfl⟩ := hfact
          exact ⟨fun hm => memory_setNew_ok busMap m hbus hm,
                 fun hm _ hbytes => memory_getPrev_ok busMap m hbus hm hbytes⟩
        | pcLookup => rw [hbus] at hfact; simp at hfact
        | byteLookup => rw [hbus] at hfact; simp at hfact
        | instructionFetch => rw [hbus] at hfact; simp at hfact
        | pageProt => rw [hbus] at hfact; simp at hfact
    -- SP1's byte bus `[op, a, b, c]`: XOR (op 2) sets `a = b ⊕ c`, U8Range (op 3) forces `a = 0`.
    -- The op selectors need `256 ≤ p` to be distinct field elements; below that the fact is none.
    byteXorSpec := fun busId =>
      match busMap busId with
      | some .byteLookup =>
          if 256 ≤ p then
            some { bound := 256, xorOp := 2, pairOp := 3, orOp := some 1, andOp := some 0,
                   decode := sp1ByteDecode,
                   encode := sp1ByteEncode, decode_map := sp1ByteDecode_map,
                   decode_mem := sp1ByteDecode_mem, decode_encode := sp1ByteDecode_encode,
                   decode_eq_encode := sp1ByteDecode_eq_encode, encode_map := sp1ByteEncode_map,
                   encode_mem := sp1ByteEncode_mem, pNeZero := inferInstance }
          else none
      | _ => none
    byteXorSpec_sound := by
      intro busId spec hspec
      have hbus : busMap busId = some .byteLookup := by
        revert hspec; cases hb : busMap busId with
        | none => simp
        | some t => cases t <;> simp
      simp only [hbus] at hspec
      by_cases hp : 256 ≤ p
      · rw [if_pos hp] at hspec
        obtain rfl := (Option.some.inj hspec).symm
        have hcast2 : ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by norm_cast
        have hcast3 : ((3 : ℕ) : ZMod p) = (3 : ZMod p) := by norm_cast
        have hp2 : (2 : ZMod p).val = 2 := by rw [← hcast2]; exact ZMod.val_natCast_of_lt (by omega)
        have hp3 : (3 : ZMod p).val = 3 := by rw [← hcast3]; exact ZMod.val_natCast_of_lt (by omega)
        refine ⟨?_, ?_, ?_⟩
        · show (match busMap busId with | some t => t.isStateful | none => false) = false
          rw [hbus]; rfl
        · intro pl
          show breaksInvariant busMap { busId := busId, multiplicity := 1, payload := pl } = false
          unfold breaksInvariant; rw [hbus]; simp
        · intro pl op o1 o2 r mult hdec
          rw [sp1ByteDecode_some] at hdec
          subst hdec
          refine ⟨fun hxor => ?_, fun hpair => ?_⟩
          · have hop2 : op = 2 := hxor
            subst hop2
            show violates busMap { busId := busId, multiplicity := mult, payload := [2, r, o1, o2] }
                = false ↔ o1.val < 256 ∧ o2.val < 256 ∧ r.val = Nat.xor o1.val o2.val
            unfold violates; rw [hbus]
            simp [hp2, isByte, and_assoc]
          · have hop3 : op = 3 := hpair
            subst hop3
            show violates busMap { busId := busId, multiplicity := mult, payload := [3, r, o1, o2] }
                = false ↔ o1.val < 256 ∧ o2.val < 256 ∧ r = 0
            unfold violates; rw [hbus]
            simp [hp3, isByte, ZMod.val_eq_zero, and_assoc]
      · rw [if_neg hp] at hspec; exact absurd hspec (by simp)
    -- SP1's byte bus also carries OR (op 1, `a = b | c`) and AND (op 0, `a = b & c`), declared as
    -- `orOp`/`andOp`.
    byteBoolSound := by
      intro busId spec hspec
      have hbus : busMap busId = some .byteLookup := by
        revert hspec; cases hb : busMap busId with
        | none => simp
        | some t => cases t <;> simp
      simp only [hbus] at hspec
      by_cases hp : 256 ≤ p
      · rw [if_pos hp] at hspec
        obtain rfl := (Option.some.inj hspec).symm
        have hcast1 : ((1 : ℕ) : ZMod p) = (1 : ZMod p) := by norm_cast
        have hp1 : (1 : ZMod p).val = 1 := by rw [← hcast1]; exact ZMod.val_natCast_of_lt (by omega)
        have hp0 : (0 : ZMod p).val = 0 := ZMod.val_zero
        intro pl op o1 o2 r mult hdec
        rw [sp1ByteDecode_some] at hdec
        subst hdec
        refine ⟨fun oop hor hopeq => ?_, fun aop hand hopeq => ?_⟩
        · obtain rfl : oop = 1 := by simpa using hor.symm
          subst hopeq
          show violates busMap { busId := busId, multiplicity := mult, payload := [1, r, o1, o2] }
              = false ↔ o1.val < 256 ∧ o2.val < 256 ∧ r.val = Nat.lor o1.val o2.val
          unfold violates; rw [hbus]
          simp [hp1, isByte, and_assoc]
        · obtain rfl : aop = 0 := by simpa using hand.symm
          subst hopeq
          show violates busMap { busId := busId, multiplicity := mult, payload := [0, r, o1, o2] }
              = false ↔ o1.val < 256 ∧ o2.val < 256 ∧ r.val = Nat.land o1.val o2.val
          unfold violates; rw [hbus]
          simp [hp0, isByte, and_assoc]
      · rw [if_neg hp] at hspec; exact absurd hspec (by simp)
    -- SP1's op-6 (`Range`) byte-bus check `[6, a, w, 0]` (w ≤ 16) is a pure range check on `a`.
    rangeCheckAt := fun busId pattern => rangeCheckAtImpl busMap busId pattern
    rangeCheckAt_sound := by
      intro busId pattern valSlot bound hfact
      unfold rangeCheckAtImpl at hfact
      split at hfact
      · rename_i op e1 w c hbus
        split_ifs at hfact with hcond
        obtain ⟨hop, hw, hc⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hfact
        obtain ⟨rfl, rfl⟩ := hfact
        refine ⟨?_, fun m hbusId hmult hmatch => ?_⟩
        · show (match busMap busId with | some t => t.isStateful | none => false) = false
          rw [hbus]; rfl
        · have hmbus : busMap m.busId = some .byteLookup := by rw [hbusId]; exact hbus
          obtain ⟨q0, q1, q2, q3, hpe⟩ := payload_four hmatch
          have hq0 : q0 = op := by
            have := hmatch.2 0 op (by simp); rw [hpe] at this; simpa using this
          have hq2 : q2 = w := by
            have := hmatch.2 2 w (by simp); rw [hpe] at this; simpa using this
          have hq3 : q3 = c := by
            have := hmatch.2 3 c (by simp); rw [hpe] at this; simpa using this
          rw [hq0, hq2, hq3] at hpe
          have hbreak : breaksInvariant busMap m = false := by
            unfold breaksInvariant; simp [hmbus, hmult]
          refine ⟨hbreak, fun x hx => ?_⟩
          have hxq : q1 = x := by rw [hpe] at hx; simpa using hx
          rw [← hxq]
          exact byte_op6_iff busMap m hmbus op q1 w c hpe hop hw hc
      · exact absurd hfact (by simp) }

end ApcOptimizer.SP1
