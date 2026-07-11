import ApcOptimizer.Implementation.BusFacts
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Implementation.MemoryBusDrop

set_option autoImplicit false

/-!
# Proven bus facts for the OpenVM semantics

The `BusFacts` instance for `openVmBusSemantics` (see `ApcOptimizer/Implementation/BusFacts.lean` for the design):
byte bounds for the bitwise-lookup operands, the bits-indexed bound of the variable range
checker, the tuple-range-checker bounds, the XOR functional dependence, and the table-free
buses. Every claim is proven here against the concrete `violates`, so none of this needs to be
audited — a wrong fact simply would not compile.

Like the semantics, the facts are parameterized by the bus map (defaulting to
`defaultBusMap`): the implementations key on the bus *type* the map assigns, so the proofs are
uniform in the map.
-/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

private def slotBoundImpl (busMap : Nat → Option OpenVmBusType) (busId : Nat) (mult : ZMod p)
    (pattern : List (Option (ZMod p))) (slot : Nat) : Option Nat :=
  match busMap busId, pattern, slot with
  | some .bitwiseLookup, [_, _, _, some op], 0 => if op.val ≤ 1 then some 256 else none
  | some .bitwiseLookup, [_, _, _, some op], 1 => if op.val ≤ 1 then some 256 else none
  -- Slot 2 is the bitwise *result* `z`: op 0 forces `z = 0`, op 1 forces `z = x ^ y` with
  -- byte operands, so `z` is a byte in either case (op ≥ 2 violates). This byte guarantee on
  -- the XOR/AND result — not just the operands — is what lets a memory pair whose data is an
  -- XOR output be cancelled (`byteJustified`).
  | some .bitwiseLookup, [_, _, _, some op], 2 => if op.val ≤ 1 then some 256 else none
  | some .variableRangeChecker, [_, some bits], 0 =>
      if bits.val ≤ 25 then some (2 ^ bits.val) else none
  | some (.tupleRangeChecker s1 _), [_, _], 0 => some s1
  | some (.tupleRangeChecker _ s2), [_, _], 1 => some s2
  -- Data limbs of a memory *receive* (multiplicity -1) from a known register / main-memory
  -- address space: slots 2–5 of the `(addressSpace, pointer, data×4, timestamp)` payload
  -- are bytes (see `violates`).
  | some .memory, [some as, _, _, _, _, _, _], 2 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | some .memory, [some as, _, _, _, _, _, _], 3 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | some .memory, [some as, _, _, _, _, _, _], 4 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | some .memory, [some as, _, _, _, _, _, _], 5 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | _, _, _ => none

private def slotFunImpl (busMap : Nat → Option OpenVmBusType) (busId : Nat)
    (pattern : List (Option (ZMod p))) (outSlot : Nat) :
    Option (List (ZMod p) → ZMod p) :=
  match busMap busId, pattern, outSlot with
  | some .bitwiseLookup, [_, _, _, some op], 2 =>
      if op.val = 1 then
        some (fun payload =>
          match payload with
          | [x, y, _, _] => ((Nat.xor x.val y.val : Nat) : ZMod p)
          | _ => 0)
      else none
  | _, _, _ => none

private def neverViolatesImpl (busMap : Nat → Option OpenVmBusType) (busId : Nat) : Bool :=
  match busMap busId with
  | some .executionBridge => true
  -- Note: the memory bus is *not* listed here. Its `violates` rejects receives of non-byte
  -- words from address spaces 1/2, so memory messages can violate (see `recvByteSlots`).
  -- Note: pcLookup is *not* listed here. Its `violates` now rejects payloads whose
  -- length is not 9, so it can violate and is not unconditionally sound.
  | _ => false

/-- The fixed-zero cell of the OpenVM memory bus: register `x0` = address `(as, ptr) = (1, 0)`,
    with the four data limbs at payload slots `2..5`. Backs the `zeroRegisterReads` admissibility
    clause; `none` for every non-memory bus. -/
private def zeroCellImpl (busMap : Nat → Option OpenVmBusType) (busId : Nat) :
    Option (List (Nat × ZMod p) × List Nat) :=
  match busMap busId with
  | some .memory => some ([(0, 1), (1, 0)], [2, 3, 4, 5])
  | _ => none

/-- A payload matching a 4-entry pattern is a 4-entry list. -/
private theorem payload_four {payload : List (ZMod p)} {p0 p1 p2 p3 : Option (ZMod p)}
    (h : Matches payload [p0, p1, p2, p3]) :
    ∃ a b c d, payload = [a, b, c, d] := by
  obtain ⟨hlen, _⟩ := h
  match payload, hlen with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- A payload matching a 2-entry pattern is a 2-entry list. -/
private theorem payload_two {payload : List (ZMod p)} {p0 p1 : Option (ZMod p)}
    (h : Matches payload [p0, p1]) :
    ∃ a b, payload = [a, b] := by
  obtain ⟨hlen, _⟩ := h
  match payload, hlen with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- A payload matching a 7-entry pattern is a 7-entry list. -/
private theorem payload_seven {payload : List (ZMod p)}
    {p0 p1 p2 p3 p4 p5 p6 : Option (ZMod p)}
    (h : Matches payload [p0, p1, p2, p3, p4, p5, p6]) :
    ∃ a0 a1 d0 d1 d2 d3 t, payload = [a0, a1, d0, d1, d2, d3, t] := by
  obtain ⟨hlen, _⟩ := h
  match payload, hlen with
  | [a0, a1, d0, d1, d2, d3, t], _ => exact ⟨a0, a1, d0, d1, d2, d3, t, rfl⟩

/-- An execution-bridge message never violates. -/
private theorem execBridge_ok (busMap : Nat → Option OpenVmBusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .executionBridge) :
    violates busMap m = false := by
  unfold violates
  rw [hbus]

/-- The data limbs of an accepted (non-violating) memory *receive* from address space 1 or 2
    are bytes. -/
private theorem memory_recv_bytes (busMap : Nat → Option OpenVmBusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = -1)
    (a0 a1 d0 d1 d2 d3 t : ZMod p) (hpay : m.payload = [a0, a1, d0, d1, d2, d3, t])
    (has : a0.val = 1 ∨ a0.val = 2)
    (hok : violates busMap m = false) :
    d0.val < 256 ∧ d1.val < 256 ∧ d2.val < 256 ∧ d3.val < 256 := by
  unfold violates at hok
  rw [hbus, hpay, hm] at hok
  have has' : (a0.val == 1 || a0.val == 2) = true := by
    rcases has with h | h <;> simp [h]
  simp only [decide_true, has', Bool.true_and, Bool.not_eq_false', List.all_eq_true,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    isByte, decide_eq_true_eq] at hok
  exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩

/-- A memory message that is not a receive (multiplicity ≠ -1) never violates. -/
private theorem memory_nonRecv_ok (busMap : Nat → Option OpenVmBusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity ≠ -1) : violates busMap m = false := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hm
  unfold violates
  rw [hbus]
  rcases payload with _ | ⟨a0, _ | ⟨a1, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩ <;>
    simp [hm]

/-- A memory *send* (multiplicity 1) never violates: either the characteristic is > 2 and a
    send is not a receive, or `p ∣ 2` and every value is trivially a byte. -/
private theorem memory_send_ok [NeZero p] (busMap : Nat → Option OpenVmBusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = 1) : violates busMap m = false := by
  by_cases hc : (1 : ZMod p) = -1
  · -- `p ∣ 2`: every value is `< 2 ≤ 256`, so the byte test never fails.
    have hadd : (1 : ZMod p) + 1 = 0 := (congrArg (· + 1) hc).trans (neg_add_cancel 1)
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_ofNat, ← one_add_one_eq_two]
      exact hadd
    have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
    have hbyte : ∀ d : ZMod p, d.val < 256 :=
      fun d => lt_of_lt_of_le (ZMod.val_lt d)
        (le_trans (Nat.le_of_dvd (by decide) hp2) (by decide))
    obtain ⟨bid, mult, payload⟩ := m
    simp only at hbus
    unfold violates
    rw [hbus]
    rcases payload with _ | ⟨a0, _ | ⟨a1, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩ <;>
      simp [isByte, hbyte]
  · exact memory_nonRecv_ok busMap m hbus (by rw [hm]; exact hc)

/-- A memory *receive* (multiplicity -1) with byte data limbs (payload slots 2–5, where
    present) never violates. -/
private theorem memory_recv_ok (busMap : Nat → Option OpenVmBusType)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = -1)
    (hslots : ∀ slot ∈ [2, 3, 4, 5], ∀ x : ZMod p, m.payload[slot]? = some x → x.val < 256) :
    violates busMap m = false := by
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hm hslots
  unfold violates
  rw [hbus]
  rcases payload with _ | ⟨a0, _ | ⟨a1, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩ <;>
    try rfl
  have h0 : d0.val < 256 := hslots 2 (by simp) d0 rfl
  have h1 : d1.val < 256 := hslots 3 (by simp) d1 rfl
  have h2 : d2.val < 256 := hslots 4 (by simp) d2 rfl
  have h3 : d3.val < 256 := hslots 5 (by simp) d3 rfl
  simp [isByte, h0, h1, h2, h3]

/-- A bus with a declared last-write-wins shape (memory or execution bridge) is stateful. -/
theorem openVm_isStateful_of_memShape {p : ℕ} (busMap : Nat → Option OpenVmBusType)
    (busId : Nat) (shape : MemoryBusShape) (h : memShapeOf busMap busId = some shape) :
    (openVmBusSemantics p busMap).isStateful busId = true := by
  show (match busMap busId with | some t => t.isStateful | none => false) = true
  unfold memShapeOf at h
  generalize busMap busId = o at h ⊢
  cases o with
  | none => simp at h
  | some t => cases t <;> simp_all [OpenVmBusType.isStateful]

/-- The proven facts about `openVmBusSemantics`, for any bus map. -/
def openVmFacts (p : ℕ) [NeZero p]
    (busMap : Nat → Option OpenVmBusType := defaultBusMap) :
    BusFacts p (openVmBusSemantics p busMap) where
  slotBound := slotBoundImpl busMap
  slotBound_sound := by
    intro m pattern slot bound x hfact hmatch hok hget
    have hok' : violates busMap m = false := hok
    unfold slotBoundImpl at hfact
    split at hfact
    · -- bitwise lookup, slot 0
      rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hx : a = x := by rw [hpay] at hget; simpa using hget
      subst hx hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hop with h0 | h0 <;>
        · simp only [h0] at hok'
          rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
          exact of_decide_eq_true hok'.1.1
    · -- bitwise lookup, slot 1
      rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hx : b = x := by rw [hpay] at hget; simpa using hget
      subst hx hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hop with h0 | h0 <;>
        · simp only [h0] at hok'
          rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
          exact of_decide_eq_true hok'.1.2
    · -- bitwise lookup, slot 2 (the XOR/AND result is a byte)
      rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hx : c = x := by rw [hpay] at hget; simpa using hget
      subst hx hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hop with h0 | h0
      · -- op = 0: `z = 0`
        simp only [h0] at hok'
        rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
        rw [of_decide_eq_true hok'.2]; decide
      · -- op = 1: `z = x ^ y` with byte operands
        simp only [h0] at hok'
        rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
        have hxa : a.val < 2 ^ 8 := of_decide_eq_true hok'.1.1
        have hxb : b.val < 2 ^ 8 := of_decide_eq_true hok'.1.2
        rw [of_decide_eq_true hok'.2]
        exact Nat.xor_lt_two_pow hxa hxb
    · -- variable range checker
      rename_i q0 bits hbus
      split_ifs at hfact with hbits
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, hpay⟩ := payload_two hmatch
      have hb : b = bits := by
        have h1 := hmatch.2 1 bits (by simp)
        rw [hpay] at h1; simpa using h1
      have hx : a = x := by rw [hpay] at hget; simpa using hget
      subst hx hb
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true] at hok'
      exact of_decide_eq_true hok'.2
    · -- tuple range checker, slot 0
      rename_i s1 s2 q0 q1 hbus
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, hpay⟩ := payload_two hmatch
      have hx : a = x := by rw [hpay] at hget; simpa using hget
      subst hx
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      simp only [] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true] at hok'
      exact of_decide_eq_true hok'.1
    · -- tuple range checker, slot 1
      rename_i s1 s2 q0 q1 hbus
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, hpay⟩ := payload_two hmatch
      have hx : b = x := by rw [hpay] at hget; simpa using hget
      subst hx
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      simp only [] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true] at hok'
      exact of_decide_eq_true hok'.2
    · -- memory receive, slot 2
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d0 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').1
    · -- memory receive, slot 3
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d1 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').2.1
    · -- memory receive, slot 4
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d2 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').2.2.1
    · -- memory receive, slot 5
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d3 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').2.2.2
    · exact absurd hfact (by simp)
  slotFun := slotFunImpl busMap
  slotFun_sound := by
    intro m pattern outSlot f z hfact hmatch hok hget
    have hok' : violates busMap m = false := hok
    unfold slotFunImpl at hfact
    split at hfact
    · rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hz : c = z := by rw [hpay] at hget; simpa using hget
      subst hz hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      simp only [hop] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
      have hxor : c.val = Nat.xor a.val b.val := of_decide_eq_true hok'.2
      rw [hpay]
      show c = ((Nat.xor a.val b.val : Nat) : ZMod p)
      rw [← hxor]
      exact (ZMod.natCast_rightInverse c).symm
    · exact absurd hfact (by simp)
  neverViolates := neverViolatesImpl busMap
  neverViolates_sound := by
    intro m h
    unfold neverViolatesImpl at h
    split at h
    · rename_i hbus; exact execBridge_ok busMap m hbus
    · exact absurd h (by simp)
  recvByteSlots busId := match busMap busId with
    | some .memory => some [2, 3, 4, 5]
    | some .executionBridge => some []
    | _ => none
  recvByteSlots_sound := by
    intro busId slots hfact m hbusId
    subst hbusId
    split at hfact
    · -- memory: sends never violate; receives need byte data limbs (slots 2–5)
      rename_i hbus
      simp only [Option.some.injEq] at hfact
      subst hfact
      exact ⟨fun hm => memory_send_ok busMap m hbus hm,
             fun hm hbytes => memory_recv_ok busMap m hbus hm hbytes⟩
    · -- execution bridge: never violates
      rename_i hbus
      exact ⟨fun _ => execBridge_ok busMap m hbus,
             fun _ _ => execBridge_ok busMap m hbus⟩
    · exact absurd hfact (by simp)
  memShape := memShapeOf busMap
  memShape_stateful := fun busId shape hshape =>
    openVm_isStateful_of_memShape busMap busId shape hshape
  admissible_sound := by
    intro msgs hadm busId shape hshape
    have hstateful : (openVmBusSemantics p busMap).isStateful busId = true :=
      openVm_isStateful_of_memShape busMap busId shape hshape
    -- `openVmBusSemantics.admissible` is the per-bus `admissibleMemoryBus` conjunction, `.1`
    have hd := hadm.1 busId shape hshape
    -- the active∧stateful-then-busId list equals the busId-then-active list (busId is stateful)
    have hlist : (msgs.filter (fun m => decide (m.multiplicity ≠ 0) &&
          (openVmBusSemantics p busMap).isStateful m.busId)).filter (fun m => m.busId = busId)
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
    -- `openVmBusSemantics.admissible` is the per-declared-bus `admissibleMemoryBus` conjunction
    -- (`.1`) together with the `zeroRegisterReads` clause (`.2`).
    intro hp1 busId shape hshape A B C S R hSbus hRbus hSm hRm haddrEq hcons hearliest hadm_full
    obtain ⟨hdisc, hzero⟩ := hadm_full
    refine ⟨fun busId' shape' hshape' => ?_, ?_⟩
    · -- memory discipline conjunct
      by_cases hbb : busId' = busId
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
        · intro m hm hmne hmaddr
          rw [List.mem_filter] at hm
          exact hearliest m hm.1 (of_decide_eq_true hm.2) hmne hmaddr
      · -- `busId' ≠ busId`: `S`, `R` are on `busId`, so they drop out and the filter is unchanged.
        have hne : busId ≠ busId' := fun h => hbb h.symm
        have heq : (A ++ B ++ C).filter (fun m => m.busId = busId')
            = (A ++ S :: B ++ R :: C).filter (fun m => m.busId = busId') := by
          simp only [List.filter_append, List.filter_cons, hSbus, hRbus,
            decide_eq_false hne, Bool.false_eq_true, if_false]
        rw [heq]
        exact hdisc busId' shape' hshape'
    · -- `zeroRegisterReads` conjunct: `A ++ B ++ C`'s members are all members of the full list.
      intro m hm hbus h0 h1
      have hmem : m ∈ A ++ S :: B ++ R :: C := by
        simp only [List.mem_append, List.mem_cons] at hm ⊢
        tauto
      exact hzero m hmem hbus h0 h1
  bytePairBus busId := match busMap busId with
    | some .bitwiseLookup => true
    | _ => false
  bytePairBus_sound := by
    intro busId h
    -- `h` forces the bus to be the bitwise-lookup bus.
    have hbus : busMap busId = some OpenVmBusType.bitwiseLookup := by
      revert h; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp
    refine ⟨?_, ?_, ?_⟩
    · -- the bitwise-lookup bus is stateless
      show (match busMap busId with | some t => t.isStateful | none => false) = false
      rw [hbus]; rfl
    · -- a multiplicity-1 packed check never breaks an invariant
      intro x y
      show breaksInvariant busMap { busId := busId, multiplicity := 1, payload := [x, y, 0, 0] }
        = false
      unfold breaksInvariant; rw [hbus]; simp
    · intro x y mult
      -- `(0 : ZMod p).val = 0` and `(1 : ZMod p).val ≤ 1` reduce the `match op.val` branches;
      -- `isByte` stays opaque — the accepted conditions on both sides coincide by boolean logic.
      have hv0 : (0 : ZMod p).val = 0 := ZMod.val_zero
      have h1le : (1 : ZMod p).val ≤ 1 := by
        rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le 1 p
      show violates busMap { busId := busId, multiplicity := mult, payload := [x, y, 0, 0] } = false ↔
        violates busMap { busId := busId, multiplicity := mult, payload := [x, x, 0, 1] } = false ∧
        violates busMap { busId := busId, multiplicity := mult, payload := [y, y, 0, 1] } = false
      unfold violates; rw [hbus]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1le with h1 | h1 <;> simp [h1, hv0]
  byteCheck busId := match busMap busId with
    | some .bitwiseLookup => true
    | _ => false
  byteCheck_sound := by
    intro busId h
    -- `h` forces the bus to be the bitwise-lookup bus.
    have hbus : busMap busId = some OpenVmBusType.bitwiseLookup := by
      revert h; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp
    refine ⟨?_, ?_, ?_⟩
    · -- the bitwise-lookup bus is stateless
      show (match busMap busId with | some t => t.isStateful | none => false) = false
      rw [hbus]; rfl
    · -- a multiplicity-1 self-check never breaks an invariant
      intro x
      show breaksInvariant busMap { busId := busId, multiplicity := 1, payload := [x, x, 0, 1] }
        = false
      unfold breaksInvariant; rw [hbus]; simp
    · intro x mult
      -- both `match op.val` branches reduce to "`x` is a byte": op 1 asserts `x ⊕ x = 0`
      -- (true) plus byte-ness; the degenerate op-0 branch (`p ∣ 2`) asserts `z = 0` (true)
      -- plus byte-ness.
      have hv0 : (0 : ZMod p).val = 0 := ZMod.val_zero
      have h1le : (1 : ZMod p).val ≤ 1 := by
        rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le 1 p
      show violates busMap { busId := busId, multiplicity := mult, payload := [x, x, 0, 1] }
          = false ↔ x.val < 256
      unfold violates; rw [hbus]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1le with h1 | h1 <;>
        simp [h1, hv0, isByte, Nat.xor_self]
  xorZeroCheck busId := match busMap busId with
    | some .bitwiseLookup => true
    | _ => false
  xorZeroCheck_sound := by
    intro busId h
    have hbus : busMap busId = some OpenVmBusType.bitwiseLookup := by
      revert h; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp
    refine ⟨?_, ?_⟩
    · show (match busMap busId with | some t => t.isStateful | none => false) = false
      rw [hbus]; rfl
    · intro x mult
      -- op 1 asserts `x ⊕ 0 = x` (true) plus byte-ness of `x`; the degenerate op-0 branch
      -- (`(1 : ZMod p).val = 0`, i.e. `p = 1`) makes every value the byte `0`.
      have hv0 : (0 : ZMod p).val = 0 := ZMod.val_zero
      have h1le : (1 : ZMod p).val ≤ 1 := by
        rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le 1 p
      show violates busMap { busId := busId, multiplicity := mult, payload := [x, 0, x, 1] }
          = false ↔ x.val < 256
      unfold violates; rw [hbus]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1le with h1 | h1
      · have hp1 : p = 1 := Nat.dvd_one.mp (Nat.dvd_of_mod_eq_zero (by
          rwa [ZMod.val_one_eq_one_mod] at h1))
        subst hp1
        have hx0 : x.val = 0 := Nat.lt_one_iff.1 (ZMod.val_lt x)
        simp [h1, hv0, hx0, isByte]
      · simp [h1, hv0, isByte, Nat.xor_zero]
  zeroCell := zeroCellImpl busMap
  zeroCell_sound := by
    intro msgs hadm busId addrReq dataSlots hfact m hm hbusId hmne haddr slot hslot v hget
    -- `zeroCell` is `some` only on memory buses; extract the fixed shape.
    unfold zeroCellImpl at hfact
    split at hfact
    · rename_i hbus
      simp only [Option.some.injEq, Prod.mk.injEq] at hfact
      obtain ⟨rfl, rfl⟩ := hfact
      -- `m` survives the active∧stateful filter, so the `zeroRegisterReads` clause applies to it.
      have hstateful : (openVmBusSemantics p busMap).isStateful m.busId = true := by
        show (match busMap m.busId with | some t => t.isStateful | none => false) = true
        rw [hbusId, hbus]; rfl
      have hmemBus : busMap m.busId = some .memory := by rw [hbusId]; exact hbus
      have hmfilt : m ∈ msgs.filter
          (fun m => decide (m.multiplicity ≠ 0) && (openVmBusSemantics p busMap).isStateful m.busId) := by
        rw [List.mem_filter]
        exact ⟨hm, by rw [hstateful, decide_eq_true hmne]; rfl⟩
      have h0 : m.payload[0]? = some 1 := haddr (0, 1) (by simp)
      have h1 : m.payload[1]? = some 0 := haddr (1, 0) (by simp)
      have hz := hadm.2 m hmfilt hmemBus h0 h1
      -- `slot ∈ [2,3,4,5]`; match it to the corresponding zero component and cancel with `hget`.
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
      rcases hslot with rfl | rfl | rfl | rfl
      · rw [hget] at hz; exact Option.some.inj hz.1
      · rw [hget] at hz; exact Option.some.inj hz.2.1
      · rw [hget] at hz; exact Option.some.inj hz.2.2.1
      · rw [hget] at hz; exact Option.some.inj hz.2.2.2
    · exact absurd hfact (by simp)

end ApcOptimizer.OpenVM
