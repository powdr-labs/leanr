import Leanr.Implementation.BusFacts
import Leanr.OpenVmSemantics
import Leanr.Implementation.MemoryBusDrop

set_option autoImplicit false

/-!
# Proven bus facts for the OpenVM semantics

The `BusFacts` instance for `openVmBusSemantics` (see `Leanr/Implementation/BusFacts.lean` for the design):
byte bounds for the bitwise-lookup operands, the bits-indexed bound of the variable range
checker, the tuple-range-checker bounds, the XOR functional dependence, and the table-free
buses. Every claim is proven here against the concrete `violates`, so none of this needs to be
audited — a wrong fact simply would not compile.

Like the semantics, the facts are parameterized by the bus map (defaulting to
`defaultBusMap`): the implementations key on the bus *type* the map assigns, so the proofs are
uniform in the map.
-/

namespace Leanr.OpenVM

variable {p : ℕ}

private def slotBoundImpl (busMap : Nat → Option OpenVmBusType) (busId : Nat)
    (pattern : List (Option (ZMod p))) (slot : Nat) : Option Nat :=
  match busMap busId, pattern, slot with
  | some .bitwiseLookup, [_, _, _, some op], 0 => if op.val ≤ 1 then some 256 else none
  | some .bitwiseLookup, [_, _, _, some op], 1 => if op.val ≤ 1 then some 256 else none
  | some .variableRangeChecker, [_, some bits], 0 =>
      if bits.val ≤ 25 then some (2 ^ bits.val) else none
  | some (.tupleRangeChecker s1 _), [_, _], 0 => some s1
  | some (.tupleRangeChecker _ s2), [_, _], 1 => some s2
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
  | some .memory => true
  -- Note: pcLookup is *not* listed here. Its `violates` now rejects payloads whose
  -- length is not 9, so it can violate and is not unconditionally sound.
  | _ => false

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
    show violates busMap m = false
    unfold neverViolatesImpl at h
    unfold violates
    split at h
    · rename_i hbus; rw [hbus]
    · rename_i hbus; rw [hbus]
    · exact absurd h (by simp)
  memShape := memShapeOf busMap
  memShape_stateful := fun busId shape hshape =>
    openVm_isStateful_of_memShape busMap busId shape hshape
  admissible_sound := by
    intro msgs hadm busId shape hshape
    have hstateful : (openVmBusSemantics p busMap).isStateful busId = true :=
      openVm_isStateful_of_memShape busMap busId shape hshape
    -- `openVmBusSemantics.admissible` is the per-bus `admissibleMemoryBus` conjunction
    have hd := hadm busId shape hshape
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
    -- `openVmBusSemantics.admissible` is the per-declared-bus `admissibleMemoryBus` conjunction.
    intro hp1 busId shape hshape A B C S R hSbus hRbus hSm hRm haddrEq hcons hearliest hadm_full
      busId' shape' hshape'
    by_cases hbb : busId' = busId
    · subst busId'
      obtain rfl : shape = shape' := Option.some.inj (hshape.symm.trans hshape')
      have hgoal : (A ++ B ++ C).filter (fun m => m.busId = busId)
          = A.filter (fun m => m.busId = busId) ++ B.filter (fun m => m.busId = busId)
            ++ C.filter (fun m => m.busId = busId) := by
        simp only [List.filter_append]
      rw [hgoal]
      have hfull := hadm_full busId shape hshape
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
      exact hadm_full busId' shape' hshape'
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

end Leanr.OpenVM
