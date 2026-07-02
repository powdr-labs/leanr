import Leanr.BusFacts
import Leanr.OpenVM.Semantics

set_option autoImplicit false

/-!
# Proven bus facts for the OpenVM semantics

The `BusFacts` instance for `openVmBusSemantics` (see `Leanr/BusFacts.lean` for the design):
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
      if bits.val ≤ 30 then some (2 ^ bits.val) else none
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
  | some .pcLookup => true
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
      simpa using hok'
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
    · rename_i hbus; rw [hbus]
    · exact absurd h (by simp)

end Leanr.OpenVM
