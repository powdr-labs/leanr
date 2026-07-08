import Leanr.Implementation.BusFacts
import Leanr.OpenVmSemantics

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

/-- The literal constant value of an expression, if it is a `const` node. Payload/multiplicity
    entries are literal constants after constant folding, so this suffices for pattern recognition. -/
private def constVal? (e : Expression p) : Option (ZMod p) :=
  match e with | .const c => some c | _ => none

private theorem constVal?_eval {e : Expression p} {c : ZMod p} (h : constVal? e = some c)
    (env : Variable → ZMod p) : e.eval env = c := by
  cases e with
  | const c' => simp only [constVal?, Option.some.injEq] at h; subst h; rfl
  | _ => simp [constVal?] at h

/-- If `bi` is a bitwise self-xor byte check — op 1 (xor) with both operands the same expression,
    active multiplicity, and `1 < p` — return the checked operand expression. Such a check asserts
    exactly that the operand is a byte (`xor x x = 0` holds automatically). -/
private def byteCheckOperand? (busMap : Nat → Option OpenVmBusType)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match bi.payload with
  | [x, x', z, op] =>
      if busMap bi.busId = some .bitwiseLookup ∧ 1 < p ∧ x = x' ∧
         constVal? bi.multiplicity ≠ some 0 ∧ constVal? bi.multiplicity ≠ none ∧
         constVal? z = some 0 ∧ constVal? op = some 1 then
        some x
      else none
  | _ => none

private theorem byteCheckOperand?_spec (busMap : Nat → Option OpenVmBusType)
    (bi : BusInteraction (Expression p)) (x : Expression p)
    (h : byteCheckOperand? busMap bi = some x) :
    1 < p ∧ busMap bi.busId = some .bitwiseLookup ∧
      (∀ env, (bi.eval env).multiplicity ≠ 0) ∧
      (∀ env, (bi.eval env).payload = [x.eval env, x.eval env, 0, 1]) := by
  unfold byteCheckOperand? at h
  split at h
  · rename_i x0 x' z op hpay
    split_ifs at h with hc
    · obtain ⟨hbus, h1p, hxx, hm0, hmn, hz, hop⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hmn
      refine ⟨h1p, hbus, fun env => ?_, fun env => ?_⟩
      · show bi.multiplicity.eval env ≠ 0
        rw [constVal?_eval hm env]
        intro h0; exact hm0 (h0 ▸ hm)
      · show bi.payload.map (fun e => e.eval env) = [x0.eval env, x0.eval env, 0, 1]
        simp only [hpay, List.map_cons, List.map_nil, ← hxx, constVal?_eval hz env,
          constVal?_eval hop env]
  all_goals exact absurd h (by simp)

/-- On the bitwise bus, a self-xor lookup `[a, a, 0, 1]` (op 1) is accepted iff `a` is a byte:
    `xor a a = 0` holds automatically, so the only real content is the byte range check on `a`.
    (Stated with `decide (a.val < 256)` — the definition of the audited-but-private `isByte`.) -/
private theorem violates_selfxor (busMap : Nat → Option OpenVmBusType) (h1p : 1 < p)
    (m : BusInteraction (ZMod p)) (a : ZMod p)
    (hbus : busMap m.busId = some .bitwiseLookup) (hpay : m.payload = [a, a, 0, 1]) :
    (violates busMap m = false) ↔ a.val < 256 := by
  haveI : Fact (1 < p) := ⟨h1p⟩
  unfold violates
  simp only [hbus, hpay, ZMod.val_one]
  change ((!(decide (a.val < 256) && decide (a.val < 256)
      && decide ((0 : ZMod p).val = Nat.xor a.val a.val))) = false) ↔ a.val < 256
  simp [ZMod.val_zero, Nat.xor_self]

/-- On the bitwise bus, an op-0 lookup `[a, b, 0, 0]` is accepted iff both `a` and `b` are bytes. -/
private theorem violates_bytepair (busMap : Nat → Option OpenVmBusType)
    (m : BusInteraction (ZMod p)) (a b : ZMod p)
    (hbus : busMap m.busId = some .bitwiseLookup) (hpay : m.payload = [a, b, 0, 0]) :
    (violates busMap m = false) ↔ (a.val < 256 ∧ b.val < 256) := by
  unfold violates
  simp only [hbus, hpay, ZMod.val_zero]
  change ((!(decide (a.val < 256) && decide (b.val < 256) && decide True)) = false)
      ↔ (a.val < 256 ∧ b.val < 256)
  simp

/-- The variable range checker accepts `[y, bits]` iff `bits ≤ 25` and `y < 2 ^ bits`. -/
private theorem violates_varrc (busMap : Nat → Option OpenVmBusType)
    (m : BusInteraction (ZMod p)) (y bits : ZMod p)
    (hbus : busMap m.busId = some .variableRangeChecker) (hpay : m.payload = [y, bits]) :
    (violates busMap m = false) ↔ (bits.val ≤ 25 ∧ y.val < 2 ^ bits.val) := by
  unfold violates
  simp only [hbus, hpay]
  simp [decide_eq_true_eq]

/-- The tuple range checker accepts `[x, y]` iff `x < s1` and `y < s2`. -/
private theorem violates_tuple (busMap : Nat → Option OpenVmBusType) (s1 s2 : Nat)
    (m : BusInteraction (ZMod p)) (x y : ZMod p)
    (hbus : busMap m.busId = some (.tupleRangeChecker s1 s2)) (hpay : m.payload = [x, y]) :
    (violates busMap m = false) ↔ (x.val < s1 ∧ y.val < s2) := by
  unfold violates
  simp only [hbus, hpay]
  simp [decide_eq_true_eq]

/-- The op-0 bitwise range check on operands `x` and `y`, asserting both are bytes. -/
private def mergedBytePair (busId : Nat) (x y : Expression p) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1, payload := [x, y, .const 0, .const 0] }

/-- Merge two single-byte range checks into one two-byte range check. Each bitwise self-xor lookup
    `[x, x, 0, 1]` asserts exactly its operand is a byte, so two such checks on `x` and `y` combine
    into the single op-0 range check `[x, y, 0, 0]` — the same conjoined obligation `x, y` bytes, but
    one fewer bus interaction. -/
private def mergeLookupsImpl (busMap : Nat → Option OpenVmBusType)
    (bi1 bi2 : BusInteraction (Expression p)) : Option (BusInteraction (Expression p)) :=
  match byteCheckOperand? busMap bi1, byteCheckOperand? busMap bi2 with
  | some x, some y =>
      if bi1.busId = bi2.busId then some (mergedBytePair bi1.busId x y)
      else none
  | _, _ => none

/-- If `bi` is an active variable-range check `[y, bits]` with a constant `bits ≤ 25`, return the
    checked value and the (constant) bit-width value. -/
private def varRcOperand? (busMap : Nat → Option OpenVmBusType)
    (bi : BusInteraction (Expression p)) : Option (Expression p × ZMod p) :=
  match bi.payload with
  | [y, bexpr] =>
      match constVal? bexpr with
      | some bval =>
          if busMap bi.busId = some .variableRangeChecker ∧
             constVal? bi.multiplicity ≠ some 0 ∧ constVal? bi.multiplicity ≠ none ∧
             bval.val ≤ 25 then some (y, bval)
          else none
      | none => none
  | _ => none

private theorem varRcOperand?_spec (busMap : Nat → Option OpenVmBusType)
    (bi : BusInteraction (Expression p)) (y : Expression p) (bval : ZMod p)
    (h : varRcOperand? busMap bi = some (y, bval)) :
    busMap bi.busId = some .variableRangeChecker ∧ bval.val ≤ 25 ∧
      (∀ env, (bi.eval env).multiplicity ≠ 0) ∧
      (∀ env, (bi.eval env).payload = [y.eval env, bval]) := by
  unfold varRcOperand? at h
  split at h
  · rename_i y0 bexpr hpay
    split at h
    · rename_i bval0 hbval
      split_ifs at h with hc
      · obtain ⟨hbus, hm0, hmn, hble⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hy, hb⟩ := h
        subst hy; subst hb
        obtain ⟨mm, hm⟩ := Option.ne_none_iff_exists'.1 hmn
        refine ⟨hbus, hble, fun env => ?_, fun env => ?_⟩
        · show bi.multiplicity.eval env ≠ 0
          rw [constVal?_eval hm env]; intro h0; exact hm0 (h0 ▸ hm)
        · show bi.payload.map (fun e => e.eval env) = [y0.eval env, bval0]
          simp only [hpay, List.map_cons, List.map_nil, constVal?_eval hbval env]
    all_goals exact absurd h (by simp)
  all_goals exact absurd h (by simp)

/-- Find a tuple-range-check bus whose sizes are `(s1, s2)` (bounded search over small bus ids). -/
private def findTupleBus (busMap : Nat → Option OpenVmBusType) (s1 s2 : Nat) : Option Nat :=
  (List.range 256).find? (fun k => decide (busMap k = some (.tupleRangeChecker s1 s2)))

private theorem findTupleBus_spec (busMap : Nat → Option OpenVmBusType) (s1 s2 k : Nat)
    (h : findTupleBus busMap s1 s2 = some k) :
    busMap k = some (.tupleRangeChecker s1 s2) := by
  unfold findTupleBus at h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact hp

/-- Try to merge `a` (a byte check) and `b` (a range check) into a tuple range check `[x, y]` on a
    `(256, 2^bits)` tuple bus. -/
private def tryTuple (busMap : Nat → Option OpenVmBusType)
    (a b : BusInteraction (Expression p)) : Option (BusInteraction (Expression p)) :=
  match byteCheckOperand? busMap a, varRcOperand? busMap b with
  | some x, some yb =>
      (findTupleBus busMap 256 (2 ^ yb.2.val)).map
        (fun k => { busId := k, multiplicity := .const 1, payload := [x, yb.1] })
  | _, _ => none

/-- Soundness of one-directional tuple packing: `a` a byte check, `b` a range check on a matching
    tuple bus. The merged tuple's obligation is `a`'s ∧ `b`'s (byte + range = the tuple's two bounds). -/
private theorem tryTuple_sound (busMap : Nat → Option OpenVmBusType)
    (a b bi3 : BusInteraction (Expression p)) (h : tryTuple busMap a b = some bi3) :
    (openVmBusSemantics p busMap).isStateful a.busId = false ∧
    (openVmBusSemantics p busMap).isStateful b.busId = false ∧
    (openVmBusSemantics p busMap).isStateful bi3.busId = false ∧
    (∀ env, (a.eval env).multiplicity ≠ 0) ∧ (∀ env, (b.eval env).multiplicity ≠ 0) ∧
    (∀ env, (bi3.eval env).multiplicity ≠ 0) ∧
    (∀ env, breaksInvariant busMap (bi3.eval env) = false) ∧
    (∀ env, violates busMap (bi3.eval env) = false ↔
      (violates busMap (a.eval env) = false ∧ violates busMap (b.eval env) = false)) := by
  unfold tryTuple at h
  split at h
  · rename_i x yb hbc hvr
    obtain ⟨y, bval⟩ := yb
    rw [Option.map_eq_some_iff] at h
    obtain ⟨k, htuple, hk⟩ := h
    subst hk
    obtain ⟨h1p, hbusB, hmB, hpayB⟩ := byteCheckOperand?_spec busMap a x hbc
    obtain ⟨hbusR, hble, hmR, hpayR⟩ := varRcOperand?_spec busMap b y bval hvr
    have hbusK : busMap k = some (.tupleRangeChecker 256 (2 ^ bval.val)) :=
      findTupleBus_spec busMap 256 (2 ^ bval.val) k htuple
    haveI : Fact (1 < p) := ⟨h1p⟩
    refine ⟨?_, ?_, ?_, hmB, hmR, ?_, ?_, ?_⟩
    · show (match busMap a.busId with | some t => t.isStateful | none => false) = false
      simp only [hbusB, OpenVmBusType.isStateful]
    · show (match busMap b.busId with | some t => t.isStateful | none => false) = false
      simp only [hbusR, OpenVmBusType.isStateful]
    · show (match busMap k with | some t => t.isStateful | none => false) = false
      simp only [hbusK, OpenVmBusType.isStateful]
    · intro env; show (Expression.const 1).eval env ≠ 0; simpa using one_ne_zero
    · intro env
      show breaksInvariant busMap
        (({ busId := k, multiplicity := .const 1, payload := [x, y] }
          : BusInteraction (Expression p)).eval env) = false
      simp [breaksInvariant, BusInteraction.eval, Expression.eval, hbusK]
    · intro env
      rw [violates_tuple busMap 256 (2 ^ bval.val) _ (x.eval env) (y.eval env) hbusK rfl,
          violates_selfxor busMap h1p (a.eval env) (x.eval env) hbusB (hpayB env),
          violates_varrc busMap (b.eval env) (y.eval env) bval hbusR (hpayR env)]
      constructor
      · rintro ⟨hx, hy⟩; exact ⟨hx, hble, hy⟩
      · rintro ⟨hx, _, hy⟩; exact ⟨hx, hy⟩
  · exact absurd h (by simp)

/-- Merge a bitwise byte check `[x,x,0,1]` (x < 256) and a variable-range check `[y, b]` (y < 2^b)
    into a single tuple range check `[x, y]` on a `(256, 2^b)` tuple bus — the same conjoined
    obligation, one fewer interaction. Tries both operand orders. -/
private def mergeTupleLookupsImpl (busMap : Nat → Option OpenVmBusType)
    (bi1 bi2 : BusInteraction (Expression p)) : Option (BusInteraction (Expression p)) :=
  match tryTuple busMap bi1 bi2 with
  | some bi3 => some bi3
  | none => tryTuple busMap bi2 bi1

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
  mergeLookups := mergeLookupsImpl busMap
  mergeLookups_sound := by
    intro bi1 bi2 bi3 hmerge
    unfold mergeLookupsImpl at hmerge
    split at hmerge
    · rename_i x y hx hy
      split_ifs at hmerge with hbuseq
      · simp only [Option.some.injEq] at hmerge
        subst hmerge
        obtain ⟨h1p, hbus1, hm1, hpay1⟩ := byteCheckOperand?_spec busMap bi1 x hx
        obtain ⟨_, hbus2, hm2, hpay2⟩ := byteCheckOperand?_spec busMap bi2 y hy
        haveI : Fact (1 < p) := ⟨h1p⟩
        have hst1 : (openVmBusSemantics p busMap).isStateful bi1.busId = false := by
          show (match busMap bi1.busId with | some t => t.isStateful | none => false) = false
          simp only [hbus1, OpenVmBusType.isStateful]
        have hst2 : (openVmBusSemantics p busMap).isStateful bi2.busId = false := by
          show (match busMap bi2.busId with | some t => t.isStateful | none => false) = false
          simp only [hbus2, OpenVmBusType.isStateful]
        refine ⟨hst1, hst2, hst1, hm1, hm2, ?_, ?_, ?_⟩
        · intro env
          show (Expression.const 1).eval env ≠ 0
          simpa using one_ne_zero
        · intro env
          show breaksInvariant busMap ((mergedBytePair bi1.busId x y).eval env) = false
          simp [breaksInvariant, mergedBytePair, BusInteraction.eval, Expression.eval, hbus1]
        · intro env
          show (violates busMap ((mergedBytePair bi1.busId x y).eval env) = false) ↔
            ((violates busMap (bi1.eval env) = false) ∧ (violates busMap (bi2.eval env) = false))
          rw [violates_bytepair busMap ((mergedBytePair bi1.busId x y).eval env)
                (x.eval env) (y.eval env) hbus1 rfl,
              violates_selfxor busMap h1p (bi1.eval env) (x.eval env) hbus1 (hpay1 env),
              violates_selfxor busMap h1p (bi2.eval env) (y.eval env) hbus2 (hpay2 env)]
    all_goals exact absurd hmerge (by simp)
  mergeTupleLookups := mergeTupleLookupsImpl busMap
  mergeTupleLookups_sound := by
    intro bi1 bi2 bi3 hmerge
    unfold mergeTupleLookupsImpl at hmerge
    split at hmerge
    · -- tuple pack in the given order (`bi1` byte, `bi2` range)
      rename_i b3 h1
      simp only [Option.some.injEq] at hmerge
      subst hmerge
      exact tryTuple_sound busMap bi1 bi2 b3 h1
    · -- the reversed order (`bi2` byte, `bi1` range); swap the symmetric components
      rename_i h1
      obtain ⟨s1, s2, s3, a1, a2, a3, inv, obl⟩ := tryTuple_sound busMap bi2 bi1 bi3 hmerge
      exact ⟨s2, s1, s3, a2, a1, a3, inv, fun env => (obl env).trans and_comm⟩
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

end Leanr.OpenVM
