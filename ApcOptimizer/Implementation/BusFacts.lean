import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Proven auxiliary knowledge about a bus semantics

`BusFacts` is the sound channel for pass-consumable facts about a `BusSemantics`: every claim
carries a proof against it, so supplying facts adds nothing to the audit surface.
`BusFacts.trivial` claims nothing. A *pattern* is a payload template (`some c` must equal the
message's entry, `none` is free), letting a fact be conditional on constant slots.
-/

variable {p : ℕ}

/-- XOR-ing a byte with `255` is the byte complement. -/
theorem nat_xor_255 : ∀ n, n < 256 → Nat.xor n 255 = 255 - n := by
  set_option maxRecDepth 4000 in decide

/-- Does a payload match a pattern? Same length, and every constant pattern entry agrees. -/
def Matches (payload : List (ZMod p)) (pattern : List (Option (ZMod p))) : Prop :=
  payload.length = pattern.length ∧
  ∀ (slot : Nat) (c : ZMod p), pattern[slot]? = some (some c) → payload[slot]? = some c

/-- VM-neutral description of a bitwise / byte-lookup bus, hiding the payload layout so the
    byte-check and XOR passes work for any VM. `decode` / `encode` reorder between the physical
    payload and the logical tuple `(op, operand₁, operand₂, result)`, layout-generic in `α`. -/
structure ByteXorSpec (p : ℕ) where
  /-- Byte bound (`256`). -/
  bound : Nat
  /-- Op-selector value denoting the XOR relation `result = op₁ ⊕ op₂`. -/
  xorOp : ZMod p
  /-- Op-selector value denoting the pair range-check (`op₁, op₂` bytes, `result = 0`). -/
  pairOp : ZMod p
  /-- Op-selector for the bitwise-OR relation `result = op₁ | op₂`, or `none` if the bus has no OR
      op. Soundness lives in `BusFacts.byteBoolSound`. -/
  orOp : Option (ZMod p) := none
  /-- Op-selector for the bitwise-AND relation `result = op₁ & op₂`, or `none`. -/
  andOp : Option (ZMod p) := none
  /-- Reorder a physical payload into logical `(op, operand₁, operand₂, result)`. -/
  decode : {α : Type} → List α → Option (α × α × α × α)
  /-- Build a physical payload from logical `(op, o₁, o₂, r)`, inverting `decode`. -/
  encode : {α : Type} → α → α → α → α → List α
  /-- `decode` commutes with mapping. -/
  decode_map : ∀ {α β : Type} (f : α → β) (pl : List α),
    decode (pl.map f) = (decode pl).map (fun t => (f t.1, f t.2.1, f t.2.2.1, f t.2.2.2))
  /-- `decode`'s outputs are drawn from the physical payload, so they introduce no new variables. -/
  decode_mem : ∀ {α : Type} (pl : List α) (op o1 o2 r : α),
    decode pl = some (op, o1, o2, r) → o1 ∈ pl ∧ o2 ∈ pl ∧ r ∈ pl
  /-- `encode` inverts `decode`. -/
  decode_encode : ∀ {α : Type} (op o1 o2 r : α),
    decode (encode op o1 o2 r) = some (op, o1, o2, r)
  /-- A payload that decodes equals the re-encoding of its fields (`decode` is injective). -/
  decode_eq_encode : ∀ {α : Type} (pl : List α) (op o1 o2 r : α),
    decode pl = some (op, o1, o2, r) → pl = encode op o1 o2 r
  /-- `encode` commutes with mapping. -/
  encode_map : ∀ {α β : Type} (f : α → β) (op o1 o2 r : α),
    (encode op o1 o2 r).map f = encode (f op) (f o1) (f o2) (f r)
  /-- Every slot of an emitted payload is one of the logical fields. -/
  encode_mem : ∀ {α : Type} (op o1 o2 r x : α),
    x ∈ encode op o1 o2 r → x = op ∨ x = o1 ∨ x = o2 ∨ x = r
  /-- The field has nonzero characteristic (so `ZMod.val` is injective). -/
  pNeZero : NeZero p

/-- Proven, pass-consumable knowledge about the bus semantics `bs`. -/
structure BusFacts (p : ℕ) (bs : BusSemantics p) where
  /-- `slotBound busId mult pattern slot = some bound`: every accepted message on `busId` at
      multiplicity `mult` matching `pattern` has `payload[slot].val < bound`. The multiplicity lets
      a fact distinguish sends from receives. -/
  slotBound : (busId : Nat) → (mult : ZMod p) → (pattern : List (Option (ZMod p))) →
    (slot : Nat) → Option Nat
  slotBound_sound :
    ∀ (m : BusInteraction (ZMod p)) (pattern : List (Option (ZMod p))) (slot bound : Nat)
      (x : ZMod p),
      slotBound m.busId m.multiplicity pattern slot = some bound →
      Matches m.payload pattern →
      bs.violatesConstraint m = false →
      m.payload[slot]? = some x →
      x.val < bound
  /-- Functional dependence: for accepted messages matching `pattern`, `outSlot`'s value is `f` of
      the rest of the payload. `f` receives the payload with `outSlot` zeroed, so it cannot depend
      on the value it determines. -/
  slotFun : (busId : Nat) → (pattern : List (Option (ZMod p))) → (outSlot : Nat) →
    Option (List (ZMod p) → ZMod p)
  slotFun_sound :
    ∀ (m : BusInteraction (ZMod p)) (pattern : List (Option (ZMod p))) (outSlot : Nat)
      (f : List (ZMod p) → ZMod p) (z : ZMod p),
      slotFun m.busId pattern outSlot = some f →
      Matches m.payload pattern →
      bs.violatesConstraint m = false →
      m.payload[outSlot]? = some z →
      z = f (m.payload.set outSlot 0)
  /-- Buses whose messages never violate a constraint (e.g. stateful buses with no table). -/
  neverViolates : (busId : Nat) → Bool
  neverViolates_sound :
    ∀ (m : BusInteraction (ZMod p)),
      neverViolates m.busId = true → bs.violatesConstraint m = false
  /-- Last-write-wins shape declared for a bus, or `none` (see `ApcOptimizer/MemoryBus.lean`). -/
  memShape : (busId : Nat) → Option MemoryBusShape
  /-- Table obligations of a memory-style stateful bus, for pair cancellation:
      `recvByteSlots busId pattern = some (slots, bound)` asserts a `setNew` never violates, and a
      `getPrevious` matching `pattern` does not violate if every slot in `slots` holds a value
      `< bound` (the VM's declared word width — `256` for OpenVM, `2^16` for SP1). The pattern lets
      the obligation be conditional on constant slots; `some ([], _)` means "never violates". -/
  recvByteSlots : (busId : Nat) → (pattern : List (Option (ZMod p))) → Option (List Nat × Nat)
  recvByteSlots_sound :
    ∀ (busId : Nat) (shape : MemoryBusShape), memShape busId = some shape →
    ∀ (pattern : List (Option (ZMod p))) (slots : List Nat) (bound : Nat),
      recvByteSlots busId pattern = some (slots, bound) →
      ∀ (m : BusInteraction (ZMod p)), m.busId = busId →
        (m.multiplicity = shape.setNewMult → bs.violatesConstraint m = false) ∧
        (m.multiplicity = -shape.setNewMult → Matches m.payload pattern →
          (∀ slot ∈ slots, ∀ x : ZMod p, m.payload[slot]? = some x → x.val < bound) →
          bs.violatesConstraint m = false)
  /-- Every bus with a declared shape is stateful. -/
  memShape_stateful : ∀ (busId : Nat) (shape : MemoryBusShape),
    memShape busId = some shape → bs.isStateful busId = true
  /-- The VM's abstract `admissible` entails the concrete `admissibleMemoryBus` discipline on each
      declared bus's active messages. -/
  admissible_sound :
    ∀ (msgs : List (BusInteraction (ZMod p))),
      bs.admissible (msgs.filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) →
      ∀ (busId : Nat) (shape : MemoryBusShape), memShape busId = some shape →
        admissibleMemoryBus shape ((msgs.filter (fun m => m.busId = busId)).filter
          (fun m => decide (m.multiplicity ≠ 0)))
  /-- Reverse bridge for pair cancellation (completeness): dropping a matched, isolated
      send→receive pair from a declared bus preserves `admissible`, given no active same-address
      message between them and the *shield* condition on the before-region `A` (every active
      same-address send in `A` is followed by an active same-address receive in `A`). Follows from
      `admissibleMemoryBus_dropPair`. -/
  admissible_dropPair :
    (1 : ZMod p) ≠ 0 →
    ∀ (busId : Nat) (shape : MemoryBusShape), memShape busId = some shape →
    ∀ (A B C : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p)),
      S.busId = busId → R.busId = busId →
      S.multiplicity = shape.setNewMult → R.multiplicity = -shape.setNewMult →
      shape.address S = shape.address R →
      (∀ m ∈ B, m.busId = busId → m.multiplicity ≠ 0 → shape.address m = shape.address S → False) →
      (∀ (A₁ : List (BusInteraction (ZMod p))) (Sx : BusInteraction (ZMod p))
         (A₂ : List (BusInteraction (ZMod p))),
         A = A₁ ++ Sx :: A₂ → Sx.busId = busId → Sx.multiplicity ≠ 0 →
         shape.address Sx = shape.address S → Sx.multiplicity = shape.setNewMult →
         ∃ m ∈ A₂, m.busId = busId ∧ m.multiplicity ≠ 0 ∧ shape.address m = shape.address S ∧
           m.multiplicity = -shape.setNewMult) →
      bs.admissible (A ++ S :: B ++ R :: C) →
      bs.admissible (A ++ B ++ C)
  /-- Variable-range-checker stateless bus: `[x, b]` accepted iff
      `b.val ≤ 17 ∧ x.val < 2 ^ b.val`. -/
  varRangeBus : (busId : Nat) → Bool
  varRangeBus_sound :
    ∀ (busId : Nat), varRangeBus busId = true →
      bs.isStateful busId = false ∧
      ∀ (x b mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, b] }
            = false ↔ (b.val ≤ 17 ∧ x.val < 2 ^ b.val)
  /-- Tuple-range-checker stateless bus: `[x, y]` accepted iff `x.val < s1 ∧ y.val < s2`, and at
      multiplicity `1` breaks no invariant. -/
  tupleRangeBus : (busId : Nat) → Option (Nat × Nat)
  tupleRangeBus_sound :
    ∀ (busId s1 s2 : Nat), tupleRangeBus busId = some (s1, s2) →
      bs.isStateful busId = false ∧
      (∀ (x y : ZMod p),
        bs.breaksInvariant { busId := busId, multiplicity := 1, payload := [x, y] } = false) ∧
      ∀ (x y mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, y] }
            = false ↔ (x.val < s1 ∧ y.val < s2)
  /-- Real-trace fixed-zero cells (e.g. the RISC-V `x0` register):
      `zeroCell busId = some (addrReq, dataSlots)` asserts that on the stateful bus `busId`, every
      active message with `payload[s] = v` for each `(s, v) ∈ addrReq` carries `0` in every slot of
      `dataSlots`. A completeness-only (`admissible`) fact. -/
  zeroCell : (busId : Nat) → Option (List (Nat × ZMod p) × List Nat)
  zeroCell_sound :
    ∀ (msgs : List (BusInteraction (ZMod p))),
      bs.admissible (msgs.filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) →
      ∀ (busId : Nat) (addrReq : List (Nat × ZMod p)) (dataSlots : List Nat),
        zeroCell busId = some (addrReq, dataSlots) →
        ∀ m ∈ msgs, m.busId = busId → m.multiplicity ≠ 0 →
          (∀ ar ∈ addrReq, m.payload[ar.1]? = some ar.2) →
          ∀ slot ∈ dataSlots, ∀ v, m.payload[slot]? = some v → v = 0
  /-- Width-0 range equality: on a stateless bus, `[x, 0]` (multiplicity `1`) is accepted iff
      `x = 0` (a 0-bit range check, `x < 2⁰ = 1`). Lets a pass convert the interaction into the
      algebraic constraint `x = 0`. -/
  zeroRangeEq : (busId : Nat) → Bool
  zeroRangeEq_sound :
    ∀ (busId : Nat), zeroRangeEq busId = true →
      bs.isStateful busId = false ∧
      ∀ (x : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := 1, payload := [x, 0] } = false
          ↔ x = 0
  /-- VM-neutral bitwise/byte-lookup fact (`ByteXorSpec`): a payload decoding to `(op, o₁, o₂, r)`
      is accepted, when `op = xorOp`, iff `o₁, o₂` are bytes and `r = o₁ ⊕ o₂`; when `op = pairOp`,
      iff `o₁, o₂` are bytes and `r = 0`. Stateless and breaks no invariant at multiplicity `1`, so
      a pass may also emit a byte check via `spec.encode`. -/
  byteXorSpec : (busId : Nat) → Option (ByteXorSpec p)
  byteXorSpec_sound :
    ∀ (busId : Nat) (spec : ByteXorSpec p), byteXorSpec busId = some spec →
      bs.isStateful busId = false ∧
      (∀ (pl : List (ZMod p)),
        bs.breaksInvariant { busId := busId, multiplicity := 1, payload := pl } = false) ∧
      ∀ (pl : List (ZMod p)) (op o1 o2 r mult : ZMod p),
        spec.decode pl = some (op, o1, o2, r) →
        (op = spec.xorOp →
           (bs.violatesConstraint { busId := busId, multiplicity := mult, payload := pl } = false
             ↔ o1.val < spec.bound ∧ o2.val < spec.bound ∧ r.val = Nat.xor o1.val o2.val)) ∧
        (op = spec.pairOp →
           (bs.violatesConstraint { busId := busId, multiplicity := mult, payload := pl } = false
             ↔ o1.val < spec.bound ∧ o2.val < spec.bound ∧ r = 0))
  /-- Soundness of the optional `orOp`/`andOp` relations, for a payload decoding to
      `(op, o₁, o₂, r)`: when `op = orOp`, accepted iff `o₁, o₂` are bytes and `r = o₁ | o₂`; when
      `op = andOp`, iff `r = o₁ & o₂`. Vacuous where the op is `none`. -/
  byteBoolSound :
    ∀ (busId : Nat) (spec : ByteXorSpec p), byteXorSpec busId = some spec →
      ∀ (pl : List (ZMod p)) (op o1 o2 r mult : ZMod p),
        spec.decode pl = some (op, o1, o2, r) →
        (∀ oop, spec.orOp = some oop → op = oop →
           (bs.violatesConstraint { busId := busId, multiplicity := mult, payload := pl } = false
             ↔ o1.val < spec.bound ∧ o2.val < spec.bound ∧ r.val = Nat.lor o1.val o2.val)) ∧
        (∀ aop, spec.andOp = some aop → op = aop →
           (bs.violatesConstraint { busId := busId, multiplicity := mult, payload := pl } = false
             ↔ o1.val < spec.bound ∧ o2.val < spec.bound ∧ r.val = Nat.land o1.val o2.val))
  /-- A single-value range check at an arbitrary payload position:
      `rangeCheckAt busId pattern = some (valSlot, bound)` means every multiplicity-`1` message on
      `busId` matching `pattern` breaks no invariant and is accepted iff `payload[valSlot].val <
      bound`. -/
  rangeCheckAt : (busId : Nat) → (pattern : List (Option (ZMod p))) → Option (Nat × Nat)
  rangeCheckAt_sound :
    ∀ (busId : Nat) (pattern : List (Option (ZMod p))) (valSlot bound : Nat),
      rangeCheckAt busId pattern = some (valSlot, bound) →
      bs.isStateful busId = false ∧
      ∀ (m : BusInteraction (ZMod p)), m.busId = busId → m.multiplicity = 1 →
        Matches m.payload pattern →
        bs.breaksInvariant m = false ∧
        ∀ (x : ZMod p), m.payload[valSlot]? = some x →
          (bs.violatesConstraint m = false ↔ x.val < bound)

/-- The fact-free instance: claims nothing, exists for every semantics. -/
def BusFacts.trivial (bs : BusSemantics p) : BusFacts p bs where
  slotBound _ _ _ _ := none
  slotBound_sound := by intro _ _ _ _ _ h; exact absurd h (by simp)
  slotFun _ _ _ := none
  slotFun_sound := by intro _ _ _ _ _ h; exact absurd h (by simp)
  neverViolates _ := false
  neverViolates_sound := by intro _ h; exact absurd h (by simp)
  recvByteSlots _ _ := none
  recvByteSlots_sound := by intro _ _ h; exact absurd h (by simp)
  memShape _ := none
  memShape_stateful := by intro _ _ h; exact absurd h (by simp)
  admissible_sound := by intro _ _ _ _ h; exact absurd h (by simp)
  admissible_dropPair := by intro _ _ _ h; exact absurd h (by simp)
  varRangeBus _ := false
  varRangeBus_sound := by intro _ h; exact absurd h (by simp)
  tupleRangeBus _ := none
  tupleRangeBus_sound := by intro _ _ _ h; exact absurd h (by simp)
  zeroCell _ := none
  zeroCell_sound := by intro _ _ _ _ _ h; exact absurd h (by simp)
  zeroRangeEq _ := false
  zeroRangeEq_sound := by intro _ h; exact absurd h (by simp)
  byteXorSpec _ := none
  byteXorSpec_sound := by intro _ _ h; exact absurd h (by simp)
  byteBoolSound := by intro _ _ h; exact absurd h (by simp)
  rangeCheckAt _ _ := none
  rangeCheckAt_sound := by intro _ _ _ _ h; exact absurd h (by simp)
