import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Proven auxiliary knowledge about a bus semantics

`BusSemantics` exposes its lookup tables only through the opaque `violatesConstraint`, so a
generic optimizer cannot learn facts like "this bus range-checks its first payload entry"
without probing the whole field. `BusFacts` is the sound channel for that knowledge: a
structure *dependent on the semantics* in which every claim carries a proof against it — the
kernel checks the facts, so supplying them adds **nothing** to the audit surface, and a pass
consuming them stays correct for arbitrary semantics (with `BusFacts.trivial` it degrades to
the fact-free behavior).

A *pattern* is a payload template: `some c` entries must equal the evaluated message's entry,
`none` entries are free. Passes build patterns from the constant entries of a concrete
interaction, so facts can be conditional on e.g. an op-selector slot (see `ApcOptimizer/Implementation/OpenVmFacts.lean`).
-/

variable {p : ℕ}

/-- XOR-ing a byte with the all-ones byte `255` is the byte complement. The 256-case `decide` is a
    one-shot kernel check (no runtime cost). Shared by the VM byte-bus fact instances and the
    byte-check / XOR passes. -/
theorem nat_xor_255 : ∀ n, n < 256 → Nat.xor n 255 = 255 - n := by
  set_option maxRecDepth 4000 in decide

/-- Does a payload match a pattern? Same length, and every constant pattern entry agrees. -/
def Matches (payload : List (ZMod p)) (pattern : List (Option (ZMod p))) : Prop :=
  payload.length = pattern.length ∧
  ∀ (slot : Nat) (c : ZMod p), pattern[slot]? = some (some c) → payload[slot]? = some c

/-- **VM-neutral description of a bitwise / byte-lookup bus**, hiding the payload *layout* so the
    byte-check and XOR passes work for any VM. `decode` reorders a physical 4-element payload into
    the logical tuple `(op, operand₁, operand₂, result)` — OpenVM's `[x, y, z, op]` decodes to
    `(op, x, y, z)`, SP1's `[op, a, b, c]` to `(op, b, c, a)`. `xorOp` / `pairOp` are the op-selector
    values for the two affine relations the passes exploit: the XOR relation `result = op₁ ⊕ op₂`
    (both operands bytes) and the pair range-check (`op₁, op₂` bytes, `result = 0`). `bound` is the
    byte bound (`256`). Being layout-generic in `α`, the same `decode` serves both the `ZMod`-level
    soundness and the `Expression`-level pass recognizers. -/
structure ByteXorSpec (p : ℕ) where
  /-- Byte bound (`256`). -/
  bound : Nat
  /-- Op-selector value denoting the XOR relation `result = op₁ ⊕ op₂`. -/
  xorOp : ZMod p
  /-- Op-selector value denoting the pair range-check (`op₁, op₂` bytes, `result = 0`). -/
  pairOp : ZMod p
  /-- Reorder a physical payload into logical `(op, operand₁, operand₂, result)`. -/
  decode : {α : Type} → List α → Option (α × α × α × α)
  /-- Build a physical payload from logical `(op, operand₁, operand₂, result)` — the inverse
      reordering of `decode`. Lets a pass *emit* a byte check in the VM's own layout without
      knowing it (OpenVM `[o₁, o₂, r, op]`, SP1 `[op, o₁, o₂, r]`). -/
  encode : {α : Type} → α → α → α → α → List α
  /-- `decode` is a pure reordering, so it commutes with mapping — this transports a decode of a
      syntactic (`Expression`) payload to a decode of its evaluation. -/
  decode_map : ∀ {α β : Type} (f : α → β) (pl : List α),
    decode (pl.map f) = (decode pl).map (fun t => (f t.1, f t.2.1, f t.2.2.1, f t.2.2.2))
  /-- `decode`'s logical operands and result are drawn from the physical payload (it reorders),
      so a pass adding a constraint from them introduces no new variables. -/
  decode_mem : ∀ {α : Type} (pl : List α) (op o1 o2 r : α),
    decode pl = some (op, o1, o2, r) → o1 ∈ pl ∧ o2 ∈ pl ∧ r ∈ pl
  /-- `encode` inverts `decode`: an emitted payload decodes back to its logical fields. -/
  decode_encode : ∀ {α : Type} (op o1 o2 r : α),
    decode (encode op o1 o2 r) = some (op, o1, o2, r)
  /-- `decode` recovers the payload (it is injective on decodable payloads): a payload that decodes
      equals the re-encoding of its fields. Lets a pass reconstruct a recognized interaction as an
      `encode`-built one. -/
  decode_eq_encode : ∀ {α : Type} (pl : List α) (op o1 o2 r : α),
    decode pl = some (op, o1, o2, r) → pl = encode op o1 o2 r
  /-- `encode` is a pure reordering, so it commutes with mapping — this evaluates an emitted
      syntactic payload slot-by-slot. -/
  encode_map : ∀ {α β : Type} (f : α → β) (op o1 o2 r : α),
    (encode op o1 o2 r).map f = encode (f op) (f o1) (f o2) (f r)
  /-- Every slot of an emitted payload is one of the logical fields (it reorders), so an emitted
      byte check introduces no variables beyond those of its operands. -/
  encode_mem : ∀ {α : Type} (op o1 o2 r x : α),
    x ∈ encode op o1 o2 r → x = op ∨ x = o1 ∨ x = o2 ∨ x = r
  /-- A byte bus lives in a field of nonzero characteristic (`ZMod.val` is then injective), which a
      generic pass needs to lift the value-level XOR relation to a field equality. The VM instances
      carry `[NeZero p]`, so they discharge this by `inferInstance`. -/
  pNeZero : NeZero p

/-- Proven, pass-consumable knowledge about the bus semantics `bs`. -/
structure BusFacts (p : ℕ) (bs : BusSemantics p) where
  /-- Accepted-value bound for one payload slot of messages matching a pattern:
      `slotBound busId mult pattern slot = some bound` means every *accepted* message on `busId`
      with multiplicity `mult` matching `pattern` has `payload[slot].val < bound`. The
      multiplicity lets a fact distinguish sends from receives (e.g. only memory *receives*
      carry the byte guarantee); multiplicity-blind facts simply ignore it. -/
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
  /-- Functional dependence: for accepted messages matching the pattern, the value in
      `outSlot` is determined by the rest of the payload via the computable `f`. `f` receives
      the payload with `outSlot` zeroed out, so it provably cannot depend on the value it
      determines — which is what lets a pass *probe* `f` on candidate inputs. -/
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
  /-- The last-write-wins shape declared for a bus, or `none`. Passes read `addressFields` to
      group same-address accesses; this is the VM-side memory knowledge (`ApcOptimizer/MemoryBus.lean`)
      the spec's abstract `admissible` predicate deliberately omits. -/
  memShape : (busId : Nat) → Option MemoryBusShape
  /-- Send/receive table obligations of a memory-style stateful bus, for pair cancellation:
      `recvByteSlots busId pattern = some (slots, bound)` asserts that a `setNew` (multiplicity
      `shape.setNewMult`, per the bus's `memShape`) never violates, and a `getPrevious` (multiplicity
      `-shape.setNewMult`) whose payload matches `pattern` does not violate provided every payload
      slot listed in `slots` (where present) holds a value `< bound`. The `bound` is the VM's
      declared word width for those slots — `256` for a byte-limbed memory (OpenVM), `2^16` for a
      16-bit-limbed memory (SP1) — so the fact is not tied to a single VM's limb size. The pattern
      lets a fact make the `getPrevious` obligation conditional on constant payload entries — e.g. a
      memory `getPrevious` whose address-space slot is a known constant ∉ {1,2} carries *no*
      obligation (`slots = []`), because the VM's `violates` only rejects out-of-range data on
      address spaces 1/2. `some ([], _)` is "this `getPrevious` (and every `setNew`) never
      violates"; `none` claims nothing. Pattern-blind facts simply ignore the argument. -/
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
  /-- Every bus with a declared shape is stateful — so its messages survive the active∧stateful
      filter that `ConstraintSystem.admissible` applies before consulting `bs.admissible`. -/
  memShape_stateful : ∀ (busId : Nat) (shape : MemoryBusShape),
    memShape busId = some shape → bs.isStateful busId = true
  /-- The VM's abstract `admissible` predicate entails the concrete consecutive-match discipline
      (`admissibleMemoryBus`) on each declared bus's active messages. For a VM whose `admissible` *is*
      that per-bus conjunction (see `ApcOptimizer/Implementation/OpenVmFacts.lean`) this is essentially
      definitional. -/
  admissible_sound :
    ∀ (msgs : List (BusInteraction (ZMod p))),
      bs.admissible (msgs.filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) →
      ∀ (busId : Nat) (shape : MemoryBusShape), memShape busId = some shape →
        admissibleMemoryBus shape ((msgs.filter (fun m => m.busId = busId)).filter
          (fun m => decide (m.multiplicity ≠ 0)))
  /-- Reverse bridge for pair cancellation (the completeness half). Dropping a matched, isolated
      send→receive pair from a declared bus preserves `admissible`: given a send `S` and a later
      receive `R` on `busId` with equal addresses, no active same-address message between them
      (`B`), and the *shield* condition on `A` — every active same-address send in `A` is followed
      by an active same-address receive in `A` (strictly weaker than "no active same-address send
      in `A`") — removing both from the active-stateful message list keeps it admissible. Gated on
      `memShape busId = some shape`, so `trivial` (no shapes) discharges it vacuously; for a VM
      whose `admissible` is the per-bus `admissibleMemoryBus` conjunction it follows from
      `admissibleMemoryBus_dropPair`. Takes `1 ≠ 0` (the pass supplies it; the degenerate `ZMod 1`
      is then out of the way). -/
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
  /-- Variable-range-checker style *stateless* bus: the 2-ary message `[x, b]` is accepted
      **iff** the requested width is supported and `x` fits (`b.val ≤ 17 ∧ x.val < 2 ^ b.val`).
      `trivial` sets it `false`; the OpenVM instance proves it for the variable range checker. -/
  varRangeBus : (busId : Nat) → Bool
  varRangeBus_sound :
    ∀ (busId : Nat), varRangeBus busId = true →
      bs.isStateful busId = false ∧
      ∀ (x b mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, b] }
            = false ↔ (b.val ≤ 17 ∧ x.val < 2 ^ b.val)
  /-- Tuple-range-checker style *stateless* bus with fixed sizes: the 2-ary message `[x, y]` is
      accepted **iff** `x.val < s1 ∧ y.val < s2`, and at multiplicity `1` it never breaks an
      invariant. Lets a pass pack a byte obligation (`s1 = 256`) and an exact-width range check
      (`2 ^ bits = s2`) into a single interaction. `trivial` declares none. -/
  tupleRangeBus : (busId : Nat) → Option (Nat × Nat)
  tupleRangeBus_sound :
    ∀ (busId s1 s2 : Nat), tupleRangeBus busId = some (s1, s2) →
      bs.isStateful busId = false ∧
      (∀ (x y : ZMod p),
        bs.breaksInvariant { busId := busId, multiplicity := 1, payload := [x, y] } = false) ∧
      ∀ (x y mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, y] }
            = false ↔ (x.val < s1 ∧ y.val < s2)
  /-- Real-trace fixed-zero cells (e.g. the hardwired RISC-V `x0` register).
      `zeroCell busId = some (addrReq, dataSlots)` asserts that on the (stateful) bus `busId`, every
      *active* message whose payload has `payload[s] = v` for each `(s, v) ∈ addrReq` carries value
      `0` in every slot of `dataSlots`. Like the memory discipline this is a completeness-only
      (`admissible`) fact — `trivial` declares none, so it discharges vacuously and a consuming pass
      degrades to a no-op. -/
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
  /-- Width-0 range equality: on a **stateless** bus, the range-check message `[x, 0]`
      (multiplicity `1`) is accepted **iff** `x = 0`. A 0-bit range check asserts `x < 2⁰ = 1`,
      i.e. `x = 0`; this is the "assert this linear form is zero" encoding OpenVM emits as a 0-bit
      range check. Recognising it lets a pass convert such a stateless interaction into the
      algebraic constraint `x = 0`, which Gaussian elimination can then consume — turning a bus
      interaction into a variable-eliminating equality. `trivial` sets it `false`. -/
  zeroRangeEq : (busId : Nat) → Bool
  zeroRangeEq_sound :
    ∀ (busId : Nat), zeroRangeEq busId = true →
      bs.isStateful busId = false ∧
      ∀ (x : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := 1, payload := [x, 0] } = false
          ↔ x = 0
  /-- **VM-neutral bitwise/byte-lookup fact** (`ByteXorSpec`): the layout-hiding replacement the
      byte-check and XOR passes consume through a shared recognizer/builder. For a bus with a
      `ByteXorSpec`, a payload decoding to `(op, o₁, o₂, r)` is accepted, when `op = xorOp`, exactly
      when `o₁, o₂` are bytes and `r = o₁ ⊕ o₂`; and when `op = pairOp`, exactly when `o₁, o₂` are
      bytes and `r = 0`. The bus is stateless and, at multiplicity `1`, breaks no invariant — so a
      pass may also *emit* a byte check (via `spec.encode`) as a genuine interaction. OpenVM provides
      it for the bitwise-lookup bus, SP1 for the byte-lookup bus; `trivial` declares none. -/
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

/-- The fact-free instance: claims nothing, exists for every semantics. Declares no memory
    shapes, so the memory/exec unify passes degrade to no-ops. -/
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
