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

/-- Does a payload match a pattern? Same length, and every constant pattern entry agrees. -/
def Matches (payload : List (ZMod p)) (pattern : List (Option (ZMod p))) : Prop :=
  payload.length = pattern.length ∧
  ∀ (slot : Nat) (c : ZMod p), pattern[slot]? = some (some c) → payload[slot]? = some c

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
  /-- Send/receive table obligations of a memory-style stateful bus, for pair cancellation:
      `recvByteSlots busId pattern = some slots` asserts that a *send* (multiplicity `1`) on
      `busId` never violates a constraint (regardless of the pattern), and a *receive*
      (multiplicity `-1`) whose payload matches `pattern` does not violate provided every payload
      slot listed in `slots` (where present) holds a value `< 256`. The pattern lets a fact make
      the receive obligation conditional on constant payload entries — e.g. a memory receive
      whose address-space slot is a known constant ∉ {1,2} carries *no* byte obligation
      (`slots = []`), because the VM's `violates` only rejects non-byte data on address spaces
      1/2. `some []` is "this receive (and every send) never violates"; `none` claims nothing.
      Pattern-blind facts simply ignore the argument. -/
  recvByteSlots : (busId : Nat) → (pattern : List (Option (ZMod p))) → Option (List Nat)
  recvByteSlots_sound :
    ∀ (busId : Nat) (pattern : List (Option (ZMod p))) (slots : List Nat),
      recvByteSlots busId pattern = some slots →
      ∀ (m : BusInteraction (ZMod p)), m.busId = busId →
        (m.multiplicity = 1 → bs.violatesConstraint m = false) ∧
        (m.multiplicity = -1 → Matches m.payload pattern →
          (∀ slot ∈ slots, ∀ x : ZMod p, m.payload[slot]? = some x → x.val < 256) →
          bs.violatesConstraint m = false)
  /-- The last-write-wins shape declared for a bus, or `none`. Passes read `addressFields` to
      group same-address accesses; this is the VM-side memory knowledge (`ApcOptimizer/MemoryBus.lean`)
      the spec's abstract `admissible` predicate deliberately omits. -/
  memShape : (busId : Nat) → Option MemoryBusShape
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
      S.multiplicity = 1 → R.multiplicity = -1 →
      shape.address S = shape.address R →
      (∀ m ∈ B, m.busId = busId → m.multiplicity ≠ 0 → shape.address m = shape.address S → False) →
      (∀ (A₁ : List (BusInteraction (ZMod p))) (Sx : BusInteraction (ZMod p))
         (A₂ : List (BusInteraction (ZMod p))),
         A = A₁ ++ Sx :: A₂ → Sx.busId = busId → Sx.multiplicity ≠ 0 →
         shape.address Sx = shape.address S → Sx.multiplicity = 1 →
         ∃ m ∈ A₂, m.busId = busId ∧ m.multiplicity ≠ 0 ∧ shape.address m = shape.address S ∧
           m.multiplicity = -1) →
      bs.admissible (A ++ S :: B ++ R :: C) →
      bs.admissible (A ++ B ++ C)
  /-- Byte-check pairing on a bitwise-style *stateless* bus. If `bytePairBus busId = true` then the
      bus is stateless and, for every pair of operand values and any multiplicity, the pair-check
      message `[x, y, 0, 0]` is accepted exactly when the two single-value checks `[x, x, 0, 1]` and
      `[y, y, 0, 1]` are. So two single-value byte checks pack losslessly into one pair check, with
      the *same* satisfying set (each side imposes "both operands are bytes") — a bus-interaction
      win. `trivial` sets it `false` (recovering fact-free behavior); the OpenVM instance proves it
      for the bitwise-lookup bus against the concrete table (see `ApcOptimizer/Implementation/OpenVmFacts.lean`). -/
  bytePairBus : (busId : Nat) → Bool
  bytePairBus_sound :
    ∀ (busId : Nat), bytePairBus busId = true →
      bs.isStateful busId = false ∧
      (∀ (x y : ZMod p),
        bs.breaksInvariant { busId := busId, multiplicity := 1, payload := [x, y, 0, 0] } = false) ∧
      ∀ (x y mult : ZMod p),
        (bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, y, 0, 0] }
            = false ↔
          bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, x, 0, 1] }
              = false ∧
            bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [y, y, 0, 1] }
              = false)
  /-- Byte-check *emission* on a stateless bitwise-style bus: the self-check `[x, x, 0, 1]`
      (multiplicity 1) never breaks an invariant and is accepted **iff** `x` is a byte. This is
      the absolute counterpart of `bytePairBus`'s relative pairing law: it lets a pass
      materialize a proven byte obligation as an explicit check — e.g. when cancelling a memory
      send/receive pair whose receive carried the only byte guarantee for a data limb.
      `trivial` sets it `false`. -/
  byteCheck : (busId : Nat) → Bool
  byteCheck_sound :
    ∀ (busId : Nat), byteCheck busId = true →
      bs.isStateful busId = false ∧
      (∀ (x : ZMod p),
        bs.breaksInvariant { busId := busId, multiplicity := 1, payload := [x, x, 0, 1] } = false) ∧
      ∀ (x mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, x, 0, 1] }
            = false ↔ x.val < 256
  /-- Byte-check *via XOR-with-zero*: on a stateless bitwise-style bus the checks `[x, 0, x, 1]`
      (`x ⊕ 0 = x`) and its mirror `[0, x, x, 1]` (`0 ⊕ x = x`) — multiplicity any — are each
      accepted **iff** `x` is a byte. The XOR-with-zero encoding is how OpenVM materializes a bare
      "this operand is a byte" obligation that was not packed into a pair; the zero can sit in
      *either* operand slot (`Nat.xor_zero` / `Nat.zero_xor`). Recognising both mirrors lets the
      redundant-byte-check dropper and the byte-check packer reach every such interaction.
      `trivial` sets it `false`. -/
  xorZeroCheck : (busId : Nat) → Bool
  xorZeroCheck_sound :
    ∀ (busId : Nat), xorZeroCheck busId = true →
      bs.isStateful busId = false ∧
      (∀ (x mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, 0, x, 1] }
            = false ↔ x.val < 256) ∧
      (∀ (x mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [0, x, x, 1] }
            = false ↔ x.val < 256)
  /-- Variable-range-checker style *stateless* bus: the 2-ary message `[x, b]` is accepted
      **iff** the requested width is supported and `x` fits (`b.val ≤ 25 ∧ x.val < 2 ^ b.val`).
      `trivial` sets it `false`; the OpenVM instance proves it for the variable range checker. -/
  varRangeBus : (busId : Nat) → Bool
  varRangeBus_sound :
    ∀ (busId : Nat), varRangeBus busId = true →
      bs.isStateful busId = false ∧
      ∀ (x b mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, b] }
            = false ↔ (b.val ≤ 25 ∧ x.val < 2 ^ b.val)
  /-- On a `varRangeBus` bus, whether a message breaks an invariant depends only on its
      multiplicity, never on its payload. Lets a pass *add* a range check whose multiplicity
      expression matches an existing check's: the new message inherits the old one's
      (non-)breaking status. `trivial` discharges it vacuously (`varRangeBus` is `false`). -/
  varRangeBusInv_sound :
    ∀ (busId : Nat), varRangeBus busId = true →
      ∀ (x b x' b' mult : ZMod p),
        bs.breaksInvariant { busId := busId, multiplicity := mult, payload := [x, b] }
          = bs.breaksInvariant { busId := busId, multiplicity := mult, payload := [x', b'] }
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
  /-- Bitwise XOR-with-zero equality: on a bitwise-style bus where an accepted multiplicity-1
      message `[a, b, c, 1]` asserts `c = a ⊕ b`, a zero operand linearizes the XOR to an equality —
      `[0, y, z, 1]` accepted ⟹ `z = y`, and `[x, 0, z, 1]` accepted ⟹ `z = x`. apc keeps these
      equalities on the bus, so Gaussian elimination never uses them to eliminate the intermediate
      byte the identity pins. Recognising them lets a pass add the entailed equality (keeping the
      interaction, which still imposes byte-ness) for Gauss to consume. `trivial` sets it `false`. -/
  xorZeroEq : (busId : Nat) → Bool
  xorZeroEq_sound :
    ∀ (busId : Nat), xorZeroEq busId = true →
      (∀ (y z : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := 1, payload := [0, y, z, 1] }
          = false → z = y) ∧
      (∀ (x z : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := 1, payload := [x, 0, z, 1] }
          = false → z = x)
  /-- Bitwise XOR-with-255 (byte complement): the sibling of `xorZeroEq`. On the same bitwise bus
      where an accepted multiplicity-1 `[a, b, c, 1]` asserts `c = a ⊕ b` with byte operands, an
      operand pinned to the all-ones byte `255` linearizes the XOR to the byte **complement** —
      `[x, 255, z, 1]` accepted ⟹ `z = 255 − x`, and `[255, y, z, 1]` accepted ⟹ `z = 255 − y`
      (`n ⊕ 255 = 255 − n` for a byte `n`). Together with `xorZeroEq` (operand 0 ⟹ identity) these
      are exactly the two constant operands for which the XOR is *affine* in the other operand, so
      Gauss can eliminate the pinned NOT-result — apc otherwise keeps these complement equalities
      only on the bus. Sound only when `255` is a genuine byte of the field (`256 ≤ p`); a small
      field, and `trivial`, set it `false`. -/
  xorComplEq : (busId : Nat) → Bool
  xorComplEq_sound :
    ∀ (busId : Nat), xorComplEq busId = true →
      (∀ (x z : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := 1, payload := [x, 255, z, 1] }
          = false → z = 255 - x) ∧
      (∀ (y z : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := 1, payload := [255, y, z, 1] }
          = false → z = 255 - y)
  /-- Byte-check *via XOR-with-255* (the NOT form): the sibling of `xorZeroCheck`. On a stateless
      bitwise-style bus the checks `[x, 255, 255 − x, 1]` (`x ⊕ 255 = 255 − x`) and its mirror
      `[255, x, 255 − x, 1]` — multiplicity any — are each accepted **iff** `x` is a byte. After
      `xorEqExtractPass` (C4b) linearizes a `255`-operand XOR and Gauss substitutes the NOT-result
      `z := 255 − x`, exactly this shape is left on the bus; its sole obligation is "`x` is a byte"
      (the third slot being `255 − x` is then vacuous), so the redundant-byte-check dropper and the
      byte-check packer should treat it as a single-value byte check on `x`. Sound only when `255`
      is a genuine byte of the field (`256 ≤ p`); a small field, and `trivial`, set it `false`. -/
  xorComplCheck : (busId : Nat) → Bool
  xorComplCheck_sound :
    ∀ (busId : Nat), xorComplCheck busId = true →
      bs.isStateful busId = false ∧
      (∀ (x mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, 255, 255 - x, 1] }
            = false ↔ x.val < 256) ∧
      (∀ (x mult : ZMod p),
        bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [255, x, 255 - x, 1] }
            = false ↔ x.val < 256)

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
  recvByteSlots_sound := by intro _ _ _ h; exact absurd h (by simp)
  memShape _ := none
  memShape_stateful := by intro _ _ h; exact absurd h (by simp)
  admissible_sound := by intro _ _ _ _ h; exact absurd h (by simp)
  admissible_dropPair := by intro _ _ _ h; exact absurd h (by simp)
  bytePairBus _ := false
  bytePairBus_sound := by intro _ h; exact absurd h (by simp)
  byteCheck _ := false
  byteCheck_sound := by intro _ h; exact absurd h (by simp)
  xorZeroCheck _ := false
  xorZeroCheck_sound := by intro _ h; exact absurd h (by simp)
  varRangeBus _ := false
  varRangeBus_sound := by intro _ h; exact absurd h (by simp)
  varRangeBusInv_sound := by intro _ h; exact absurd h (by simp)
  tupleRangeBus _ := none
  tupleRangeBus_sound := by intro _ _ _ h; exact absurd h (by simp)
  zeroCell _ := none
  zeroCell_sound := by intro _ _ _ _ _ h; exact absurd h (by simp)
  zeroRangeEq _ := false
  zeroRangeEq_sound := by intro _ h; exact absurd h (by simp)
  xorZeroEq _ := false
  xorZeroEq_sound := by intro _ h; exact absurd h (by simp)
  xorComplEq _ := false
  xorComplEq_sound := by intro _ h; exact absurd h (by simp)
  xorComplCheck _ := false
  xorComplCheck_sound := by intro _ h; exact absurd h (by simp)
