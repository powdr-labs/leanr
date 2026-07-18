import ApcOptimizer.Spec
import ApcOptimizer.MemoryBus

set_option autoImplicit false

namespace ApcOptimizer.SP1

variable {p : ℕ}

/-- The SP1 bus types that appear in the default bus map. -/
inductive Sp1BusType where
  /-- The CPU state ("execution bridge"): an instruction receives the current `(clk, pc)` and
      sends the next one. Payload: `(clk... (2 fields), pc... (3 fields))`. -/
  | executionBridge
  /-- To access a memory cell, instructions send the previous record and receive the new one.
      Payload: `(clk... (2 fields), address... (3 limbs), data... (4 × 16-bit limbs))`. -/
  | memory
  /-- Program lookup: fetch the instruction at the current pc. Payload has 16 fields. -/
  | pcLookup
  /-- Byte lookup. Format `(op, a, b, c)`, where `op` selects the operation on bytes `b`, `c`:
      0 `AND` (`a = b & c`), 1 `OR`, 2 `XOR`, 3 `U8Range` (`a = 0`), 4 `LTU` (`a = [b < c]`),
      5 `MSB` (`a = b >> 7`, `c = 0`), 6 `Range` (`a < 2^b`, `c = 0`, `b ≤ 16`). -/
  | byteLookup
  /-- Instruction-fetch lookup (the untrusted instruction table). Payload has 22 fields. -/
  | instructionFetch
  /-- Page-protection lookup. Payload has 6 fields. -/
  | pageProt
  deriving Repr, DecidableEq

/-- A mapping from bus IDs to bus type. -/
abbrev BusMap := Nat → Option Sp1BusType

/-- A concrete bus map as parsed from a powdr export's `bus_map.bus_ids` field:
    an association list bus id ↦ bus type. -/
abbrev BusMapList := List (Nat × Sp1BusType)

/-- Convert a `BusMapList` to a `BusMap` lookup function. -/
def BusMapList.toBusMap (busMap : BusMapList) : BusMap :=
  fun busId => busMap.lookup busId

/-- The hard-coded default SP1 bus map, mirroring powdr's `sp1_bus_map`. -/
def defaultBusMap : BusMap
  | 1 => some .memory
  | 2 => some .pcLookup
  | 5 => some .byteLookup
  | 7 => some .executionBridge
  | 16 => some .instructionFetch
  | 18 => some .pageProt
  | _ => none

/-- Stateful buses are the execution bridge and memory; the rest are stateless lookups. -/
def Sp1BusType.isStateful : Sp1BusType → Bool
  | .executionBridge => true
  | .memory => true
  | .pcLookup => false
  | .byteLookup => false
  | .instructionFetch => false
  | .pageProt => false

/-- Whether a field element is a byte (`0 ≤ x < 256`). -/
def isByte (x : ZMod p) : Bool := decide (x.val < 256)

/-- Whether a field element is a 16-bit limb (`0 ≤ x < 2^16`). -/
def is16Bit (x : ZMod p) : Bool := decide (x.val < 2 ^ 16)

/-- Whether a message conflicts with the lookup table of the bus it is sent on. -/
def violates (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Bool :=
  match busMap msg.busId, msg.payload with
  -- As for OpenVM's PC lookup, we only check the arity of these lookups: the input circuit has
  -- already fixed the looked-up fields to constants, so the optimizer cannot change them.
  | some .pcLookup, args => !decide (args.length = 16)
  | some .instructionFetch, args => !decide (args.length = 22)
  | some .pageProt, args => !decide (args.length = 6)

  | some .byteLookup, [op, a, b, c] =>
    match op.val with
    -- AND: range check b, c to be bytes; a must be b & c.
    | 0 => !(isByte b && isByte c && decide (a.val = Nat.land b.val c.val))
    -- OR: a must be b | c.
    | 1 => !(isByte b && isByte c && decide (a.val = Nat.lor b.val c.val))
    -- XOR: a must be b ^ c.
    | 2 => !(isByte b && isByte c && decide (a.val = Nat.xor b.val c.val))
    -- U8Range: range check b, c to be bytes; a must be 0.
    | 3 => !(isByte b && isByte c && decide (a.val = 0))
    -- LTU: a must be 1 if b < c, else 0.
    | 4 => !(isByte b && isByte c && decide (a.val = if b.val < c.val then 1 else 0))
    -- MSB: a must be the top bit of the byte b, and c must be 0.
    | 5 => !(isByte b && decide (c.val = 0) && decide (a.val = b.val >>> 7))
    -- Range: check that a < 2^b, that c = 0, and that b ≤ 16 (the largest width the table holds).
    | 6 => !(decide (b.val ≤ 16) && decide (c.val = 0) && decide (a.val < 2 ^ b.val))
    -- Other ops are invalid.
    | _ => true
  | some .byteLookup, _ => true

  -- Stateful buses.
  | some .executionBridge, _ => false

  -- In SP1, the invariant is that memory data limbs are 16-bit range-checked. A *send*
  -- (multiplicity 1) reads the previous record, so its data must be 16-bit. The payload is
  -- `(clk, clk, address, address, address, data, data, data, data)`.
  | some .memory, _ :: _ :: _ :: _ :: _ :: d0 :: d1 :: d2 :: d3 :: _ =>
    decide (msg.multiplicity = 1) && !([d0, d1, d2, d3].all is16Bit)
  | some .memory, _ => false

  -- Invalid bus ID. Won't have a matching receive.
  | none, _ => true

/-- Whether a message breaks an invariant on which soundness depends. -/
def breaksInvariant (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Bool :=
  -- Note that this function is not called for multiplicity = 0
  match busMap msg.busId with
  -- Lookups are only ever sent (multiplicity 1).
  | some .pcLookup | some .byteLookup | some .instructionFetch | some .pageProt =>
    !decide (msg.multiplicity = 1)
  -- The execution bridge is stateful: it is sent (1) or received (-1).
  | some .executionBridge =>
    !decide (msg.multiplicity = 1 ∨ msg.multiplicity = -1)
  -- Memory is stateful (multiplicity 1 or -1), and additionally maintains the invariant that its
  -- data limbs are 16-bit range. The payload is `(clk, clk, address×3, data×4)`.
  | some .memory =>
    !decide (msg.multiplicity = 1 ∨ msg.multiplicity = -1) ||
    (match msg.payload with
      | _ :: _ :: _ :: _ :: _ :: d0 :: d1 :: d2 :: d3 :: _ =>
        !([d0, d1, d2, d3].all is16Bit)
      | _ => false)
  -- Circuits should not send messages to an unknown bus.
  | none => true

/-- Assume that reading register `x0` (address `0`) always returns `0`. This should be enforced
    globally by all SP1 chips. -/
def x0ReturnsZero (busMap : BusMap) (msgs : List (BusInteraction (ZMod p))) : Prop :=
  ∀ m ∈ msgs, busMap m.busId = some .memory →
    -- If all three address limbs are 0 (register x0), then the four data limbs must be 0.
    m.payload[2]? = some 0 → m.payload[3]? = some 0 → m.payload[4]? = some 0 →
      m.payload[5]? = some 0 ∧ m.payload[6]? = some 0 ∧
        m.payload[7]? = some 0 ∧ m.payload[8]? = some 0

/-- Maps a bus ID to its memory bus shape, if applicable. For SP1 *memory*, the `getPrevious` sends
    the previous record and the `setNew` receives the new one, so `direction := .sendThenReceive`
    (`setNewMult = -1`) — the reverse of OpenVM. The *execution bridge* is different: like every VM's,
    an instruction sends the next CPU state and receives the current one, so its `setNew` (the next
    state) is the send — `direction := .receiveThenSend` (`setNewMult = 1`), matching OpenVM's
    execution bridge and OpenVM memory, *not* SP1 memory. -/
def memShapeOf (busMap : BusMap) (busId : Nat) : Option MemoryBusShape :=
  match busMap busId with
  -- The *actual* memory bus, with the three address limbs in payload slots 2, 3 and 4.
  | some .memory => some { addressFields := [2, 3, 4], direction := .sendThenReceive }
  -- The execution bridge is a single-global-cell (address `[]`) memory bus that sends the *next*
  -- CPU state. As in OpenVM, this makes completeness partial: we assume the prover always proves
  -- consecutive cycles.
  | some .executionBridge => some { addressFields := [], direction := .receiveThenSend }
  | _ => none

/-- The SP1 bus semantics for a given bus map (default: the hard-coded default bus map). -/
def sp1BusSemantics (p : ℕ) (busMap : BusMap := defaultBusMap) :
    BusSemantics p where
  isStateful busId :=
    match busMap busId with
    | some t => t.isStateful
    | none => false
  violatesConstraint := violates busMap
  breaksInvariant := breaksInvariant busMap
  -- The memory discipline, per declared bus. On SP1 *memory* the `setNew` multiplicity is `-1`
  -- (`direction := .sendThenReceive`); on the *execution bridge* it is `1` (`.receiveThenSend`, which
  -- sends the next CPU state). Either way `admissibleMemoryBus` pairs each `setNew` with the next
  -- same-address `getPrevious` directly in list order.
  admissible msgs :=
    (∀ (busId : Nat) (shape : MemoryBusShape), memShapeOf busMap busId = some shape →
      admissibleMemoryBus shape (msgs.filter (fun m => m.busId = busId)))
    ∧ x0ReturnsZero busMap msgs

/-- SP1's proving-backend degree bound (powdr's `DEFAULT_DEGREE_BOUND` for SP1), used when the
    optimizer is run directly rather than with a bound passed in over the FFI. -/
def defaultDegreeBound : DegreeBound := { identities := 3, busInteractions := 1 }

/-- The KoalaBear field modulus, `2^31 - 2^24 + 1` — the field all powdr SP1 exports use. -/
def koalaBear : Nat := 2130706433

instance : NeZero koalaBear := ⟨by decide⟩

end ApcOptimizer.SP1
