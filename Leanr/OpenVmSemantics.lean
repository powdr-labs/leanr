import Leanr.Spec
import Leanr.MemoryBus

set_option autoImplicit false

namespace Leanr.OpenVM

variable {p : ℕ}

/-- The OpenVM bus types that appear in the default bus map. -/
inductive OpenVmBusType where
  /-- A instruction should receive a `(pc, timestamp)` and send updated values to the bus. -/
  | executionBridge
  /-- To access a memory cell, instructions should:
      1. Receive a `(address_space, pointer, data... (4 bytes), prev_timestamp)` tuple
      2. Send a `(address_space, pointer, data... (4 bytes), current_timestamp)` tuple. -/
  | memory
  /-- Lookup to get the instruction flags from the current pc. Format: `(pc, flags...)` -/
  | pcLookup
  /-- Check that a value is in a certain range. Format: `(value, bits)` -/
  | variableRangeChecker
  /-- Check that a value is in a certain range. Format: `(x, y, z, op)` where `op` is either
      0 (range check) or 1 (xor). The bus checks that `x` and `y` are bytes, and either
      `op = 0 ∧ z = 0` (range check) or `op = 1 ∧ z = x ^ y` (xor). -/
  | bitwiseLookup
  /-- Check that a tuple of two values is in a certain range. Format: `(x, y)` where
      `x < size1` and `y < size2`. -/
  | tupleRangeChecker (size1 size2 : Nat)
  deriving Repr, DecidableEq

/-- A mapping from bus IDs to bus type. -/
abbrev BusMap := Nat → Option OpenVmBusType

/-- A concrete bus map as parsed from a powdr export's `bus_map.bus_ids` field:
    an association list bus id ↦ bus type. -/
abbrev BusMapList := List (Nat × OpenVmBusType)

/-- Convert a `BusMapList` to a `BusMap` lookup function. -/
def BusMapList.toBusMap (busMap : BusMapList) : BusMap :=
  fun busId => busMap.lookup busId

/-- The hard-coded default OpenVM bus map, mirroring powdr's `default_openvm_bus_map` -/
def defaultBusMap : BusMap
  | 0 => some .executionBridge
  | 1 => some .memory
  | 2 => some .pcLookup
  | 3 => some .variableRangeChecker
  | 6 => some .bitwiseLookup
  | 7 => some (.tupleRangeChecker 256 2048)
  | _ => none

/-- Stateful buses are the execution bridge and memory; the rest are stateless lookups. -/
def OpenVmBusType.isStateful : OpenVmBusType → Bool
  | .executionBridge => true
  | .memory => true
  | .pcLookup => false
  | .variableRangeChecker => false
  | .bitwiseLookup => false
  | .tupleRangeChecker _ _ => false

/-- Whether a field element is a byte (`0 ≤ x < 256`). -/
def isByte (x : ZMod p) : Bool := decide (x.val < 256)

/-- Whether a message conflicts with the lookup table of the bus it is sent on. -/
def violates (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Bool :=
  match busMap msg.busId, msg.payload with
  -- ISSUE:
  -- The PC lookup is a bit special: We would have to know the program to
  -- check whether the PC lookup is valid. So this semantics is **wrong**,
  -- and in theory, the optimizer could add failing PC lookups, losing
  -- completeness.
  -- However, the input circuit already has constraints fixing all of the
  -- lookup fields to constants (added here: [1]), so the optimizer would
  -- not be able to change any of the flags.
  -- Also, the completeness issue could be solved by checking that the
  -- optimized circuit does not contain any PC lookups (they can always
  -- be removed in practice).
  -- [1] https://github.com/powdr-labs/powdr/blob/f94a24f19249af67efbea92ff9c3db6e3e50e7fd/autoprecompiles/src/symbolic_machine_generator.rs#L185-L192
  | some .pcLookup, args => !decide (args.length = 9)

  | some .bitwiseLookup, [x, y, z, op] =>
    match op.val with
    -- Op 0: range check x and y to be bytes, z must be 0.
    | 0 => !(isByte x && isByte y && decide (z.val = 0))
    -- Op 1: range check x and y to be bytes, z must be x ^ y.
    | 1 => !(isByte x && isByte y && decide (z.val = Nat.xor x.val y.val))
    -- Other ops are invalid.
    | _ => true

  | some .variableRangeChecker, [x, bits] =>
    -- Check that x < 2^bits, and that the number of bits requested is one the checker
    -- supports: OpenVM's variable range checker rejects any lookup of more than 25 bits.
    !(decide (bits.val ≤ 25) && decide (x.val < 2 ^ bits.val))

  | some (.tupleRangeChecker s1 s2), [x, y] =>
    -- Range check that x < s1 and y < s2.
    !(decide (x.val < s1) && decide (y.val < s2))

  -- For lookups, reject if the number of arguments is not as expected.
  | some .bitwiseLookup, _ => true
  | some .variableRangeChecker, _ => true
  | some (.tupleRangeChecker _ _), _ => true

  -- Stateful buses.
  | some .executionBridge, _ => false

  -- In OpenVM, the invariant is that only range-checked values are sent to
  -- the register & memory address spaces.
  | some .memory, addressSpace :: _pointer :: b0 :: b1 :: b2 :: b3 :: _timeStamp =>
    decide (msg.multiplicity = -1) &&
      (addressSpace.val == 1 || addressSpace.val == 2) &&
      !([b0, b1, b2, b3].all isByte)
  | some .memory, _ => false

  -- Invalid bus ID. Won't have a matching receive.
  | none, _ => true

/-- Whether a message breaks an invariant on which soundness depends. -/
def breaksInvariant (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Bool :=
  -- Note that this function is not called for multiplicity = 0
  match busMap msg.busId with
  -- Lookups are only ever sent (multiplicity 1).
  | some .pcLookup | some .variableRangeChecker | some .bitwiseLookup
  | some (.tupleRangeChecker _ _) =>
    !decide (msg.multiplicity = 1)
  -- The execution bridge is stateful: it is sent (1) or received (-1).
  | some .executionBridge =>
    !decide (msg.multiplicity = 1 ∨ msg.multiplicity = -1)
  -- Memory is stateful (multiplicity 1 or -1), and additionally maintains the invariant
  -- that data limbs written to the register / main-memory address spaces (1 and 2) are
  -- byte-range. The payload is `(address_space, pointer, data.. (4 bytes), timestamp)`.
  | some .memory =>
    !decide (msg.multiplicity = 1 ∨ msg.multiplicity = -1) ||
    (match msg.payload with
      | addressSpace :: _pointer :: b0 :: b1 :: b2 :: b3 :: _timeStamp =>
        bif (addressSpace.val == 1 || addressSpace.val == 2) then
          !([b0, b1, b2, b3].all (fun d => decide (d.val < 256)))
        else false
      | _ => false)
  -- Circuits should not send messages to an unknown bus.
  | none => true

/-- Maps a bus ID to its memory bus shape, if applicable. -/
def memShapeOf (busMap : BusMap) (busId : Nat) : Option MemoryBusShape :=
  match busMap busId with
  -- The *actual* memory bus, with address (address space, pointer) in payload slots 0 and 1.
  | some .memory => some { addressFields := [0, 1] }
  -- The execution bridge can also be viewed as a memory bus with a single global cell (address `[]`).
  -- Note that in this bus, the memory discipline (for any consecutive send/receive pair, the values
  -- must match) is *not* enforced by the bus itself. By adding the execution bridge here, make
  -- completeness partial: We assume that the prover will always *chose* to prove consecutive cycles.
  | some .executionBridge => some { addressFields := [] }
  | _ => none

/-- The OpenVM bus semantics for a given bus map (default: the hard-coded default bus map). -/
def openVmBusSemantics (p : ℕ) (busMap : BusMap := defaultBusMap) :
    BusSemantics p where
  isStateful busId :=
    match busMap busId with
    | some t => t.isStateful
    | none => false
  violatesConstraint := violates busMap
  breaksInvariant := breaksInvariant busMap
  admissible msgs :=
    ∀ (busId : Nat) (shape : MemoryBusShape), memShapeOf busMap busId = some shape →
      admissibleMemoryBus shape (msgs.filter (fun m => m.busId = busId))
  -- OpenVM's proving backend bound (powdr's `DEFAULT_DEGREE_BOUND`).
  degreeBound := { identities := 3, busInteractions := 2 }

/-- The BabyBear field modulus, `2^31 - 2^27 + 1` — the field all powdr OpenVM exports use. -/
def babyBear : Nat := 2013265921

instance : NeZero babyBear := ⟨by decide⟩

end Leanr.OpenVM
