import Leanr.Spec

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

/-- The hard-coded default OpenVM bus map, mirroring powdr's `default_openvm_bus_map` -/
def defaultBusMap : Nat → Option OpenVmBusType
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
private def isByte (x : ZMod p) : Bool := decide (x.val < 256)

/-- Whether a message conflicts with the lookup table of the bus it is sent on. -/
def violates (msg : BusInteraction (ZMod p)) : Bool :=
  match defaultBusMap msg.busId, msg.payload with
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
    -- Check that x < 2^bits.
    !decide (x.val < 2 ^ bits.val)

  | some (.tupleRangeChecker s1 s2), [x, y] =>
    -- Range check that x < s1 and y < s2.
    !(decide (x.val < s1) && decide (y.val < s2))

  -- For lookups, reject if the number of arguments is not as expected.
  | some .bitwiseLookup, _ => true
  | some .variableRangeChecker, _ => true
  | some (.tupleRangeChecker _ _), _ => true

  -- Stateful buses.
  -- TODO: Some of these *might* actually enforce constraints. For example, under the
  -- invariant that all *sent* memory values are range-checked, *received* memory values
  -- can be assumed to be range-checked.
  | some .executionBridge, _ => false
  | some .memory, _ => false

  -- Invalid bus ID. Won't have a matching receive.
  | none, _ => true

/-- Whether a message breaks an invariant on which soundness depends. -/
def breaksInvariant (msg : BusInteraction (ZMod p)) : Bool :=
  -- Note that this function is not called for multiplicity = 0
  match defaultBusMap msg.busId with
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

/-- The OpenVM bus semantics, using the hard-coded default bus map.

    The memory bus (id 1) is declared as a last-write-wins memory
    (**audited assumption**, justified by OpenVM's offline-memory-checking argument and its
    per-instruction exclusive timestamp windows): payload layout
    `[address_space, pointer, data_0, …, data_3, timestamp]`, so the address is slots `[0, 1]`,
    the timestamp slot `6`, and timestamps are range-checked below `2^29`. -/
def openVmBusSemantics (p : ℕ) : BusSemantics p where
  isStateful busId :=
    match defaultBusMap busId with
    | some t => t.isStateful
    | none => false
  violatesConstraint := violates
  breaksInvariant := breaksInvariant
  memoryBus busId :=
    if busId = 1 then some { addressFields := [0, 1], tsField := 6, tsBound := 2 ^ 29 }
    else none

end Leanr.OpenVM
