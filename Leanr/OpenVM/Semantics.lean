import Leanr.Spec

/-!
# OpenVM bus semantics

An instance of the spec-level `BusSemantics` (see `Leanr/Spec.lean`) for the OpenVM zkVM.

This is the spec-level counterpart of powdr's `OpenVmBusInteractionHandler`
(`openvm-bus-interaction-handler` crate). That handler *refines range constraints*; here we
instead capture the two soundness-relevant predicates the spec asks for:
`violatesConstraint` (does a message conflict with a lookup table?) and `breaksInvariant`
(does a message break an invariant soundness depends on?), plus statefulness.

powdr's handler supports a dynamic `BusMap`; we do too: every definition takes the bus map as
a parameter (defaulting to the *default* OpenVM bus map, `default_openvm_bus_map`), because
real programs assign different bus ids (e.g. the reth benchmark has `TupleRangeChecker` on bus
8, not 7).
-/

set_option autoImplicit false

namespace Leanr.OpenVM

variable {p : ℕ}

/-- The OpenVM bus types that appear in the default bus map. -/
inductive OpenVmBusType where
  | executionBridge
  | memory
  | pcLookup
  | variableRangeChecker
  | bitwiseLookup
  | tupleRangeChecker (size1 size2 : Nat)
  deriving Repr, DecidableEq

/-- The hard-coded default OpenVM bus map, mirroring powdr's `default_openvm_bus_map`:
    `0 → ExecutionBridge, 1 → Memory, 2 → PcLookup, 3 → VariableRangeChecker,
     6 → BitwiseLookup, 7 → TupleRangeChecker([256, 2048])`. -/
def defaultBusMap : Nat → Option OpenVmBusType
  | 0 => some .executionBridge
  | 1 => some .memory
  | 2 => some .pcLookup
  | 3 => some .variableRangeChecker
  | 6 => some .bitwiseLookup
  | 7 => some (.tupleRangeChecker 256 2048)
  | _ => none

/-- A concrete bus map as parsed from a powdr export's `bus_map.bus_ids` field:
    an association list bus id ↦ bus type. -/
abbrev BusMap := List (Nat × OpenVmBusType)

/-- View a parsed `BusMap` as the lookup function the semantics consume. -/
def BusMap.toFun (busMap : BusMap) : Nat → Option OpenVmBusType :=
  fun busId => busMap.lookup busId

/-- Stateful (order-dependent) buses are the execution bridge and memory; the rest are
    stateless lookups. -/
def OpenVmBusType.isStateful : OpenVmBusType → Bool
  | .executionBridge => true
  | .memory => true
  | .pcLookup => false
  | .variableRangeChecker => false
  | .bitwiseLookup => false
  | .tupleRangeChecker _ _ => false

/-- Whether a field element is a byte (`0 ≤ x < 256`). -/
private def isByte (x : ZMod p) : Bool := decide (x.val < 256)

/-- Whether a message conflicts with the lookup table of the bus it is sent on.

    Only the stateless lookup buses have such tables:
    - `BitwiseLookup (x, y, z, op)`: `x, y` are bytes and either `op = 0 ∧ z = 0` (range check)
      or `op = 1 ∧ z = x ^ y` (xor); any other `op` conflicts.
    - `VariableRangeChecker (x, bits)`: `x < 2 ^ bits`.
    - `TupleRangeChecker (x, y)` with sizes `(s1, s2)`: `x < s1 ∧ y < s2`.

    Stateful buses (execution bridge, memory) and the PC lookup carry no static table in this
    model, so they never conflict. -/
def violates (busMap : Nat → Option OpenVmBusType) (msg : BusInteraction (ZMod p)) : Bool :=
  match busMap msg.busId, msg.payload with
  | some .bitwiseLookup, [x, y, z, op] =>
    match op.val with
    | 0 => !(isByte x && isByte y && decide (z.val = 0))
    | 1 => !(isByte x && isByte y && decide (z.val = Nat.xor x.val y.val))
    | _ => true
  | some .variableRangeChecker, [x, bits] =>
    !decide (x.val < 2 ^ bits.val)
  | some (.tupleRangeChecker s1 s2), [x, y] =>
    !(decide (x.val < s1) && decide (y.val < s2))
  | _, _ => false

/-- Whether a message breaks an invariant on which soundness depends.

    We model the memory invariant: values written to the register / main-memory address spaces
    (`1` and `2`) must be byte-range limbs. The memory payload is
    `(address_space, pointer, data.., timestamp)`, so the data limbs are the middle elements.
    Other buses carry no such invariant here.

    (Not exercised by the identity-optimizer snapshot test in `Leanr/OpenVM/Snapshot.lean`;
    it is a faithful-but-uncorroborated modeling choice.) -/
def breaks (busMap : Nat → Option OpenVmBusType) (msg : BusInteraction (ZMod p)) : Bool :=
  match busMap msg.busId, msg.payload with
  | some .memory, _addressSpace :: _pointer :: rest =>
    match msg.payload with
    | addressSpace :: _ =>
      bif (addressSpace.val == 1 || addressSpace.val == 2) then
        !(rest.dropLast.all (fun d => decide (d.val < 256)))
      else false
    | _ => false
  | _, _ => false

/-- The OpenVM bus semantics for a given bus map (default: the hard-coded default bus map).

    The memory bus is declared as a last-write-wins memory
    (**audited assumption**, justified by OpenVM's offline-memory-checking argument and its
    per-instruction exclusive timestamp windows): payload layout
    `[address_space, pointer, data_0, …, data_3, timestamp]`, so the address is slots `[0, 1]`,
    the timestamp slot `6`, and timestamps are range-checked below `2^29`. The payload layout
    is fixed by OpenVM independently of which bus id the map assigns to memory. -/
def openVmBusSemantics (p : ℕ) (busMap : Nat → Option OpenVmBusType := defaultBusMap) :
    BusSemantics p where
  isStateful busId :=
    match busMap busId with
    | some t => t.isStateful
    | none => false
  violatesConstraint := violates busMap
  breaksInvariant := breaks busMap
  memoryBus busId :=
    match busMap busId with
    | some .memory => some { addressFields := [0, 1], tsField := 6, tsBound := 2 ^ 29 }
    -- The execution bridge is a linear-consumption bus (see `BusSemantics.memoryBus`):
    -- payload `[pc, timestamp]`, a single global cell (empty address). **Audited
    -- assumption**: each `(pc, ts)` state is produced and consumed exactly once, at most
    -- one instruction starts per timestamp, timestamps are globally range-checked below
    -- `2^29`, and the fragment executes in an exclusive contiguous timestamp window, so a
    -- state produced strictly before another of the fragment's own productions is consumed
    -- by one of the fragment's own receives.
    | some .executionBridge => some { addressFields := [], tsField := 1, tsBound := 2 ^ 29 }
    | _ => none

/-- The BabyBear field modulus, `2^31 - 2^27 + 1` — the field all powdr OpenVM exports use. -/
def babyBear : Nat := 2013265921

instance : NeZero babyBear := ⟨by decide⟩

end Leanr.OpenVM
