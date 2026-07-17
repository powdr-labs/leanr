import ApcOptimizer.Spec

set_option autoImplicit false

/-! Helper definitions to encode the semantics of memory buses, used to implement
    `BusSemantics.admissible`. Memory buses are stateful: bus interactions come in
    `getPrevious`/`setNew` pairs — a `setNew` commits a cell's value, and the next access's
    `getPrevious` to the same cell reads it back. So a `setNew` and the next same-address
    `getPrevious`, with no intervening same-address interaction, carry equal payloads (address,
    timestamp and value). Both memory reads and memory writes are such a `getPrevious`/`setNew`
    pair (a read additionally constrains the two values to agree).

    `admissibleMemoryBus` just *asserts* that this discipline holds. In practice it could be
    enforced (e.g. by an argument like [1]), or not enforced but guaranteed that the prover *can*
    satisfy it (without sacrificing completeness).

    Note that this assumes that *bus interactions are ordered by time*!

    [1] https://link.springer.com/article/10.1007/BF01185212
-/

variable {p : ℕ}

/-- A memory access is a `getPrevious` (reading the cell's current value) followed by a `setNew`
    (committing its next value); the two carry opposite multiplicities. The variant is named for
    that order — `⟨getPrevious's operation⟩Then⟨setNew's operation⟩` — which fixes which is the
    *send* (multiplicity `1`) and which the *receive* (`-1`). -/
inductive MemoryBusDirection where
  /-- `getPrevious` receives (`-1`), `setNew` sends (`1`) — so `setNewMult = 1`. This is OpenVM's
      memory convention (send the new record, receive the previous), and every VM's execution
      bridge, which sends the next CPU state and receives the current one. -/
  | receiveThenSend
  /-- `getPrevious` sends (`1`), `setNew` receives (`-1`) — so `setNewMult = -1`. This is SP1's
      memory convention (it sends the previous record and receives the new one). -/
  | sendThenReceive
  deriving Repr, DecidableEq

/-- A description of a memory bus interaction. -/
structure MemoryBusShape where
  /-- Payload positions forming the access key (e.g. OpenVM's two-limb address).
      Can be empty for a single global cell. -/
  addressFields : List Nat
  /-- Which of the matched consecutive `setNew`/`getPrevious` pair is the send and which the
      receive (see `MemoryBusDirection`). -/
  direction : MemoryBusDirection

/-- The multiplicity a `setNew` carries on this bus (`1` for `receiveThenSend`, `-1` for
    `sendThenReceive`); the `getPrevious` reading it back carries the negation. -/
def MemoryBusShape.setNewMult (shape : MemoryBusShape) : ZMod p :=
  match shape.direction with
  | .receiveThenSend => 1
  | .sendThenReceive => -1

/-- The address projection of an evaluated message, per a memory-bus shape. -/
def MemoryBusShape.address (shape : MemoryBusShape) (m : BusInteraction (ZMod p)) :
    List (Option (ZMod p)) :=
  shape.addressFields.map (fun (slot : Nat) => m.payload[slot]?)

/-- Given an ordered list of memory bus interaction messages *on the same bus*, decide whether
    it follows the memory bus discipline: after a `setNew` to a given address (multiplicity
    `shape.setNewMult`), the next `getPrevious` from the same address (multiplicity
    `-shape.setNewMult`) observes the same payload, with no intervening active messages to the same
    address. -/
def admissibleMemoryBus (shape : MemoryBusShape) (L : List (BusInteraction (ZMod p))) : Prop :=
  ∀ (pre mid post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p)),
    L = pre ++ S :: mid ++ R :: post →
    S.multiplicity = shape.setNewMult → R.multiplicity = -shape.setNewMult →
    shape.address S = shape.address R →
    (∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = shape.address S → False) →
    S.payload = R.payload
