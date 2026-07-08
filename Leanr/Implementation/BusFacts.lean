import Leanr.MemoryBus

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
interaction, so facts can be conditional on e.g. an op-selector slot (see `Leanr/Implementation/OpenVmFacts.lean`).
-/

variable {p : ℕ}

/-- Does a payload match a pattern? Same length, and every constant pattern entry agrees. -/
def Matches (payload : List (ZMod p)) (pattern : List (Option (ZMod p))) : Prop :=
  payload.length = pattern.length ∧
  ∀ (slot : Nat) (c : ZMod p), pattern[slot]? = some (some c) → payload[slot]? = some c

/-- Proven, pass-consumable knowledge about the bus semantics `bs`. -/
structure BusFacts (p : ℕ) (bs : BusSemantics p) where
  /-- Accepted-value bound for one payload slot of messages matching a pattern:
      `slotBound busId pattern slot = some bound` means every *accepted* message on `busId`
      matching `pattern` has `payload[slot].val < bound`. -/
  slotBound : (busId : Nat) → (pattern : List (Option (ZMod p))) → (slot : Nat) → Option Nat
  slotBound_sound :
    ∀ (m : BusInteraction (ZMod p)) (pattern : List (Option (ZMod p))) (slot bound : Nat)
      (x : ZMod p),
      slotBound m.busId pattern slot = some bound →
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
      group same-address accesses; this is the VM-side memory knowledge (`Leanr/MemoryBus.lean`)
      the spec's abstract `admissible` predicate deliberately omits. -/
  memShape : (busId : Nat) → Option MemoryBusShape
  /-- Every bus with a declared shape is stateful — so its messages survive the active∧stateful
      filter that `ConstraintSystem.admissible` applies before consulting `bs.admissible`. -/
  memShape_stateful : ∀ (busId : Nat) (shape : MemoryBusShape),
    memShape busId = some shape → bs.isStateful busId = true
  /-- The VM's abstract `admissible` predicate entails the concrete consecutive-match discipline
      (`admissibleMemoryBus`) on each declared bus's active messages. For a VM whose `admissible` *is*
      that per-bus conjunction (see `Leanr/Implementation/OpenVmFacts.lean`) this is essentially
      definitional. -/
  admissible_sound :
    ∀ (msgs : List (BusInteraction (ZMod p))),
      bs.admissible (msgs.filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) →
      ∀ (busId : Nat) (shape : MemoryBusShape), memShape busId = some shape →
        admissibleMemoryBus shape ((msgs.filter (fun m => m.busId = busId)).filter
          (fun m => decide (m.multiplicity ≠ 0)))

/-- The fact-free instance: claims nothing, exists for every semantics. Declares no memory
    shapes, so the memory/exec unify passes degrade to no-ops. -/
def BusFacts.trivial (bs : BusSemantics p) : BusFacts p bs where
  slotBound _ _ _ := none
  slotBound_sound := by intro _ _ _ _ _ h; exact absurd h (by simp)
  slotFun _ _ _ := none
  slotFun_sound := by intro _ _ _ _ _ h; exact absurd h (by simp)
  neverViolates _ := false
  neverViolates_sound := by intro _ h; exact absurd h (by simp)
  memShape _ := none
  memShape_stateful := by intro _ _ h; exact absurd h (by simp)
  admissible_sound := by intro _ _ _ _ h; exact absurd h (by simp)
