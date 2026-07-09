import ApcOptimizer.Spec

set_option autoImplicit false

/-! Helper functions to encode the semantics of memory buses, to be used to implement
    `BusSemantics::admissible`. Memory buses are stateful buses that follow the pattern
    that bus interactions come in pairs like:
    `send(memBusId, (<address 1>, <timestamp>, <value>))`
    `receive(memoryBusId, (<address 2>, <previous timestamp>, <previous value>))`
    such that if `<address 1> = <address 2>`:
    - `<timestamp> = <previous timestamp>`
    - `<value> = <previous value>`

    Using `admissibleMemoryBus` just *asserts* that this discipline is followed. In practice,
    it could be enforced (e.g. by an argument like [1]), or it could be not enforced, but guaranteed
    that the prover *can* satisfy the property (without sacrificing completeness).

    Note that this assumes that *bus interactions are ordered by time*!

    [1] https://link.springer.com/article/10.1007/BF01185212
-/

variable {p : ℕ}

/-- A description of a memory bus interaction. -/
structure MemoryBusShape where
  /-- Payload positions forming the access key (e.g. OpenVM's two-limb address).
      Can be empty for a single global cell. -/
  addressFields : List Nat

/-- The address projection of an evaluated message, per a memory-bus shape. -/
def MemoryBusShape.address (shape : MemoryBusShape) (m : BusInteraction (ZMod p)) :
    List (Option (ZMod p)) :=
  shape.addressFields.map (fun (slot : Nat) => m.payload[slot]?)

/-- Given an ordered list of memory bus interaction messages *on the same bus*, decide whether
    it follows the memory bus discipline: After a *send* to a given address, the next *receive*
    from the same address observes the same payload, with no intervening active messages to the
    same address. -/
def admissibleMemoryBus (shape : MemoryBusShape) (L : List (BusInteraction (ZMod p))) : Prop :=
  ∀ (pre mid post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p)),
    L = pre ++ S :: mid ++ R :: post →
    S.multiplicity = 1 → R.multiplicity = -1 →
    shape.address S = shape.address R →
    (∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = shape.address S → False) →
    S.payload = R.payload

-- TODO: Move this out of the auditing surface
/-- The consumption form the passes use. Given `admissibleMemoryBus` over the **active** sublist of a
    raw (all-multiplicity) message list `Lraw`, a send `S` followed by a receive `R` to the same
    address in `Lraw`, with no active same-address message between them, have equal payloads. The
    passes exhibit the split of `Lraw` (the raw per-bus interaction list) directly; this lemma
    filters it to the active sublist that `admissibleMemoryBus` ranges over (`S`, `R` survive as they
    are active, given `1 ≠ 0`). -/
theorem admissibleMemoryBus.consecutive (shape : MemoryBusShape)
    (Lraw : List (BusInteraction (ZMod p))) (hp1 : (1 : ZMod p) ≠ 0)
    (h : admissibleMemoryBus shape (Lraw.filter (fun m => decide (m.multiplicity ≠ 0))))
    (pre mid post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p))
    (hsplit : Lraw = pre ++ S :: mid ++ R :: post)
    (hS : S.multiplicity = 1) (hR : R.multiplicity = -1)
    (haddr : shape.address S = shape.address R)
    (hmid : ∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = shape.address S → False) :
    S.payload = R.payload := by
  have hPS : decide (S.multiplicity ≠ 0) = true := by
    simp only [hS, decide_eq_true_eq]; exact hp1
  have hPR : decide (R.multiplicity ≠ 0) = true := by
    simp only [hR, decide_eq_true_eq]; exact fun hh => hp1 (neg_eq_zero.mp hh)
  refine h (pre.filter (fun m => decide (m.multiplicity ≠ 0)))
    (mid.filter (fun m => decide (m.multiplicity ≠ 0)))
    (post.filter (fun m => decide (m.multiplicity ≠ 0))) S R ?_ hS hR haddr ?_
  · subst hsplit
    simp only [List.filter_append, List.filter_cons, hPS, hPR, if_true]
  · intro m hm hmne hmaddr
    exact hmid m (List.mem_of_mem_filter hm) hmne hmaddr
