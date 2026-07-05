import Leanr.Spec

set_option autoImplicit false

/-! # Last-write-wins bus discipline (the concrete, VM-side memory knowledge)

`Spec.lean` is deliberately VM-agnostic: it carries only an abstract `BusSemantics.admissible`
predicate on the evaluated messages of the stateful buses. This file provides the *concrete*
memory/execution-bridge discipline that a VM's `admissible` is built from, and that the
optimizer's unify passes consume. It is neither part of the audited spec nor specific to one
zkVM — it is the shared "last-write-wins over program-ordered accesses" notion.

The core predicate is `admissibleBus`: **consecutive same-address send→receive pairs match**.
In program (list) order the active accesses to one address alternate receive/send, and each
send is read back by the *next* same-address receive. Stated as a split: whenever a send `S`
is followed by a receive `R` to the same address with no active same-address message strictly
between them, their payloads are equal. This is exactly the fact the unify passes need — the
chaining link `R.payload = S.payload` — and it dissolves the anchored-maximum / monotonicity
machinery the old `disciplineOn` needed (the terminal send of a block simply has no following
receive, so it is unconstrained).

Everything is purely propositional; no field/primality assumptions. -/

variable {p : ℕ}

/-- Shape of a last-write-wins bus: which payload slots form the access key (address). For an
    ordinary memory bus this is the address-space/pointer limbs; for a linear-consumption bus
    (execution bridge) it is `[]` — a single global cell. All other payload slots are the value
    (including the timestamp), which the discipline carries verbatim through a matched pair. -/
structure MemoryBusShape where
  /-- Payload positions forming the access key (e.g. OpenVM's two-limb address). -/
  addressFields : List Nat

/-- The address projection of an evaluated message, per a memory-bus shape. -/
def MemoryBusShape.address (shape : MemoryBusShape) (m : BusInteraction (ZMod p)) :
    List (Option (ZMod p)) :=
  shape.addressFields.map (fun (slot : Nat) => m.payload[slot]?)

/-- **Consecutive same-address send→receive match** over a list of evaluated messages: whenever
    the list splits as `pre ++ S :: mid ++ R :: post` with `S` an active send, `R` an active
    receive, the same address, and no active same-address message in `mid`, the payloads of `S`
    and `R` agree.

    This is the audited last-write-wins assumption in the form the passes consume: `R` is the
    access that reads `S`'s write (the next same-address access), so it observes `S`'s value and
    timestamp. A VM declares its stateful buses admissible by proving its `BusSemantics.admissible`
    entails `admissibleBus` on each such bus (see `Leanr/OpenVM/`). -/
def admissibleBus (shape : MemoryBusShape) (L : List (BusInteraction (ZMod p))) : Prop :=
  ∀ (pre mid post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p)),
    L = pre ++ S :: mid ++ R :: post →
    S.multiplicity = 1 → R.multiplicity = -1 →
    shape.address S = shape.address R →
    (∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = shape.address S → False) →
    S.payload = R.payload

/-- The consumption form the passes use. Given `admissibleBus` over the **active** sublist of a
    raw (all-multiplicity) message list `Lraw`, a send `S` followed by a receive `R` to the same
    address in `Lraw`, with no active same-address message between them, have equal payloads. The
    passes exhibit the split of `Lraw` (the raw per-bus interaction list) directly; this lemma
    filters it to the active sublist that `admissibleBus` ranges over (`S`, `R` survive as they
    are active, given `1 ≠ 0`). -/
theorem admissibleBus.consecutive (shape : MemoryBusShape)
    (Lraw : List (BusInteraction (ZMod p))) (hp1 : (1 : ZMod p) ≠ 0)
    (h : admissibleBus shape (Lraw.filter (fun m => decide (m.multiplicity ≠ 0))))
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
