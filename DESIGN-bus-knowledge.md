# Design proposal: giving the optimizer sound access to bus knowledge

Status: **implemented** (Layer 1: commit `9e711ce`; Layer 2: commits `805abe8`, `86008f7`; snapshot at 36/11 ≈ 3.27). Kept as the design rationale. Prompted by the two hints in `log.md` (entries 14–15):
both remaining optimizations are blocked because the optimizer sees `BusSemantics` only as three
opaque functions. This document proposes **two independent layers** that unblock them without
giving up machine-checked correctness, honoring two constraints: nothing OpenVM-specific in the
reusable parts, and a minimal audit surface (everything that *can* be proven is proven; only
genuine assumptions about the rest of the VM are audited).

The two hints fail for different reasons, and that difference dictates the design:

| | why blocked today | nature of the missing knowledge | mechanism |
|---|---|---|---|
| c-limbs, XOR/NOT, range facts | information *is* in `violatesConstraint`, but extracting it generically costs Ω(p) probes | **derivable** from the concrete semantics | Layer 1: proven auxiliary input (zero audit) |
| memory send/receive cancellation | unsound under `equivalentTo` (support-cardinality countermodel, log entry 14) | an **assumption about the rest of the VM** (Blum et al. offline memory checking + timestamp-window ownership) | Layer 2: one audited field in `BusSemantics` + one conjunct in `satisfies` |

---

## Layer 1: `BusFacts` — proven auxiliary knowledge (no `Spec.lean` change)

### Shape

A structure *dependent on the bus semantics*, every field paired with a soundness proof, so the
whole thing is untrusted (the kernel checks it; auditing it adds nothing):

```lean
/-- Proven, pass-consumable knowledge about a bus semantics. A "pattern" is a payload template:
    `some c` entries must match the evaluated message exactly, `none` entries are free.
    `Matches (payload : List (ZMod p)) (pattern : List (Option (ZMod p))) : Prop` holds when
    the lists have equal length and every `some c` pattern entry equals the payload entry. -/
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
      m.payload.get? slot = some x →
      x.val < bound

  /-- Functional dependence: for accepted messages matching the pattern, the value in
      `outSlot` is *determined* by the rest of the payload, via the computable `f`.
      `f` receives the payload with `outSlot` zeroed out, so it provably cannot depend on the
      value it determines — which is what lets a pass *probe* `f` on candidate inputs. -/
  slotFun : (busId : Nat) → (pattern : List (Option (ZMod p))) → (outSlot : Nat) →
            Option (List (ZMod p) → ZMod p)
  slotFun_sound :
    ∀ (m : BusInteraction (ZMod p)) (pattern : List (Option (ZMod p))) (outSlot : Nat)
      (f : List (ZMod p) → ZMod p) (z : ZMod p),
      slotFun m.busId pattern outSlot = some f →
      Matches m.payload pattern →
      bs.violatesConstraint m = false →
      m.payload.get? outSlot = some z →
      z = f (m.payload.set outSlot 0)

  /-- Buses whose messages never violate (e.g. stateful buses carrying no table). -/
  neverViolates : (busId : Nat) → Bool
  neverViolates_sound :
    ∀ (m : BusInteraction (ZMod p)),
      neverViolates m.busId = true →
      bs.violatesConstraint m = false
```

`BusFacts.trivial bs` (all `none`/`false`) exists for every semantics. *Bounds* are the
primitive rather than explicit value lists: they compose with `ZMod.val` arithmetic (see
digit-decomposition below) and yield enumerable domains (`List.range bound`) exactly when small.
The vocabulary is VM-agnostic — bus ids, arities and functions are all data. If a VM has a
table that is neither an interval nor functional, the structure extends with new proven fields
without touching the spec.

### Worked example: `slotFun` for the OpenVM bitwise bus

OpenVM's bitwise-lookup bus (id 6) accepts payloads `[x, y, z, op]`, where `op = 1` rows are
the XOR table: `x, y` bytes and `z = x ^^^ y`. The fact says exactly that slot 2 is determined
whenever a message matches the pattern "op is the constant 1":

```lean
openVmFacts.slotFun 6 [none, none, none, some 1] 2 =
  some (fun payload =>
    match payload with
    | [x, y, _, _] => ((x.val ^^^ y.val : Nat) : ZMod p)
    | _ => 0)
```

(All other `(busId, pattern, outSlot)` queries return `none`. The soundness proof is the
`bitwise_xor_fun` keystone lemma below — 6 lines against the concrete `violates`.)

How the NOT-optimization consumes it, on a circuit containing
`mult = 1, args = [255, x, z, 1]`:

1. the interaction's obligation (multiplicity `1 ≠ 0`) gives `violatesConstraint = false`;
2. `slotFun_sound` then gives the entailment `env z = f [255, env x, 0, 1]` — note the zeroed
   slot 2, so this is well-defined without knowing `z`;
3. `slotBound` (same pattern, slot 1) gives `(env x).val < 256`;
4. the pass probes `f [255, v, 0, 1]` for all `v ∈ [0, 256)` — 256 evaluations of *direct
   code*, no field sweeps — fits the affine candidate `255 − v`, and decidably verifies the
   fit on all 256 points;
5. combined: `env z = 255 − env x` holds for every satisfying assignment, and the existing
   `subst_correct` eliminates `z`. A wrong affine guess fails step 4 and simply skips the
   optimization; it can never produce a wrong circuit.

### Feasibility (de-risked)

The three facts needed for the current snapshot are each a ~6-line proof against
`Leanr.OpenVM.Semantics.violates` (checked, they compile):
byte-ness of the bitwise bus's first two slots when `op = 0`; `z.val = x.val ^^^ y.val` when
`op = 1`; `x.val < 2 ^ bits.val` for the variable range checker. `openVmFacts` is the
dictionary of these plus `neverViolates` for buses 0/1/2.

### How the optimizer takes it

The public binary `optimizer` and the spec's `optimizerMaintainsCorrectness` stay exactly as
they are. Added alongside:

```lean
def optimizerWith (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    ConstraintSystem p
-- optimizer cs bs = optimizerWith cs bs (BusFacts.trivial bs)

theorem optimizerWith_correct (cs bs) (facts : BusFacts p bs) :
    ((optimizerWith cs bs facts).equivalentTo cs bs) ∧
    (cs.guaranteesInvariants bs → (optimizerWith cs bs facts).guaranteesInvariants bs)
```

(the same two clauses `optimizerMaintainsCorrectness` demands, stated per-instance because
facts are `bs`-dependent — a `bs`-indexed family of nontrivial facts cannot exist uniformly).
The snapshot test would call `optimizerWith addiInput (openVmBusSemantics babyBear) openVmFacts`
— a one-line test change that needs your sign-off.

### New/extended passes it enables

1. **Bus-domain propagation** — feeds `slotBound`-derived domains for variables occurring as
   payload slots of constant-nonzero-multiplicity interactions into the existing finite-domain
   enumeration (its entailment lemma extends from `hsat.1` to also consume `hsat.2`).
   On the snapshot: `c__0_0, c__1_0 ∈ [0,256)` — 65 536-point enumeration of the two-line
   constraint pins `(1, 0)`; the bitwise row becomes the constant `[1,0,0,0]` and is
   tauto-dropped. **19 → 17 variables.**
2. **Table-function interpolation** — for an interaction binding `z` through `slotFun` with the
   input slots bounded: probe `f` on the input domain (2^8–2^16 evaluations of *direct code*,
   not field sweeps), fit an affine expression, verify the fit decidably on the whole domain,
   then substitute `z` away via the existing `subst_correct`. This is exactly powdr's
   NOT(x) = XOR(0xff, x) = 0xff − x discovery, but the fit is *verified*, so a wrong guess
   cannot produce a wrong circuit — only a missed optimization.
3. **Digit-decomposition solving** — from an entailed `x + B·y = c` with `x.val < B`,
   `y.val < M`, `B·M ≤ p`: lift to ℕ (no wraparound) and solve uniquely
   (`x = c.val % B, y = c.val / B`) — constant-time, no enumeration. This is what pins
   `wdec0 = 1, wdec1 = 0` once Layer 2 forces `wdec0 + 2^17·wdec1 = 1`.
4. **Fact-aware tautology dropping** — with slot bounds, a lookup whose payload became a
   *known-in-range* constant is droppable even when `violatesConstraint` was never probed.

## Layer 2: last-write discipline — one audited field (small `Spec.lean` change)

### Why it cannot be a proven fact

The cancellation needs: *the receive of the second access to an address returns exactly what
the fragment's own previous access sent*. That is false for arbitrary provers of the local
fragment (the countermodel of log entry 14) and is not derivable from `violatesConstraint` —
it is guaranteed by the **global** offline-memory-checking argument (Blum et al.; multiset of
receives ⊆ multiset of sends with increasing timestamps) *plus* the VM rule that no other chip
uses timestamps inside the fragment's window. Both are assumptions about the rest of the VM —
exactly the kind of thing the audit surface is for.

### Minimal encoding

One field in `BusSemantics` and three generic conjuncts in `satisfies` (defined once,
VM-agnostic). The declaration names the payload roles by *position lists*, so the layout is
entirely the VM's business — address first, value first, split across non-adjacent slots: all
fine. (`addressFields` per your suggestion; the honest conjuncts below also need to know which
slot is the timestamp, hence a small structure rather than a bare list.)

```lean
/-- Shape of a last-write-wins memory bus. Payload slots not in `addressFields` and not
    `tsField` are the value limbs. -/
structure MemoryBusShape where
  /-- Payload positions forming the access key (e.g. OpenVM's two-limb address:
      address space and pointer). -/
  addressFields : List Nat
  /-- Payload position of the timestamp (a send carries its write time; a receive carries the
      time of the write it observes). -/
  tsField : Nat
  /-- Audited upper bound on timestamp values on this bus (e.g. `2^29` for OpenVM). -/
  tsBound : Nat

structure BusSemantics (p : ℕ) where
  ...
  /-- Declares a stateful bus to follow last-write-wins memory discipline (offline memory
      checking, Blum et al.). `none`: no such discipline (default; e.g. an execution bridge). -/
  memoryBus : (busId : Nat) → Option MemoryBusShape
```

For OpenVM, whose memory payload is `[address_space, pointer, data_0, …, data_3, timestamp]`:

```lean
memoryBus := fun busId =>
  if busId = 1 then some { addressFields := [0, 1], tsField := 6, tsBound := 2^29 } else none
```

A VM sending `[data_0, …, data_3, addr, ts]` would declare
`{ addressFields := [4], tsField := 5, … }`. Nothing about position or contiguity is assumed.

New conjuncts in `ConstraintSystem.satisfies`, quantifying over the *evaluated* interactions of
the fragment (`active` = multiplicity ≠ 0; "send"/"receive" distinguished by multiplicity sign
convention of the declaration; `address m` = the `addressFields` projection, `ts m` = the
`tsField` entry, `value m` = the rest). **No list-order assumption anywhere:**

> 1. **Timestamp uniqueness / matching** — for an active send `S` and an active receive `R`
>    with `address R = address S` and `ts R = ts S`: `value R = value S`.
>    *(Blum: a receive's tuple equals some send's tuple, and `(address, ts)` identifies a send
>    uniquely across the system.)*
> 2. **In-window consumption** — for active sends `S, S'` with `address S' = address S`,
>    `(ts S).val < (ts S').val`, and no active send to that address with timestamp value
>    strictly between: some active receive `R` in the fragment has the *identical tuple* as
>    `S`. *(Window exclusivity: between two of the fragment's own accesses to an address, the
>    context cannot access it, so the earlier send's consumer is in the fragment.)*
> 3. **Timestamp range** — every active interaction `m` on the bus has `(ts m).val < tsBound`.
>    *(The VM's global range-checking of timestamps; needed so `.val` comparisons in clause 2
>    reflect field arithmetic without wraparound.)*

On the snapshot, these make the unification an **entailment**: clause 3 rules out timestamp
wraparound, clause 2 applied to the two active sends `(b, T)` and `(a, T+2)` yields an active
receive with tuple `(addr, b, T)`, Layer-1 bounds on the read-receive's decomposition limbs
prove its timestamp differs from `T` (value arithmetic, no enumeration), so the write-receive
is the match: `writes_aux__prev_data = b ∧ W = T`. The *existing* substitution machinery
(`subst_correct`) then eliminates the witnesses — no change to
`implies`/`equivalentTo`/`optimizerMaintainsCorrectness` at all — and the countermodel dies
because garbage-witness assignments violate clause 2. The cancelled ±pair (now syntactically
identical payloads) is dropped by a small pass using Layer 1's `neverViolates`.

### What if the interactions are not ordered by time?

Nothing breaks — this is why the conjuncts are formulated over evaluated timestamps rather
than list positions. All three clauses are order-free, so they remain *true* of every real
witness no matter how the fragment lists its interactions; a strange ordering can only make the
optimizer's entailment search fail to fire, i.e. **cost effectiveness, never correctness**.

This is deliberate. The first draft of this section paired send/receive by **list adjacency**
("no same-key interaction between `i` and `j`"), which is simpler — but if a fragment ever
listed accesses out of time order, that conjunct would assert a *false* matching: `satisfies`
would exclude witnesses that the real memory argument accepts, and the "optimized" circuit
would reject valid executions (a completeness break against reality, invisible inside the
formal system because the strengthened `satisfies` is exactly what the proofs are relative
to). An audited assumption that silently converts a data-ordering convention into a soundness
requirement is a bad trade; the timestamp-based clauses put the assumption where the VM
actually guarantees it. The price is a more involved derivation in the pass (value-arithmetic
on bounded timestamps — machinery shared with Layer 1's digit-decomposition solving).

Audit surface added: the per-VM `MemoryBusShape` declaration plus the three clauses'
justifications above (Blum multiset argument, window exclusivity, global timestamp ranging).

### Rejected alternative: contextual equivalence

Re-defining equivalence as "satisfiability preserved under all balanced context completions" was
considered and rejected: it is a much larger spec change, and the naive version is *still*
unsound for the cancellation, because an adversarial context can supply the matching garbage
send — the discipline has to be encoded somewhere regardless. Strengthening `satisfies` is the
minimal sound insertion point, and it composes with everything already proven.

## Predicted impact on the snapshot

| configuration | distinct variables | effectiveness |
|---|---|---|
| today (generic floor) | 19 | 36/19 ≈ 1.89 |
| + Layer 1 | 17 (`c` limbs derived) | 36/17 ≈ 2.12 |
| + Layer 2 | 13 (prev-data + write decomp unified) | 36/13 ≈ 2.77 |
| + both | **11** (`a×4, b×4, from_ts, rdec0, rdec1`) | **36/11 ≈ 3.27** |

The remaining 11 are irreducible: all observable in stateful side effects except the read's
decomposition limbs, which parameterize genuine witness freedom (the previous access may be the
context's).

## Decision points

1. **Layer 1** — OK to add the `facts` argument via `optimizerWith` and switch the snapshot
   test to `optimizerWith … openVmFacts` (one line)? No spec change, zero audit.
2. **Layer 2** — OK to add `memoryBus : (busId : Nat) → Option MemoryBusShape` to
   `BusSemantics` and the three timestamp-based clauses to `satisfies` (both in `Spec.lean`),
   plus the OpenVM declaration
   `{ addressFields := [0, 1], tsField := 6, tsBound := 2^29 }` for bus 1? This is the audited
   part.

Layer 1 is implementable immediately and independently; Layer 2 builds on it (pair dropping and
digit solving reuse Layer 1 facts) but touches the frozen spec, so it ships second and separately
revertable.
