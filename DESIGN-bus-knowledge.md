# Design proposal: giving the optimizer sound access to bus knowledge

Status: proposal, awaiting sign-off. Prompted by the two hints in `log.md` (entries 14–15):
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

One field in `BusSemantics` and one generic conjunct in `satisfies` (defined once, VM-agnostic).
The key is given as a *list of payload positions*, so the payload layout is entirely the VM's
business — address first, value first, key split across non-adjacent slots: all fine.

```lean
structure BusSemantics (p : ℕ) where
  ...
  /-- Declares a stateful bus to follow last-write-wins memory discipline.
      `lastWriteKey busId = some keySlots` means: the payload entries at positions `keySlots`
      form the access key (the "address"), and all *other* entries are the observed cell
      content (value limbs, timestamps, ...). `none`: no such discipline (default; e.g. an
      execution bridge). Audited assumption for `some`: the surrounding VM implements offline
      memory checking (Blum et al.) on this bus and grants a fragment an exclusive timestamp
      window, so within a fragment, consecutive same-key accesses observe each other. -/
  lastWriteKey : (busId : Nat) → Option (List Nat)
```

For OpenVM, whose memory payload is `[address_space, pointer, data_0, …, data_3, timestamp]`:

```lean
lastWriteKey := fun busId => if busId = 1 then some [0, 1] else none
```

A VM that sends `[data_0, …, data_3, addr]` would declare `some [4]`; one with the key split
around the value, `some [0, 5]`. Nothing about position or contiguity is assumed.

New conjunct in `ConstraintSystem.satisfies` (the *only* semantic change), for
`keys m := keySlots.map (fun (slot : Nat) => m.payload.get? slot)`:

> For any two interactions at list positions `i < j` on a bus with
> `lastWriteKey busId = some keySlots`, writing `mᵢ = (busInteractions[i]).eval env` and
> `mⱼ = (busInteractions[j]).eval env`: if `keys mᵢ = keys mⱼ` (same address), no interaction
> strictly between `i` and `j` evaluates to that same key (no intervening access), and
> `mᵢ.multiplicity ≠ 0` with `mⱼ.multiplicity = −mᵢ.multiplicity` (an active send/receive
> pair), then `mᵢ.payload.get? slot = mⱼ.payload.get? slot` for every `slot ∉ keySlots`.

With this, `writes_aux__prev_data = b` and `W = from_ts` become **entailments of `satisfies`**,
so the *existing* substitution machinery (`subst_correct`) eliminates them — no change to
`implies`/`equivalentTo`/`optimizerMaintainsCorrectness` at all, and the countermodel dies
because garbage-witness assignments are no longer satisfying. The cancelled ±pair (now
syntactically identical payloads) is dropped by a small pass using Layer 1's `neverViolates`.

Audit surface added: the per-VM one-liner above plus the documented justification. Caveat to
audit consciously: the conjunct uses **list order** as the fragment's access order (powdr emits
memory interactions sorted; your hint relies on the same). A timestamp-ordered formulation is
possible but much heavier, for no benefit on well-formed inputs.

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
2. **Layer 2** — OK to add `lastWriteKey` to `BusSemantics` and the adjacency conjunct to
   `satisfies` (both in `Spec.lean`), plus
   `lastWriteKey := fun busId => if busId = 1 then some [0, 1] else none` in the OpenVM
   instance? This is the audited part.

Layer 1 is implementable immediately and independently; Layer 2 builds on it (pair dropping and
digit solving reuse Layer 1 facts) but touches the frozen spec, so it ships second and separately
revertable.
