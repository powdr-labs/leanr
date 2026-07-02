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
    `some c` entries must match the evaluated message exactly, `none` entries are free. -/
structure BusFacts (p : ℕ) (bs : BusSemantics p) where
  /-- Accepted-value bound for payload slot `i` of messages matching a pattern:
      `slotBound busId pattern i = some B` means accepted payloads have `payload[i].val < B`. -/
  slotBound : Nat → List (Option (ZMod p)) → Nat → Option Nat
  slotBound_sound : ∀ m pattern i B, slotBound m.busId pattern i = some B →
    Matches m.payload pattern → bs.violatesConstraint m = false →
    ∀ x, m.payload.get? i = some x → x.val < B

  /-- Functional dependence: slot `out` is a computable function of the whole payload
      whenever a matching message is accepted (e.g. the XOR slot of a bitwise table). -/
  slotFun : Nat → List (Option (ZMod p)) → Nat → Option (List (ZMod p) → ZMod p)
  slotFun_sound : ∀ m pattern out f, slotFun m.busId pattern out = some f →
    Matches m.payload pattern → bs.violatesConstraint m = false →
    ∀ x, m.payload.get? out = some x → x = f m.payload

  /-- Buses whose messages never violate (e.g. stateful buses carrying no table). -/
  neverViolates : Nat → Bool
  neverViolates_sound : ∀ m, neverViolates m.busId = true → bs.violatesConstraint m = false
```

`BusFacts.trivial bs` (all `none`/`false`) exists for every semantics. *Bounds* are the
primitive rather than explicit value lists: they compose with `ZMod.val` arithmetic (see
digit-decomposition below) and yield enumerable domains (`List.range B`) exactly when small.
The vocabulary is VM-agnostic — bus ids, arities and functions are all data. If a VM has a
table that is neither an interval nor functional, the structure extends with new proven fields
without touching the spec.

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

One field in `BusSemantics` and one generic conjunct in `satisfies` (defined once, VM-agnostic):

```lean
structure BusSemantics (p : ℕ) where
  ...
  /-- `some k`: this stateful bus is a last-write-wins memory whose access key is the first
      `k` payload entries. Audited assumption: the surrounding VM implements offline memory
      checking on this bus and grants the fragment an exclusive timestamp window, so within a
      fragment, consecutive same-key accesses observe each other. -/
  lastWriteKey : Nat → Option Nat
```

New conjunct in `ConstraintSystem.satisfies` (the *only* semantic change):

> For any two interactions `i < j` (list order) on a bus with `lastWriteKey = some k`, with no
> interaction of the same evaluated key strictly between them, if
> `(bi_i.eval env).multiplicity ≠ 0` and
> `(bi_j.eval env).multiplicity = −(bi_i.eval env).multiplicity`, then the evaluated payloads
> of `i` and `j` agree beyond the key prefix.

With this, `writes_aux__prev_data = b` and `W = from_ts` become **entailments of `satisfies`**,
so the *existing* substitution machinery (`subst_correct`) eliminates them — no change to
`implies`/`equivalentTo`/`optimizerMaintainsCorrectness` at all, and the countermodel dies
because garbage-witness assignments are no longer satisfying. The cancelled ±pair (now
syntactically identical payloads) is dropped by a small pass using Layer 1's `neverViolates`.

Audit surface added: the per-VM one-liner (`lastWriteKey 1 = some 2` for OpenVM) plus the
documented justification above. Caveat to audit consciously: the conjunct uses **list order**
as the fragment's access order (powdr emits memory interactions sorted; your hint relies on the
same). A timestamp-ordered formulation is possible but much heavier, for no benefit on
well-formed inputs.

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
   `satisfies` (both in `Spec.lean`), plus `lastWriteKey := fun 1 => some 2 | _ => none` in the
   OpenVM instance? This is the audited part.

Layer 1 is implementable immediately and independently; Layer 2 builds on it (pair dropping and
digit solving reuse Layer 1 facts) but touches the frozen spec, so it ships second and separately
revertable.
