# Ideas for future optimization passes

Regenerated from scratch (2026-07-14). Every number here was re-measured this session: fresh
`opt-export` of all 100 openvm-eth cases + keccak (measurement base `656a9d8`, post-#114),
diffed against the checked-in `*.powdr_opt.json.gz` with canonical-polynomial comparison (mod p;
note powdr's export uses **binary `"-"`** nodes — tooling must handle both encodings). While
this regeneration was in flight, **#117 (entry 77) and #119 (entry 78) merged**, landing idea 2
(a)+(b) and the op-0 half of idea 4(d) below; the baselines and those two ideas were refreshed
on rebase from the entries' measured numbers. Older write-ups had stale or wrong gap
attributions; re-measure before trusting anything, including this file.

## Where we stand (post-#117/#119 + entry 80 = idea 4(b)+(c) + entry 81 = digit fold + entry 82 = NOT-form byte checks)

Absolute output totals (identical inputs, so `agg` effectiveness follows directly):

| benchmark | axis | apc | powdr | apc − powdr |
|---|---|---|---|---|
| openvm-eth (100) | variables | 27,762 | 30,885 | **−3,123 (lead; entry 85 JAL ladders −6)** |
| | bus interactions | 16,424 | 16,722 | **−298 (lead)** |
| | constraints | 10,955 | 20,299 | −9,344 (lead; entry 83 −60, entry 84 −252) |
| keccak | variables | 2,021 | 2,021 | **exact parity** |
| | bus interactions | 1,752 | 1,734 | **+18 (was +218; entry 82 −200)** |
| | constraints | 186 | 186 | **exact parity** |

Per-case standings on eth: variables **31 W / 7 L / 62 T** (entries 83/84 flipped 2 losses;
entry 85 flipped apc_034/066 to exact parity).
Bus per-case was **7 W / 67 L / 26 T** (+588 over losing cases) at the measurement base;
#117/#119 improved 37 case-measurements with 0 regressions (agg 3.439× → 3.479×, geo 2.723× →
2.753×; powdr 3.480× / 2.822×) — re-measure the standings before quoting them. The reported
`geo` metric is a per-case geomean, so the many small per-case bus losses — not the absolute
total — are why the bus number still trails on geo. **Variables are won; the remaining fight is
per-case bus hygiene.** Closing the losses below would put apc ahead of powdr on every axis of
both benchmarks except keccak, where the identified fixes land exactly on powdr's 1734/2021/186
— measured floor; nothing below it was found (see dead ends).

Exact gap decomposition (verified on the live circuits at the measurement base; buckets marked
LANDED are done — the remainder still adds up to the current gaps):

- **eth variables ~+22 over 7 cases** (was +172 over 29) = ~~M1 constant decompositions +135~~
  (**LANDED**: entry 81 −165 incl. cascades; entry 85 −6 = the mask-bounded `JAL` ladders,
  apc_034/066 now exact parity; residual = ladders with no mask check on the top limb, parts of
  apc_038/042/064) · ~~M2 comparison gadgets (apc_037 +14, apc_018 +9)~~ (**LANDED**: entry 83
  seqz collapse) · ~~M3 dead `bit_multiplier` +14~~ (**LANDED**: entry 84 −14, apc_038/051) ·
  everything else nets in apc's favor.
- **eth bus** (was +588 over losing cases; −191 + −132 + −141 landed) = ~~width-1 range checks
  90~~ (**LANDED**: entry 80 −89) · ~~cancellable memory pairs 78~~ + op-0 coverage waste
  (**LANDED**: #117 −76, #119 −115) · ~~constant-family checks ~126~~ (**LANDED**: entry 81
  −141) · long same-address chains **64** (apc_010 still 247 vs 239) · tuple-slot coverage waste
  (**remainder of the ≥112 bucket**) · ~~subsumed range checks 22~~ (**LANDED**: entry 80 ≈ −43,
  the base also catches byte/memory-subsumed wide checks) · ~~NOT-form byte checks 23~~
  (**LANDED**: entry 82 −20) · residual scattered.
- **keccak bus +218 → +18** (was +614; #117 −276 memory = exact powdr parity, #119 −45 op-0 waste,
  entry 80 −68 width-1, entry 81 −7, **entry 82 −200 NOT-form**) = ~18 misc — the bus-3
  width histograms are otherwise *identical* to powdr's, and NOT-form byte checks are gone.

## In flight / recently landed — check `git log origin/main` and open PRs before picking anything up

- **#117 merged** (interior memory pair cancellation = idea 2 (a)+(b)): keccak memory at powdr
  parity, eth −76. Only sub-items (c) and (d) of idea 2 remain.
- **#119 merged** (coda byte-pair splitting): the op-0 explode/dedup/drop/repack half of
  idea 4(d); keccak −45, eth −115. The tuple-slot half of 4(d) remains.
- **#114 merged** (is-equal sum-of-squares collapse). **#112 merged** (entry 79) — consolidated
  the collapse into a generalized `hintCollapse`, removing the standalone `EqCollapse` pass;
  effectiveness-neutral, ~half the collapse-stage runtime.
- **#122 merged** (entry 80 = idea 4(b)+(c)): width-1 → booleanity + subsumed range-check drop;
  eth bus −132 (aggregate flips to a lead), keccak bus −68.
- **Entry 81 (#120 merged): the bounded-payload digit fold** — lands the payload-ladder core of
  idea 1 below; see the re-scoped idea 1.
- **Entry 85 (PR #123): probed slot bounds** — reads the XOR-mask range facts
  (`[x, 192, 192 + x, 1]` ⟺ `x < 64`) into `BoundsMap`, closing idea 1's mask-bounded `JAL`
  ladder slice (apc_034/066 to exact parity). The same session built and *withdrew* the
  constraint-side fold after measuring it at +0 vars / +12 bus on top of the digit fold —
  see idea 1's closed slice and the dead ends.
- **#116 open** (gated constant-decomposition fold): fully subsumed — the digit fold (entry 81)
  lands the family from the payload side, and the ungated constraint-side angle measured at
  zero residual value (idea 1's closed slice). Close it.

---

## 0b. SP1 (rsp): after entries 93–99, the residual is the identity-result packing sensitivity + memory telescoping

**Entries 97–99 landed the dead-byte clusters and the degenerate range checks.** SP1 rsp
**variables 3.686× → 3.745×, bus 2.518× → 2.553×** (aggregate var gap vs powdr 837 → 658, bus gap
876 → 765; 0 regressions; OpenVM keccak byte-identical throughout):
- **Entry 97**: `xorEqExtract` generalized XOR→OR/AND (constant-only target — a wider target
  regresses; see below); `scaledZero` gained the two-term slot `k·v − k·w` forcing `v = w`.
- **Entry 98** (`RangeForceZero.lean`): SP1 op-6 width-0 check `[6, L, 0, 0]` → the equality `L = 0`
  (via `rangeCheckAt` bound 1), Gauss-consumable. −23 var gap, −51 bus gap.
- **Entry 99** (`RangeBool.lean`): SP1 op-6 width-1 check `[6, x, 1, 0]` → booleanity `x·(x−1)=0` +
  drop (the `rangeCheckAt` half of `ZeroWidthRange`'s width-1 arm). −44 bus gap (+44 constraints).

The k256 blocks (apc_024/030/040) still trail (apc_024 550 v vs powdr 490). Two residual levers,
both **investigated and found to need architectural work, not an incremental pass**:

### The identity-result packing sensitivity (biggest var lever, ~60 vars/k256-case) · BLOCKED

The `[1, result, byte_var, 0]` OR interactions (`result = OR(byte_var, 0) = byte_var`) leave `result`
as a redundant copy powdr substitutes away (`result := byte_var`). Enabling that in `xorEqExtract`
(a bare-variable target, not just a constant) is **correct** — but measured a **regression** on
apc_024 (556→612 v, 431→561 bus). Diagnosis (single-var vs const-only export diff): **memory is
untouched (32/32 both)**; the blow-up is a **range-check re-packing/re-encode explosion** — op-3
byte-pairs +44, op-6 +88, and `reencode` materialises +56 fresh byte variables when the substitution
changes the byte-check expressions. So the win requires making the packing/`reencode` passes
*representation-robust* (idempotent under a `result := byte_var` rename), not the extraction itself.
The extraction infrastructure (`ByteXorSpec.orOp/andOp`, `byteBoolSound`, `boolEq?`) is landed and
proven — only the constant-target guard holds it back.


Entries 93–96 landed four general, proven, `Implementation/`-only mechanisms — the reciprocal
nonzero-witness address-disequality certificate (`addrNonzeroNeq`), affine bound propagation in
`byteJustifiedW`, the SP1 byte-op result-slot bound, and **scaled-byte-forces-zero (`ScaledZero.lean`,
entry 96)** — taking SP1 from **variables 2.938× → 3.686×, bus 1.957× → 2.518×** (aggregate var gap vs
powdr 3715 → 837, bus gap 3209 → 876, both ~75 % closed; per-case-by-variables W/L/T 0/69/31 →
1/52/47). OpenVM is untouched throughout (keccak byte-identical). The register-access chains telescope
almost fully and the dead upper bitwise bytes are gone.

**Dead upper bitwise bytes — SOLVED impl-only (entry 96), was mis-diagnosed as an ISA floor.** The
earlier note here claimed powdr's upper-byte pruning needed an audited zero-extension assumption. That
was wrong: the fact is already in the circuit. SP1's byte-lookup range-check trick checks each operand
byte both bare (`v < 256`) and scaled (`8323072·v < 256`); a byte whose large-scaled copy is also a
byte must be `0`. `scaledZeroPass` intersects the two `slotBound` obligations and seeds `v = 0`; the
existing fold/`slotFun`/disconnected passes cascade it. No spec change was ever needed.

What remains, biggest first:

- **Carry / negative-coefficient memory slots (bus + vars, the big residual on the k256 blocks).**
  The register/RAM pairs that still don't telescope (apc_024/030/040) carry data limbs like
  `65536·(higher_limb_26 − higher_limb_27) + 8192·lower_limb_26 + higher_limb_0_27` — coefficient
  `p − 65536` — that are 16-bit **only when `higher_limb_26 = higher_limb_27`** (a same-address
  telescoping relation). `affineJustified`'s natural bound fails on the negative coefficient, and the
  sign-split (entry 97's `two_term_zero` machinery, which *does* handle mixed signs) still can't
  justify it because the slot is genuinely wide unless the relation holds — powdr's global sort-based
  memory argument establishes it; apc's *local* pair-cancellation checks the 16-bit obligation
  per-pair, before the relation is known, so it's circular. Two angles, both non-trivial: (a) a
  **relation-aware justification** — when a memory pair at address A is being cancelled, the
  send/receive data equality `d_send = d_recv` it would establish is exactly what makes the
  negative-coefficient slot 16-bit, so justify-then-cancel could be interleaved; (b) unify the
  interleaved same-address limb variables (`higher_limb_26`/`_27`) *before* the range check via a
  memory-value equality pass. Simpler slices that DID land are gone (the `8192·lower_limb` slots,
  `lower_limb < 8` from an op-6 `[6, _, 3, 0]`, are already justified by `affineJustified`).
- **Certificate generalizations** (cheap follow-ups to entry 93): match a nonzero witness up to a
  nonzero *scalar* (`g = λ·Σ(mᵢ − Sᵢ)`), not just `±1`; recognize reciprocal constraints in more
  additive shapes if a census finds `addrNonzeroNeq` missing live pairs.

## 0. wasm-eth: variable gap closed; global range-obligation repack is the last axis (after entries 87–89)

The `wasm-eth` corpus (100 cases, merged #131) had apc **far behind** powdr — the worst cases
(k256 `FieldElement10x26` square/mul, tiny_keccak `keccakf`) sat at 4.2–4.85× the powdr variable
count. Entries 87 (`addrAffineNeq`, the affine same-base address-disequality certificate) and 88
(pattern-aware `recvByteSlots`, which drops the vacuous byte obligation on non-{1,2} address-space
memory receives) closed the memory-forwarding failure that caused it. Re-measured full-corpus
(stack vs pre-fix `c6a167b`):

| axis | apc | powdr | apc − powdr |
|---|---|---|---|
| variables | 17,035 | 19,628 | **−2,593 (lead)** |
| bus interactions | 13,535 | 12,552 | +983 (**trails, +8%**) |
| constraints | 15.2× agg | 9.7× agg | lead |

Per-case variables W/L/T vs powdr **16/11/73**; worst variable-ratio case now **1.15×** (was 4.85×).
**Variables and constraints are won; the one remaining axis is bus interactions**, concentrated in
the two big k256 cases (apc_037 +351, apc_012 +511; mid cases small). Memory is fully telescoped
(apc_004 bus-1 44 = powdr 44).

### The remaining bus gap: global range-obligation rebuild  ·  *bus, wasm-eth*  ·  high value / medium effort

Measured on apc_004 (bus-1 memory already at parity), the excess is entirely **range-check
packing** — the large-corpus version of the existing repack ideas (§4, `TupleRange.lean` /
`ByteCheckPack.lean`), which apc's *pairwise* packers cannot recover after large-scale unification:

- apc emits **one tuple-range check (bus 7) per timestamp `lower_decomp` limb** —
  `[a__i, …timestamp_lt…lower_decomp__1]` — where powdr **batches** several decomposition limbs
  into a single arg as a linear combination: `[a__i, 15360·prev_ts + 15360·decomp + …]`.
  apc bus-7 **68** vs powdr **22** on apc_004.
- apc range-checks single `a__` result byte limbs on the tuple bus; powdr uses **byte-*pair***
  checks on the bitwise bus (bus 6): `[a__i, a__j, 0, 0]`. apc bus-6 **1** vs powdr **24**.

A **global** range-obligation rebuild would: collect every surviving range obligation, drop the
solver-implied ones, keep the strongest per normalized expression, and re-pack into batched
tuple/byte-pair checks. Bus-only (variable-neutral), so lexicographically acceptable. Highest-value
wasm follow-up; touches no audited surface.

### Residuals that fell out of the cascade — do NOT build (re-measured, now minor)

- **`bit_shift_carry` / `a__` result-limb variable excess.** The naive pre-fix estimate feared
  ~500 excess vars on apc_037; post-forwarding apc_037 is **+33 vars** and the corpus leads powdr.
  There is no var-side pass to write here (consistent with the `bit_shift_carry` dead-end below —
  representation choice is count-neutral).
- **Functional (op-1) bitwise XOR/rotate lookups.** Partly collapsed once forwarding turned the
  `b`/`c` operand limbs into actual values; re-measure on apc_037 before pursuing, and only after
  the range repack (smaller residual).
- **The ≤1-emitted-check cap** (`BusPairCancel.findCancelGoIdx`) is **not binding on wasm**:
  apc_004 memory is at exact parity, so write-back `prev_data` pairs telescope without needing
  multiple emitted checks. Leave the cap alone (it guards a measured apc_005-class eth regression).

### Runtime note (profiling target, not a regression)

The fixes are output-size wins at **flat runtime**: wasm-eth wall 1924 s (pre-fix) → 1965 s (stack),
*not* a collapse. Forwarding now succeeds, but the enabling scans (`findConsumer`/`midRefuted`
crossing the newly-refutable slots, plus the extra cancellations that now land) cost about what the
shrink saves; the big k256 cases still spend ~300–490 s each in the cleanup fixpoint. A cheap lever,
deliberately *not* taken in entry 87 (correctness-first): the affine disequality re-runs
`linearize` on both address slots per (S, m) pair; a memoized pre-linearized address-slot side
table (like `TwoRootMap`, passed as a plain argument) would cut the `busPairCancel`/`busUnify` scan
cost. Profile apc_037 first to confirm that is where the time goes.

---

## 1. Constant-decomposition folding — **CORE LANDED (entry 81, the bounded-payload digit fold)**

**What landed.** `DigitFold.lean` (cleanup cycle): a bitwise pair check asserting an affine
mixed-radix ladder `K ± (g·v₀ + 256g·v₁ + …)` is a byte, plus each ladder variable's own range
check, force the digits — after **wrap analysis** (BabyBear `p ≡ 1 (mod 256)` admits a phantom
digit vector per wrap count; the narrow top-limb range checks, e.g. the 6-bit PC limb, kill
them). The pass enumerates the whole (byte, wrap) grid and substitutes constants only on a
singleton solution set; one substitution per invocation, the cleanup fixpoint cascades (the
pinned digits resolve the adder carry disjunctions downstream — constant seeding *does* cascade
when the seed is the byte-check digits). Measured (entry 81): **eth −165 vars / −141 bus / −36
constraints over 33 cases, 0 regressions; keccak −4 vars = exact powdr variable parity.** This
covered the AUIPC+JALR ×14 chains (apc_026/045/055/085/094) and most of the `rd = pc+4`
link-register family; no keccak pair-matching regression (unlike #116's ungated constraint-side
attempt).

**Remaining slices of this idea:**
- ~~**Mask-bounded `JAL` link ladders** (apc_034/066 +3 each)~~ (**LANDED**: entry 85 — the
  "missing" top-limb bound existed as the genuine-XOR identity `[rd₃, 192, 192 + rd₃, 1]`
  ⟺ `rd₃ < 64`; the probed slot bound (`probedSlotBoundAt`) reads it into `BoundsMap` and the
  entry-81 fold does the rest. Both cases at exact powdr parity.)
- **Ladders with no mask check on the top limb** (parts of apc_038/042/064, ≲ +10 vars): the
  mod-p alias (digits of `K + p`) is then a satisfying *admissible* assignment, so no per-check
  fold is sound (`isCompleteReplacementOf` quantifies over all admissible assignments) — see
  dead ends. The only route is joint multi-constraint refutation (enumerate the adder cluster's
  carry booleans against the range facts, fold on a singleton). Census the exact residue before
  building anything; low ceiling.
- **Constraint-side affine seeds** (`Σ cᵢ·xᵢ = K` as an algebraic constraint rather than a
  payload ladder): **measured dead end** — built in full (entry 82's session: ungated batch
  `SubstMap` fold before `gauss` + seed-aware pivot declining + slot-form decode with remainder
  bound) and A/B'd on top of the digit fold at **+0 vars on all 100 eth cases / +12 bus**.
  Gauss's pivot mangling is what *feeds* the payload-side fold (`g`-scaled slot ladders are
  more rigid than raw seeds: `M % g = 0` kills wrap phantoms); protecting seeds starves it.
  Do not rebuild; close #116.

---

## 2. Memory-bus completion: the two remaining sub-items  ·  *bus, eth*  ·  medium value / medium effort

**Status.** Sub-items (a) two-root mid-region refutation and (b) entailed payload matching
**landed as #117** (entry 77): keccak memory is at powdr parity (258; −276), eth −76 with 0
regressions. As predicted, zero keccak variables died with the pairs — pure bus win. What
remains:

**(c) MemoryUnify stops at exactly two sends** (eth ~64 interactions; apc_010 is still 247 vs
powdr 239 after #117). The LOADB chains alternate `send(expr)/recv(var)` on one register with
only one limb differing syntactically; powdr adds receive=send equalities and telescopes the
whole chain (apc_010's register 44 had 7 sends + 7 recvs vs powdr's 1+1; also
apc_008/014/031/091/097). Extend `MemoryUnify`/`busUnify` chaining to fold N≥3 same-address
accesses iteratively (each step is the existing two-access argument; `iterateToFixpoint` already
drains repeated applications if the pass handles one link per pass). Re-measure the per-case
residue first — #117's coda invocation may have taken part of this.

**(d) Equal-timestamp pairs are self-certifying** (medium confidence; size the residue first).
A `+1/−1` pair with *identical* payload including timestamp needs no mid-region scan at all: any
real interleaved same-address access would have bumped the receive's prev-timestamp. This is a
completeness argument against `admissible` (last-write-wins in list order) — a new side condition
for `admissible_dropPair`. Also note #117's log entry deliberately forwent −6 keccak / −6
apc_100 bus (documented there) — check whether (d) or a cheaper tweak recovers them.

**Runtime.** #117 hit keccak 2.4× with naive per-cycle maps and fixed it with a once-per-pass
`Thunk`-built `TwoRootMap` + coda-only aggressive invocation; follow that pattern for (c).

---

## 3. Comparison-gadget completion: the seqz idiom  ·  *variables*  ·  **LANDED (entry 83, `SeqzCollapse.lean`)**

**Gap (post-#114 residue ≈ +57 vars).** `sltu rd, x, 1` ("set if x < 1", i.e. x == 0): powdr
recognizes the constant operand and replaces OpenVM's whole LessThan machinery — 4 `diff_marker`
booleans + `diff_val` + the `[diff_val − 1, 0, 0, 0]` bitwise send — with the two-line is-zero
gadget `cmp·(Σ xᵢ) = 0 ∧ inv·(Σ xᵢ) + cmp − 1 = 0` (byte limbs ⟹ `Σ xᵢ = 0 ⇔ x == 0`, no wrap).
apc kept 5 private witnesses per instance; instances: apc_037 ×4, apc_018 ×2, and a `+3..+7` tail.

**What actually landed.** A structural recognizer for the post-`monicScale` cluster (14 constraints
+ the range-check bus + the five private witnesses `m0..m3, diff_val`) collapses it to the two
is-zero constraints, dropping the five witnesses and introducing one `QuotientOrZero`-derived `inv`.
Runs in the coda after `monicScale` (so it matches the stabilised `-1 + x` serialisation and the
monic constant `2K = −1`); field-independent (matches the constants structurally), identity under
`BusFacts.trivial`.

**The previous mechanism note was wrong.** It claimed we could "reuse `collapse_correct`'s
parameterized reassignment" (#114). We can't: `collapse_correct` collapses **one** bilinear
reciprocal-witness constraint with **bus-free** witnesses, and `reencode_correct` keeps **every**
bus. Here the cluster is **14** constraints and one witness (`diff_val`) lives **inside a bus
interaction** (the range check), so neither framing applies. It needed a **bespoke ~500-line
`PassCorrect`**: a value-level characterization of the gadget (`seqz_forward` for completeness,
`seqz_reconstruct` for soundness — a per-limb case analysis rebuilding the markers), a template↔value
bridge (`clusterEval_iff`), the absolute byte law for the range bus (chaining `bytePairBus` with
`byteCheck`), and stateless-bus-drop framing for side effects / admissibility (`admissible_filterBus`).
It is emphatically **not impossible** under the current spec — the transformation is a genuine
refinement (powdr performs it) and is now fully machine-checked with no new axioms — just far larger
than the one-liner the earlier note imagined.

**Impact (measured).** apc_037 706 → 690 vars (now below powdr's 692); the pass fires on every
recognised `sltu x, 1` instance across eth. See entry 83 for aggregate figures. Keccak: none (its
one gadget landed with #114). Residual `+3/case` of inlined boolean-dataflow vars (powdr writes
`cmp1 + cmp2 − cmp1·cmp2` directly into payloads) is a separate, still-open idiom.

---

## 4. Stateless-check hygiene: recognize, justify, repack  ·  *bus, both benchmarks*  ·  high value / low-medium effort per item

Four convergent fixes to how byte/range obligations are recognized and laid out; (d)'s op-0
half landed as #119, **(b)+(c)** as entry 80, and **(a)** as entry 82 (below). The remainder —
(d)'s tuple half — is worth a few dozen eth bus interactions. Independent items — land separately.

**(a) NOT-form byte checks — LANDED (entry 82).** New fact `BusFacts.xorComplCheck` (bitwise bus,
gated `256 ≤ p`); `RedundantByteDrop.byteCheckOperands?` and `ByteCheckPack.svCheck?` gained the two
NOT arms `[x, 255, 255 − x, 1]` / `[255, x, 255 − x, 1]` (third slot decided `= 255 − x` by
`normalize`/`constValue?`), so the coda drops them when the operand is byte-justified and the
cleanup-cycle packer folds them into pairs. **keccak −200 bus** (1952 → 1752; variables and
constraints unchanged — DigitFold/#120 already reached 2021-var parity, so no further var cascade
and no runtime cost); **eth −20 bus over 3 cases, 0 regressions, variable-neutral** (bus agg
3.536× → 3.541×). *The "reflection / AND-OR justification rule" the earlier write-up demanded (84
keccak operands via a `255 − v` rule in `byteJustified`) was unnecessary: re-measured, every one of
the 200 NOT-form operands also occurs as a raw variable in a genuine-XOR slot that `slotBound`
already bounds to 256, so `byteJustified` justifies all 200 with the existing machinery — the
84-via-reflection figure was a stale attribution from base 656a9d8.*

**(b) Width-1 range checks → booleanity — LANDED (entry 80).** `[e, 1]` on the var-range bus ⟺
`e ∈ {0,1}` ⟺ `e·(e−1) = 0` (degree 2 ≤ 3). `ZeroWidthRange.lean` grew a width-1 arm: ADD the
booleanity via `PassCorrect.ofEnvEq` (accepted `[e,1]` forces `e.val < 2`), DROP the interaction
via `filterBusEntailed_correct`. **No new `BusFacts` field was needed** — the width-1 iff comes
straight from the existing mult-generic `varRangeBus` fact, so the idea's proposed `oneRangeBool`
was redundant. Gated on `p` prime (backward direction needs an integral domain) with a
per-candidate degree gate (`e.degree ≤ 1`) so it never trips the whole-pass `guardDegree` revert.
Measured: keccak −68 bus / +68 con, eth −89 bus / +90 con, **0 variable regressions**.

**(c) Subsumed range checks — LANDED (entry 80).** `SubsumedRange.lean` (coda) drops a var-range
check `[x, w]` when the **non-circular base** (interactions this pass never drops) already bounds
`x` by `b' ≤ 2^w`, via the proven `findVarBound` (`slotBound`-derived: tuple slots, byte-limb
memory receives, any retained range check) + `filterBusEntailed_correct` — the exact structure of
`RedundantByteDrop`. Two corrections to the original write-up: the direction is **`≤`, not strict
`<`** (apc_038's `mem_ptr_limbs__1` sits in a `[256, 8192]` tuple slot bounding it by exactly
`2^13`, which a strict test would miss; the non-circular base — not strictness — is what prevents
mutual-subsumption double-drops), and because the base subsumes byte/memory sources too it reaches
**~43 eth interactions**, not 22. Measured: eth ≈ −43 bus, **0 variable/bus regressions**; keccak
has no such pairs (0).

**(d) Coverage repack after unification — tuple-slot half** (op-0 half **LANDED as #119**,
entry 78: explode `[a,b,0,0]` into single-value checks in the coda, dedup, drop justified
operands, re-pack — keccak −45, eth −115, 0 regressions). Root cause was: packing passes run in
the cleanup cycle, then `gauss`/collapses unify variables, and nothing re-normalized coverage.
The **tuple bus got no such treatment**: duplicate-covered v2 slots (apc_100 covers
`mem_ptr_limbs__1_{0,38,46}` twice) and constants burning v1 slots (apc_026/051/071:
`v1 ∈ {0, 245, 78, 32}`) remain. Extend the #119 coda sequence to tuple interactions: unpack
`[x, y]` back into byte-check + range-check obligations, run the same dedup/justify/drop, and
re-pack exact-cover (pair byte+≤2048 into tuple slots, bytes two-per op-0). Same building blocks
(`svCheck?`, `mergeStateless2_correct`, `tupleRangeBus`/`varRangeBus` facts); like the split
pass, it transiently increases the bus count, so **coda only**, never inside the size-decreasing
fixpoint. Size the residue first (a few dozen eth interactions). Caution: 2–7-bit range checks
must NOT be packed as bytes — that *weakens* them (measured: none of the 202 sub-byte checks on
keccak are exactly 8 bits).

---

## 5. One-hot annihilation — **LANDED (entry 84, `OneHotAnnihilate.lean`)**  ·  *variables*

`OneHotAnnihilate.lean` (cleanup cycle): a dead shift-multiplier `x` is kept alongside
`mᵢ · x = 0` (for each one-hot marker) and the closer `±(Σ mᵢ − 1) · x = 0`; these force `x = 0`
(`s·x = 0` from the products, `(s∓1)·x = 0` from the closer). The pass recognizes the closer's
affine cofactor `±(Σ mᵢ − 1)`, checks each marker product is present, and adds the entailed
`x = 0` (`addConstraints_correct`); Gauss then eliminates `x` and its ~18 product constraints.
Measured (vs #125): **eth −14 vars / −252 constraints over 2 cases (apc_038, apc_051), 0
regressions** (agg vars 4.548× → 4.551×, W/L/T 31/10/59 → 31/9/60); keccak unchanged (no-op),
runtime neutral.
The `Σ mᵢ = 1` need not be a standalone constraint — the recognizer works from the closer alone,
and accepts both closer signs (mid-cycle the optimizer holds the negated `(1 − Σ mᵢ)·x` form).

---

## Smaller follow-ups

- **Register-increment tail on keccak (−4 vars, −3 op-0)**: the final-instruction
  read-modify-write chain keeps `rs1_data`/`rd_data`/`a` vars powdr substitutes through to the
  original read. Only worth it bundled with other keccak work.
- **op-0 checks with a constant slot** (keccak 2, eth handful): `[120, a__1_672, 0, 0]` wastes a
  slot on a constant — fold into the packer (part of 4d).
- **Multiplicity-guarded duplicate stateless sends** (`[t] mult f` + `[t] mult (1−f)` → `[t]
  mult 1`): not observed in current outputs; only revisit if a census finds instances.

## Measured dead ends (all re-verified this session — do not re-propose without new evidence)

- **Constraint-side digit folding / pre-Gauss seed protection** (entry 85's session): the
  complete mechanism (ungated batch `SubstMap` fold before `gauss`, seed-aware pivot
  declining/deferral under optimistic bounds, slot-form decode with a remainder bound) measures
  **+0 vars on all 100 eth cases / +12 bus** on top of the payload-side digit fold. Pivot
  mangling *feeds* the digit fold; protecting seeds starves it. Also learned: `BoundsMap` is
  empty in cleanup cycle 1 (every multiplicity is validity-flag-guarded until the first `gauss`
  pins the flag), so bounds-gated passes are inert there.
- **Per-check folding of ladders whose limbs are genuinely all-byte**: the mod-p alias (digits
  of `K + p`) is a satisfying, admissible assignment, so a per-constraint/per-check fold breaks
  `isCompleteReplacementOf` — not merely unproven, *incorrect*. Check for a mask/range fact on
  the top limb first (entry 85 reads the XOR-mask encoding); only genuinely uncovered ladders
  need joint refutation.
- **Keccak below powdr**: nothing exists. XOR dag is *perfectly clean* — 0 duplicate operand
  pairs, 0 trivial identities, 0 dead results, 0 collapsible `(a⊕b)⊕a` chains; apc's 862 genuine
  XORs ≡ powdr's 862 (87 differ only in inlining depth). Memory: no semantic pairs beyond the
  142 exact ones. Range: no redundant widths. The identified fixes land exactly on 1734/2021/186.
- **Timestamp-decomp encodings**: 2 vars per first access is the floor; apc keeps {lo, hi},
  powdr {prev_ts, lo} — verified 1:1 wash in all 100 cases + keccak (258 = 258).
- **mem_ptr decomposition**: 2 vars/pointer floor (carry already collapsed by carryBranch);
  powdr identical (2,578 vs 2,632 corpus-wide, apc slightly ahead).
- **bit_shift_carry**: representation choice (carry- vs output-byte witnesses), count-neutral
  except one +4 case; width-1 instances are handled by idea 4b, width-5 ones are a wash.
- **Variable-count via derived columns / functional dependence**: structurally impossible
  (variables are counted syntactically; XOR is neither polynomial nor a `ComputationMethod`).
- **Result-zero XOR `[x,y,0,1]`**: zero instances in optimized outputs (measured 3×).
- **Constant-operand XOR beyond {0,255}**: those are the only affine constants; C4a/C4b landed.
- **Packing 2–7-bit range checks as bytes**: unsound direction (weakens the bound) — none are
  exactly 8 bits.
- **`flags` refolding, varRange-as-variables, `b`/`c` naming diffs, PC-lookup drops,
  disconnected witnesses, DigitEq wiring**: no targets (apc already wins `flags` by ~4,500 vars
  corpus-wide; keep it that way — test any new pass against the apc_005/009 flag folds).

## Working rules (from this iteration's failures)

- **Check for duplicates first**: #112 and #114 implemented the same idea concurrently; #112's
  effort was wasted. Look at open `optimizer-only` PRs and recent `claude/*` branches.
- **Runtime is a de-facto merge criterion**: +54% (#112) and +16% (#116) stalled; +1.4% (#114)
  merged. Build per-pass indexes once (`TwoRootMap`, `CoveredIndex` precedents); never rescan
  the system per candidate; put once-suffices passes in the coda, not the fixpoint cycle.
- **Measure per-case, not just aggregate**: `opt-export` + a canonical-form diff against
  `*.powdr_opt.json.gz` finds the mechanism; `benchmark.py` (+ keccak) confirms the totals. The
  geo metric moves with per-case wins — 67 small bus losses cost more than one big one.

## Runtime leftovers (from the entry-90 runtime overhaul — see that log entry for the map)

Levers identified but not taken, in rough value order (keccak profile shares at entry-87's end
state; every item is output-preserving unless noted):

- **domainBatch on keccak (~19 %)**: per-target work is now the unordered covered gather +
  `assignments` box materialization + `DomainTable` rebuild per invocation. Candidates:
  stream the box instead of materializing (`assignments` allocates the full product), and a
  domainFold-style single-var prefilter for the *constraint-sourced* domain targets (bus-fact
  domains make the general case harder). The user-suggested SAT-style propagation (prune the
  box by evaluating constraints on partial assignments) fits `forcedOver`'s certificate shape —
  the checked survivor scan visits every box point today; a DPLL-style search needs the skipped
  subtrees refuted by a partially-determined covered item, which is provable but a real proof.
- **reencode/domainFold accept-path on keccak**: `reencodeOut`/`foldOut` rewrite the whole
  system per accept (inherent), but reencode also rebuilds its covered index + `cs.vars`
  HashSet per accept; a stale-bucket refresh (the `FoldIdx.refresh` trick — buckets are
  positional supersets when items are mapped in place) does not directly apply because
  `reencodeOut` *removes* covered constraints (positions shift). A position-stable
  `reencodeOut` variant would unlock it for both passes' constraint side.
- **gauss (~6 % keccak)**: untouched this round.
- **dedup (~4 % keccak)**: `List.dedup` over constraints and the `bi ∈ seen` scan are both
  quadratic with deep equality. Hash-bucketed variants need `mem`-iff lemmas (the pass proof
  consumes `List.mem_dedup`); ~100 lines of HashMap invariant proofs.
- **rootPairUnify (~2-8 %)**: `scaledSlotBound`/`anyVarBound` rescan interactions per variable —
  the `findVarBound`-per-candidate pattern that busPairCancel just shed.
- **zeroWidthRange (~1.7 s/eth case)**: two `rangeEq?` scans per invocation (filterMap + keep);
  fusing them into one tagged pass needs the `filterBus`-shaped proof reworked.
- **Cross-cycle memoization (the big structural one)**: the cleanup cycle runs 5–9 times and the
  enumeration passes rediscover the same negatives every cycle. A pass-state channel (e.g.
  `VerifiedPassW` threading an opaque cache blob validated by cheap hashes) would cut the
  steady-state tail of *every* pass at once; needs a framework change in
  `Implementation/OptimizerPasses/Basic.lean`'s glue, so weigh against the audit-surface rule.

## Runtime leftovers II (generated-C audit of the wasm-eth heavy cases)

Reading the compiled C (`.lake/build/ir/`) plus a flat `perf` profile of wasm-eth `apc_012`
(435 s at entry-90 state) shows ~40 % of big-case runtime is heap churn (`lean_dec_ref_cold`
19.7 %, allocator 14.8 %, `List.reverseAux` copying 4.8 %), with `Variable` equality at 10.3 %.
Pass ranking there: gauss 98 s, tupleRange 96 s (**taken — see the batch-drain entry**),
busPairCancel 52 s, rootPairUnify 51 s, domainBatch 34 s. Levers not yet taken, in value order
(all output-preserving unless noted):

- **ZMod instance reconstruction per scalar op**: e.g. `addCoeff`'s merge branch compiles to
  `ZMod.commRing p` → three structure projections → `lean_apply_2` **per field addition**; 400+
  such construction sites across the pass C files. BabyBear values keep even products inside
  Lean's tagged-scalar Nat range, so the arithmetic is nearly free — the whole cost is
  dictionary building + dispatch. Fix: extend `IExpr.evalWith`'s hoisted-ops pattern
  (DomainBatch) to `addCoeff`/`mergeTerms`/`linearize` and other hot arithmetic, or `@[csimp]`
  fast ZMod ops compiling to direct `Nat` add/mod.
- **gauss reduces every constraint unconditionally**: `pending = cs ++ cs` — each constraint
  pays `substF` (full tree copy; shared nodes defeat ctor reuse) + `normalize` (quadratic
  `addCoeff` merge) twice per invocation even when the solution map is empty or disjoint from
  the constraint. Fix: solved-vars mention prefilter (HashSet), plus a var → dependent-solutions
  index instead of `σ.map.toList.filter` per accepted pivot.
- **rootPairUnify quadratic seen-join**: `rpLoop` probes `seen.findSome?` per candidate with
  deep key comparison (`e.key == xk.2` compares full term lists); `seen` grows over the sweep.
  Fix: hash-bucket `seen` by key hash (the `Expression.structHash` precedent from BusUnify).
  Also `rpCandidates` runs `c.vars.eraseDups` (quadratic, string-compare equality) per
  constraint, and a `ZMod` inverse per candidate.
- **`sizeKey`/`varCount` ≈ 7.6 % of the run**: `Expression.vars` compiles to a per-node
  `List.appendTR` (copies the whole left sublist — O(size × depth) cons allocations), then
  `varCount` string-hashes every occurrence; `iterateToFixpoint` recomputes the key twice per
  step (the previous step already computed it). Fix: fold the tree straight into the `HashSet`
  and thread the computed key through the recursion.
- **Variable identity ≈ 12 %**: the parser creates a fresh `String` per occurrence (~340 k
  occurrences / ~17.5 k distinct on `apc_012`, names avg 24 chars with long shared prefixes),
  so `lean_string_eq`'s pointer fast path never fires; every hash walks the full string; and
  the derived `DecidableEq Variable` allocates a closure per names-equal comparison (generic
  `Option Nat` dispatch — visible in `Spec.c`). Fix: intern variables in the parser
  (`HashMap String Variable` pool; Implementation-only). A hand-written `DecidableEq Variable`
  or a dense-id representation would also help but touches `Spec.lean` (audited).
- **Runtime `decide p.Prime` per invocation** in flagFold (×3 entry points), flagUnify,
  rootPairUnify, busPairCancel — trial division (`Nat.minFacAux`, ~22 k steps for babyBear);
  in redundantByteDrop the decide sits **inside the per-element lambda**
  (`ops.all (fun e => byteJustified (decide p.Prime) …)`). Dominates the small-APC tail. Fix:
  hoist out of the lambda; longer-term decide once at pipeline entry and thread the result.
- **flagFold derive-and-discard**: the box-constraint predicate recomputes `c.vars.eraseDups`
  four times inside one expression; compute once per constraint, HashSet-dedup.
- Lower priority: `withPtrEq`-shortcut structural equality for `Expression`/`BusInteraction`
  (safe, Implementation-only; helps `dedup`'s quadratic `bi ∈ seen` and remaining split
  decides); `substF` no-change signaling to preserve sharing; incremental lengths in `sizeKey`.

## Runtime leftovers III (post the "de-quadratify seen-scans / dedup / enumeration" PR)

That PR **cleared** these earlier leftovers (all output-preserving, proven, verified byte-identical):
- **rootPairUnify seen-join** and **flagUnify/flagFold-A seen-scans** — the `seen` history is now a
  `Std.HashMap UInt64 (List …Seen)` bucketed by a hash of the match key; the O(C²)/O(B²) scan
  becomes a per-bucket scan (the search is proof-free — a re-checked certificate — so bucketing
  preserves the picked element and every proof).
- **dedup bus-side `bi ∈ seen`** — bucketed by `BusInteraction.bHash`; `dedupStatelessFast_eq`
  proves the identical list via a HashMap↔list-agreement induction; **keccak dedup 16.6 s → 7.0 s**.
- **reencode/domainFold enumeration eval** (the entry-54 `evalFast`/`envOf` tax) — `groupSurvivorsE`
  compiles the covered constraints once per target to positional `IExpr` with hoisted ring ops
  (`compileEs`/`survZeroCW`, the `domainBatch` `compiledSurv` treatment); `groupSurvivorsE_eq` proves
  the identical survivor list. Helps the DIRECT path (<8192 constraints); keccak already indexed.
- **flagFold-B O(N²) eraseDups**, **domainFold double `foldOut`**, **domainBatch `fdoms.map fst`**
  recompute — hoisted / linearized.

**Dropped after measuring** (do NOT re-propose without new evidence): domainFold index-threshold
lowering (index is circuit-dependent — helped some large eth cases, regressed others); constraint-
side dedup hash-pair (keccak dedup is bus-side-dominated → pure overhead); gauss substF-rebuild-skip
for solved-var-disjoint constraints (neutral on keccak — the solution map is large, few disjoint).

### Remaining quadratic (or worse) algorithms, rough value order

- **The cleanup fixpoint is an O(size) structural multiplier**: `iterateToFixpoint cleanupCycle`
  runs ~O(#vars+#bus) cycles (keccak 9), each re-running every pass over the whole system, and the
  enumeration passes rediscover the same negatives every cycle. Cross-cycle memoization (a pass-state
  channel threaded through `VerifiedPassW`) would cut every pass's steady-state tail at once — but it
  needs a `Basic.lean` glue change; weigh against the audit-surface rule.
- **Finite-domain enumeration trio (keccak's dominant ~57 %) — near-linear-with-large-constant, not
  quadratic, on keccak** (indexed paths, >8192 constraints). The residual is `CoveredIndex.coveredIdx`
  gather + `CoveredIndex.build` **rebuild-per-accept** in `reencode`. A **position-stable
  `reencodeOut`** (keep covered constraints in place, marked dead, so positions don't shift) would let
  it use `FoldIdx.refresh` like `domainFold` instead of a full rebuild — **the single biggest keccak
  lever left**. `domainBatch`'s box scan is already `compiledSurv`-hoisted; its residual is the
  pinned-(domain-1)-var box bloat — substitute pinned constants and enumerate only free vars, needs
  `forcedOver` soundness reproven against the reduced box.
- **gauss — O(V²) resolved-map maintenance** (`σ.map.toList.filter (·.mentions x)` per adopted pivot,
  `Gauss.lean` ~line 200): materializes the whole solution map per pivot. Needs a proof-carrying
  reverse index `var → keys-whose-value-mentions-it` in `Solved`, with a **completeness invariant
  maintained through resolution** (adopting `x:=t` moves entries from `depIdx[x]` to `depIdx[t.vars]`)
  — that invariant is the hard part.
- **busPairCancel — O(B²), worst O(B³)**: the from-index-0 live-prefix rebuild + `shieldOk` scan per
  drop, inside its own `iterateToFixpoint` (one pair/drop). The shield depends on the prefix, so this
  is **positional/consecutive, NOT value-bucketable** — needs incremental shield state. Just
  array-optimized in #151; high risk.
- **busUnify — O(B²)**: `candidateSplits` per active send × `findConsumer` forward scan, no
  amortization. Positional (first forward consumer), not value-bucketable.
- **dedup constraint-side — O(C²)**: `cs.algebraicConstraints.dedup` (`List.dedup`, deep `Expression`
  equality). A `(structHash c, c)` hash-pair + `dedup_map_of_injective` is a cheap CONSTANT-factor win
  (short-circuit on the hash) but stays O(C²); a true O(C) needs `List.dedup`'s keep-last order
  preserved through a HashMap dedup (a mem-iff / list-equality proof).
- **oneHotAnnihilate O(C²)** (`hasProd` scans all constraints per marker; in the cleanup cycle →
  O(C³) compounded), **hintCollapse O(C²+C·B)** (`occursOnlyInTarget` full-system scan per
  single-occurrence variable), **seqzCollapse O(G²·C)** (self-fixpoint, one gadget/full-scan step,
  coda) — smaller absolute cost; per-container / bucket-by-shape indexes would help.
- **reencode/domainFold DIRECT paths O(C²)** — only reached below 8192 constraints (small, fast);
  harmless, noted for completeness.

**Why keccak vs SHA differ**: keccak is dominated by the near-linear-large-constant enumeration
(above the index threshold), so it scales ~n^1.4; the genuinely-quadratic passes above are a smaller
keccak slice. For larger circuits (SHA) the O(B²)/O(V²)/O(C²) passes outgrow the enumeration and
dominate (~n^2.5 effective). The seen-scan/dedup fixes above are asymptotic, so they help SHA-scale
disproportionately; a full "massive SHA" result also needs busPairCancel/gauss/busUnify de-quadratified.

Cross-cutting constant factors (from leftovers II, still open): `Variable` is a fresh `String` per
occurrence → equality/hash walk the full name (~10–15 % of big-case time; intern in the parser,
Implementation-only); ZMod-instance reconstruction per scalar op (extend the `IExpr.evalWith` /
`Expression.evalFast` hoist to `addCoeff`/`mergeTerms`).
