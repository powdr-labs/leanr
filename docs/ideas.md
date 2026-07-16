# Ideas for future optimization passes

Regenerated from scratch (2026-07-16) by a fresh-eyes structural pass at measurement base
`e0d2911` (post-#140, the tupleRange coda deferral). Method: `opt-export` + **canonical mod-p
polynomial** diffs against `*.powdr_opt.json.gz` on sampled cases (wasm 004/012/037, eth 010; the
big-case exports take 5–8 min each), an exact packing-optimality model checked against all 201
`powdr_opt` files, and full `benchmark.py` runs of both 100-case corpora. The previous
regeneration (2026-07-14) predates #140, which closed most of the then-open wasm bus gap — every
older per-case number in the log is stale for layout questions; re-measure before trusting.

## Where we stand (post-#140, full benchmark runs 2026-07-16)

| benchmark | axis | apc (agg / geo) | powdr (agg / geo) | verdict |
|---|---|---|---|---|
| wasm-eth (100) | variables | **7.228× / 3.588×** | 6.273× / 3.542× | lead (agg + geo) |
| | bus interactions | **6.099× / 2.886×** | 5.666× / 2.868× | **lead — the last trailing axis flipped with #140** |
| | constraints | 15.165× / 10.438× | 9.671× / 11.949× | agg lead, geo tail |
| openvm-eth (100) | variables | **4.552× / 3.887×** | 4.092× / 3.787× | lead (agg + geo) |
| | bus interactions | **3.557× / 2.812×** | 3.480× / 2.822× | agg lead, geo −0.010 tail |
| | constraints | 10.845× / 12.026× | 5.853× / 10.311× | lead (agg + geo) |
| keccak | variables / constraints | parity (2,021 / 186) | | parity |
| | bus interactions | 1,752 | 1,734 | +18 (measured floor, see dead ends) |

Per-case variables W/L/T vs powdr: wasm 16/11/73 (losses are a handful of vars on tiny blocks),
eth 31/7/62. **apc-optimizer now leads or ties powdr on every aggregate axis of every corpus.**
The remaining apc-vs-powdr deltas are Gauss pivot-order noise (±1–4 % per case, see §k256), and
the remaining distance to the *information floor* is a sum of scattered ≤2 % residues. **No
double-digit in-spec lever was found** — a floor argument per mass class is below, then the
out-of-spec levers that *would* be big, then the small in-scope leftovers.

## Output mass structure (what the surviving size *is*)

powdr output totals (apc's are the same shape; from the 2026-07-16 census):

| corpus | bus composition | top variable classes |
|---|---|---|
| openvm-eth | varRange 8,611 (51 %) · memory 5,690 (34 %) · tuple 1,178 · bitwise 1,043 · exec 200 | boundary data (prev/read/write_data) ~12.3k (40 %) · flags 4.5k (powdr only — apc already drops them) · a/b/c ALU 3.6k · mem_ptr_limbs 2.6k · timestamp lt (prev_ts + decomp) ~5.6k (18 %) |
| wasm-eth | varRange 3,684 · bitwise 3,376 · tuple 2,850 · memory 2,442 · exec 200 | `a` (k256 wide-mul byte witnesses) 8,854 (45 %!) · boundary data ~2.3k · timestamp lt ~1.6k · shift markers ~1.6k |

So: **range checking is 51–77 % of all surviving bus interactions; boundary data + timestamp
machinery + ALU byte witnesses are ~80 % of surviving variables.** Any big idea must attack one
of these masses — and each is at a floor:

## The floor analysis (why the big masses cannot shrink in-spec)

1. **Stateless-check packing is already optimal.** Model: obligations partition into
   *exactly-8-bit* (op-0/tuple-slot-1 eligible), *exactly-s2* (tuple-slot-2 eligible), and *solo*
   (everything else — varRange only). Optimal interaction count = solo + a maximal pairing of the
   first two classes. Measured **gap = 0 on all 201 `powdr_opt` files and on all sampled apc
   exports** (`packgap.py` method in the session notes). Two soundness walls make the model tight:
   *slot weakening is unsound* (placing a width-w obligation in a slot asserting a bound > 2^w
   loses soundness — output assignments stop mapping into the input; this kills 12-bit→8192-slot,
   7-bit→byte-slot, and all "batch into a wider varRange width" variants), and *linear-combination
   batching of two unknowns is unsound* (bit stealing: `x + 2^a·y < 2^(a+b)` admits `x ≥ 2^a`).
   A single table row certifies at most log₂(table size) bits of fresh witness: varRange ≈ 2^26,
   tuple 2^19–2^21, bitwise op-0 2^16. Do **not** build a global set-cover repack pass.
2. **Timestamp lt-machinery is floored at 2 vars + 2 interactions per boundary address on eth
   (2 vars + 1.5 interactions on wasm).** The obligation is 29 bits (`cur − prev − 1 = d_lo +
   2^17·d_hi`, `d_lo < 2^17`, `d_hi < 2^12`); the largest single slot is 25 bits, so ≥ 2 pieces
   and (with one Gauss-eliminable limb) exactly 2 variables. Re-splitting into byte-friendly
   pieces — e.g. `(8, 21)`: byte + 21-bit, the byte packable at density 2, worth ~−1,400 eth
   interactions — **requires witnesses `ComputationMethod` cannot express**: the spec's grammar
   is `constant | quotientOrZero | ifEqZero` (Spec.lean), and `⌊d/256⌋`/`d mod 256` are neither
   (an ifEqZero tree would need 2^17 leaves). eth's tuple slot-2 is 8192 = 2^13 (per-corpus
   bus_map — see working rules) but placing the 12-bit limb there is slot weakening (unsound).
   wasm's (256, 4096) slot-2 exactly fits the 12-bit limb and is already used (that is the whole
   apc/powdr wasm-vs-eth tuple-count difference).
3. **Memory is floored at 2 interactions per boundary address** — the bus interface itself
   (consume the cell state, re-produce it; identical-payload interior pairs already telescope).
   Verified complete: eth apc_010 total 239 = powdr 239 (the old "247 vs 239" 2(c) chain item is
   **closed** by #117+#140); eth010 bus-1 78 = 78; keccak memory 258 = parity since #117.
4. **Boundary data is floored at 4 limbs/word**: read words carry 4 free receive-payload
   variables (byte bounds are multiplicity-aware receive facts, no checks); written words carry 4
   dead-but-mandatory `prev_data` receive variables plus the written limbs (already expressions
   wherever their definition is linear; their byte checks are mandated by `breaksInvariant`).
5. **ALU/wide-mul byte witnesses (45 % of wasm variables) are floored by the degree bound**:
   their defining constraints are degree-2 and their use sites are degree-2 (payloads capped at
   2, identities at 3), so substitution is blocked, and each private byte witness needs its own
   table row (information bound, item 1).
6. **k256 shift-window residue** — the only measurable apc-vs-powdr output delta left anywhere:
   wasm037 +33 vars/+57 bus, wasm012 +27/+52 (~1.7 %/4 % of those cases; far less corpus-wide).
   Canonical-polynomial diffing shows the surviving check sets are **identical except for which
   alias of an equal value survives** (e.g. apc's `b__7_79` vs powdr's `a__7_67` in otherwise
   coefficient-identical shift-window checks — each system keeps exactly one representative, they
   just pick different Gauss pivots, and apc's pick wastes ~1 var + ~2 width-2 checks per shift
   window). Steering pivot order is high-risk/low-reward: pivot mangling is what *feeds*
   DigitFold (measured, see dead ends), and the value is ~1 % corpus-wide.

## Out of scope for this repo, recorded for spec/toolchain owners

These would be big, but they change the audited surface or the benchmark input format — not
autoopt material; do not attempt them in the loop:

- **Extend `ComputationMethod` with floor/mod (or byte-extract)**: unlocks re-splitting every
  range decomposition to byte-aligned pieces; the timestamp (8,21) re-split alone is ~−1,400 eth
  bus interactions (−8.5 %), variable-neutral.
- **Size the tuple checker to the lt-decomp on the input side** (e.g. (2^17, 2^12)): one tuple
  interaction per boundary address = ~−2,850 eth bus (−17 %).
- Both were checked against the current spec and are cleanly blocked (derivation grammar;
  slot-weakening soundness).

## Remaining in-scope items (all small; ranked by value/risk)

1. **k256 pivot steering** (§6 above): ~+60 vars/+110 bus recoverable on the two heavy wasm
   cases, unknown small tail elsewhere. High risk (DigitFold feeding, apc_005-class flag folds).
   Only attempt with a per-case A/B harness ready and the dead-end list in hand.
2. **Constraint-count geo tail (lowest-priority axis)**: wasm constraint geo 10.438× vs powdr
   11.949× — powdr wins the geomean on small cases while losing the aggregate 15.165× vs 9.671×.
   If the geo metric matters, census the smallest blocks' constraints; likely `is_valid`-guard
   or booleanity layout differences. Strictly third-axis, variable/bus-neutral work.
3. **Equal-timestamp self-certifying pairs (old 2d)**: −6 keccak / −6 eth bus, and only reachable
   mid-cycle where entailed matching measured as a net loss (+34 bus per apc_005-class case,
   keccak 2.4× runtime — entry 77). Effectively dead; left here so nobody re-derives it.
4. **keccak +18 bus**: previously measured floor (XOR dag clean, memory at parity, ranges
   optimal). Nothing found below 1,752 this session either.

## Measured dead ends (do not re-propose without new evidence)

New this session (2026-07-16):

- **Global stateless-check repack / set-cover pass**: layout already optimal, gap 0 on all 201
  powdr files and all apc samples (floor item 1).
- **Mod-p duplicate checks surviving dedup**: none — canonical-polynomial hashing over wasm037's
  1,347 stateless interactions finds 1,347 distinct (and 1,292/1,292 for powdr). Dedup is
  airtight; sign/normalization noise in JSON-level diffs is not a real gap (powdr serializes
  binary `-`, apc `p−k` constants — canonicalize before diffing or you will see ~1,000 phantom
  "only" entries per side).
- **Operand-copy unification (`b`/`c` vs `read_data`)**: a renaming wash, not a gap — 0
  constraints mention both aliases; each system keeps exactly one representative per value
  (§k256). The set-level var-prefix diffs (48 `b` vs 40 `read_data` etc.) are pivot-choice noise.
- **Timestamp decomposition re-splits (any shape)**: blocked by the derivation grammar (floor
  item 2). This includes (8,21), (11,18), (18,11), 3-limb byte splits, and cross-address batching
  (bit stealing).
- **Weakened-slot packing**: 12-bit limbs into eth's 8192 tuple slot-2, 7-bit checks into byte
  slots, `[e1 + 4·e2, 4]` merges of width-2 checks — all unsound (slot weakening / bit stealing).

Carried forward (all re-verified or still binding):

- **Constraint-side digit folding / pre-Gauss seed protection**: +0 vars / +12 bus measured;
  pivot mangling feeds the payload-side digit fold. Also: `BoundsMap` is empty in cleanup cycle 1.
- **Per-check folding of genuinely-all-byte ladders**: mod-p alias (`K + p` digits) is
  admissible — per-check folds are *incorrect*, not merely unproven; joint refutation only.
- **Keccak below powdr's 1,734**: XOR dag perfectly clean; memory parity; no redundant widths.
- **Timestamp-decomp encodings** ({lo,hi} vs {prev,lo}): 1:1 wash, verified corpus-wide.
- **mem_ptr decomposition**: 2 vars/pointer floor; apc slightly ahead of powdr corpus-wide.
- **bit_shift_carry representation**: count-neutral; width-1 handled by ZeroWidthRange.
- **Variable-count via derived columns / functional dependence**: structurally impossible
  (variables counted syntactically; XOR is not a `ComputationMethod`).
- **Result-zero XOR `[x,y,0,1]`**, **constant-operand XOR beyond {0,255}**,
  **packing 2–7-bit checks as bytes** (unsound), **`flags` refolding, varRange-as-variables,
  PC-lookup drops, disconnected witnesses**: no targets / unsound, as before. apc wins `flags`
  by ~4,500 eth vars — test any new pass against the apc_005/009 flag folds.
- **Multiplicity-guarded duplicate stateless sends**: still not observed.

## Working rules (accumulated)

- **Canonicalize mod p before diffing circuits** (binary `-` vs `p−k` encodings; see dead ends).
- **Per-corpus bus maps differ and flow through `Main.lean` correctly**: tuple checker is
  (256, 8192) on eth, (256, 4096) on wasm, (256, 2048) declared-but-unused on keccak. The Lean
  `defaultBusMap` (2048) is only a fallback. Don't reason from the default.
- **Check for duplicates first**: look at open `optimizer-only` PRs and recent `claude/*`
  branches before building (the #112/#114 lesson).
- **Runtime is a de-facto merge criterion**: build per-pass indexes once; keep once-suffices
  passes in the coda; measure with the same-runner CI A/B (`Runtime Bench`), not this container
  (±15 %).
- **Measure per-case, not just aggregate**: the geo metric moves with per-case wins; 67 small
  losses cost more than one big one.
- **The two heavy wasm cases (apc_012/037) dominate wall time** (~5–8 min each); sample them
  only when the change targets them.

## Runtime leftovers (from the entry-90 runtime overhaul)

- ~~tupleRange per-pair bill~~ (**TAKEN**: entry 91's batch-drain with split-by-construction,
  ≈38× on the pass, −25 % on apc_012 profile).
- **domainBatch on keccak (~19 %)**: stream the `assignments` box; single-var prefilter for
  constraint-sourced domain targets; DPLL-style partial-assignment pruning fits `forcedOver`'s
  certificate shape but needs a real proof.
- **reencode/domainFold accept-path**: a position-stable `reencodeOut` would unlock stale-bucket
  refresh (`FoldIdx.refresh` trick) for both passes' constraint side.
- **gauss (~6 % keccak)**, **dedup (~4 %, quadratic deep-equality)**, **rootPairUnify
  (per-variable rescans)**, **zeroWidthRange (two `rangeEq?` scans)**.
- **Cross-cycle memoization**: a pass-state channel would cut every enumeration pass's
  steady-state tail at once; needs `Basic.lean` glue changes — weigh against the audit rule.

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
- ~~Runtime `decide p.Prime` per invocation~~ (**TAKEN**: #141 `PrimeWitness` decides once per
  run).
- **flagFold derive-and-discard**: the box-constraint predicate recomputes `c.vars.eraseDups`
  four times inside one expression; compute once per constraint, HashSet-dedup.
- Lower priority: `withPtrEq`-shortcut structural equality for `Expression`/`BusInteraction`
  (safe, Implementation-only; helps `dedup`'s quadratic `bi ∈ seen` and remaining split
  decides); `substF` no-change signaling to preserve sharing; incremental lengths in `sizeKey`.
