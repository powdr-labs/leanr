# Ideas for future optimization passes

Ranked by **expected benefit**. Effectiveness priority is **variables > bus interactions >
constraints**, used as the tiebreak. With #2 landed (entry 77) and the coda byte-pair splitting
(entry 78), the eth bus deficit (−0.001, the only trailing axis) and keccak's bus gap (+293) are
the remaining aggregate gaps; both decompose into the smaller items below.

## Where we stand (measured on `c007db0`; keccak/eth refreshed for merged C4b #109, the bitwise byte-check cleanup (entry 75), the is-equal collapse (entry 76), and the coda byte-pair splitting (entry 78))

| benchmark | apc-optimizer | powdr | apc gap |
|---|---|---|---|
| **keccak** (`apc_001_pckeccak`) | 2025 v / 120 c / 2027 bus | 2021 / 186 / 1734 | vars **+4 (near parity)**, **bus +293** (memory at parity; wins constraints) |
| **openvm-eth** (100-case agg / geo) | vars 4.518× / 3.837× · bus 3.479× / 2.753× | vars 4.092× / 3.787× · bus 3.480× / 2.822× | leads vars agg (geo +0.050); **trails bus by 0.001** |
| **apc_010** (`pc0x200c18`) | 466 v / 251 c / 247 bus | 498 / 331 / 239 | wins vars+constraints, **bus +8** |

C4b (#109, entry 74) closed the keccak *variable* gap to near-parity; the bitwise byte-check cleanup
(entry 75) cut the bitwise-bus gap; the is-equal collapse (entry 76) flipped 13 variable losses
(per-case by variables now **27 W / 29 L / 44 T**; residual variable losses concentrated in the
signed-compare and constant-limb families, bus gap net ≈ +300). Both gaps decompose into a *small* number of
structural families, each addressed by one idea below.

- **keccak bus +614** = memory interior pairs +276 (landed, entry 77) · bitwise (bus 6) ≈ +212
  (post entry-75 pack and entry-78 pair splitting) · width-1 range (bus 3) +68.
- **eth bus** = bitwise (reduced by entries 75/78; genuine-XOR checks remain) ·
  tupleRange +160 (22 cases) · memory +144 (15 cases) · varRange **−376** (apc already *wins* — do not touch).
- **eth vars ~+243** = `rd_data` write-result limbs ~93 (23 cases) · comparison gadget ~130 markers/flags
  (43 cases) · `bit_shift_carry` +67 (13 cases) · `apc_071` intermediate address bytes. (Per-case
  numbers below were measured on `c007db0`; C4b shifted only the `255`-XOR NOT cases on `apc_071`/`apc_037`,
  otherwise per-case-neutral.)

---

## 1. Fold constant limb decompositions — **RE-SCOPED (entry 78): needs chain reasoning, not a digit lemma**  ·  *variables*  ·  high effort

**Mechanism correction (measured, entry 78).** The sketched pass — fold affine
`Σ cᵢ·xᵢ = K` under range bounds — measures **−2 / −3 / 0 vars** on apc_045/apc_026/apc_013
(faithful pin-and-reoptimize what-if): the clean equations exist only in the raw input, cover
only the `imm_limbs` slice, and constant-seeding does **not** cascade. (An optimistic what-if
claiming −54/−141/−154 was traced to unsoundly pinning `Σ flagᵢ = 1` one-hot selector sums —
excluded.) Do not build the affine-only pass.

**Where the (still-real) gap lives** — apc_045/apc_026 remain +14 vars each vs powdr, which
folds every one of these limbs to literals:
- **Bounded-payload idiom** (~3 vars/case): memory payload `K − Σ 256ⁱ⁺¹·rdᵢ` asserted a byte by
  a bitwise pair check; with the limbs' range checks the digits are forced (hand-verified =
  powdr's values). Recognizer needs payload linearization + bus-side byte facts; a contained
  sub-pass, worth building if the census over the ~20 affected cases justifies it.
- **Guarded two-root carry chains** (~11 vars/case): `(L−r₁)(L−r₂) = 0` with both roots inside
  the operands' interval per-constraint — only the joint chain + range facts disambiguate.
  Requires multi-constraint interval/relational reasoning (idea #6-class saturation), not a
  mixed-radix lemma. carryBranch cannot be unblocked by constant seeding (measured).

Census refresh needed before any build: the "+93 vars / 23 cases" figure predates #114/#117
(apc_013 is now a variable tie).

---

## 2. Cancel interior memory send/receive pairs — **LANDED (entry 77)**

Both recognizer gaps fixed in `BusPairCancel.lean`: (a) the two-root address-disequality
(`addrTwoRootNeq`) now backs `midRefuted`/`preRefuted`/`shieldScan` (Thunk'd `TwoRootMap`, once
per invocation, transported across drops), telescoping keccak's interior heap pairs — **memory
534 → 258 = exact powdr parity, keccak bus 2348 → 2072 (−276)**; (b) constraint-entailed payload
matching (`EqConstraintMap` of normalized constraints + `payloadEntailedEq`), run **only in a new
aggressive coda invocation** (`busPairCancelLate` + `bytePackLate`) — mid-cycle it measures as a
net loss (premature emission racing the justification machinery, apc_005 class +34 bus each, and
keccak 2.4× runtime) while at the coda each drop is net ≤ −1 bus by construction. eth: **bus agg
3.439× → 3.455×, 10 cases / −76 bus / 0 regressions** (apc_010 271 → 247 vs powdr 239);
vars/constraints byte-neutral; runtime eth −2.5%, keccak +1.3%. Deliberately forgone: −6 keccak /
−6 apc_100 reachable only by mid-cycle entailed matching. Residual keccak bus gap +338 = bitwise
≈257 (genuine-XOR representation) + width-1 range 68 (→ booleanity conversion, see below) + ~13.

---

## 3. Collapse comparison gadget witnesses — signed-compare slice (is-equal slice LANDED)  ·  *variables*  ·  medium confidence · high effort

**Landed (entry 76, 2026-07-13): the is-equal / is-zero slice.** `EqCollapse.lean` (rebased from
the `c6-tuple-range-pack` prototype) collapses the per-limb inverse-marker gadget
`−cmp + Σ (aᵢ−bᵢ)·diff_inv_markerᵢ = 0` to powdr's single **sum-of-squares** witness
`inv · Σ (aᵢ−bᵢ)² = cmp` (one derived `QuotientOrZero` column; sound because each `(aᵢ−bᵢ)²`
< 256² so the sum can't wrap — `sumSq_zero_all_eq`; the *byte-weighted* form sketched here
previously was superseded by sum-of-squares, which needs no positional weighting). Measured:
**16 cases × −3 vars = −48, 0 regressions, bus/constraints byte-neutral; keccak 2028 → 2025;
vars agg 4.509× → 4.517×, W/L/T 25/42/33 → 27/29/44**. Runtime +1.4% total (outliers: apc_044
+25%, apc_019 +19% — gate the collector on multi-marker constraints if this ever matters).

**Remaining gap (this idea):** the signed-compare / sltu families — `diff_marker` +24, `c_msb_f`
+27, `b_msb_f` +19 (plus `apc_018` +9 and `apc_037`'s marker block) — where powdr keeps a single
comparison-result witness and apc keeps per-limb markers + msb flags.

**Mechanism** — generalize the matcher to the signed-compare shape:

```
-- signed / sltu:  fold {a_msb_f, b_msb_f} + per-limb diff_marker into the single result
--   via sign-split byte-bounded coefficients (CarryBranch.splitSumMax style; accept coefficients
--   that are DIFFERENCES of byte-bounded variables — the generalization hintCollapse currently lacks).
```

**Why sound.** Sign-split no-wrap over byte-bounded differences (`boundedSumMax`-style, already in
`MemoryUnify`); the result witness must be a derived column to stay constrained. Proof risk:
robustly matching the marker gadget and proving the consumer needs only the comparison result is
delicate — flagged medium.

**Expected impact.** ~30–60 further variables across the signed-compare cases. Top-priority axis;
higher proof cost than #1.

---

## Smaller follow-ups (worth landing, lower ceiling)

- **Width-1 range-check → booleanity constraint** (`ZeroWidthRange` width-0 → width-1). `[e,1]` on a
  var-range bus ⟹ `e·(e−1)=0`, drop the interaction. Equivalence (uses the existing `varRangeBus`
  fact; degree 2, within bound). **keccak −68 bus** (bus 3 → powdr parity), variable-neutral; trades
  68 bus for 68 constraints — a strict lexicographic win (bus ≻ constraints, and apc has 10.6× agg
  constraint headroom).
- **Widening tuple-range packing + `mem_ptr` high-limb sharing** (`tupleRangePass` + `MemoryUnify`).
  Pack `byte+byte`/`byte+over-wide` into one `TupleRangeChecker` guarded by `byteJustified` re-derival
  of the narrowed slot; share the provably-equal 13-bit high limb across same-base accesses. **eth
  tupleRange +160 over 22 cases** (`apc_006` +76). Bus-only.
- **Affine/product no-wrap rule for `byteJustified`.** `e = c·y` (y boolean) or `e = c₀ + Σ cᵢ·yᵢ`
  with `c₀ + Σ|cᵢ|(Bᵢ−1) < 256`, via `MemoryUnify.boundedSum_val`. A *helper*, not a headline: census
  shows it is **not** the keccak memory blocker (idea #2a is), but it generalizes #2 to affine
  memory receives and rotation-carry data slots. Would also let the entry-75 byte-check dropper drop
  more mirror checks (currently many keccak `[0,x,x,1]` operands are only *packable*, not droppable,
  because their byteness is not re-derivable from an affine memory receive).

## Rejected / measured dead-ends (do not re-propose without re-measuring)

- **Degree-bounded witness inlining + per-candidate degree planning (roadmap 4.7/4.10):** measured
  **zero** corpus-wide (entry 79, alternation what-if through the real optimizer, cascade-capable).
  Constant-coefficient nonlinear pivots barely exist post-optimization (4 on apc_051, 1 on keccak)
  and all are blocked by the **bus payload bound** — the inlined variable is the bus-facing value,
  beyond any booleanity legalization. The audit's deg-4 "near-misses" are conditional pivots
  (already measured dead). Do not build; 4.10 only ever with a measured consumer.

- **Result-zero XOR extraction (`[x,y,0,1] ⟹ x=y`):** **measured dead-end (entry 75).** The census
  behind the old idea #3(i) was stale: the *optimized* keccak circuit contains **zero** `[x,y,0,1]`
  interactions — every op-1 bitwise message carries a genuine XOR-result variable (XOR chaining), the
  representation artifact recorded in the functional-dependence dead-end below, not a result-zero
  equality. A proven `xorResultZeroEq` prototype left both benchmarks byte-identical and was dropped.
- **Bitwise byte-check cleanup (mirror `[0,x,x,1]` drop + form-agnostic pack):** **landed** (entry 75).
  The `[0,x,x,1]` XOR-with-zero mirror is now recognized by `RedundantByteDrop` (drop when justified)
  and by the generalized `ByteCheckPack` packer (which packs single-value checks in *any* encoding —
  `[x,x,0,1]`/`[x,0,x,1]`/`[0,x,x,1]` — via the existing `mergeStateless2_correct`, subsuming the old
  `bytePackPass`). keccak bus 2418 → 2348; eth bus 3.401× → 3.439×; variable-/constraint-neutral. The
  *non-packable* residue (genuine XORs, and pair-checks whose operands are not byte-justified) is not
  removable — powdr keeps equivalent checks.
- **Constant-operand XOR extraction (`⊕0` C4a, `⊕255` C4b):** **landed** (entries 70 / 74, #109);
  `{0, 255}` are the only operands making `x ⊕ c` affine, so the mechanism is **exhausted** — do not
  re-propose a generic constant-operand XOR pass.
- **Result-zero XOR equality extraction `[x,y,0,1] ⟹ x = y`:** built, proven, measured **exact
  no-op** (2026-07-13) — the shape occurs nowhere in the corpus (0 in outputs, 0 mid-pipeline under
  an instrumented counter with positive control); the old "50 on keccak" census had miscounted the
  55 op-0 pair checks `[x,y,0,0]`. Change discarded; see the log entry.
- **Timestamp re-encoding** (`lower_decomp__1` vs `prev_timestamp`): measured **wash** — equal free-var
  counts each side on every case.
- **Carry-witness substitution** for genuine two-root carries: measured **wash** (log 67) — eliminating
  a derived limb adds a carry witness, net 0 vars.
- **Drop never-violating PC lookups:** **no gap remains** — exec/PC bus tied 200/200 on the benchmark.
- **`disconnectedComponent` smarter witnesses:** measured **empty** (log 61) — outputs contain 0
  disconnected vars.
- **keccak genuine-XOR bus gap (+321) as a dedup pass:** **not removable** — no duplicate/ shared-pair
  lookups; it is a variable-representation artifact (XOR chaining), and the artifact itself is not
  removable either (next bullet), so it is neither a bus pass nor a variable pass.
- **Functional-dependence derived columns for read/write limbs (was idea #5):** **infeasible — measured
  dead-end** (attempted 2026-07-13, log entry above). The variable count (`ConstraintSystem.variables`,
  Size.lean) is purely syntactic: a name is counted iff it appears in some constraint/interaction, and
  `Derivations` are a *separate* list, so registering a `ComputationMethod` for a limb does **not**
  drop it — only substituting the name away (Gauss/Subst) or re-encoding a group into fewer fresh vars
  (Reencode) can. But the functional dependences that keep limbs alive are all **XOR/bitwise**
  (`z = x⊕y`), which is **not a low-degree `ZMod p` polynomial** (no `Expression` to substitute) and
  **not expressible as a `ComputationMethod`** (only `const`/`quotientOrZero`/`ifEqZero`); `slotFun`
  gives only the *value-level* soundness function, not a substitutable expression. The affine
  functional dependences (ADD/SUB carry limbs) are already eliminated by Gauss (degree-1 subst into
  stateful memory payloads). Measured on the live renders: keccak's surviving functional limbs are 359
  pure-XOR chain intermediates + 458 XOR-results in memory + 159 redundant range-checks on XOR results
  — **all XOR, none affine** — and **powdr keeps the same limbs** (1 derived column total on keccak, via
  `QuotientOrZero`), consistent with keccak's +7 variable near-parity. So there is no sound,
  effectiveness-improving pass here. (The redundant range-checks on byte-guaranteed XOR results *are* a
  separate bus-only opportunity — see the width-1 / redundant-byte follow-ups above.)
- **`bit_shift_carry` elimination (+67):** keccak rho-rotation encoding — VM-specific / overfit, high
  proof risk. Excluded by the generality rule.
- **varRange bus / range-check packing as a *variables* lever:** apc already **wins** varRange bus net
  −376; range packing is bus-only (a follow-up), not a variable opportunity.
- **`b`/`c` per-family variable diffs:** a **naming artifact** (apc names read-data `b`/`c` where powdr
  names it `read_data`); they cancel in net accounting. Only structurally-unique families
  (`rd_data`, `diff_inv_marker`, `bit_shift_carry`, `msb_f`, intermediate `a`/`c`) are genuine.
- **`apc_003` signed-compare:** no longer a loss — now a **tie** (tuple packing, entry 71, closed it).
