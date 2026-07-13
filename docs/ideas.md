# Ideas for future optimization passes

Ranked by **expected benefit**. Effectiveness priority is **variables > bus interactions >
constraints**, used as the tiebreak; the cheap high-confidence bus win #2 is ranked early because it
is nearly free and closes part of the *only* axis on which apc-optimizer trails powdr in aggregate,
plus keccak's dominant gap.

## Where we stand (measured on `c007db0`; keccak/eth refreshed for merged C4b #109 and the bitwise byte-check cleanup, entry 75)

| benchmark | apc-optimizer | powdr | apc gap |
|---|---|---|---|
| **keccak** (`apc_001_pckeccak`) | 2028 v / 120 c / 2348 bus | 2021 / 186 / 1734 | vars **+7 (near parity)**, **bus +614** (wins constraints) |
| **openvm-eth** (100-case agg / geo) | vars 4.511× / 3.822× · bus 3.439× / 2.723× | vars 4.092× / 3.787× · bus 3.480× / 2.822× | leads vars agg (geo only +0.035); **trails bus by 0.040** |
| **apc_010** (`pc0x200c18`) | 466 v / 251 c / 271 bus | 498 / 331 / 239 | wins vars+constraints, **bus +32** |

C4b (#109, entry 74) closed the keccak *variable* gap to near-parity; the bitwise byte-check cleanup
(entry 75) cut the bitwise-bus gap. **keccak's dominant remaining loss is bus (+614)**; on openvm-eth
the story is unchanged except bus improved (per-case by variables **25 W / 42 L / 33 T**; variable
losses total ~+243 over 42 cases, bus gap net now ≈ +300). Both gaps decompose into a *small* number of
structural families, each addressed by one idea below.

- **keccak bus +614** = memory interior pairs +276 · bitwise (bus 6) ≈ +257 (post entry-75 pack) ·
  width-1 range (bus 3) +68.
- **eth bus** = bitwise (reduced by entry 75, but genuine-XOR / non-packable checks remain) ·
  tupleRange +160 (22 cases) · memory +144 (15 cases) · varRange **−376** (apc already *wins* — do not touch).
- **eth vars ~+243** = `rd_data` write-result limbs ~93 (23 cases) · comparison gadget ~130 markers/flags
  (43 cases) · `bit_shift_carry` +67 (13 cases) · `apc_071` intermediate address bytes. (Per-case
  numbers below were measured on `c007db0`; C4b shifted only the `255`-XOR NOT cases on `apc_071`/`apc_037`,
  otherwise per-case-neutral.)

---

## 1. Fold byte/limb decompositions of compile-time constants  ·  *variables*  ·  high confidence · medium effort

**Gap:** `rd_data`/PC-limb families are the single largest variable loss — ~93 vars over 23 cases,
and **powdr keeps zero of them**. On JAL/JALR-terminated blocks the return address and jump target
are compile-time constants, so powdr folds every limb to a literal; apc keeps them free because
cracking `Σ 256ⁱ·byteᵢ = K` under byte bounds needs positional-uniqueness reasoning Gauss can't do
(the 256³ combination space is too large for domain enumeration). Measured: `apc_045` +14 (all
constant-PC limbs), `apc_026` +14, and the return-address part of the `+3` cluster
(`apc_011/013/022/027/033/034/040/043`).

**Mechanism** (new `VerifiedPass`; `ZeroWidthRange` is the `K=0`, single-term special case):

```
for each affine constraint  Σ cᵢ·xᵢ = K   (K a field constant):
    require each xᵢ range-bounded 0 ≤ xᵢ < Bᵢ   (from its range-check bus fact / byteJustified)
    sort terms by |cᵢ|; require a non-overlapping mixed-radix system:
        cᵢ·(Bᵢ−1) < c_{i+1}   for all i,   and   Σ cᵢ·(Bᵢ−1) < p   (no wrap)
    then the xᵢ are UNIQUELY forced:  xᵢ = digitᵢ(K)  by iterated div/mod
    emit  Derivation xᵢ := ComputationMethod.Constant (digitᵢ K)
    substitute the literal everywhere; drop the now-entailed range checks
```

**Why sound.** Soundness = uniqueness of a bounded mixed-radix representation (a `Nat.div`/`Nat.mod`
digit lemma — no `native_decide`): the constraint already forces `xᵢ = digitᵢ(K)`, so substituting
the constant preserves the satisfying set. Completeness: a real trace's column literally holds that
constant, so the `Constant` method reproduces it (`derivesWitness` holds). Dropped range checks are
entailed (`digitᵢ(K) < Bᵢ`).

**Expected impact.** ~40–65 of the 103 extra vars across the losing cases; flips ~6–10 losses to
ties/wins (roughly 25 W / 42 L → ~32 W / 34 L, and lifts the thin +0.031 geomean variable lead).
Top-priority axis.

---

## 2. Cancel interior memory send/receive pairs  ·  *bus*  ·  high confidence · low–medium effort

**Gap:** the memory bus is where apc systematically trails on the memory-heavy blocks and on keccak.
A register/heap cell accessed *N* times emits 2N memory interactions, but only the first receive and
last send are externally observable — the N−1 interior send/receive pairs are exact `+1`/`−1`
message negations and cancel. powdr does this; apc does not, purely because `busPairCancelPass`
cannot *recognize* the pairs. Two independent recognizer gaps, both local to `BusPairCancel.lean`:

**(a) Symbolic-address step-over** (keccak, the −276 chunk). Measured: 137/138 of keccak's memory
pairs are **byte-identical `+1`/`−1` including the timestamp expression**; the send and its matching
receive sit ~130 lines apart with *only other-pointer heap accesses* between them. `midRefuted`
(line ~863) refutes an interleaved message as different-address only via `addrConstsNeq`, which needs
**both** addresses to be literal constants — but heap pointers are expressions
(`mem_ptr_limbs__0 + 65536·mem_ptr_limbs__1`), so no pair is ever cleared. The fix is to OR the
**already-proven** `addrTwoRootNeq` (`AddrDiseq.lean`, built and used by `busUnify` since entry 71)
into `midRefuted`:

```
midRefuted shape busId S m :=
      decide (m.busId ≠ busId)
   || multConst m == some 0
   || addrConstsNeq shape S m
   || addrTwoRootNeq twoRootMap shape S m      -- NEW: two-root branch disequality
```

Thread the once-per-pass `TwoRootMap` in (as `busUnify` does) and add the `hsat` hypothesis to
`midRefuted_sound` (the exact plumbing entry 71 added to `checkPair_sound`).

**(b) Constraint-entailed payload matching** (apc_010 registers, the −32 chunk). Measured: apc_010's
16 register pairs share the address, timestamp and last three data slots; slot 0 differs
*syntactically* — send `(1−flag)·srd0 + flag·srd1`, receive `read_data__X` — even though `busUnify`
**already added** the equality `read_data__X − ((1−flag)·srd0 + flag·srd1) = 0`. Gauss can't apply it
(`read_data` occurs at degree 3 in the `write_data` constraints; substituting its degree-2 definition
would hit degree 4 > the bound of 3, so `guardDegree` reverts). So generalize the match from
syntactic to entailed:

```
payloadsMatch cs S R :=
    addrConstsEq shape S R                         -- unconditional address equality
 && ∀ value-slot i:  S[i] == R[i]                  -- syntactic, OR
       || (eqExpr S[i] R[i]).normalize ∈ cs.algebraicConstraints.map normalize   -- entailed
```

Re-key the receive index on `(address ++ tail-slots)` and weaken `dropPair_correct`'s hypothesis from
`S.payload = R.payload` to the env-conditioned `evaluated payloads equal under the algebraic
constraints`.

**Why sound.** `sideEffects_dropPair_equiv` (already stated over *evaluated* payloads) gives net-zero
cancellation once evaluated payloads are equal — discharged from the algebraic constraints, which
hold in both `refines` directions. `admissible_dropPair` needs only address equality (unconditional).
The dropped receive's byte obligation is discharged by the existing `recvSlotsJustified`
(`byteJustified`/`deepBoundOk`) — which already covers apc_010's plain-var and `255·bit` single-var
slots. No new `BusFacts`, no audited-surface change.

**Expected impact.** keccak memory **534 → 258 = exact powdr parity (−276 bus)** via (a); apc_010
**271 → 239** (now *beats* powdr on all three axes), `apc_014` 151→135, `apc_008` −2, and every other
sign-extending-load / heap-heavy block via (b). ~120–150 bus across the memory-heavy eth cases.
Strictly variable-neutral.

---

## 3. Collapse comparison gadget witnesses — signed-compare slice (is-equal slice LANDED)  ·  *variables*  ·  medium confidence · high effort

**Landed (entry 75, 2026-07-13): the is-equal / is-zero slice.** `EqCollapse.lean` (rebased from
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
