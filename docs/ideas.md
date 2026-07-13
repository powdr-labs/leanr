# Ideas for future optimization passes

Ranked by **expected benefit**. Effectiveness priority is **variables > bus interactions >
constraints**, used as the tiebreak; the cheap high-confidence bus win #1 is ranked early because it
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
  (43 cases) · `bit_shift_carry` +67 (13 cases) · `apc_071` intermediate address bytes. The positional
  constant-fold (C5, entry 76) is landed but is gated to limbs that do **not** feed a stateful payload, so it
  leaves the eth `rd_data`/PC family untouched — those limbs are block outputs feeding memory/exec, and
  folding them would break memory pair-cancellation; recovering them needs idea #1 (pair-cancellation on
  constant data slots) first. (The bulk is also degree-2 disjunctions / 32-bit wrapping decompositions a
  sound uniqueness fold cannot reach.)

---

## 1. Cancel interior memory send/receive pairs  ·  *bus*  ·  high confidence · low–medium effort

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

## 2. Collapse comparison / is-equal / is-zero gadget witnesses  ·  *variables*  ·  medium confidence · high effort

**Gap:** the comparison gadgets are the broadest variable family — extra markers/flags in **43 of 100
cases**: `diff_inv_marker` +61 (16 cases), `diff_marker` +24, `c_msb_f` +27, `b_msb_f` +19. This is
the long `+3` per-case loss tail plus `apc_018` (+9) and `apc_037`'s marker block (+16). powdr keeps a
single inverse-hint / comparison-result witness where apc keeps one per limb.

**Mechanism** — generalize `hintCollapse`'s matcher (which today needs single-variable byte-bounded
coefficients) to the is-equal and signed-compare shapes:

```
-- is-equal / is-zero (k inverse markers -> 1):
gadget:  −cmp + Σ (aᵢ−bᵢ)·inv_markerᵢ = 0,   aᵢ,bᵢ byte-bounded
replace by:   cmp·S = 0     and     inv·S + cmp − 1 = 0
   where  S = Σ 256ⁱ·(aᵢ − bᵢ)      -- byte-weighted difference, no-wrap since k·255·256^{k-1} < p
   cmp := ComputationMethod.QuotientOrZero/IfEqZero   (derived; avoids under-constraint)
   drop every inv_markerᵢ         (−(k−1) vars per gadget)

-- signed / sltu:  fold {a_msb_f, b_msb_f} + per-limb diff_marker into the single result
--   via sign-split byte-bounded coefficients (CarryBranch.splitSumMax style; accept coefficients
--   that are DIFFERENCES of byte-bounded variables — the generalization hintCollapse currently lacks).
```

**Why sound.** `S = 0 ⟺ all limbs equal`, given byte bounds so the weighted sum cannot wrap
(`boundedSumMax`-style no-wrap, already in `MemoryUnify`). The is-zero witness pair is standard;
`cmp` must be a derived column (`QuotientOrZero`, already in `ComputationMethod`) to stay constrained.
Proof risk: robustly matching the marker gadget and proving the consumer needs only equality (not
signed `<`) is delicate — flagged medium.

**Expected impact.** ~60–90 recoverable variables across the 43 affected cases (the whole `+3` tail
plus `apc_018`/`apc_037`). Top-priority axis, broadest reach.

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
  shows it is **not** the keccak memory blocker (idea #1a is), but it generalizes #1 to affine
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
- **Fold positional decompositions of a compile-time constant (C5, `ConstDecomp`):** **landed**
  (entry 76). For an affine `Σ cᵢ·xᵢ = K` whose range-checked limbs form a non-overlapping positional
  system that cannot wrap the field, it adds the entailed `xᵢ = digitᵢ(K)` digit equalities (mixed-radix
  uniqueness, `annDecode_forces`; no `native_decide`, 3-axiom clean) for Gauss to eliminate. **Gated** to
  limbs that do not feed a stateful (memory/exec) payload: pinning such a limb to a constant strips the
  variable range-check that memory pair-cancellation needs for byte-justification (an ungated prototype
  cost keccak **+187 bus** and eth −0.021× bus, and doubled runtime). Gated, it is a **clean win on keccak**
  (2028→2024 vars, 2348→2339 bus, 120→118 constraints — all three axes) and **neutral on openvm-eth**
  (eth’s positional constants are all stateful-connected, so the gate skips them). The residual eth family
  is idea #1 (memory pair-cancellation on constant data slots).
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
