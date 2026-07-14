# Ideas for future optimization passes

Regenerated from scratch (2026-07-14). Every number here was re-measured this session: fresh
`opt-export` of all 100 openvm-eth cases + keccak (measurement base `656a9d8`, post-#114),
diffed against the checked-in `*.powdr_opt.json.gz` with canonical-polynomial comparison (mod p;
note powdr's export uses **binary `"-"`** nodes — tooling must handle both encodings). While
this regeneration was in flight, **#117 (entry 77) and #119 (entry 78) merged**, landing idea 2
(a)+(b) and the op-0 half of idea 4(d) below; the baselines and those two ideas were refreshed
on rebase from the entries' measured numbers. Older write-ups had stale or wrong gap
attributions; re-measure before trusting anything, including this file.

## Where we stand (main `9c92008`, post-#117/#119)

Absolute output totals (identical inputs, so `agg` effectiveness follows directly):

| benchmark | axis | apc | powdr | apc − powdr |
|---|---|---|---|---|
| openvm-eth (100) | variables | 27,967 | 30,885 | **−2,918 (lead)** |
| | bus interactions | 16,727 | 16,722 | **+5 (agg deficit −0.001)** |
| | constraints | 11,213 | 20,299 | −9,086 (lead) |
| keccak | variables | 2,025 | 2,021 | +4 |
| | bus interactions | 2,027 | 1,734 | **+293** |
| | constraints | 120 | 186 | −66 |

Per-case standings on eth: variables **27 W / 29 L / 44 T** (+172 total over the losing cases).
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

- **eth variables +172** = M1 constant decompositions **+135** · M2 comparison gadgets residue
  **≈ +57** (of the original +105, #114 landed −48) · M3 dead `bit_multiplier` **+14** ·
  everything else nets in apc's favor (−114 value cluster).
- **eth bus** (was +588 over losing cases; −191 landed) = width-1 range checks **90** ·
  ~~cancellable memory pairs 78~~ + op-0 coverage waste (**LANDED**: #117 −76, #119 −115) ·
  long same-address chains **64** (apc_010 still 247 vs 239) · constant-family checks **~126**
  (84 solvable directly) · tuple-slot coverage waste (**remainder of the ≥112 bucket**) ·
  subsumed range checks **22** · NOT-form byte checks **23** · residual scattered.
- **keccak bus +293** (was +614; #117 −276 memory = exact powdr parity, #119 −45 op-0 waste) =
  NOT-form byte checks **200** · width-1 checks **68** · ~25 misc — the bus-3 width histograms
  are otherwise *identical* to powdr's.

## In flight / recently landed — check `git log origin/main` and open PRs before picking anything up

- **#117 merged** (interior memory pair cancellation = idea 2 (a)+(b)): keccak memory at powdr
  parity, eth −76. Only sub-items (c) and (d) of idea 2 remain.
- **#119 merged** (coda byte-pair splitting): the op-0 explode/dedup/drop/repack half of
  idea 4(d); keccak −45, eth −115. The tuple-slot half of 4(d) remains.
- **#114 merged** (is-equal sum-of-squares collapse). **#112 open** — reworked from a duplicate into
  a consolidation: generalizes `hintCollapse` to subsume the collapse and removes the standalone
  `EqCollapse` pass; effectiveness-neutral vs main, ~half the combined collapse-stage runtime
  (no separate per-cycle scan). A structural cleanup, not a new win — take it or leave it.
- **#116 open** (gated constant-decomposition fold): eth-neutral because its gate skips every
  profitable case. Idea 1 below subsumes it; reuse its proven digit-uniqueness core.

---

## 1. Constant-decomposition folding, done right  ·  *variables (top axis) + bus*  ·  high value / medium-high effort

**Gap.** The single biggest eth variable family: **+135 vars** (6 AUIPC+JALR chains ×14:
apc_026/045/051/055/085/094; 17 `rd = pc+4` link-register writes ×3: apc_011/024/025/034/042/043/
048/050/058/066/071/074/077/078/084/087/096) **plus ~126 bus interactions** (their range/byte
checks, e.g. apc_042 keeps the op-0 check `(3559368 − 256·rd0 − 65536·rd1 − …, rd0)` on a JALR
return address that is just the digits of 3559368). powdr ships literal constants — payloads like
`[1, 4, 20, 66, 41, 0, ts+26]` and a constant exec-bridge target.

**Why apc misses it.** The input contains pure-affine seeds, e.g. apc_045:
`imm_limbs__0 + 256·imm_limbs__1 + 65536·imm_limbs__2 = 16777200` with byte-checked limbs — the
digits (240,255,255) are *uniquely forced* (mixed-radix uniqueness). But Gauss consumes the seed
first: it unit-pivots ONE limb away and leaves quadratics, so no later pass ever sees the
decomposition. The constants then need to cascade through the adder carry disjunctions
`(A)·(A−256) = 0`: with A's variables pinned, exactly one root is feasible — pruning it yields a
new affine equation, which unlocks the next fold, etc.

**Mechanism** (extend #116's `ConstDecomp.lean`, which already proves digit uniqueness
`annDecode_forces` + the no-wrap lemma `annSum_val`):

```
repeat (within the pass, to a local fixpoint):
  1. for each affine constraint Σ cᵢ·xᵢ = K with every xᵢ range-bounded (BoundsMap:
     bus-3 checks, bitwise op-0/op-1 slots, tuple slots) and non-overlapping positional
     coefficients (sorted, cᵢ·(Bᵢ−1) < c_{i+1}, Σ cᵢ·(Bᵢ−1) < p):
       substitute ALL xᵢ := digitᵢ(K) at once (SubstMap, like Gauss — not one equality
       at a time; that is what #116 got wrong operationally and why it needed Gauss)
  2. for each constraint (A)·(A − k) = 0 with A affine over now-pinned/bounded vars:
       if interval analysis (CarryBranch.splitSumMax machinery) refutes one root,
       replace by the affine constraint of the live root; goto 1
```

Run it in `cleanupPasses` **before `gauss`** (as #116 does). Drop the `statefulPayloadVars` gate
entirely.

**The #116 keccak regression, diagnosed.** The gate was added because ungated folding cost keccak
+187 bus. The stated rationale (folding strips byte-justification) is wrong —
`byteJustified` already accepts constants < 256 (BusPairCancel.lean ~line 399). The real
mechanism is almost certainly **pair matching**: a folded (constant) send payload no longer
*syntactically* matches the unfolded receive side, so `busUnify`/`busPairCancel` miss pairs.
First implementation step: reproduce ungated, `opt-export` keccak, diff the missed pairs against
the 142 known-cancellable ones, and make the matcher compare **constant-folded normal forms** of
payload slots (or match slots up to entailed constant equality). Do not re-add the gate.

**Two more gotchas.** (a) A paired op-0 check `[folded_limb, live_expr, 0, 0]` must survive with
a constant arg unless the partner folds too (powdr drops all 6 per chain because *everything*
folds — expect that after the disjunction cascade). (b) Runtime: #116 measured +16% (gauss 3.2×)
because it added equalities for Gauss to rediscover; substituting directly via `SubstMap` avoids
the extra fixpoint pressure.

**Why sound.** Digit uniqueness is proven in #116; substitution of entailed constants is the
standard `Subst` correctness; root pruning replaces a constraint by one it entails on the
satisfying set (interval refutation of the other root — `CarryBranch` precedent).

**Expected impact.** eth: −135 vars (flips the six +14 cases and most +3 cases; ~29 L → ~10 L),
−84..126 bus; keccak: −4 v / −9 b / −2 c (#116's measured numbers, kept by the ungated version);
the +187 regression must be gone (the 142 pairs still cancel).

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

## 3. Comparison-gadget completion: the seqz idiom  ·  *variables*  ·  medium value / medium effort

**Gap (post-#114 residue ≈ +57 vars).** `sltu rd, x, 1` ("set if x < 1", i.e. x == 0): powdr
recognizes the constant operand and replaces OpenVM's whole LessThan machinery — 4 `diff_marker`
booleans + `diff_val` + msb flags + the `[diff_val − 1, 0, 0, 0]` bitwise send — with the
two-line is-zero gadget `cmp·(Σ 256ⁱ·xᵢ) = 0 ∧ inv·(Σ 256ⁱ·xᵢ) + cmp = 1` (byte limbs ⟹ the
weighted sum can't wrap). apc keeps 5–6 witnesses per instance; instances: apc_037 ×4, apc_018
×2, and the `+3..+7` tail cases (apc_013/022/027/040/099…). Plus ~+3/case of boolean dataflow
vars powdr inlines as expressions (`cmp1 + cmp2 − cmp1·cmp2` directly in payloads/multiplicities).

**Mechanism.** A recognizer for the LessThan gadget *with a constant comparand* (the
`diff_marker`/`diff_val` cluster is identified by its constraint shapes; the constant side makes
the comparison collapsible): for `x < 1`, emit the is-zero pair with one fresh
`QuotientOrZero`-derived `inv` (exact `hintCollapse`/#114 machinery — reuse `collapse_correct`'s
parameterized reassignment), substitute `cmp` consumers, drop the marker vars, their booleanity
constraints, their bus interactions. Generalize to other constant comparands only if the census
finds any (this session found only `< 1`).

**Why sound.** Same proof pattern as #114 (which is in-tree): the collapsed witness set
reproduces exactly the is-zero semantics; completeness via the derived-column bookkeeping;
no-wrap from byte bounds (`boundedSumMax`-style, in `MemoryUnify`).

**Expected impact.** eth −40..57 vars concentrated on the remaining loss cases (apc_037 +14 →
~+3, apc_018 +9 → ~+2), plus the freed bitwise/range interactions (−1..3/instance). Keccak:
none (its one gadget landed with #114).

---

## 4. Stateless-check hygiene: recognize, justify, repack  ·  *bus, both benchmarks*  ·  high value / low-medium effort per item

Four convergent fixes to how byte/range obligations are recognized and laid out; (d)'s op-0
half already landed as #119. The remainder is worth ~**270 keccak** (lands it on powdr's 1734
floor) + ~**135+ eth** bus interactions. Independent items — land separately.

**(a) NOT-form byte checks** (keccak **200**, eth **23**). After C4b substitutes `z := 255 − x`,
the interaction remains as `[x, 255, 255 − x, 1]` — semantically just "x is a byte" — but
`RedundantByteDrop.byteCheckOperands?` / `ByteCheckPack.svCheck?` only match
`[x,x,0,1] / [x,0,x,1] / [0,x,x,1] / [x,y,0,0]`. Add the two NOT arms: payload `(x, 255, z, 1)`
(or mirrored) where `z` normalizes to `255 − x`. Fact side: mirror `xorZeroCheck` as
`xorComplCheck` (needs `256 ≤ p` like C4b — over small fields `255 − x` is not the complement).
On keccak **all 200 are droppable outright** — every checked operand is already forced < 256 by a
genuine-XOR slot (96 as x, 8 as y, 12 as z, 84 via "255−v occurs as an XOR operand and
`255−v ∈ [0,256) ⟺ v ∈ [0,256)`" — add that reflection rule to `byteJustified` too). On eth the
23 sit on raw memory-receive slots (slotBound-justified). Expected: keccak −200, eth −23, both
variable-neutral.

**(b) Width-≤1 range checks → booleanity** (keccak **68**, eth **90**). `[e, 1]` on the
var-range bus ⟺ `e ∈ {0,1}` ⟺ `e·(e−1) = 0` (degree 2 ≤ 3; all current instances have e of
degree 1). Extend `ZeroWidthRange.lean` (width-0 → equality) with a width-1 arm: same two-step
proof — ADD the booleanity constraint via `PassCorrect.ofEnvEq` (an accepted `[e,1]` forces
`e.val < 2`), then DROP the interaction via `filterBusEntailed_correct` (booleanity + `p` prime
⟹ value < 2 ⟹ accepted). New `BusFacts` field `oneRangeBool` mirroring `zeroRangeEq`. Trades
bus −1 for constraints +1: a strict lexicographic win, compatible with the fixpoint `sizeKey`.
On eth, powdr additionally *eliminates* the freed boolean via the new constraint + an affine
relation (e.g. the SRL-by-1 `bit_shift_carry` vars vanish entirely) — Gauss gets that for free
once the equality is algebraic. Worked example (keccak, 68×): `[bit_shift_marker_k, 1]` →
`bit_shift_marker_k² − bit_shift_marker_k = 0`.

**(c) Subsumed range checks** (eth **22**). apc keeps `[v, 13]` on bus 3 while the same `v`
also sits in a tuple v2 slot (< 2048 ⊂ < 8192). Drop any bus-3 check whose bound is already
entailed by a *stronger* retained check on the canonically-equal value (BoundsMap lookup; the
drop is `filterBusEntailed_correct` again). Keep direction strict: only drop the *weaker* check.

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

## 5. One-hot annihilation  ·  *variables*  ·  small, clean / low effort

**Gap (+14 eth vars: apc_051 +7, apc_038 +7).** Shift chips with a runtime shift amount but a
fixed direction keep BOTH `bit_multiplier_left` and `bit_multiplier_right`; one of them is dead —
forced to 0 by the existing constraints, but only through a *linear combination across the
one-hot family*: with markers `Σ mᵢ = 1`, `mᵢ · x = 0` for all i ⟹ `x = 0`. Gauss can't see it
(the products are nonlinear); powdr's monomial-level elimination does.

**Mechanism.** A small pass (or a `domainBatch` rule): find a variable `x` such that for a
marker set {mᵢ} with a proven `Σ mᵢ = 1` constraint, every `mᵢ·x = 0` is present (syntactically,
after normalize); add `x = 0` and let constant-fold cascade. Soundness: summing the constraints
gives `x·Σmᵢ = x = 0` — a one-line entailed equality (`addConstraints_correct`).

**Expected impact.** −14 vars, a few dropped checks; flips apc_051/apc_038 closer to parity.
Check the census for non-shift instances of the same pattern before scoping.

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
