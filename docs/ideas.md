# Ideas for future optimization passes

Regenerated from scratch (2026-07-14). Every number here was re-measured this session: fresh
`opt-export` of all 100 openvm-eth cases + keccak (measurement base `656a9d8`, post-#114),
diffed against the checked-in `*.powdr_opt.json.gz` with canonical-polynomial comparison (mod p;
note powdr's export uses **binary `"-"`** nodes — tooling must handle both encodings). While
this regeneration was in flight, **#117 (entry 77) and #119 (entry 78) merged**, landing idea 2
(a)+(b) and the op-0 half of idea 4(d) below; the baselines and those two ideas were refreshed
on rebase from the entries' measured numbers. Older write-ups had stale or wrong gap
attributions; re-measure before trusting anything, including this file.

## Where we stand (post-#117/#119 + entry 80 = idea 4(b)+(c) + entry 81 = the digit fold)

Absolute output totals (identical inputs, so `agg` effectiveness follows directly):

| benchmark | axis | apc | powdr | apc − powdr |
|---|---|---|---|---|
| openvm-eth (100) | variables | 27,802 | 30,885 | **−3,083 (lead)** |
| | bus interactions | 16,454 | 16,722 | **−268 (lead; was +5)** |
| | constraints | 11,267 | 20,299 | −9,032 (lead) |
| keccak | variables | 2,021 | 2,021 | **exact parity** |
| | bus interactions | 1,952 | 1,734 | **+218 (was +293)** |
| | constraints | 186 | 186 | **exact parity** |

Per-case standings on eth: variables **30 W / 11 L / 59 T** (+56 total over the losing cases).
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

- **eth variables +56 over 11 cases** (was +172 over 29) = ~~M1 constant decompositions +135~~
  (**LANDED**: entry 81 −165 incl. cascades; residual = full-byte-top `rd_data` ladders,
  apc_034/066 +3 each) · M2 comparison gadgets residue (apc_037 +14, apc_018 +9 — idea 3) ·
  M3 dead `bit_multiplier` **+14** · everything else nets in apc's favor.
- **eth bus** (was +588 over losing cases; −191 + −132 + −141 landed) = ~~width-1 range checks
  90~~ (**LANDED**: entry 80 −89) · ~~cancellable memory pairs 78~~ + op-0 coverage waste
  (**LANDED**: #117 −76, #119 −115) · ~~constant-family checks ~126~~ (**LANDED**: entry 81
  −141) · long same-address chains **64** (apc_010 still 247 vs 239) · tuple-slot coverage waste
  (**remainder of the ≥112 bucket**) · ~~subsumed range checks 22~~ (**LANDED**: entry 80 ≈ −43,
  the base also catches byte/memory-subsumed wide checks) · NOT-form byte checks **23** ·
  residual scattered.
- **keccak bus +218** (was +614; #117 −276 memory = exact powdr parity, #119 −45 op-0 waste,
  entry 80 −68 width-1, entry 81 −7) = NOT-form byte checks **200** · ~18 misc — the bus-3
  width histograms are otherwise *identical* to powdr's.

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
- **Entry 81 (this branch): the bounded-payload digit fold** — lands the payload-ladder core of
  idea 1 below; see the re-scoped idea 1.
- **#116 open** (gated constant-decomposition fold): eth-neutral because its gate skips every
  profitable case; the digit fold (entry 81) lands the same family from the payload side, so
  #116 is now fully subsumed — close it, but its proven digit-uniqueness core (`annDecode_forces`,
  `annSum_val`) remains the natural starting point for the constraint-side remainder of idea 1.

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
- **Shifted `rd_data__{1,2,3}` ladders whose top limb is a full byte** (apc_034/066 +3 each,
  parts of apc_038/042/064): all-byte bounds genuinely admit wrap phantoms; needs a tighter
  top-limb bound from another constraint, if one exists. Low ceiling (~6–15 vars).
- **Constraint-side affine seeds** (`Σ cᵢ·xᵢ = K` as an algebraic constraint rather than a
  payload ladder), which Gauss unit-pivots away before any digit solver sees them. #116's
  `ConstDecomp.lean` proves the digit-uniqueness core (`annDecode_forces`, `annSum_val`); if
  built, substitute all digits at once via `SubstMap` *before* `gauss`, and heed #116's measured
  traps: the ungated version cost keccak +187 bus (folded constant send payloads stop matching
  unfolded receives in `busUnify`/`busPairCancel` — fix the matcher, don't re-add the gate) and
  +16% runtime (don't emit equalities for Gauss to rediscover). Unclear residual value now that
  the payload side landed — re-census first.

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
half already landed as #119, and **(b)+(c) landed together** (entry 80): keccak −68, eth −132
bus, 0 variable/bus regressions. The remainder — (a) NOT-form byte checks and (d)'s tuple half —
is worth ~**270 keccak** + a few dozen eth bus interactions. Independent items — land separately.

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
