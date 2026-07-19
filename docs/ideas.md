# Ideas for future optimization passes

Rewritten from scratch (2026-07-18, entries 101–103 session). Every number here was re-measured
this session: fresh `opt-export` of all 100 SP1 rsp cases at each iteration, diffed per-case
against the checked-in `*.powdr_opt.json.gz` with canonical-polynomial comparison (mod p), plus
the PR #163 CI matrix (all five benchmark sets vs main). Older write-ups had stale or wrong gap
attributions; re-measure before trusting anything, including this file.

## Where we stand (post entries 101–103: interval forcing, basis justification, OR-identity checks)

| benchmark | axis | apc (agg) | powdr (agg) | status |
|---|---|---|---|---|
| sp1/rsp (100) | variables | 3.922× | 3.980× | gap 55 vars over ~20 cases; W/L/T 15/42/43 |
| | bus interactions | 2.703× | 2.822× | gap 319 = memory 180 + byte 139 |
| | constraints | 9.372× | 9.810× | gap 219 (lowest-priority axis) |
| sp1/keccak (1) | variables | 5.163× | 4.809× | **ahead** |
| | bus interactions | 3.017× | 3.137× | 2173 vs powdr's ~2100 |
| openvm-eth (100) | all axes | 4.553× / 3.558× / 10.845× | 4.092× / 3.480× / 5.853× | **ahead on all three** |
| keccak (OpenVM) | bus | 7.587× | 7.648× | 1748 vs 1734; vars/constraints exact parity |
| wasm-eth (100) | vars / con | 7.254× / 15.173× | 6.273× / 9.671× | **ahead** |
| | bus | 6.211× | 5.666× | ahead agg; geo 2.894× vs 2.868× ahead too |

**SP1 rsp is the remaining fight**, and within it: memory-chain telescoping blocked on quadratic
range knowledge (below), then the byte-bus checks, then the long variable tail. The three passes
this session (`intervalForce`, `basisJustified`, the OR-identity byte-check arms) closed var gap
442 → 55 and bus gap 765 → 319 with 0 per-case regressions; the mechanisms are general (each also
improved wasm-eth and/or OpenVM keccak).

## Open ideas, priority order

### 1. Quadratic root domains as bounds (`x·(x − c) = 0 → x ∈ {0, c}`)  ·  *bus + vars, sp1*  ·  high value / medium effort

The single biggest residual class. The un-telescoped SP1 memory chains that remain (apc_030's
register-16 `subw` chain +12, apc_097 +16, apc_037/031/063 +14 each — memory gap ~180 total)
carry data limbs like `subw_operation__value__0_49` whose 16-bit justification is not affine at
all: the value's range comes from **quadratic** relations the subw/comparison gadgets leave
behind, e.g. `(v₄₉ + v₅₁)² = 65536·(v₄₉ + v₅₁)` (so the sum ∈ {0, 65536}) together with borrow
booleanities. powdr's range solver reads quadratic roots; apc's `findVarBound` is bus-fact-only
and `findDomainAlg` only consumes single-variable constraints.

Concretely: an arm that recognizes a constraint linearizing (after normalize) to
`E² − c·E = 0` for an affine form `E` — giving `E ∈ {0, c}` — and feeds it as (a) a domain for
`domainBatch`-style case analysis, or (b) a bound `E ≤ c` consumable by `affineJustified` /
`basisJustified` / `intervalForce` as another basis form. (b) is the cheap slice: extend
`formBoundAt`-style facts with constraint-derived bounded forms (bound `c + 1` for the form `E`).
Same proof shape as `two-term`-era arguments: field equation + integral domain → root set.
The apc_048-style comparison gadgets (+27 vars, the largest single var case) are squared
differences `(a − b)²…` — the same machinery opens them, but the var win there also needs the
gadget collapsed (seqzCollapse-like), so size the bus slice first.

### 2. Basis justification for `SubsumedCheck` (redundant op-6 w=16 drops)  ·  *bus-5, sp1*  ·  medium value / medium effort

apc_024 keeps 75 op-6 w=16 checks vs powdr's 52: a w=16 check on an expression that finer checks
already imply (`d = 16384·F + h₀` with `F < 4` op-6-checked and `h₀ < 2¹⁴`) is redundant.
`SubsumedCheck` currently drops only `findVarBound`-justified (bare-variable) checks; giving it
the `basisJustified` arm — with a **non-circular base** (justify only against checks this pass
never drops, the `RedundantByteDrop` discipline) — would drop them. Byte-bus gap attributable to
this class ≈ 20–40. Watch the runtime: the coda-side plain `byteJustified` keeps the basis arm
disabled for a reason (measured 63 s/case when fed the whole region per query); reuse the
`buildFormIdx` untrusted-position-index pattern instead.

### 3. Census the op-3 packing parity  ·  *bus-5, sp1*  ·  low-medium value / low effort

Post entry 103, apc packs identity-OR byte obligations pairwise, but powdr still shows more op-3
pair checks (76 vs 44 on apc_024 pre-103; re-census). If apc still leaves unpacked singles (odd
leftovers per invocation, or singles the packer's pair scan doesn't reach across positions),
`byteCheckPackPass`'s pairing scan is the place. Pure layout; variable-neutral.

### 4. The variable tail (~55 over ~20 cases)  ·  *vars, sp1*  ·  case-by-case

- apc_048 (+27): quadratic comparison-gadget cluster (see idea 1's second half).
- apc_064/080/085 (+15/+15/+14): leftover `lower_limb`/`higher_limb`/result-byte families —
  likely partially unlocked by idea 1 (their chains still hold un-telescoped pairs whose death
  would disconnect the byte clusters); re-export and re-diff after idea 1 lands.
- apc_027 (+15): heterogeneous (rnc/addr/c_bits leftovers); census only if the above land.
- The ~30 cases at +1..+5: mostly one `state__clk`-family variable and a stray byte; powdr keeps
  a different-but-equal-count basis on many ties, so audit per case before building anything.

### 5. Constraint-axis gap (219, lowest priority)  ·  *constraints, sp1*  ·  only as tie-break

apc 9.372× vs powdr 9.810× aggregate. Never trade the higher axes for it; only touch if a pass
is otherwise neutral. Not yet attributed; the +27 on apc_027 and +15/16 on apc_030/070 suggest
the same quadratic gadgets from idea 1.

### 6. wasm-eth global range-obligation repack  ·  *bus, wasm*  ·  medium value / medium effort

Still open from the previous file (re-checked: still real). apc trails powdr's bus count only in
range-check *layout* on the big k256 cases (apc_037 +351, apc_012 +511 pre-102; entry 102's basis
arm already recovered −128 on apc_006, so re-measure first): powdr batches several decomposition
limbs into one tuple-range arg and uses byte-*pair* checks where apc emits per-limb checks. A
global rebuild — collect every surviving range obligation, drop solver-implied ones, re-pack
exact-cover — is bus-only and variable-neutral. Caution: 2–7-bit checks must not be packed as
bytes (weakens them).

## Runtime

Rewritten 2026-07-18 from a fresh profiling session (per-pass `profile`, per-cycle timing, gdb
stack sampling, and a size-scaling sweep — all on this container, serial). **Runtime is
end-to-end quadratic in circuit size** (openvm-eth sweep: input 2.3k → 8.8k items costs
1.8 s → 24.6 s, exponent ≈ 1.95), and the largest inputs are exactly where it hurts: openvm
keccak (28.6k constraints / 13.3k interactions / 27.5k vars) takes **252 s**; openvm SHA is ~8×
keccak, so anything superlinear is fatal there.

### Where the time goes (measured)

- keccak per-pass (254 s profile): domainFold 48 s, domainBatch 48 s, reencode 42 s,
  busPairCancel 26 s, intervalForce 21 s, flagFold 16 s, busUnify 12.5 s, rootPairUnify 9.4 s,
  dedup 6.6 s, bytePack 5.5 s, gauss 4.5 s — no single villain; the cost is systemic.
- **Post entries 109–113** (same container, serial): keccak 215 s → ~150 s expected — domainFold
  47 → 14.2 s, busUnify 12.7 → 10.5 s, reencode's ~49 s was **1276-of-1276 degree-rejected
  re-encodings per run** (each paying the freshness scan + full `reencodeOut` + degree walk,
  retried every cycle) — killed by the `degPreReject` necessary-condition pre-gate. Remaining
  big rocks: domainBatch ~50 s (productive enumeration + per-target gathers), flagFold ~20 s
  (samples: `pdKeep` re-verification `findIdx?` deep-eq scans + boxTauto `mentions`/
  `findDomainAlg`), rootPairUnify ~7.6 s, busPairCancel ~7.4 s.
- keccak per-cycle (10 cycles): **cycles 0–2 are ~80 % of the total** (system still 28k→9.7k
  constraints there); the tail cycles 6–9 are ~1 % each. Fixing the big-system per-pass
  quadratics matters more than fixing the fixpoint tail.
- eth apc_100 (5.7k constraints, 24.6 s, 8 cycles): reencode 6.2 s is the top pass (unindexed —
  see idea R3); the last three cycles cost 20 % to remove 24 vars + 5 bus; the final (no-change)
  cycle burns 1.7 s.
- SP1 apc_030 (26.8 s): domainBatch 19 s, **all in one cycle** (the enumeration unlocks late);
  identitySubst 2.7 s.
- gdb samples (keccak, mid-run): `findConsumer` (busUnify), `reencodeLoop`, `foldLoopDirect`
  (domainFold's unindexed path), `collectForBus` — matching the analysis below.

### Open runtime ideas, priority order

Priority = impact at SHA scale (8× keccak) ÷ effort. The pattern for all index work stays the
entry-90 discipline: *untrusted, re-checked-at-use* candidate indexes (`buildFormIdx`,
`recvIndexAll`, `CoveredIndex`) — a wrong index entry costs time, never soundness, so most of
these need no new proof.

**R1. Kill the true O(N²) loops that dominate the big early cycles**  ·  mostly **done**:
   - ~~`busUnify.findConsumer` per-send forward scans~~ **done (entries 111–112)**: single
     left-to-right sweep per bus with canonical-address-keyed open windows (`sweepGo` —
     all-constant messages are provably invisible to other constant keys, so they cost one map
     probe; `checkPair` re-verifies every emitted candidate, so the sweep is untrusted beyond
     the split equations, which are recovered by drop arithmetic). `TwoRootMap`/`NonzeroWits`
     thunked; the pass body's per-invocation `HashSet.ofList cs.vars` replaced by the
     by-construction variable guarantee (`memEqConstraints_vars`) and the hash-bucket build
     gated on nonempty candidates. Output byte-identical.
   - `busPairCancel`: `shieldOk` re-scans (and `liveArr` **materializes**) the whole before-region
     per candidate send (`BusPairCancel.lean` `shieldOk`/`findCancelGoIdx`) — O(B²) time *and*
     allocation on the long same-address chains the pass exists for; in coda mode the `addrHash`
     bucket is O(B) per hot address — add a position cursor. **Still open**, but whole-run
     samples put busPairCancel at only ~4 % on keccak post-111; the same per-key sweep pattern
     as busUnify applies (`shieldOk` left-folds to a single per-key `pending` bit), complicated
     by the tombstone-drop restarts. ~~`dropWits` from-0 array scan per
     queried variable~~ **done (entry 105)**: per-variable position index (`buildBoundIdx`),
     re-checked at use.
   - ~~`dedup` constraint-side `List.dedup` O(C²·E)~~ **done (entry 104)**: bucketed
     proven-identical twin (`HashedDedup.hashedDedup`), keccak 6.6 s → noise.
   - ~~`intervalForce` seed filters / `eraseDups` / per-slot pattern re-maps~~ **done (entry
     104)**: keccak 20.7 s → 1.1 s. (`walk`'s O(t²) with `maxTerms = 32` cap remains — bounded,
     low value.)
   - ~~`rootPairUnify` re-linearization per candidate var~~ **done (entry 104)** — factors
     linearized once per constraint. `anyVarBound` memoization across pairs still open (only
     matters if key-matched pairs are common; measure first).
   - ~~`flagFold` triple `eraseDups` in `btPre`~~ **done (entry 104)**. `singleVarCs`/`btCert`
     still recompute per-constraint `eraseDups`, but only on gate-passing constraints (proofs
     unfold them — rework only if they show up in profiles).

**R2. domainBatch setup: stop re-gathering and re-dedup-ing**  ·  **done (entry 104)** except:
(c) `constraintRedundant` full-box scans (`:899`) remain (they pay once to save per-target work);
hot-variable bucket capping remains open (not byte-identical — the gates read `esFull`). The
enumeration core itself (SP1 apc_030's 19 s single-cycle spike) is untouched: that lever is
**cross-cycle memoization of enumeration negatives** (needs pass-state threading — R6's
substrate), not setup cost.

**R3. domainFold/reencode: fuse the duplicate whole-system scans; retire the 8192 raw-count
index gate**  ·  mostly **done (entries 105/107/109)**:
   - reencode: the pruned index (`CoveredIndex.buildPruned`, entry 105 — items with more than 8
     distinct variables can never be covered by a ≤8-variable target, so pruning keeps covered
     sets identical) stays, but **behind the 8192 gate again** (entry 107): CI measured
     always-indexed at 1.19× on the dense openvm-eth blocks with no keccak gain — the entry-73a
     direct-path trade-off is real. Do not retire the gate without a same-runner A/B on eth.
   - ~~domainFold's direct-path double `coveredBy` sweep~~ **done**: one `partition` per target
     feeds both the covered set and the no-op gate (`systemHasFoldableW`).
   - ~~both passes' doubled `c.vars.dedup` setup~~ **done** (`hashedDedup`, computed once).
   - ~~domainFold's per-accept rebuild~~ **done (entry 109)**: `foldOut` is order-preserving
     (in-place rewrite), `FoldIdx` carries bucket-completeness invariants (stale supersets fine,
     re-checked at use), `refresh` keeps the buckets with no rebuild, and the fold itself is
     computed sparsely over candidate positions (`foldOutIdx`). keccak domainFold 47 s → 10.4 s.
     The **pattern generalizes**: any pass that rewrites items in place (shrinking variable
     sets) can keep one inverted index for its whole run via
     `coveredIdx_eq_filter_of_complete`; reencode is the next candidate (its rewrite *adds* bit
     columns and drops covered constraints, so it needs the remap or a pruned-completeness
     argument).
   - **Still open — reencode's `checkReencode`** re-runs the covered scan after `buildReencode`
     (`Reencode.lean:852/858`); rarely reached (post-gates), so low value now.

**R4. Constant-factor levers that touch every pass**  ·  *medium value, cheap*:
   - **Variable interning-lite, `Implementation/`-only**: parse-time interning is **done (entry
     106)**. Still open: swap the `Hashable Variable` instance (`Implementation/Variable.lean`,
     unaudited) to hash `powdrId?` first — O(1) vs O(name length) on almost every key. Caution:
     hash values leak into `Std.HashMap`/`HashSet` **iteration orders**; audit (or
     export-verify) every `toList`/`fold` whose order reaches the output before landing.
   - ~~`identitySubst`~~ **done (entry 106)**: the 2.8 s was an **arity-expansion bug** — a
     `def … : X → Y := let heavy := …; fun y => …` re-evaluates `heavy` per call (the map was
     rebuilt per queried occurrence). 2827 ms → 9 ms on apc_030. **Working rule: bind heavy
     values in the fully-applied pass body and pass them as parameters** (the `FlagFold`
     comment's pattern); when a pass's profile makes no sense relative to its work, suspect this
     first and bisect with a skip-the-body experiment.
   - ~~`normalize` linearize fusion~~ **done (entry 115)** for `normalizePass`
     (`normalizeFused`, proven equal). Gauss's per-constraint `substF |> normalize` still walks
     the old way — left alone deliberately: open PR #156 rewrites gauss's sweeps (dirty second
     sweep, allocation-free pivots) and should not be conflicted with.
   - ~~`iterateToFixpoint` sizeKey recomputation~~ **done (entry 115)**: the input's key is
     threaded (`iterateToFixpointFrom`), halving the per-cycle occurrence-list walks (~6 % of
     whole-run samples).
   - `gauss`: covered by open **PR #156** (proven dirty second sweep + allocation-free pivot
     selection, 0.78× on eth) — do not duplicate here.

**R5. Framework: track "pass returned input unchanged" and skip the per-pass degree check**  ·
*medium value, one framework change*. Every pass is `guardDegree`-wrapped, and the guard runs
`withinDegreeB` — a full AST walk — on every pass output, ~30×/cycle, ~245×/run
(`FactPass.lean:98`), even though most invocations return `cs` itself (the #146 measurement: ~61 %
of invocations are no-op full scans). Add an `unchanged : Option (out = cs ∧ derivs = [])` field
(default `none`) to `PassResult`; no-op branches supply `some ⟨rfl, rfl⟩`; `guardDegree` returns
`r` directly when set (out = cs is within-degree by the pipeline invariant — provable, not
pointer magic); `andThen` propagates; `iterateToFixpoint` skips both `sizeKey` recomputations
when the whole cycle is unchanged, and carries the previous cycle's `sizeKey` forward instead of
recomputing `cs.sizeKey` (`FactPass.lean:77`, one redundant O(E) HashSet build per cycle today).

**R6. Cross-cycle dirtiness (the real fix for no-op rescans)**  ·  *large refactor; the cheap
slice is now a measured dead end*. **Do not build a cross-cycle negative-memo for domainBatch**:
per-target fingerprints (target vars + domain descriptors + covered es/bis content hashes) were
measured across invocations — keccak repeats only **62 of 16,748** enumerations with unchanged
inputs (0.4 %), apc_030 257 of 1,641 (16 %, and its expensive cycle-5 enumeration is first-time)
— gauss's per-cycle substitutions rewrite the covered sets, so the fingerprints churn. Any
cross-cycle scheme must therefore be *finer* than whole-target skipping (powdr-style dirty
worklists where a substitution dirties only the items mentioning substituted variables — the full
#146 architecture), and its payoff must be re-estimated per pass first: at target granularity the
~61 % invocation-level no-op measurement does **not** translate into reusable work. domainBatch's
remaining cost is *productive first-time enumeration*; the levers there are effectiveness-side
(replace enumeration classes with algebra, cf. the quadratic-roots effectiveness idea 1) or
intra-enumeration (survivor-scan compilation is already tuned).

**R7. Intra-pass parallelism**  ·  partially **done (entry 114)**: domainBatch's per-target
enumerations are `Task`-parallel with ordered joins (byte-identical σ; keccak domainBatch
55 → 18 s on 4 cores — CI's 32 cores have more headroom). Still open: domainFold's and
reencode's per-target *gating* work is also independent between accepts, but their loops rewrite
`cs` on accept, so parallelizing needs a speculative gather-then-replay structure — only worth it
if their serial remainder grows relative to the rest. busPairCancel/busUnify are inherently
sequential scans (window state).

**R8. busPairCancel residual quadratics** (formerly part of R1)  ·  ~7 % of the post-114 keccak
profile. `shieldOk` re-scans (and `liveArr` materializes) the whole live before-region per
candidate send; `midRefuted` likewise materializes the between-region. Two designs, in
increasing effort: (a) fuse the materialization away — array-index twins of
`liveArr`+`shieldScan`/`List.all` with `…_eq` lemmas (the `liveArr_eq` pattern), removing the
O(i) allocation per candidate but keeping the O(i) scan; (b) the busUnify entry-111 treatment —
`shieldOk` left-folds to a single per-address-key `pending` bit, maintainable across one sweep,
but the pass's tombstone-and-restart structure (drops invalidate prefix state: removing a
consumed receive un-shields earlier messages) forces a recompute-on-drop scheme, bounded by
#drops × O(B). The whole-run sample share (~5 %) says (a) first, (b) only if SHA-scale profiles
promote it.

### Runtime dead ends (measured; do not re-propose without new evidence)

- **Whole-system content-hash gating of passes across cycles**: catches ~0 % — the fixpoint only
  retains cycles that changed something, so some pass always dirties the hash (#146 measurement).
  Only fine-grained dirtiness (R6) reaches the ~61 % no-op invocations.
- **Unsafe pointer-identity freshness checks** (`@[implemented_by]` ptr-eq): rejected — breaks the
  fully-machine-checked, three-axioms-only guarantee (#145 discussion). The safe variant is the
  `unchanged` *proof* field of R5.
- **Eager per-sweep variable→bound witness maps in busPairCancel**: ~30× the work of the
  early-exit query-time scan on eth (entry 90). Query-time scans + per-variable *position*
  indexes are the pattern.
- **Feeding whole regions into per-query justification arms**: 63 s/case for −3 interactions
  (entry 102). Use a position index or nothing.
- CI notes: the effectiveness-matrix runtime row is parallel-contended (±10 % noise); the serial
  `Runtime Bench` workflow (dispatch-only, openvm sets only) is the real A/B. This container has
  ±15 % run-to-run variance; keccak numbers above were taken serially, and the per-cycle keccak
  run was inflated ~30 % by a concurrent gdb sampler — compare shapes, not absolutes, and let CI
  arbitrate.

## Measured dead ends (do not re-propose without new evidence)

- **OpenVM keccak below 1734 bus / 2021 vars / 186 constraints**: measured floor (XOR dag clean,
  memory exact-pair floor, range widths minimal). The 1748 → 1734 residual is 14 interactions of
  bus-3 layout parity, repeatedly measured as not worth a pass.
- **eth constant-decomposition folding beyond DigitFold**: constraint-side seeds measured +0 vars
  /+12 bus (Gauss pivot mangling *feeds* the payload-side fold; protecting seeds starves it).
- **Per-check folding of genuinely-all-byte ladders**: mod-p alias is admissible — a per-check
  fold is *incorrect*, not merely unproven (`isCompleteReplacementOf` quantifies over admissible
  assignments).
- **Timestamp-decomp / mem_ptr encodings**: count-neutral representation choices, verified 1:1.
- **Variable count via derived columns / functional dependence**: structurally impossible
  (variables are counted syntactically).
- **`identitySubst` in the cleanup cycle**: still a regression (re-encode explosion); its coda
  placement (now pre-drop/pack, entry 103) is the working point.
- **Feeding `rest` as the basis lookup in the coda's `byteJustified`**: 63 s/case for −3
  interactions (entry 102). Use an index or nothing.

## Working rules (accumulated)

- **Don't trust prior conclusions — re-measure.** Two of this session's three wins contradicted
  the previous file's "residual is X" attributions (the "carry/negative-coefficient" class was
  actually forced equalities the interval argument sees; the "memory telescoping needs
  architectural work" class fell to one justification arm).
- **Prefer generalizing an existing mechanism over a new pass**: entry 101 replaced ScaledZero
  with its generalization; entry 102 is an arm of the existing justification; entry 103 is two
  recognizer arms + a reorder. Each was cheaper to prove than a fresh pass and composes with the
  whole cascade.
- **Per-case diff before/after every candidate** (`opt-export` + canonical compare): aggregate
  effectiveness hides single-case regressions that the lexicographic merge rule forbids.
- **Runtime is a de-facto merge criterion**: build per-invocation indexes once; keep expensive
  arms out of hot per-query paths; put once-suffices passes in the coda.
- **Check open PRs / recent `claude/*` branches for duplicates before implementing.**
