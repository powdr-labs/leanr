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

**R1. Kill the true O(N²) loops that dominate the big early cycles**  ·  *high value, mostly
proof-free*. Confirmed quadratics, in rough per-case cost order:
   - `busUnify.findConsumer` scans forward through the whole tail per send, and `checkPair`
     re-scans the mid region `findConsumer` just stepped over (`BusUnify.lean:217/146`); each
     step can hit `addrNonzeroNeq` = O(2^A·C) (`AddrDiseq.lean:519`). Fix: `(busId, addrHash)`
     position buckets (port `recvIndexAll`), and thunk the eager `TwoRootMap`/`NonzeroWits`
     builds (`BusUnify.lean:309-311`) so no-op invocations skip them.
   - `busPairCancel`: `shieldOk` re-scans (and `liveArr` **materializes**) the whole before-region
     per candidate send (`BusPairCancel.lean:1861/2428`) — O(B²) time *and* allocation on the long
     same-address chains the pass exists for. A per-sweep suffix table of `shieldScan` results (or
     a left-to-right open-sends accumulator) makes it O(B); the Bool is identical so
     `checkCancel_sound` keeps its hypothesis. Same file: `dropWits` scans the whole array from
     position 0 per queried variable (`:2146`) — give it the `buildFormIdx` treatment; in coda
     mode the `addrHash` bucket is O(B) per hot address (`:1255`) — add a position cursor.
   - `dedup`: the constraint side is still `List.dedup` = O(C²·E) structural comparisons
     (`Dedup.lean:241`) — 28k constraints in keccak cycle 0, ~230k for SHA. Bucket by the
     existing `Expression.bHash` exactly as `dedupStatelessFast` already does for interactions;
     the `dedupStatelessFast_eq` proof pattern transfers.
   - `intervalForce`: per-seed `cs.vars.contains` over the *non-deduped occurrence list* and
     per-seed `algebraicConstraints.contains` (`IntervalForce.lean:618-619`), `eraseDups` =
     O(seeds²·E) (`:585`), the O(t²) `walk` with `seen ++ rest` re-summing (`:245`), and O(P²)
     payload `List` indexing (`:531`). Fix: one `HashSet` of vars + one hash-bucketed constraint
     set per invocation, running window sums, arrays.
   - `rootPairUnify`: `twoRootOf?` re-linearizes both factors per candidate var and again per
     checked pair (`RootPairUnify.lean:74/427`), and `anyVarBound` re-scans all interactions per
     pair with no memo (`:397`). Linearize once per constraint, carry the decomposition in
     `RPSeen`, memoize `anyVarBound` per variable.
   - `flagFold`: `c.vars.eraseDups` (O(E_c²)) recomputed 3-4× per constraint across
     `singleVarCs`/`btPre`/`btCert` (`FlagFold.lean:25/43/32`); compute once, via HashSet.

**R2. domainBatch setup: stop re-gathering and re-dedup-ing**  ·  *high value on SP1 + keccak,
proof-free*. Four measured hot spots (`DomainBatch.lean`): (a) the covered-set gather runs
**three times per target** (`forcedOver:1259-1262`) and `es ⊆ esFull` makes the third gather pure
duplication — gather once, filter by a redundancy flag; hot-variable buckets (selector/is_real
vars with O(C) buckets) are re-gathered and mostly Q-rejected per target — cap or skip oversized
buckets (index incompleteness only costs effectiveness of *this* probe, and only via `seen`-dedup
order). (b) `c.vars.dedup` = O(occ²) recomputed 3× per item (`:347/1352/901`) — compute each
item's deduped var set once per invocation. (c) `constraintRedundant` full-box scans (`:899`).
(d) `interactionBound` re-maps `constValue?` over the whole payload per raw slot (O(P²) per
interaction, `DomainProp.lean:318`) — cache the constant-pattern per interaction. Also applies to
`biInformative` (`:887`).

**R3. domainFold/reencode: fuse the duplicate whole-system scans; retire the 8192 raw-count
index gate**  ·  *high value at eth/mid-keccak scale*. Both passes have a proven-equal inverted
index (`coveredCsIdx_eq`) that is **disabled below 8192 constraints**
(`DomainFold.lean:658/682`, `Reencode.lean:1498/1621`) — so every eth case and keccak cycles 3+
run the direct O(targets × system) path (reencode is apc_100's single most expensive pass). The
gate exists because dense small systems lose on bucket gathering; replace raw count with a
sharing-density criterion, or make the index path cheap enough to win everywhere. Independent of
the gate: domainFold evaluates `coveredBy` twice per (target × constraint)
(`coveredCsOf` + `systemHasFoldable`, `DomainFold.lean:651/443`) — thread the covered set through;
reencode's `checkReencode` re-runs the *third* full covered scan after `buildReencode`'s
(`Reencode.lean:852/858`) — thread `es` + `doms` through (small `hes ▸` plumbing, transport core
untouched); and both passes recompute `c.vars.dedup` twice per constraint in setup
(`DomainFold.lean:674/678`, `Reencode.lean:1613/1617`).

**R4. Constant-factor levers that touch every pass**  ·  *medium value, cheap*:
   - **Variable interning-lite, `Implementation/`-only**: the parser mints a fresh `String` per
     occurrence (`Variable.ofPowdrName`, `JsonParser.lean:101`); intern one shared object per
     distinct name so the runtime's pointer fast-path (`lean_string_eq`: `s1 == s2 || …`) makes
     every hit-comparison O(1). Swap the `Hashable Variable` instance
     (`Implementation/Variable.lean:19`, unaudited) to hash `powdrId?` first — O(1) vs O(name
     length) on almost every key. `Spec.lean`'s `Variable` stays untouched.
   - `identitySubst`: the substitution closure linear-scans the pair list per variable occurrence
     (`IdentitySubst.lean:154`) — 2.7 s on apc_030. HashMap it; optionally resolve
     operand→operand chains up front to drop the `iterateToFixpoint` wrapper.
   - `normalize`: `linearize` re-runs on the whole subtree at every node along non-affine paths
     (O(E·depth), `Normalize.lean:306`); fuse into one bottom-up pass returning per-node linear
     forms. Also feeds gauss's per-constraint reduce.
   - `gauss`: skip `c.substF σ.fn |> normalize` for constraints mentioning no solved key, and skip
     sweep 2 when sweep 1 adopted nothing (`Gauss.lean:592`). (PR #156 has a proven dirty-sweep
     variant of this — check its status before redoing.)

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

**R6. Cross-cycle dirtiness (the real fix for no-op rescans)**  ·  *large refactor, do after
R1-R5*. Even with all per-pass fixes, every cycle re-runs every pass over the whole system, and
~61 % of invocations find nothing (#146's measurement; whole-system version gating catches 0 %
because the fixpoint only retains changing cycles). The powdr-style fix is a worklist: stable
item positions + tombstones + a variable→positions occurrence index, passes consume/produce
dirty-sets, substitutions dirty only the items mentioning the substituted variables. PR #146
(`IndexedState`, stacked on #145 `FactStore`) built the substrate but nothing consumes it; PR
#145's lesson stands — input-dependent caches without incremental maintenance don't pay. If R1-R5
land and large cases are still cycle-bound, this is the next mountain; budget for reworking
`Basic.lean`/`FactPass.lean` pass signatures (allowed: it is implementation, not audited surface).

**R7. Intra-pass parallelism**  ·  *wall-clock lever, orthogonal*. The per-target enumeration in
domainBatch/reencode/domainFold is embarrassingly parallel and pure; `Task.spawn`/`Task.get` with
ordered joins keeps the output deterministic. CI runners have 32 cores; the serial Runtime Bench
would show the win directly. Worth it only after the algorithmic waste is gone (parallelizing a
triple-redundant gather is throwing cores at garbage).

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
