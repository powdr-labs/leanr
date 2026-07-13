# Ideas for future optimization passes

## keccak: unify read-data limbs to close the variable gap (variables — top priority)

**Read-value substitution: LANDED (entry 71, symbolic-ts forwarding).** The "widen `findConsumer`'s
mid-refutation" angle is done: `AddrDiseq.lean`'s two-root address-disequality (`addrTwoRootNeq`) lets
`busUnify` step over interleaved other-pointer heap accesses (their addresses are `mem_ptr_limbs`
expressions, not constants), so the send↔consumer slot equalities now fire on the heap. keccak
**3056 → 2224 vars (−832), 2862 → 2411 bus**; `lower_decomp` 534→164, `prev_data` 448→148, width-12/17
range checks → 129/129 (= powdr). Gap to powdr now +203 (was +1035).

**Constant-operand XOR extraction: LANDED (C4a entry 70, C4b entry 74).** The affine constant-operand
XORs (`⊕0`, `⊕255`) are done — see the dedicated section below. Stacked on the entry-71 forwarding
baseline, C4b (`[x,255,z,1] ⟹ z=255−x`) eliminated the residual `c`-family NOT-results: keccak
**2224 → 2028 vars (−196)**, so the gap to powdr collapsed to **+7** (2028 vs 2021 — near parity).

The bitwise-**result** byte bound itself is now landed (`openVmFacts.slotBound` slot 2, entry 58) —
do not re-propose it.

## AND-gadget byte justification (`apc_037`, minor)

`apc_037`'s blocked chain writes `b = x AND y`, encoded as the adder identity
`x + y − 2·b = x ⊕ y` on a bitwise interaction (so `b`'s byteness needs the bit-identity
`a + b − (a⊕b) = 2·(a∧b)` and `a∧b < 256`). Not a clean finite-domain shape; a dedicated
AND-result recogniser would justify it, but it is one case and low priority — do the earliest-send
relaxation first.

**Remaining variable gap (≈203, the residual `b`/`c` read-data limbs).** powdr additionally eliminates
each read limb via the **XOR functional dependence** (`slotFun` proves `z = x ⊕ y`): a bitwise
`[x, y, z, 1]` determines `z`. A pass turning `z` into a derived column (`ComputationMethod`, like
`reencode`) reading `x, y` removes `z` as a free variable. Needs the completeness `derivesWitness`
bookkeeping, but `slotFun` already carries the soundness half. This is the reencode-class residual.

**Two cheap bus follow-ups unlocked by entry 71:**
- **1.2 identical-tuple cancellation (−≈282 bus).** The forwarding created 282 memory interactions in
  syntactically-identical ±1 pairs (was 178) that `busPairCancel` cannot cancel: the dropped receive's
  data slots are rotation *expressions* (`128·a__1 + bit_shift_carry__…`) and `byteJustified` has no
  affine rule. Add a no-wrap affine byte rule: for `e = c₀ + Σ cᵢ·yᵢ` with every `yᵢ` bounded and
  `c₀ + Σ cᵢ·(Bᵢ−1) < 256`, conclude `e < 256`. Shares the bound machinery with the shift-carry work.
- **2.2 AS2 middle-pair telescoping (below powdr's 200 floor).** Wire `addrTwoRootNeq` into
  `busPairCancel`'s `midRefuted` (same predicate) so the heap middle pairs telescope — AS2 count
  (still 482 here) could drop toward / below powdr's 200.

## Genuine two-root carries: carry-witness substitution — MEASURED WASH, do not build

**Measured a wash (faithful census what-if, 2026-07).** `carryCollapsePass` (log 67) collapses only
*pure copies* `(L)·(L±256)=0` where a byte bound rules out one root, correctly leaving **genuine**
two-root carries intact (both roots reachable): the 3-operand ADD limb carry `(b+c−a)·(b+c−a−256)=0`
and the `mem_ptr` page-boundary carry (gap 65536). It looked like a large win — an *optimistic* what-if
(zero one root, ignore whether the bound holds, re-optimize) claimed up to **−249 vars** on apc_037,
−52 on apc_071. But the **faithful** transform (introduce the boolean carry witness it actually needs,
`a = b+c − 256·carry`, plus booleanity, then re-optimize) nets **exactly 0 variables** on every case:
eliminating `a` as a derived column adds `carry`, a pure swap with no cascade. powdr matches apc on
these blocks (e.g. apc_061/003 var-identical). The ceiling was entirely unsound one-root collapse.
Do not build a carry-witness pass; the residual C1 gap is not a real variable opportunity.

## Bitwise-XOR constant-operand equality extraction — COMPLETE (C4a entry 70, C4b entry 74)

Both **affine** constant operands are now landed in `xorEqExtractPass`: the 0-operand
(`[0,y,z,1] ⟹ z=y`, `[x,0,z,1] ⟹ z=x`, C4a entry 70, `Nat.zero_xor`/`Nat.xor_zero`) and the
255-operand byte complement (`[x,255,z,1] ⟹ z=255−x`, `[255,y,z,1] ⟹ z=255−y`, C4b entry 74,
`n ⊕ 255 = 255−n` for a byte `n`, `xorComplEq` fact gated on `256 ≤ p`). `{0, 255}` are the **only**
constants for which `x ⊕ c` is affine in `x` (every other makes the XOR bit-dependent), so this
mechanism is **exhausted — do not re-propose a generic constant-operand XOR pass.** C4b removed 196
keccak variables on the post-#105 base (2224 → 2028, +7 from powdr parity), openvm-eth
variable-positive / per-case-neutral. The remaining XOR-computation gap to powdr is the **pure-XOR
intermediates** — `b`/`c` limbs that appear *only* as an XOR result then an XOR operand — which no
affine extraction can reach: eliminating them needs turning the XOR result into a **derived column**
(the XOR-result-derivation angle in the keccak idea below), not another equality.

## Intermediate effective-address elimination (deeper residual, after C4a/C4b)

`zeroWidthRangePass` (log 69, C3) converts the width-0 range checks `[expr, 0]` into equalities
`expr = 0`, letting Gauss eliminate the pinned limbs — closing ~40 of apc_071's 123-variable gap to
powdr (and 11 on apc_020, 3 on apc_037). The **residual** gap on apc_071 is the `a` (48) and `c`
(16) families: intermediate effective-address bytes. For each access at `base + offsetᵢ`, apc
materializes the effective address as a fresh 4-byte decomposition via a two-root carry chain and
then decomposes again into `mem_ptr_limbs`; powdr derives `mem_ptr_limbs` **directly** from
`rs1_data + offsetᵢ`, skipping the intermediate byte layer entirely. Eliminating it needs a
derived-column pass (reencode-class): recognise `addr = base + offset` carry chains feeding only a
memory address / byte-decomposed write, and express the `mem_ptr` limbs affinely in `base + offset`
with carry witnesses, without materializing the intermediate bytes. Higher proof cost; the true
"highest cost" item of the old C4 cluster. Note the naive per-limb carry-witnessing is net-neutral
(swap 4 address bytes for 4 carries — same wash as the carry-witness follow-up below); the win comes
only from *not materializing the intermediate layer at all* while still satisfying the memory bus's
byte requirement.

## Consider dropping `reencode` in favour of `domainFoldPass` alone (entry-47 option B)

`domainFoldPass` (`DomainFold.lean`, log entry 48) is now landed **alongside** `reencode` (option A) —
effectiveness-neutral but the general, powdr-style mechanism made explicit. The remaining open decision
is entry-47 **option B**: drop `reencode` and keep only the fold pass. Measured trade-off on the
apc_005 load/store class: fold-only reaches **1939** vars (keeping all flags, close to powdr's 1808),
vs **1683** with `reencode` — i.e. option B is more principled / powdr-aligned but gives up the ~13%
flag binary-compression (512 ternary flags → 256 bits) that currently makes apc-optimizer *beat* powdr there.
Only worth it if the flag-compression edge is judged not worth `reencode`'s complexity/runtime; the fold
pass would then also want a `bits ≥ vars` / large-group path (groups `reencode` skips) to claw some of
it back. Left for Georg to decide.

Effectiveness priority: **variables > bus interactions > constraints**. As of carry-branch
resolution (log entry 57), on the full 100-case `openvm-eth` benchmark apc-optimizer *wins* variables on
aggregate (4.135× vs 4.092×) and trails on geomean (3.706× vs 3.787×; per-case: 17 wins / 52
losses / 31 ties — the losses are a few variables each, dominated by the sltu-compare
`diff_marker` family below) and leads clearly on constraints; the remaining *systematic* gap is
bus interactions. The bus gap decomposes as: (a) range-check packing via the tuple range checker,
(b) memory-pointer-limb 13-bit checks on memory-heavy blocks, (c) residual bitwise checks that
are not self-XOR byte checks, (d) occasional missed memory send↔receive cancellations. See the
`docs/log.md` entry 42/46/49/57 discussion for measurements.

## Drop never-violating stateless lookups (close the residual pc-lookup bus gap)

After memory/exec send↔receive pair cancellation (log entry 46), apc-optimizer is at near-parity with powdr
on bus interactions; the residual gap is essentially the **PC lookups** (bus 2): powdr removes them,
apc-optimizer keeps them (never-violating model), so they inflate the bus count without affecting variables.

A `VerifiedPass` that drops a stateless bus interaction whose multiplicity is provably `0`, or that
is proven never-violating via `BusFacts.neverViolates`, would be sound (removing a
never-violating, non-stateful interaction changes no stateful side effect) and would raise bus
effectiveness without regressing variables — a clean win under the priority order
(variables > bus interactions > constraints). Check the existing zero-multiplicity drop in
`cleanupCycle` first; this may be an extension of it rather than a new pass.

## Widening tuple packs: byte + byte → `TupleRangeChecker` (bus interactions)

`tupleRangePass` (log entry 71) packs a byte check with an **exact**-width range check
(`2^bits = s2`) into one tuple interaction — an equivalence, so it needs no justification. powdr
additionally packs two byte checks into a tuple `[x, y]` whose second slot only enforces
`y < s2` (2048/8192) — a *widening*: the packed form loses `y`'s byte bound, so it is sound only
when `y < 256` is re-derivable from the remaining system (the `byteJustified`/`deepBoundOk`
machinery busPairCancel already uses). This is where powdr's remaining ~4-per-case tuple edge on
register-only blocks (apc_003: powdr 8 tuples vs our 4) comes from. Same for packing the second
slot of an existing `[x, y, 0, 0]` bitwise pair check into a tuple.

## Extend byte-check packing to non-self and cross-form checks (bus interactions)

`bytePackPass` (entry 49) recognises only the self-XOR byte check `[e, e, 0, 1]`. Some blocks
(e.g. apc_008) keep bitwise interactions in other forms — genuine XOR `[x, y, z, 1]` with `x ≠ y`,
or byte checks already half-packed — that it leaves alone, so its bitwise count stays above powdr's.
Generalise the recogniser (and the `bytePairBus` fact) to pack any two messages that each impose a
"this operand is a byte" obligation, regardless of the carrier form. Still a stateless, sound,
variable-neutral bus win.

## Memory-pointer-limb residuals: cross-offset chaining and duplicate cleanup

On memory-heavy blocks (e.g. apc_005) apc-optimizer keeps ~2× powdr's `mem_ptr_limbs` decompositions and
their 13-bit range checks (the high/"page" limb is identical across same-base accesses but apc-optimizer
re-decomposes and re-checks per access). The limbs are pinned by **degree-2 carry constraints**
`(L₁)(L₂) = 0` whose roots are `base + offset` (parameterised by the base variable).
**Update (log 57):** carry-branch resolution (`CarryBranch.lean`) is now landed and does *not*
close this family — measured on apc_005, both factors' value intervals genuinely contain `0`
(e.g. `300 + rs1₀ + 256·rs1₁ − mp₀` ranges over `[−65235, 65835]` with `mp₀ < 2^16`: the 16-bit
wrap really happens on some traces), so no sound one-factor refutation exists and the constraint
is irreducibly two-branched. Closing the gap instead needs **cross-access unification**: two
accesses off the same base at close offsets have provably equal high limbs (`mp₁` differs only
when the low-limb carry differs, a bounded-no-wrap argument in the style of
`MemoryUnify.boundedSumMax`), so the duplicate decomposition + 13-bit check of the second access
can be replaced by the first's limbs plus a small correction. Sound but needs the proven byte
bounds on the base register word (present since the log-50 receive-byte spec change).

## Widen `hintCollapse` to the sltu-style compare gadget (variables)

On comparison blocks powdr collapses the per-limb `diff_marker` witnesses into one inverse hint;
`hintCollapse` (entry 52) does this only when the constraint matches its exact `Σ aᵢ·dimᵢ + t = 0`
shape with byte-bounded single-variable coefficients. The sltu-style gadget (most-significant
difference selection, one marker per limb) doesn't match yet — apc_018 measured after
carry-branch resolution (entry 57): ours 43 vars vs powdr 34; this family is the bulk of the
residual. Generalizing the matcher (coefficients that are *differences* of byte-bounded
variables, sign-split like `CarryBranch.splitSumMax`) should capture it.
**Update (log 57):** the equal-address half is landed — `rootPairUnifyPass` unifies duplicate
same-address decompositions via the two-root/no-wrap argument (−128 vars on each of the
apc_005-class blocks; apc-optimizer now leads powdr on aggregate variable effectiveness). Two
residuals remain:

1. **Duplicate-structure cleanup:** landed as `dedupPass` (log 58) and `flagUnifyPass`
   (log 59). Remaining: per unified pair, one flag component relates to the survivor's
   *non-componentwise* (the encodings differ), so the scaled check never becomes a syntactic
   duplicate. Unifying it needs a derived-variable substitution `b := f(a₀, a₁)` — interpolate
   the relation over the ≤ 4-point joint box (the certificate data already exposes it) and
   substitute a degree-≤ 2 solution, degree-guarded. Would remove the last per-pair flag var
   and (via dedup) the duplicate scaled check: another ~−64 vars and −64 bus on apc_005-class.
2. **Cross-offset chaining** (`ptr` and `ptr+4` sharing the high limb): powdr-side this needs
   reasoning that the low limb doesn't cross the 2¹⁶ page boundary, which is not statically
   true — presumably a carry-witness argument. Harder, unclear value after (1).

## Is-zero / is-equal witness reduction (variables)

An equality/is-zero gadget `cmp = [vector ≠ 0]` is encoded with one inverse-marker witness per limb
(`diff_inv_marker__i`, in the single constraint `−cmp + Σ (a_i − b_i)·inv_i = 0`); powdr collapses
the `k` markers to **one** by combining the byte-bounded limbs into a single value whose zeroness is
equivalent (a weighted sum `Σ 256ⁱ (a_i − b_i)` is zero iff all limbs are, given byte bounds so the
sum can't wrap). Reduces `k−1` variables per comparison. Sound but byte-bound-dependent (needs the
`boundedSumMax`-style no-wrap argument and a transport via `reencode_correct_D`). Note: `cmp` itself
must become a derived column (powdr's `QuotientOrZero`/`IfEqZero`, already in `ComputationMethod`),
since a free `cmp` with the certificate dropped would be under-constrained. Small per case, and
variables are ~tied overall — do the cheaper bus wins first. **Update (log 50):** the `a_i` limbs
are typically *received* register/memory words, which now carry proven byte bounds
(multiplicity-aware `slotBound`); `byteJustified`/`deepBoundOk` in `BusPairCancel.lean` are
reusable justification building blocks.

## Signed-comparison gadget: fold the msb flags into the comparison result (variables)

Log entry 62: on slt/blt-shaped blocks (apc_003 class) we keep `{a_msb_f, b_msb_f, cmp_lt}`
where powdr keeps a single `{cmp_result}` — +2 vars per case, and these cases are the long-tail
losses. The msb booleans are pinned by the sign-decomposition constraints; folding them needs
either a derived-column substitution (each msb flag becomes a `ComputationMethod` over the
operand limbs, with the pinning constraint dropped as entailed) or a `reencode`-style
compression of the three-variable group. Diagnose the exact gadget constraints on apc_003
before choosing.

## Read-read data sharing blocked on the last flag component (variables)

Log entry 62: powdr keeps one copy of same-address read-data words across consecutive accesses
(apc_047 class, ~+3 vars per case). **Log 63 correction:** apc_047's final output has *zero*
scaled-check pairs, so this is *not* blocked on the flag residual there — the duplication needs
its own diagnosis (render the accesses; the addresses presumably differ structurally). The
flag→address→busUnify cascade may still apply on apc_005-class blocks.

## Reuse the deep byte justification beyond pair cancellation

`deepBoundOk` (log 50) proves `x < 256` by enumerating the finite domains of a defining
constraint's selector flags and checking each branch pins `x` to a byte constant or a
byte-bounded variable. **Update (log 68):** part (a) — the redundant byte-check dropper — is
**landed** as `redundantByteDropPass` (C2), consuming `byteJustified`/`deepBoundOk` to drop
entailed bitwise byte checks in the coda. Remaining: (b) wider domains for `domainProp` (a
deep-justified byte var gets a `[0,256)` domain even when no interaction carries it raw).
Generalising the two-term branch to `x = c₀ + Σ cᵢ·yᵢ` with a no-wrap interval bound would
subsume the is-zero and mem-ptr-limb ideas' bound side.

## Smarter witnesses for `disconnectedComponentPass` — measured empty (log 61)

**Do not build without re-measuring.** As of log 61 the optimized outputs contain **zero**
disconnected variables on every sampled case (the entry-43 orphan pattern was consumed by the
entry-50/51 facts and the entry-57–59 cleanup chain), and the only single-occurrence variables
are `hintCollapse`'s reciprocal hints, which are not unconditionally solvable and hence not
removable under powdr's `remove_free_variables` rule either. The witness-finder generalization
only becomes relevant again if a future pass starts stranding non-zero-satisfiable components.

## Batch pair cancellation in one traversal (performance)

`busPairCancelPass` (entry 46) drops one pair per invocation and is drained via `iterateToFixpoint`;
`bytePackPass` (entry 49) is the same shape. On the largest blocks this is O(pairs·n). A
single-traversal multi-drop would be O(n) but needs a multi-drop discipline lemma. As of entry 53
it **is** a measured bottleneck: with the `hintCollapse`/`reencode` rescans fixed, `busPairCancel`
is ~24 s of apc_005's 65 s optimizer time (second only to `domainBatch`, whose fix is sketched in
entry 45's remaining-bottleneck note).

## Runtime: extend the covered-set inverted index (entry 72 / 73 follow-ups)

Entry 72 added `CoveredIndex.lean` (a variable→positions index + `coveredIdx`) and wired it into
`domainBatch` and `reencode`; entry 73 added `coveredIdx_eq_filter` (the completeness/equality
lemma — `build` bucket completeness + `HashSet`/`mergeSort` collapse) and wired it into `domainFold`,
and hashed `busUnify`'s `z ∈ cs.vars` membership (−72 % on that pass). Remaining keccak-profile hot
spots, in rough priority:

- **`busUnify`'s `cs.algebraicConstraints.contains c` (residual, after entry 73).** The variable
  membership is now O(1); the other per-equality scan is a structural `List.contains` over all
  constraints. It is **not** load-bearing for correctness (only the kept-set effectiveness), so a
  structHash-keyed `Std.HashSet` (heuristic; collision-safe re-verify to keep the output identical)
  would cut it. Needs a `Hashable (Expression p)` instance (+ `LawfulHashable` via `structHash`) —
  which would also unblock the `dedup` pass and `flagFold` below.
- **`flagFold` (~51 s).** Same pattern as the old `busUnify`: per-candidate `z ∈ cs.vars` and
  structural `contains`/dedup scans. A once-built `Std.HashSet Variable` for `cs.vars` membership
  (as in entry 73) plus the `Hashable (Expression p)` index above would cut it.
- **Finite-domain enumeration residual.** After indexing, `domainBatch`/`domainFold`'s remaining
  cost is the box scan (`scanInit`/`scanForced`) and `constraintRedundant`; the `envOf` linear
  lookup (log entry 45's note, `docs/log.md:1030`) — substitute pinned domain-1 constants and
  enumerate only free vars — is the algorithmic follow-up (needs `forcedOver` soundness reproven
  over the reduced box).
- **`coveredIdx` on hub variables.** A variable shared across many constraints yields a large
  candidate bucket; most candidates fail the `Q` (⊆xs) re-check. Cost is O(bucket) per target.
  Acceptable while partitioned, but a conjunctive (smallest-bucket-first) gather could help if a
  future circuit has heavy hubs.
