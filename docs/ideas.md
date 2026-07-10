# Ideas for future optimization passes

## keccak: unify read-data limbs to close the variable gap (variables — top priority)

On the keccak stress case, after the bitwise-result byte bound (log entry 58) cancelled the memory
send/receive chains (bus 5206 → 3904), the **variable** gap is now the story: apc-optimizer 3622
vs powdr 2021. The bulk is ~1200 read-data limbs (`b__*`, `c__*` classes — powdr has *none* of
them) that survive because, although their memory interactions cancelled, the same limbs still
occur as **operands/results of the XOR (bitwise) interactions**. powdr eliminates them by
substituting each read limb by the value written to that cell (memory last-write-wins: a read
returns the send's payload, so `read_limb = written_limb`) and/or by the XOR functional dependence
(`slotFun` already proves `z = x ⊕ y` for the bitwise result). Two concrete angles:
- **Read-value substitution.** When `busUnify` pairs a constant-address send `S` (writing value
  `V`) with the next receive `R` (reading `W`), it already adds `W = V`; Gauss should then
  substitute `W := V` and drop `W`. Check why this is not eliminating the keccak `b`/`c` limbs —
  likely the chain's *first* receive reads a genuine pre-block value (no earlier send), so only
  the initial limb is irreducible and the rest should collapse. If `busUnify`'s constant-address
  gate or `findConsumer`'s mid-refutation is missing these, widening it is the win.
- **XOR-result derivation.** A bitwise interaction `[x, y, z, 1]` functionally determines `z`
  (`slotFun`, entry-for the XOR). A pass that turns `z` into a derived column
  (`ComputationMethod`, like `reencode`) reading `x, y` would remove `z` as a free variable. Needs
  the completeness `derivesWitness` bookkeeping, but `slotFun` already carries the soundness half.

The bitwise-**result** byte bound itself is now landed (`openVmFacts.slotBound` slot 2, entry 58) —
do not re-propose it.

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

## Range-check packing via the tuple range checker (bus interactions)

powdr merges a byte check and an N-bit range check into a single `TupleRangeChecker` interaction
`[x, y]` (checking `x < s1 ∧ y < s2`); apc-optimizer keeps them as two separate `variableRangeChecker`
lookups. This is the same shape as the byte-check packing already landed (entry 49): add a
`BusFacts` fact that a tuple-range message `[x, y]` is accepted iff the two single range checks
`[x, bits1]`, `[y, bits2]` are, then a pass that pairs a byte check with a matching-width range
check into one tuple interaction. Sound (identical satisfying set), stateless, variable-neutral —
a clean bus win. Modest per case (~2–8 interactions), but general.

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
(apc_047 class, ~+3 vars per case); our receive-equals-send chaining should entail the same but
the addresses are not syntactically equal — the entry-59 residual (one flag component per
unified pair relates non-componentwise). The derived-variable interpolation `b := f(a₀, a₁)`
(see the mem-ptr residuals item) would make the addresses syntactically equal and likely
unlock the whole cascade: flag → address → busUnify data equations → word unification.

## Reuse the deep byte justification beyond pair cancellation

`deepBoundOk` (log 50) proves `x < 256` by enumerating the finite domains of a defining
constraint's selector flags and checking each branch pins `x` to a byte constant or a
byte-bounded variable. Today only `busPairCancelPass` consumes it. It could also power (a) a
redundant-range-check dropper (a stateless byte check whose operands are deep-justified from the
*rest* of the system is removable — same `filterBus` shape as `tautoBusDropPass` but with an
env-dependent justification), and (b) wider domains for `domainProp` (a deep-justified byte var
gets a `[0,256)` domain even when no interaction carries it raw). Generalising the two-term
branch to `x = c₀ + Σ cᵢ·yᵢ` with a no-wrap interval bound would subsume the is-zero and
mem-ptr-limb ideas' bound side.

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
