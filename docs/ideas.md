# Ideas for future optimization passes

## Consider dropping `reencode` in favour of `domainFoldPass` alone (entry-47 option B)

`domainFoldPass` (`DomainFold.lean`, log entry 48) is now landed **alongside** `reencode` (option A) —
effectiveness-neutral but the general, powdr-style mechanism made explicit. The remaining open decision
is entry-47 **option B**: drop `reencode` and keep only the fold pass. Measured trade-off on the
apc_005 load/store class: fold-only reaches **1939** vars (keeping all flags, close to powdr's 1808),
vs **1683** with `reencode` — i.e. option B is more principled / powdr-aligned but gives up the ~13%
flag binary-compression (512 ternary flags → 256 bits) that currently makes leanr *beat* powdr there.
Only worth it if the flag-compression edge is judged not worth `reencode`'s complexity/runtime; the fold
pass would then also want a `bits ≥ vars` / large-group path (groups `reencode` skips) to claw some of
it back. Left for Georg to decide.

Effectiveness priority: **variables > bus interactions > constraints**. As of the byte-check
packing pass (log entry 49), on the top-12 `openvm-eth` sample leanr and powdr are ~tied on
variables (leanr wins the aggregate, powdr the geomean) and leanr leads on constraints; the
remaining *systematic* gap is bus interactions. The bus gap now decomposes as: (a) range-check
packing via the tuple range checker, (b) memory-pointer-limb 13-bit checks on memory-heavy blocks,
(c) residual bitwise checks that are not self-XOR byte checks, (d) occasional missed memory
send↔receive cancellations. See the `docs/log.md` entry 42/46/49 discussion for measurements.

## Drop never-violating stateless lookups (close the residual pc-lookup bus gap)

After memory/exec send↔receive pair cancellation (log entry 46), leanr is at near-parity with powdr
on bus interactions; the residual gap is essentially the **PC lookups** (bus 2): powdr removes them,
leanr keeps them (never-violating model), so they inflate the bus count without affecting variables.

A `VerifiedPass` that drops a stateless bus interaction whose multiplicity is provably `0`, or that
is proven never-violating via `BusFacts.neverViolates`, would be sound (removing a
never-violating, non-stateful interaction changes no stateful side effect) and would raise bus
effectiveness without regressing variables — a clean win under the priority order
(variables > bus interactions > constraints). Check the existing zero-multiplicity drop in
`cleanupCycle` first; this may be an extension of it rather than a new pass.

## Range-check packing via the tuple range checker (bus interactions)

powdr merges a byte check and an N-bit range check into a single `TupleRangeChecker` interaction
`[x, y]` (checking `x < s1 ∧ y < s2`); leanr keeps them as two separate `variableRangeChecker`
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

## Eliminate memory-pointer-limb decompositions / redundant range checks (bus interactions)

On memory-heavy blocks (e.g. apc_005) leanr keeps ~2× powdr's `mem_ptr_limbs` decompositions and
their 13-bit range checks (the high/"page" limb is identical across same-base accesses but leanr
re-decomposes and re-checks per access). The limbs are pinned by **degree-2 carry constraints**
`(L₁)(L₂) = 0` whose roots are `base + offset` (parameterised by the base variable), so no linear
(`gauss`/`affine`) or finite-*constant*-domain (`domainProp`/`domainBatch`/`reencode`) pass can
touch them. Closing it needs a **carry-branch-resolution** step: use the proven byte/range bounds
(`BusFacts.slotBound`) to show one factor of the product can't vanish, collapsing `(L₁)(L₂)=0` to
the linear `Lᵢ=0` so Gauss can unify the shared limb and drop the duplicate check. This is the
hardest of the current ideas — dropping a range check is sound only if the shared limb is *proven*
equal (a bounded-no-wrap argument in the style of `MemoryUnify.boundedSumMax`) — and it is a bus
win on an axis where leanr is already ~tied with powdr on variables, so lower leverage than the
packing passes. **Update (log 50):** the base `mem_ptr_limbs` derive from *received* register
words, whose limbs now carry proven byte bounds (`slotBound` on memory receives, since the
receive-byte spec change) — the missing input bound for the no-wrap argument now exists.

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

## Smarter witnesses for `disconnectedComponentPass`

`disconnectedComponentPass` (entry 43) removes a disconnected component only if the **all-zero**
witness certifies it satisfiable. This misses the common orphaned-register-read pattern (data limbs
surviving only in a bitwise byte-check `[K − Σ 256ⁱ·limbᵢ, limb₀, 0, 0]` plus range checks), where
the satisfying witness is the base-256 decomposition of `K`, not `0`. A witness *finder* that solves
the component's lookups (probe `violatesConstraint`) would capture them. Only the finder changes,
not the proof. Phrase it as a general "solve the component's lookups" search, not hard-coded
base-256, to avoid overfitting to the OpenVM limb structure.

## Batch pair cancellation in one traversal (performance)

`busPairCancelPass` (entry 46) drops one pair per invocation and is drained via `iterateToFixpoint`;
`bytePackPass` (entry 49) is the same shape. On the largest blocks this is O(pairs·n). A
single-traversal multi-drop would be O(n) but needs a multi-drop discipline lemma. As of entry 53
it **is** a measured bottleneck: with the `hintCollapse`/`reencode` rescans fixed, `busPairCancel`
is ~24 s of apc_005's 65 s optimizer time (second only to `domainBatch`, whose fix is sketched in
entry 45's remaining-bottleneck note).
