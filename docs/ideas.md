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

## Smarter witnesses for `disconnectedComponentPass`

`disconnectedComponentPass` (entry 43) removes a disconnected component only if the **all-zero**
witness certifies it satisfiable (every dropped constraint evaluates to `0`, every dropped
stateless interaction is non-violating). This captures dead range-checked auxiliaries (e.g. the
`bit_shift_carry` limbs) but **not** the most common disconnected pattern in the benchmark: an
orphaned register read, whose data limbs survive only in a bitwise byte-check
`[K − Σ 256ⁱ·limbᵢ, limb₀, 0, 0]` plus range checks. There, `0` is not a satisfying assignment (the
first bitwise slot is a large constant, not a byte); the satisfying witness is the base-256
decomposition of `K` (~29 benchmark cases, 3 vars each).

Capturing them needs a witness *finder* that solves a small system of range/byte lookups. The
correctness machinery already supports any witness (it only re-checks `violatesConstraint`/`eval`
at run time), so **only the finder needs to change**, not the proof. Caveat: a decomposition solver
leans toward the OpenVM limb structure — phrase it as a general "solve the component's lookups"
search (probe `violatesConstraint`) rather than hard-coding base-256, to avoid overfitting.

## Batch pair cancellation in one traversal

`busPairCancelPass` (entry 46) drops one pair per invocation and is drained via `iterateToFixpoint`
inside the cleanup cycle. On the largest blocks (~hundreds of pairs) this is the dominant per-pass
cost. A single-traversal "drop all matched interior send/receive pairs per address" would be O(n)
instead of O(pairs·n), but needs a multi-drop discipline lemma (the current proof is per-pair via
`admissibleMemoryBus_dropOne` applied twice). Only worth it if the pass becomes a benchmark
bottleneck.