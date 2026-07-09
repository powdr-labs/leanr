# Ideas for future optimization passes

## Collapse the multi-limb is-zero inverse hint to one (finish powdr's `seqz`)

After entry 47 (`ZeroRegister.lean`) pins `x0 = 0`, a `beqz`/`bnez` gadget is left as
`cmp·(cmp−1)=0`, `(cmp−1)·aᵢ=0` (i=0..3), `Σ aᵢ·dimᵢ = cmp`, with **four** `diff_inv_marker` hints
`dimᵢ`. powdr keeps only **one** inverse hint: `(1−cmp)·(Σaᵢ)=0`, `inv·(Σaᵢ)=cmp`. Collapsing 4 hints
→ 1 (−3 vars/branch, ≈ the residual 264-var gap) needs **no spec change** — it is sound under the
current spec:
- **soundness** (out→in): reconstruct `dimⱼ = 1/aⱼ` for a differing limb (from `cmp=1 ⇒ Σaᵢ≠0 ⇒ some
  aⱼ≠0`); `cmp=0 ⇒ all aᵢ=0` from the kept `(cmp−1)·aᵢ=0`. No byte facts needed.
- **completeness** (in→out): introduce `inv = QuotientOrZero(cmp, Σaᵢ)`; the `Σaᵢ=0 ⇒ cmp=0` case
  needs `aᵢ` **byte-bounded** (so `Σaᵢ=0 ⇒ all aᵢ=0`), available from the range-check bus via
  `slotBound`/`BoundsMap` (as in `MemoryUnify`), with `n·(B−1) < p`.

Two sub-parts: (a) a gadget *pattern match* (boolean `cmp`; hint vars `dimᵢ` occurring only in the
one bilinear constraint; the `(cmp−1)·aᵢ` limb constraints), and (b) introducing the derived `inv`
and dropping `dimᵢ`. The pattern match is the fragile/overfitting risk — phrase it generally
("witnesses appearing only in a single `Σ aᵢ·xᵢ = target` constraint with byte-bounded `aᵢ`"), not
tied to `diff_inv_marker`. Effort is comparable to entry 47; deferred to keep that commit small.

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