# Ideas for future optimization passes

## Domain-constant subexpression folding (powdr-style; recovers most of `reencode`'s gain without re-encoding)

**Motivation (investigation, 2026-07):** `reencode` is responsible for a large, *concentrated* share of
effectiveness — ~zero on register-only blocks (apc_003/069 identical with/without it) but ~half the
variable reduction on load/store-heavy blocks (apc_005: **3619 → 1683 vars** with reencode vs without).
That gain decomposes into two very different parts:

1. **Direct flag compression** (`m`-valued flag group → `⌈log₂ m⌉` bits): genuinely unique to reencode.
   On apc_005 this is 512 ternary `flags` → 256 `rnc` bits, i.e. −256 vars. powdr keeps all 512 flags.
2. **Indirect chaining unblock (the bulk, ~87%):** re-encoding *constant-folds flag-polynomial memory
   addresses as a side effect* (entry 37's `interpOf` constant emission). The OpenVM destination-register
   write has address `[space=1, offset = 52 − flag_poly]` — same address space as the source-register
   reads `[1, 40, …]`, with an offset that is a degree-2 flag polynomial but is **identically constant on
   the flags' constrained domain** (= 52). leanr's `busUnify`/`addrConstsNeq` can only prove two accesses
   differ when *both* offsets are syntactic constants, so the symbolic offset blocks chaining the source
   reads across it. Folding `52 − flag_poly → 52` unblocks it, and the register/data/timestamp chains
   collapse (rs1_data 516 → 8, the `lower_decomp` limbs with them).

**powdr does exactly this fold and keeps the flags:** on apc_005 powdr reaches 1808 vars with *all 512
flags intact* and *every* register-space offset folded to a constant (20/20 register accesses constant, 0
symbolic; heap-space offsets stay symbolic in both). So the indirect part is not tied to re-encoding — it
is ordinary range/domain-constraint simplification, powdr's `optimize_range_constraints` + rule-based
folding.

**Proposed pass:** for a small variable group with a finite enumerable joint domain (the same
`groupDoms`/survivor enumeration `reencode`/`domainBatch` already build), replace any subexpression that
takes the **same value on every survivor** by that constant — *without* introducing bits, dropping the
group, or touching the flags. Soundness is a pure rewrite: `e − c = 0` is entailed by the group-local
constraints, so `e.eval env = c` on every satisfying assignment (env' = env, no new variables, no
derivations) — strictly simpler than `reencode` (no witness transport / backward direction), and it can
reuse `reencode`'s domain-enumeration certificate (`patts.all (decide (e.eval = c))`). It is a strict
generalization of `domainBatch` (which only substitutes a *single* variable forced to a size-1 domain)
and of `ConstantFold` (syntactic constants only): the new capability is recognizing that a *compound*
expression is constant on the *joint* domain.

Expected effect: recovers ~most of reencode's load/store gain (powdr's 1808 is the rough target; leanr's
chaining is if anything stronger than powdr's, entry 41), is VM-agnostic and generally useful, and fires
on groups reencode skips (m too large to compress, or `bits ≥ vars`). Decision to settle before
implementing: **keep both** (fold pass + reencode → strictly ≥ current, most general) vs **replace**
reencode with the fold pass (more principled / powdr-aligned, but loses the ~7-13% flag-compression edge
that currently makes leanr *beat* powdr on these blocks, e.g. 1683 < 1808).

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