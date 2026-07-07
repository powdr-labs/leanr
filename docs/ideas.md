# Ideas for future optimization passes

## Drop never-violating stateless lookups (bus-interaction effectiveness)

The new bus-interaction metric (log entry 42) shows leanr well behind powdr on bus interactions
(~1.4× vs ~2.5× on a small sample), while at variable parity. powdr removes PC lookups and other
stateless lookups that are proven never to violate; leanr keeps them (never-violating model), so
they inflate the bus count without affecting variables.

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