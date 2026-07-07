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