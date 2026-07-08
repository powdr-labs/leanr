# Ideas for future optimization passes

## Batch all merges per pass (bus-interaction effectiveness)

`mergeTuplePass` and `mergeLookupPass` (entries 43–44) each perform *one* merge per cleanup cycle,
so they race for the shared byte checks: on `apc_003` only 4 of 8 possible `tupleRangeChecker[a, m]`
packings form before the remaining `a__k` get byte-paired instead. Making each pass remove *all*
disjoint mergeable pairs in a single application would capture the rest (and converge faster). This
needs a batch version of `ConstraintSystem.mergeLookups_correct` — a positional/simultaneous-removal
proof over a list of pairs rather than the current single-pair `bi3 :: filter (≠bi1) (≠bi2)`. Modest
gain (the un-packed leftovers are few), moderate proof effort.

## Broaden `mergeLookups` instances

The generic `mergeLookups` / `mergeTupleLookups` passes accept any obligation-preserving 2→1 merge a
`BusFacts` instance certifies. Beyond the two OpenVM instances landed (bitwise byte-pair; byte +
`varRC[·,b]` → `(256, 2^b)` tuple), other same-obligation packings could be added as new
`OpenVmFacts` cases with no pass change — e.g. two `varRC[·,b]` on the same width into a `(2^b, 2^b)`
tuple bus (when such a bus is declared), or a byte check + `varRC[·,8]` into a bitwise op-0 check
(stays on the bitwise bus, no tuple bus needed). Check the benchmark for which widths actually occur
before adding (apc_003 varRC widths are 12/13/14/17; only 13 matches the declared `(256,8192)` bus).

## Smarter witnesses for `disconnectedComponentPass`

`disconnectedComponentPass` removes a disconnected component only if the **all-zero**
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

## (Investigated, blocked) Stateful send/receive chain collapse — exec bridge & memory

The dominant bus-interaction gap vs powdr is stateful (entry 43: exec 328 vs 2, memory 952 vs 362):
powdr collapses a receive→send→receive→…→send chain to just the first receive and last send, since
the identical middle send/receive pairs cancel. This is **not currently provable** in this spec:
cancelling active stateful interactions changes the active∧stateful message list, and completeness
(`impliesAdmissible`) then needs `bs.admissible` *reconstructed* for the output. `bs.admissible` is
an opaque `BusSemantics` field that `BusFacts` can only *consume* (`admissible_sound`, one
direction); a reverse fact cannot be a `BusFacts` field because `BusFacts.trivial` (arbitrary `bs`)
could not supply it. Worse, naive identical-pair cancellation is genuinely *unsound* for memory when
a write is shadowed (a `[addr,v1]` write, then `[addr,v2]` write/read pair removed, exposes an
unintended `[addr,v1]`→later-read match). Any attempt needs either a spec/`BusSemantics` change
(out of scope: don't touch the audited surface) or a very carefully restricted, separately-justified
transformation. Left here as a known-hard item, not a quick win.
