# Proposal: program-order timestamp monotonicity (the dominant remaining lever)

Status: **spec clause ADDED (commit `115e40a`), pending your review; no pass consumes it
yet.** You approved adding the assumption; it is now clause 5 of `MemoryBusShape.disciplineOn`
(`msgs.Pairwise` on active-message timestamps), proven behavior-neutral — snapshot
byte-identical, both correctness theorems still 3-axiom. It *reverses a deliberate design
choice* (the discipline was order-free by your entry-17 decision), which is why it needed
your sign-off. The `ExecChain` consumption (anchor = last active send) is the next step and is
deliberately left for after your review — see log entry 34 for the proof route and the two
open design points. The rest of this doc is the original motivation/impact analysis.

## The result it would unblock

Current: leanr **2.54× aggregate** (2.67× geomean) on the top-100 set, every output within
the degree bound, both `optimizer_maintainsCorrectness` and `optimizer_respectsDegree` proven
(3 standard axioms). powdr: 4.32×.

Root cause of most of the gap, established by class-diffing the largest laggards against
powdr: **one lever, cross-instruction timestamp chaining.** Where it fires, effectiveness
is powdr-class; where it's blocked, timestamps survive per-instruction and drag every
dependent class with them.

- apc_034: terminal send anchorable → **1** `from_state__timestamp` survivor (fully chained),
  5.27×.
- apc_012: terminal jump to a **symbolic** target → **21** survivors (one per instruction),
  2.01×.
- apc_031: same → **99** survivors, 2.24×.

Everything downstream of a surviving timestamp also survives: `rsN_data`, `read_data`,
`prev_data`, and the `_timestamp_lt_aux__lower_decomp` / `_prev_timestamp` limbs. On apc_012,
chaining the 21 timestamps to `ts_0 + const` would (by the dependency structure) take it from
423 vars toward powdr's 179.

## Why it's blocked, precisely

`ExecChain` (the execution-bridge unifier) uses an **anchored-maximum** argument: it needs
one active send whose payload is provably `≠` every receive's — that send has no in-fragment
consumer, so by the in-window clause it is the timestamp maximum, and every other send is
then consumed in-fragment, yielding `ts_{i+1} = ts_i + 3`.

A basic block's last interaction is a control-flow op. When its target is symbolic
(`pc' = 2·to_pc_limbs_0 + 65536·to_pc_limbs_1` for JALR/branch), that terminal send's pc
**cannot be proven ≠** the in-block receive pcs (the bounded limbs could, a priori, land on
an in-block address). So there is **no anchor**, and the *entire* chain fails — including the
20 clean straight-line links before it. Since essentially every real block ends in a
control-flow instruction, this blocks the majority of cases.

The memory bus avoids this because its timestamps come out as *constant* offsets
(`ts_i + k`), so `ChainUnify` orders the accesses by constant gap without needing an anchor.
The execution bridge's timestamps are all independent variables — the anchored maximum is the
only order signal, and the symbolic jump removes it.

## The proposed assumption

Interactions on a memory/linear-consumption bus are emitted by the APC generator **in
program (execution) order**, and timestamps are non-decreasing in that order. Formally, add to
`MemoryBusShape` a flag (or a fourth `disciplineOn` conjunct gated on it):

> For active sends `S`, `S'` appearing in list positions `i < j`, `tsVal S ≤ tsVal S'`.

Then the **last** active send in list order has the maximal timestamp — it is the anchor,
with no proof about its (symbolic) pc needed. `ExecChain` gets its anchor unconditionally and
the whole chain collapses.

Soundness/audit story: this holds de facto for powdr's exports (the generator lists exec-bridge
interactions in execution order, and OpenVM timestamps increase monotonically along a
fragment's execution). powdr *relies* on exactly this — its optimizer treats the bus rows as
ordered. It is an audited assumption of the same kind as the offline-memory-checking one, but
about the generator's *ordering* rather than its uniqueness.

## Why I did not implement it

Your entry-17 note is explicit: *"Order-freedom is deliberate: a fragment listing its
accesses out of time order can only cost optimizations, never correctness."* This proposal
**reverses** that — it makes list order load-bearing for soundness of the resulting
optimizations. That is your call, not mine to make unilaterally (unlike the exec-bridge
discipline and the degree bound, which extended the contract without contradicting a prior
decision).

Threading cost if you approve: the new clause quantifies over the same evaluated-message list
as the existing three, so it transfers through `substF`/`mapExpr`/`filterBus` with the same
machinery (substitution preserves list order; the clause compares evaluated ts values under
the rebound env, exactly like clauses 1/2/4). `ExecChain` gains a list-order anchor rule
(pick the last active send) alongside the existing payload-refutation rule. Estimate: a few
hours, mechanical.

## The second, independent lever (for completeness)

Even with timestamps chained, a residual gap remains on load/store-heavy blocks (apc_034:
1814 vs powdr 1060, dominated by `mem_ptr_limbs` 330 vs 146 and `prev_data` 380 vs 196).
This is **heap-data chaining**: two accesses to the same *runtime* address whose pointer
decompositions are separately witnessed. Recognizing them as the same address needs
address-**equality-by-value** reasoning (the two symbolic pointers provably equal). The
`DigitEq.lean` pass (proven, in the tree, unwired) handles the case where a single constraint
links the two decompositions as `Σ magᵢ(xᵢ−yᵢ)=0`; it fires on no OpenVM benchmark case
because the circuits don't emit that linking constraint — the two pointers are equal only
*through* the register values that feed them, which requires the register chain (lever 1)
first. So lever 2 is largely downstream of lever 1; worth revisiting after order-monotonicity.

## powdr comparison caveat

powdr's reported 4.32× also includes eliminations that are **not** equivalence-preserving in
any static sense (its serialized `optimistic_constraints` — assumptions checked separately at
proving time). A like-for-like "sound static optimizer" comparison would put the achievable
ceiling somewhat below 4.32×. Order-monotonicity is the honest, auditable version of powdr's
ordering assumption and is where the bulk of the remaining sound gain lies.
