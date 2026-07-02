# Proposal: an audited execution-bridge discipline to unlock cross-instruction chaining

Status: **proposal, nothing implemented.** It touches the audited surface (`Spec.lean` /
`Leanr/OpenVM/Semantics.lean`), which is frozen for the optimizer work, so it needs your
sign-off and ideally your edit. Everything downstream (passes and their correctness proofs)
can then be built without further spec decisions.

An earlier draft of this document also proposed adding program-table knowledge to the pc
lookup. That proposal is **withdrawn** — see the post-mortem at the end: the
generator-added constraints already pin every pc-lookup field, the optimizer already
exploits them fully, and the classes I had attributed to "table opacity" are either runtime
witnesses that powdr keeps too (`flags`) or already eliminated (`is_load`).

## Why (measured ceiling)

Full top-100 sweep at defaults: leanr 150323 → 88195 vars (1.704× aggregate) vs powdr's
4.324×. Per-class diffs against powdr's serialized outputs show the dominant residue is
*cross-instruction value flow*. On case 5 (5406 vars, load/store-heavy): we keep 520
`rsN_data` limbs, powdr keeps 8; `mem_ptr_limbs` 258 vs 130; the read/write/prev data and
prev-timestamp classes shrink similarly on powdr's side. On case 2 (ALU block): our 57
remaining vs powdr's 36 differ almost exactly by the per-instruction timestamps and the
`b := earlier a` register-chain values. All of it is downstream of one missing fact:

    from_state__timestamp_{i+1} = from_state__timestamp_i + k_i    (and the pc analogue)

which lives on the **execution bridge**. Without it, memory accesses from different
instructions never have a constant timestamp gap, so `memoryUnifyBatchPass` can never chain
them, regardless of how good its certificates are. Under the current spec this is provably
out of reach: bus 0 has no declared discipline, its messages are observable side effects,
and there is an explicit countermodel (log entry 21) in which a block's instructions
execute in a rotated order with garbage timestamps while satisfying everything.

The fix follows the entry-17 pattern: an **audited declaration** about the execution
bridge, consumed by passes whose proofs are checked against it.

## The declaration

The execution bridge is a linear-consumption bus: each instruction receives the current
`(pc, timestamp)` state (multiplicity −1) and sends the next one (+1). This is the
last-write-wins shape with an **empty address** — a single global "cell" (the execution
state), whose "value" is the `(pc, ts)` pair itself. Concretely, in `openVmBusSemantics`:

```lean
  memoryBus busId :=
    match busMap busId with
    | some .memory          => some { addressFields := [0, 1], tsField := 6, tsBound := 2 ^ 29 }
    | some .executionBridge => some { addressFields := [],     tsField := 1, tsBound := 2 ^ 29 }
    | _ => none
```

(Payload is `[pc, ts]`, so `tsField := 1`; execution-bridge timestamps are the same
globally range-checked timestamps as the memory bus's, hence the same `tsBound`.)

Audit story, clause by clause (mirroring the memory-bus story in `Spec.lean`):
1. *matching* — globally, at most one instruction starts at any timestamp, so `(⟨⟩, ts)`
   identifies a bridge tuple: a send and receive with equal timestamp value carry the same
   tuple.
2. *in-window consumption* — the consumer of a send `(pc', ts')` is the instruction
   fetching at time `ts'`; if the fragment emits another, later send, the fragment is still
   executing at `ts'`, and window exclusivity (the VM grants the block a contiguous,
   exclusive timestamp window) puts that consumer inside the fragment.
3. *timestamp range* — global range-checking, as for memory.

## One new clause in `MemoryBusShape.disciplineOn`

The three existing clauses are not quite enough for the empty-address instantiation: two
sends with *equal* timestamp values make the in-window clause vacuous, and the degenerate
assignment `ts_0 = ts_1` ("both instructions at the same time") satisfies everything while
breaking the chain entailment. The missing fact is timestamp *uniqueness*, which both audit
stories already rely on implicitly (clause 1 is its send-receive face). Proposed fourth
conjunct:

```lean
  -- 4. timestamp uniqueness — two active sends (dually, receives) to the same address
  --    with the same timestamp value carry the same payload (globally, (address, ts)
  --    identifies at most one send and one receive).
  (∀ S ∈ msgs, ∀ S' ∈ msgs, S.multiplicity = 1 → S'.multiplicity = 1 →
    shape.address S = shape.address S' → shape.tsVal S = shape.tsVal S' →
    S.payload = S'.payload) ∧
  (∀ R ∈ msgs, ∀ R' ∈ msgs, R.multiplicity = -1 → R'.multiplicity = -1 →
    shape.address R = shape.address R' → shape.tsVal R = shape.tsVal R' →
    R.payload = R'.payload)
```

Audit delta for the *memory* instantiation: none — offline checking already assumes
per-address timestamp uniqueness.

Proof impact: the `disciplineOn` transfer lemmas (`Subst.lean`, `SubstMap.lean`,
`Rewrite.lean` `mapExpr`/`filterBus`, `MemoryUnify.lean` `addConstraints_correct`) destruct
the conjunction structurally; threading two more conjuncts through them is mechanical (the
clauses quantify over the same evaluated-message list, so the existing `hact`/`hsub`
machinery in `memoryDiscipline_filterBus_zero` covers them verbatim).

## What becomes entailed, and the consuming pass

Notation for a straight-line block of `n` instructions after cycle-1 constant substitution:
receives `r_i = (pcᵢ, ts_i)` with `pcᵢ` a *distinct constant* (the generator pins all
`from_state__pc_i`), sends `s_i = (pcᵢ₊₁, ts_i + kᵢ)` for `i < n−1`, and the last send's pc
slot possibly non-constant (branch target).

Claim (the "anchored maximum" argument): if some send `s_m`'s pc slot provably differs from
**every** receive's pc constant (typically the final send: `pc_n = start + 4n` is outside
the block), then for every other send `s_k` whose pc slot matches **exactly one** receive
`r_{k+1}`:

    r_{k+1}.payload = s_k.payload      (hence ts_{k+1} = ts_k + kₖ)

Reasoning, entirely inside the declared discipline: active sends have pairwise-distinct
timestamp values (clause 4: equal values would force equal payloads, refuted slot-wise on
the distinct pc constants), so they are strictly ordered; every send except the
timestamp-maximal one is the earlier member of an adjacent pair with nothing strictly
between, so clause 2 gives it an in-fragment consumer receive with equal payload; `s_m`
can have no consumer (payload equality is refuted against every receive on the constant pc
slot), so `s_m` *is* the maximum and every other send is consumed; the consumer of `s_k` is
identified by refuting every receive whose pc constant differs — leaving exactly
`r_{k+1}`.

This is the certificate structure of `MemoryUnifyBatch.checkMemMatchG` with two
substitutions: the constant-timestamp-gap premise is replaced by the anchored-maximum
premise, and the refutations run on the *pc payload slot* (constant disagreement — the
existing `addrConstsNeq` generalized to arbitrary payload slots) instead of the timestamp.
No new proof cores beyond the discipline clause; I would add it as a separate
`ExecChain.lean` pass rather than complicating `checkMemMatchG`.

Cascade: once `ts_{i+1} := ts_i + kᵢ` is substituted, all memory-bus timestamps become
constant offsets of `ts_0`, and the **existing** `memoryUnifyBatchPass` chains register and
heap accesses across instructions with no further changes — this is where the `rsN_data`,
`b`-limb, `prev_data`, prev-timestamp and decomposition classes collapse.

## Known limitation

Blocks whose final branch can provably-possibly target an in-block pc (tight self-loops)
have no anchorable maximum, and the chain is genuinely not entailed by the declaration (the
rotated-execution assignment satisfies all four clauses). Those blocks keep today's
behavior. If they matter — they are hot-loop APCs — the stronger audited claim "the
fragment's bridge actives alternate receive/send in timestamp order" would cover them, but
it is a bigger audit step; I'd start without it and measure.

## Expected impact

Case 2 by hand: 57 → ~34 remaining (3 timestamp links, 12 `b`-limbs, 4 `a`-limbs, plus
decomposition knock-ons), i.e. ≈ powdr's 36 modulo the `diff_inv` witnesses. Case 5's 520
`rsN_data` (powdr: 8) and half its `mem_ptr_limbs` are this class. Rough expectation:
aggregate 1.70× → 2.3–2.8×.

---

## Appendix: the withdrawn pc-lookup proposal (post-mortem)

The earlier draft proposed threading the program table (which the exports carry in
`block.blocks[].instructions`, verified: 7,581 constant payload slots match, zero
mismatches) into `violates` for the pc lookup. Investigating your question — "shouldn't
there already be constraints pinning the opcode?" — showed the premise was wrong:

- The generator-added constraints ([1] in your `openvm-bus-semantics` comment) are indeed
  in every export and pin **all** pc-lookup fields, including the opcode expression
  (e.g. case 3's constraint `[27]`, whose variables are exactly the four `flags__i_0`,
  fixes the opcode polynomial to `529`).
- Enumerating `flags ∈ {0,1,2}⁴ × is_load ∈ {0,1}` against *all* the instr-0 flag
  constraints of case 3 (booleanity products, sum constraint, the opcode pin, the
  flags/is_load link) leaves exactly four survivors — `(0,0,0,2), (0,0,1,0), (0,1,0,0),
  (1,0,0,0)`, all with `is_load = 1`. The four flag encodings are *runtime* freedom (they
  encode the load's shift amount, a function of the accessed address), and powdr keeps
  them too (8 on case 3, 512 on case 5 — identical to our current output).
- `is_load`, which *is* forced, is already eliminated by the joint-enumeration pass
  (log entry 22) — my draft cited a stale pre-entry-22 render.

So a program table would add no effectiveness: its information content is exactly the
generator pins, which the optimizer already consumes. What remains of the topic is only
your documented modeling caveat (never-violating pc lookup is wrong in the completeness
direction). For the current optimizer that is benign — no pass ever *adds* interactions,
and `tautoBusDropPass` only drops constant, accepted messages — but if you ever want the
model exact, the `program` parameter sketched in the withdrawn draft (defaulting to
`fun _ => none` = today's behavior) is the shape I'd suggest. Not needed for effectiveness.
