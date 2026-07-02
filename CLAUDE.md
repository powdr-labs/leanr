# Claude instructions

This repository will become a lean port of powdr autoprecompiles: https://github.com/powdr-labs/powdr
In particular, we are trying to build a circuit optimizer similar to https://github.com/powdr-labs/powdr/blob/main/autoprecompiles/src/optimizer.rs

This repository has been started by Chris. I (Georg) want to get started with the project. But this is my first Lean project, so you should constantly question my ideas.

## Background

This is an example circuit:
```
// Bus 1 (MEMORY):
mult=is_valid, args=[state__clk_high_0, adapter__op_b_memory__access_timestamp__prev_low_0, 0, 0, 0, 0, 0, 0, 0]
mult=-is_valid, args=[state__clk_high_0, 65536 * state__clk_16_24_0 + state__clk_0_16_0 + 3, 0, 0, 0, 0, 0, 0, 0]
mult=is_valid, args=[state__clk_high_0, adapter__op_a_memory__access_timestamp__prev_low_0, 29, 0, 0, adapter__op_a_memory__prev_value__0__0_0, adapter__op_a_memory__prev_value__0__1_0, adapter__op_a_memory__prev_value__0__2_0, adapter__op_a_memory__prev_value__0__3_0]
mult=-is_valid, args=[state__clk_high_0, 65536 * state__clk_16_24_0 + state__clk_0_16_0 + 4, 29, 0, 0, 5, 0, 0, 0]

// Bus 5 (BYTE):
mult=is_valid, args=[3, 0, state__clk_16_24_0, state__clk_16_24_0 + 32512 * adapter__op_a_memory__access_timestamp__prev_low_0 + 32512 * adapter__op_a_memory__access_timestamp__diff_low_limb_0 - (32512 * state__clk_0_16_0 + 97536)]
mult=is_valid, args=[3, 0, state__clk_16_24_0 + 32512 * adapter__op_b_memory__access_timestamp__prev_low_0 + 32512 * adapter__op_b_memory__access_timestamp__diff_low_limb_0 - (32512 * state__clk_0_16_0 + 65024), 0]
mult=is_valid, args=[6, 266338304 - 266338304 * state__clk_0_16_0, 13, 0]
mult=is_valid, args=[6, adapter__op_a_memory__access_timestamp__diff_low_limb_0, 16, 0]
mult=is_valid, args=[6, adapter__op_b_memory__access_timestamp__diff_low_limb_0, 16, 0]

// Bus 7 (EXECUTION_BRIDGE):
mult=-is_valid, args=[state__clk_high_0, 65536 * state__clk_16_24_0 + state__clk_0_16_0, 0, 0, 0]
mult=is_valid, args=[state__clk_high_0, 65536 * state__clk_16_24_0 + state__clk_0_16_0 + 8, 4, 0, 0]

// Algebraic constraints:
is_valid * (is_valid - 1) = 0
```

This circuit could be a chip in a zkVM. Multiple chips can interact via the bus (more on that below).

Some notes:
- All arithmetic is done in a finite field.
- Algebraic constraints: An algebraic expression that has to evaluate to zero.
- Bus interactions:
    - In general, a bus interaction like `mult=is_valid, args=[6, add_operation__value__0__3_0, 16, 0]` sends a tuple of field elements (in this case 4) to the bus, with a given multiplicity (in this case is_valid). The concrete tuple is called the *bus interaction message*.
    - The constraint here is that *globally* the bus has to be balanced: Adding up the multiplicities of all distinct bus interaction messages has to yield zero. For example, three sends of the same tuple with multiplicity 2, 3, and -5 would be balanced.

In practice, bus interactions usually have a hard-coded bus ID in the tuple. This emulates multiple distinct buses that cannot interact. In the example above, this ID has already been stripped and bus interactions have been grouped by bus.

Also, in practice, different buses fall into one of two categories:
- **Stateless buses (a.k.a. lookups)**: Here, the pattern is that all instruction chips just send with multiplicity 0 or 1, and a dedicated chip receives all of the tuples with the necessary multiplicity. It can only receive tuples in a precomputed table. For example, in the BYTE bus, the table includes all tuples `[6, X, 13, 0]` where `0 <= x < 2^13`. Therefore, the bus interaction `mult=is_valid, args=[6, 266338304 - 266338304 * state__clk_0_16_0, 13, 0]` asserts that `266338304 - 266338304 * state__clk_0_16_0` is a 13-bit number (if `is_valid` is 1).
- **Stateful buses**: These actually change the state of the system. The execution bridge is an example: Each chip receives (`mult = -1`) the current time stamp and PC and sends (`mult = 1`) an updated timestamp and PC.

### Circuit equivalence

Informally, two circuits are equivalent if one implies the satisfiability of the other **and** the effect on the stateful buses is the same. For example, if a chip has bus interactions `mult=is_valid, args=[X]` and `mult=-is_valid, args=[X]`, these two bus interactions can be removed, because they will cancel each other out for all possible values of `is_valid` and `X`. This is an example of a circuit optimization.

## Vision

Ideally, this repository would be fully maintained by AI. The idea to achieve that is:
1. Specify a notion of circuit equivalence in Lean. Any output of the optimizer should be equivalent to the input circuit.
2. Specify a notion of circuit size (e.g.: number of variables).
3. Prove correctness of the optimizer (initially: the trivial optimizer that does nothing) in Lean.
4. Merge PRs automatically if they do not change the spec, still compile, and reduce the circuit size on a number of test cases.

## Approach

My mid-term goals are as follows:
- Write a *minimal* spec of circuit equivalence. I want to do this starting from scratch in Spec.lean. The existing data structures include some implementation details, which I want to keep out of the spec.
- Add an optimizer that does nothing, and prove that it is correct with respect to the spec.
- Add some test cases, to measure "effectiveness" (the factor by which the circuit size is reduced) of the optimizer.
- Start implementing very simple optimizations, e.g. when there is a constraint `x = 3`, replace `x` by `3` everywhere.
- Go on to more advanced optimizations from there.

## Current status

_Keep this section up to date: whenever the state of the work changes materially (a file's purpose changes, a milestone is reached, or a goal above is started/finished), update the notes below in the same change._

- **`Leanr/Spec.lean`** — Georg's from-scratch spec of circuit equivalence, and the audited contract (extended 2026-07 with Georg's sign-off by `MemoryBusShape`/`memoryBus` and the `memoryDiscipline` conjunct of `satisfies` — the audited last-write-wins assumption; see `DESIGN-bus-knowledge.md`). Models algebraic constraints *and* bus interactions: `BusSemantics` (stateful/stateless, `violatesConstraint`, `breaksInvariant`), stateful side effects compared up to net multiplicity (`≈` on `BusState`), and `optimizerMaintainsCorrectness` (equivalence + invariant preservation). All reusable lemmas and the optimizer now live under `Optimizer.lean`/`OptimizerPasses/`, not here.
- **The optimizer, in three layers** (public signature fixed at `ConstraintSystem p → BusSemantics p → ConstraintSystem p` for the tooling/snapshot):
    - **`Leanr/OptimizerPasses/Basic.lean`** — the **scaffolding**: full equivalence-relation glue (`BusState.equiv_{refl,symm,trans}`, `ConstraintSystem.implies_{refl,trans}`, `equivalentTo_{refl,symm,trans}`); `PassCorrect` (the per-step obligation: equivalent-to-input + invariant-preserving); `VerifiedPass` (a pass bundled with its `PassCorrect` proof — un-gameable, since the proof *is* the return value); `VerifiedPass.id`/`VerifiedPass.andThen` (seed and compose passes via `equivalentTo_trans`).
    - **`Leanr/OptimizerPasses/*.lean`** — reusable proven cores and one file per pass. Cores: `Subst.lean` (`ConstraintSystem.subst_correct` — substituting `x := t` when satisfying assignments force `x = t`; plus the `substFromConstraint` solver→pass combinator), `SubstMap.lean` (**batch** counterpart: `substF` substitutes a whole map in one traversal, `substF_correct`), `Rewrite.lean` (`mapExpr_correct` for eval-preserving rewrites, `filterConstraints_correct`, `filterBus_correct`), `Affine.lean` (`linearize`/`LinExpr`, `solveAffine` with `±1`-preferring *unit*-coefficient pivots, the proven `pm1PivotsOf`/`unitPivotsOf` candidate enumerations), `Normalize.lean` (term-merging `LinExpr.norm`), `TautoBus.lean` (`filterBusStateless_correct`), `MonicScale.lean` (`mapConstraintsIff_correct`; monic scaling with checked unit certificates). Batch passes (the ones the pipeline uses; each collects *all* its deductions per cycle and applies one `substF`): `Gauss.lean` (`gaussElimPass` — Gaussian elimination: constraints reduced against a resolved, proof-carrying `Solved` hash map, duplication-cost pivot choice with a penalty for rewriting raw stateless payload slots), `DomainBatch.lean` (`domainBatchPass` — proof-carrying `DomainTable` from constraint roots + fact-bounded raw slots; **joint enumeration** of each target's domain box against all constraints/obligations covered by its variable set, so coupled systems like one-hot selectors resolve; work-capped, targets deduped by variable set), `MemoryUnifyBatch.lean` (`memoryUnifyBatchPass` — send/receive unification for *any* number of accesses: per-interaction exclusion of in-between sends via constant multiplicity / constant-address disagreement / constant timestamp offsets outside the window, receives identified by refutation; all certified matches' equalities added per cycle). Single-step predecessors (`ConstantSubst`, `Affine`'s `affineSubstPass`, `DomainProp`'s `domainPropPass`, `MemoryUnify`'s `memoryUnifyPass`) remain as proof libraries/reference but are out of the pipeline. All passes field-agnostic except the domain passes (runtime `p.Prime` gate).
    - **`Leanr/Optimizer.lean`** — the thin assembly: `cleanupCycle` = `gauss → normalize → fold → domainBatch → normalize → fold → drop-trivial → drop-zero-mult → drop-tauto-lookup → memoryUnifyBatch`, run via `VerifiedPassW.iterateStable` (stops at a structural fixpoint, so the `iters` budget — default 32 — is free once converged), then monic canonicalization + fold; `optimizerWith` takes proven `BusFacts`, `optimizer` uses `BusFacts.trivial`; `optimizer_maintainsCorrectness` is a projection of the carried proof.
    - **To add an optimization:** create a `VerifiedPass` in a new `Leanr/OptimizerPasses/` file (typically via one of the cores), import it in `Optimizer.lean`, and `.andThen` it into `cleanupCycle`/`pipelineIters`. Do not touch `Spec.lean` or the glue in `Basic.lean`. **Current effectiveness: 36/11 ≈ 3.27** on the ADD-immediate snapshot; on the top-100 openvm-eth benchmark set see `log.md` entries 19–23 (aggregate ≈ 1.7×, sum-based; powdr ≈ 4.3× — the rest is behind two frozen-spec walls: execution-bridge timestamp/pc chaining and pc-lookup table opacity, both documented in log entries 21/14/15). `DESIGN-bus-knowledge.md` describes the knowledge architecture: proven `BusFacts` (`Leanr/BusFacts.lean`, OpenVM instance in `Leanr/OpenVM/Facts.lean` — zero audit surface) feed fact-domains and pointwise `violatesConstraint` probing; the audited `memoryBus` declaration (`Spec.lean`, `MemoryBusShape`) licenses memory unification.
- **`Leanr/Utils/Dsl.lean`** — reusable, zkVM-agnostic sugar for the spec types: `Add/Mul/Neg/Sub` and `OfNat` instances on `Expression` (write `V "x" * (V "x" - 1)`, numeric literals lower to field constants; `-`/negation lower to `·* -1`), plus a precedence-aware, bus-grouped `render : ConstraintSystem p → String` and a `matchesSnapshot` helper for `#guard`s.
- **`Leanr/OpenVM/Semantics.lean`** — a concrete `BusSemantics` instance for OpenVM (`openVmBusSemantics`), the spec-level counterpart of powdr's `OpenVmBusInteractionHandler`. Like powdr's, it takes the bus map as a parameter (`busMap : Nat → Option OpenVmBusType`, default `defaultBusMap` = `0 ExecutionBridge, 1 Memory, 2 PcLookup, 3 VariableRangeChecker, 6 BitwiseLookup, 7 TupleRangeChecker[256,2048]`) — real exports differ (the reth benchmark has TupleRangeChecker on bus **8**), and an unmapped bus would be unsoundly modeled as a no-op. `isStateful` and `violatesConstraint` follow OpenVM's lookup semantics, `breaksInvariant` models the memory byte-range invariant (a documented modeling choice, not yet corroborated); `memoryBus` keys on the map's `.memory` entry. Also home of `BusMap` (the parsed association-list form, `BusMap.toFun`) and `babyBear`. `Leanr/OpenVM/Facts.lean`'s `openVmFacts` takes the same parameter — its impls key on the mapped bus *type*, so the proofs are uniform in the map.
- **`Leanr/OpenVM/Snapshot.lean`** — a snapshot test mirroring powdr's `apc_builder_single_instructions`. Ports the constraint system that is the *input* to powdr's `optimize()` for a single OpenVM ADD-immediate (powdr `single_add_1`; 36 cols / 20 bus interactions / 32 constraints), runs `optimizer` on it, and `#guard`s the *output's* rendered string against a stored snapshot plus the invariant `effectiveness ≥ 1` (never grows the circuit), reporting the measured shrink factor via `#eval`. The stored snapshot string is regenerated whenever the optimizer's output changes (it now reflects the 11-variable optimized circuit). Build/verify with `lake build` (the whole library builds).
- **`Leanr/OpenVM/SnapshotCorrect.lean`** — the correctness counterpart of the snapshot: machine-checked `addiOptimized.equivalentTo addiInput` and invariant preservation for the exact test circuit (a direct instance of `optimizer_maintainsCorrectness`; only the standard Mathlib axioms, no primality instance needed).
- **`Leanr/JsonParser.lean`** — parser for powdr `SymbolicMachine` exports (`ApcWithBusMap` JSON: `machine.constraints` as expression trees, `machine.bus_interactions` as `{id, mult, args}`, `bus_map.bus_ids`), adapted from the `main`-branch parser to the `Spec.lean` types. Parses the bus map structurally into `OpenVmBusType` (hard error on unknown bus types) and needs no primality instance. Carries a `#guard_msgs` regression eval against `apc_reth_op_bug.json` (9168 constraints / 3117 bus interactions / 6 bus types), so `lake build` is the parser's regression gate.
- **`Main.lean` + benchmarks** — the benchmark CLI (see README): `leanr run [--iters N] <file>` parses an export (`.json` / `.json.gz` via `gunzip -c`), runs `optimizerWith` with the file's own bus map + facts, and reports vars/constraints/bus-interactions before/after plus effectiveness; `leanr vars`/`leanr render` dump the optimized system's variables / rendering (diagnostics); `leanr powdr <unopt> <opt>` reports powdr's effectiveness from its serialized output; `leanr compare` does both. `OpenVm/Benchmark/` (top level, tracked) holds the older interim top-20 keccak set; **`Leanr/OpenVm/Benchmark/`** (untracked data drop) holds the real top-100 openvm-eth set + `manifest.json` that the current numbers refer to. The whole 100-case sweep runs in ~25 minutes (largest case 5406 vars ≈ 25 s at default `--iters 32`, which `iterateStable` makes a converged fixpoint).

So for me (Georg) this is effectively day 1: I'm starting the spec fresh in `Spec.lean` and pulling in existing code deliberately, not by default.