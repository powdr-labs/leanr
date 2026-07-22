# apc-optimizer: A Verified Constraint System Optimizer

apc-optimizer is a verified constraint system optimizer, designed to be a drop-in replacement for the [`powdr_autoprecompiles::optimizer::optimize`](https://github.com/powdr-labs/powdr/blob/5395a66442c82abc3c095d758f170773c4b5857d/autoprecompiles/src/optimizer.rs#L31-L41) function. It comes with a proof of correctness, meaning that the optimizer is *proven to maintain a notion of circuit equivalence*.

## Auditing Correctness

apc-optimizer is designed to have a small auditing surface. The audited files live directly under
[`ApcOptimizer/`](./ApcOptimizer); everything under [`ApcOptimizer/Implementation/`](./ApcOptimizer/Implementation) needs **no** audit — its correctness is guaranteed by
the theorems below. To audit
apc-optimizer, it should be sufficient to review:
1. [`ApcOptimizer/Spec.lean`](./ApcOptimizer/Spec.lean): Defining the notion of circuit equivalence and optimizer correctness.
2. [`ApcOptimizer/OpenVmSemantics.lean`](./ApcOptimizer/OpenVmSemantics.lean) and [`ApcOptimizer/Sp1Semantics.lean`](./ApcOptimizer/Sp1Semantics.lean): The OpenVM- and SP1-specific semantics, needed for the corresponding VM-specific optimizations. You only need to audit the semantics of the VM you use; to support a further VM, provide its semantics (an audited file like these) in order to use apc-optimizer.
3. [`ApcOptimizer/MemoryBus.lean`](./ApcOptimizer/MemoryBus.lean): The memory-discipline utility the semantics above build on (its `direction` selects OpenVM's send-then-receive convention or SP1's reverse); likely useful for other VMs as well.
4. The correctness theorems in [`ApcOptimizer/Optimizer.lean`](./ApcOptimizer/Optimizer.lean): `optimizerWithBusFacts_maintainsCorrectness` — the master statement that the optimizer maintains correctness for *any* proven bus facts — together with its instances, `simpleOptimizer_maintainsCorrectness` (the fact-free optimizer), `openVmOptimizer_maintainsCorrectness` (the `openVmOptimizer` the CLI actually runs), and `sp1Optimizer_maintainsCorrectness` (the SP1 optimizer). Audit the statements and check that the proofs are correct by running `lake build`.

### Assumptions (OpenVM)

The theorem is proven against the spec and the OpenVM semantics above. For the guarantee to carry over to a real OpenVM circuit, the auditor must verify that the following assumptions hold on the *input* circuits:

- **Memory and execution-bridge interactions are listed in chronological order.** The `admissible` predicate pairs each send with the next same-address receive *in list order* (see [`ApcOptimizer/MemoryBus.lean`](./ApcOptimizer/MemoryBus.lean)), so the exporter must emit these interactions in time order. If this was not the case, completeness might be violated.
- **The input guarantees invariants and respects the degree bound.** The optimizer *preserves* `guaranteesInvariants` and `withinDegree`, but only assuming the input has them (e.g. that written memory limbs are byte-range-checked). Confirm this for the circuits you feed it.
- **PC lookups are pinned.** [`ApcOptimizer/OpenVmSemantics.lean`](./ApcOptimizer/OpenVmSemantics.lean) checks only the arity of a PC lookup, not the program table. We assume that constraints like `opcode = 0x5b` have already been added to the input circuit, pinning the lookup table values.
- **Every memory writer in the deployed system is byte-range-checked.** `violates` in [`ApcOptimizer/OpenVmSemantics.lean`](./ApcOptimizer/OpenVmSemantics.lean) treats a memory *receive* (multiplicity `-1`) from the register / main-memory address spaces (1 and 2) with a non-byte data limb as conflicting, so the optimizer may assume received memory words are bytes. This is justified only if *every* chip sending into these address spaces — including the initial-memory boundary — maintains the byte-range invariant that `breaksInvariant` demands of the circuits optimized here (which is OpenVM's memory discipline).

## Usage

The `apc-optimizer` executable runs the optimizer on powdr `SymbolicMachine` exports (`ApcWithBusMap` JSON, plain or gzipped) and reports effectiveness — the factor by which each of three size measures shrinks, `before / after`, in priority order: distinct variables, then bus interactions, then algebraic constraints:

```bash
lake build

# Optimize one case and report effectiveness (`[vm]` = openvm (default) | sp1)
lake exe apc-optimizer run Benchmarks/OpenVM/openvm-eth/apc_001_pc0x4ecc54.json.gz

# apc-optimizer and powdr side by side, where `<opt>` is powdr's own serialized optimizer output
# (add `sp1` after the subcommand for SP1 / KoalaBear inputs)
lake exe apc-optimizer compare <unopt>.json.gz <unopt>.powdr_opt.json.gz

# Optimize and write the result as {machine, bus_map} JSON (readable by compare/report above)
lake exe apc-optimizer opt-export <unopt>.json.gz <out>.json
```

The benchmark sets live under [`Benchmarks/`](./Benchmarks/), grouped by VM ([`Benchmarks/OpenVM/`](./Benchmarks/OpenVM/), [`Benchmarks/SP1/`](./Benchmarks/SP1/); see their READMEs); the main one, used for optimization, is the top-100 `openvm-eth` set in [`Benchmarks/OpenVM/openvm-eth/`](./Benchmarks/OpenVM/openvm-eth/).

## Benchmark

As the main benchmark, we use `openvm-eth`: the 100 costliest basic blocks in [openvm-eth](https://github.com/powdr-labs/openvm-eth), a guest program verifying Ethereum blocks. For details, see [`Benchmarks/OpenVM/README.md`](./Benchmarks/OpenVM/README.md).

To sweep a benchmark set in parallel and report aggregate apc-optimizer-vs-powdr effectiveness (`--vm` selects the VM — `openvm` (default) or `sp1` — and the positional argument selects the set by name, defaulting to `openvm-eth` / `rsp`):

```bash
Benchmarks/benchmark.py                # all openvm-eth cases (--jobs = cores)
Benchmarks/benchmark.py --n 20         # top 20 by cost rank
Benchmarks/benchmark.py --vm sp1       # all rsp (SP1) cases
Benchmarks/benchmark.py --n 10 --report report.html   # + interactive HTML report
```

The on-demand `Effectiveness Bench` CI workflow runs the same script from GitHub, by default also
benching `main` for a per-case comparison — sizes are deterministic, so it lists exactly which
circuits changed (`gh workflow run "Effectiveness Bench"`, optionally `-f pr=<N>` to bench a PR
head and post the table there as a sticky comment).

To bench the optimizer's *runtime* instead — the wall time of each optimizer call plus per-pass
attribution (`apc-optimizer profile`) — use `runtime_bench.py`; the on-demand `Runtime Bench`
workflow (`gh workflow run "Runtime Bench" -f pr=<N>`) benches the full set from source against
`main`, both sides on the same runner (cross-runner timings don't compare):

```bash
Benchmarks/runtime_bench.py            # all openvm-eth cases, serial (stable timings)
Benchmarks/runtime_bench.py --n 20 --repeat 3   # top 20, best-of-3 per case
```