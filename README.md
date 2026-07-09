# Leanr: A Verified Constraint System Optimizer

Leanr is a verified constraint system optimizer, designed to be a drop-in replacement for the [`powdr_autoprecompiles::optimizer::optimize`](https://github.com/powdr-labs/powdr/blob/5395a66442c82abc3c095d758f170773c4b5857d/autoprecompiles/src/optimizer.rs#L31-L41) function. It comes with a proof of correctness, meaning that the optimizer is *proven to maintain a notion of circuit equivalence*.

## Auditing Correctness

Leanr is designed to have a small auditing surface. The audited files live directly under
[`Leanr/`](./Leanr); everything under [`Leanr/Implementation/`](./Leanr/Implementation) needs **no** audit — its correctness is guaranteed by
the theorems below and. To audit
Leanr, it should be sufficient to review:
1. [`Leanr/Spec.lean`](./Leanr/Spec.lean): Defining the notion of circuit equivalence and optimizer correctness.
2. [`Leanr/OpenVmSemantics.lean`](./Leanr/OpenVmSemantics.lean): The OpenVM-specific semantics. These are needed for our OpenVM-specific optimizations. If you are instead interested in a different VM, you can skip this file, but must provide semantics for your VM in order to use Leanr.
3. [`Leanr/MemoryBus.lean`](./Leanr/MemoryBus.lean): Utility used in the OpenVM semantics above (and likely useful for other VMs as well).
4. The correctness theorems in [`Leanr/Optimizer.lean`](./Leanr/Optimizer.lean): `optimizerWithBusFacts_maintainsCorrectness` — the master statement that the optimizer maintains correctness for *any* proven bus facts — together with its two instances, `simpleOptimizer_maintainsCorrectness` (the fact-free optimizer) and `openVmOptimizer_maintainsCorrectness` (the `openVmOptimizer` the CLI actually runs). Audit the statements and check that the proofs are correct by running `lake build`.

### Assumptions (OpenVM)

The theorem is proven against the spec and the OpenVM semantics above. For the guarantee to carry over to a real OpenVM circuit, the auditor must verify that the following assumptions hold on the *input* circuits:

- **Memory and execution-bridge interactions are listed in chronological order.** The `admissible` predicate pairs each send with the next same-address receive *in list order* (see [`Leanr/MemoryBus.lean`](./Leanr/MemoryBus.lean)), so the exporter must emit these interactions in time order. If this was not the case, completeness might be violated.
- **The input guarantees invariants and respects the degree bound.** The optimizer *preserves* `guaranteesInvariants` and `withinDegree`, but only assuming the input has them (e.g. that written memory limbs are byte-range-checked). Confirm this for the circuits you feed it.
- **PC lookups are pinned.** [`Leanr/OpenVmSemantics.lean`](./Leanr/OpenVmSemantics.lean) checks only the arity of a PC lookup, not the program table. We assume that constraints like `opcode = 0x5b` have already been added to the input circuit, pinning the lookup table values.
- **Every memory writer in the deployed system is byte-range-checked.** `violates` in [`Leanr/OpenVmSemantics.lean`](./Leanr/OpenVmSemantics.lean) treats a memory *receive* (multiplicity `-1`) from the register / main-memory address spaces (1 and 2) with a non-byte data limb as conflicting, so the optimizer may assume received memory words are bytes. This is justified only if *every* chip sending into these address spaces — including the initial-memory boundary — maintains the byte-range invariant that `breaksInvariant` demands of the circuits optimized here (which is OpenVM's memory discipline).

## Usage

The `leanr` executable runs the optimizer on powdr `SymbolicMachine` exports (`ApcWithBusMap` JSON, plain or gzipped) and reports effectiveness — the factor by which each of three size measures shrinks, `before / after`, in priority order: distinct variables, then bus interactions, then algebraic constraints:

```bash
lake build

# Optimize one case and report effectiveness
lake exe leanr run OpenVmBenchmarks/openvm-eth/apc_001_pc0x4ecc54.json.gz

# powdr's own effectiveness, from its serialized optimizer output
lake exe leanr powdr <unopt>.json.gz <unopt>.powdr_opt.json.gz

# Both, side by side
lake exe leanr compare <unopt>.json.gz <unopt>.powdr_opt.json.gz
```

The benchmark sets live in [`OpenVmBenchmarks/`](./OpenVmBenchmarks/) (see its README); the main one, used for optimization, is the top-100 `openvm-eth` set in [`OpenVmBenchmarks/openvm-eth/`](./OpenVmBenchmarks/openvm-eth/).

## Benchmark

As the main benchmark, we use `openvm-eth`: the 100 costliest basic blocks in [openvm-eth](https://github.com/powdr-labs/openvm-eth), a guest program verifying Ethereum blocks. For details, see [`OpenVmBenchmarks/README.md`](./OpenVmBenchmarks/README.md).

To sweep a benchmark set in parallel and report aggregate leanr-vs-powdr effectiveness (the positional argument selects the benchmark by name, defaulting to `openvm-eth`):

```bash
OpenVmBenchmarks/benchmark.py                # all openvm-eth cases (--jobs = cores)
OpenVmBenchmarks/benchmark.py --n 20         # top 20 by cost rank
OpenVmBenchmarks/benchmark.py --n 10 --report report.html   # + interactive HTML report
```