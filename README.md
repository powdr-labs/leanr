# Leanr: A Verified Constraint System Optimizer

Leanr is a verified constraint system optimizer, designed to be a drop-in replacement for the [`powdr_autoprecompiles::optimizer::optimize`](https://github.com/powdr-labs/powdr/blob/5395a66442c82abc3c095d758f170773c4b5857d/autoprecompiles/src/optimizer.rs#L31-L41) function. It comes with a proof of correctness, meaning that the optimizer is *proven to maintain a notion of circuit equivalence*.

## Auditing Correctness

Leanr is designed to have a small auditing surface. To audit Leanr, it should be sufficient to review:
1. [`Leanr/Spec.lean`](./Leanr/Spec.lean): Defining the notion of circuit equivalence and optimizer correctness.
2. [`Leanr/OpenVM/Semantics.lean`](./Leanr/OpenVM/Semantics.lean): The OpenVM-specific semantics. These are needed for our OpenVM-specific optimizations. If you are instead interested in a different VM, you can skip this file, but must provide semantics for your VM in order to use Leanr.
3. [`Leanr/MemoryBus.lean`](./Leanr/MemoryBus.lean): Utility used in the OpenVM semantics above (and likely useful for other VMs as well).
4. The `optimizer_maintainsCorrectness` theorem in [`Leanr/Optimizer.lean`](./Leanr/Optimizer.lean): Audit the statement and check that the proof is correct by running `lake build`.

### Assumptions (OpenVM)

The theorem is proven against the spec and the OpenVM semantics above. For the guarantee to carry over to a real OpenVM circuit, the auditor must also accept these assumptions about the *input* circuits — none are checked at runtime:

- **Memory and execution-bridge interactions are listed in timestamp order.** The `admissible` predicate pairs each send with the next same-address receive *in list order* (see [`Leanr/MemoryBus.lean`](./Leanr/MemoryBus.lean)), so the exporter must emit these interactions in time order. This only affects completeness: a wrong order can make the optimizer keep a variable it could have removed, never make the output unsound.
- **The input guarantees invariants and respects the degree bound.** The optimizer *preserves* `guaranteesInvariants` and `withinDegree`, but only assuming the input has them (e.g. that written memory limbs are byte-range-checked). Confirm this for the circuits you feed it.
- **PC lookups are pinned.** [`Semantics.lean`](./Leanr/OpenVM/Semantics.lean) checks only the arity of a PC lookup, not the program table. This is sound because the input pins every PC-lookup field to a constant and the optimizer never introduces new ones.
- **Refinement is per constraint system.** Correctness is proven for one chip; substituting it into the full VM relies on the usual bus-balance argument (stateless tables accept any valid entry; stateful buses' net effect is preserved), which is outside this development.

## Usage

The `leanr` executable runs the optimizer on powdr `SymbolicMachine` exports (`ApcWithBusMap` JSON, plain or gzipped) and reports effectiveness — distinct variables before / after:

```bash
lake build

# Optimize one case and report effectiveness
lake exe leanr run [--iters N] OpenVmBenchmark/data/apc_001_pc0x4ecc54.json.gz

# powdr's own effectiveness, from its serialized optimizer output
lake exe leanr powdr <unopt>.json.gz <unopt>.powdr_opt.json.gz

# Both, side by side
lake exe leanr compare [--iters N] <unopt>.json.gz <unopt>.powdr_opt.json.gz
```

`--iters` caps the optimizer's cleanup-cycle loop (default 32). The loop runs the cleanup cycle to a fixpoint and stops as soon as a cycle changes nothing, so `--iters` is only an upper bound, not a fixed count — in practice even the largest benchmark case (≈9.5k variables) converges well within 32 cycles, so raising it does not change the result. The top-100 openvm-eth benchmark set lives in [`OpenVmBenchmark/`](./OpenVmBenchmark/) (see its README).

## Benchmark

As the main benchmark, we use the 100 costliest basic blocks in [openvm-eth](https://github.com/powdr-labs/openvm-eth), a guest program verifying Ethereum blocks. For details, see [`OpenVmBenchmark/README.md`](./OpenVmBenchmark/README.md).

To sweep the whole set in parallel and report aggregate leanr-vs-powdr effectiveness:

```bash
OpenVmBenchmark/benchmark.py                # all cases (--iters 32, --jobs = cores)
OpenVmBenchmark/benchmark.py --n 20         # top 20 by cost rank
OpenVmBenchmark/benchmark.py --n 10 --report report.html   # + interactive HTML report
```