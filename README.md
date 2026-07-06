# Leanr: A Verified Constraint System Optimizer

Leanr is a verified constraint system optimizer, designed to be a drop-in replacement for the [`powdr_autoprecompiles::optimizer::optimize`](https://github.com/powdr-labs/powdr/blob/5395a66442c82abc3c095d758f170773c4b5857d/autoprecompiles/src/optimizer.rs#L31-L41) function. It comes with a proof of correctness, meaning that the optimizer is *proven to maintain a notion of circuit equivalence*.

## Auditing

Leanr is designed to have a small auditing surface. To audit Leanr, it should be sufficient to review:
1. [`Leanr/Spec.lean`](./Leanr/Spec.lean): Defining the notion of circuit equivalence and optimizer correctness.
2. [`Leanr/OpenVM/Semantics.lean`](./Leanr/OpenVM/Semantics.lean): The OpenVM-specific semantics. These are needed for our OpenVM-specific optimizations. If you are instead interested in a different VM, you can skip this file, but must provide semantics for your VM in order to use Leanr.
3. [`Leanr/MemoryBus.lean`](./Leanr/MemoryBus.lean): Utility used in the OpenVM semantics above (and likely useful for other VMs as well).
4. The `optimizer_maintainsCorrectness` theorem in [`Leanr/Optimizer.lean`](./Leanr/Optimizer.lean): Audit the statement and check that the proof is correct by running `lake build`.