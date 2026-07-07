# Claude instructions

This repository is a Lean port of a circuit optimizer from
[powdr autoprecompiles](https://github.com/powdr-labs/powdr) (cf.
[`autoprecompiles/src/optimizer.rs`](https://github.com/powdr-labs/powdr/blob/main/autoprecompiles/src/optimizer.rs)).

The idea of this repository is that it is fully maintained by AI: As long as the agent does not change the correctness specification or benchmark, any PR that can demonstrate an increase in effectiveness can be merged without review.

## What a circuit is

Over a finite field, a circuit has **algebraic constraints** (expressions that must evaluate to
zero) and **bus interactions** (tuples sent to a global bus with a multiplicity; globally the bus
must balance). Buses are either **stateless lookups** (range/table checks — a chip sends with
multiplicity 0/1 and a table chip receives) or **stateful** (memory, execution bridge — they carry
state such as timestamp/PC). An optimization must **refine** the circuit: *sound* — every
satisfying assignment of the output maps to one of the input with the same effect on stateful
buses — and *complete for real traces* — every intended (real-trace) satisfying assignment of the
input is reproduced by the output. The precise relation is `refines` in `Leanr/Spec.lean`.

## Layout

The audited surface lives directly under `Leanr/`; everything under `Leanr/Implementation/` needs
no audit (its correctness is discharged by the theorems below and, for `BusFacts`, by
construction — a wrong fact would not compile), and `Leanr/Utils/` is tooling.

- `README.md` — A readme file for humans. Defines the auditing surface. Read it and any files mentioned there.
- `Leanr/Spec.lean` — the audited spec: `refines`, `optimizerMaintainsCorrectness`, the degree bound.
- `Leanr/OpenVmSemantics.lean`, `Leanr/MemoryBus.lean` — the audited OpenVM bus semantics and the
  memory-discipline utility they build on.
- `Leanr/Optimizer.lean` — the audited top: `optimizerWithBusFacts_maintainsCorrectness` (the
  master theorem, for all bus facts) plus its instances `simpleOptimizer_maintainsCorrectness` and the
  OpenVM `openVmOptimizer` (with `openVmOptimizer_maintainsCorrectness`).
- `Leanr/Implementation/OptimizerPasses/Basic.lean`, `FactPass.lean` — the framework: a `VerifiedPass` bundles its
  own `PassCorrect` proof, so a pass cannot be written without discharging it.
- `Leanr/Implementation/OptimizerPasses/*.lean` — one file per optimization pass.
- `Leanr/Implementation/Optimizer.lean` — assembles the passes into `optimizer` /
  `optimizerWithBusFacts` (`cleanupCycle`, `pipeline`).
- `Leanr/Implementation/BusFacts.lean`, `Leanr/Implementation/OpenVmFacts.lean` — the proven
  `BusFacts` (design + OpenVM instance); zero audit surface.
- `Leanr/Implementation/JsonParser.lean`, `Main.lean` — the powdr-export parser and the benchmark CLI (see
  `README.md`).
- `docs/design/architecture.md` — how the optimizer is built: the spec, the verified-pass
  framework, `BusFacts`, and the audited `admissible` predicate.

## Adding an optimization

Write a `VerifiedPass` in a new `Leanr/Implementation/OptimizerPasses/` file, import it in
`Leanr/Implementation/Optimizer.lean`, and `.andThen … |>.guardDegree` it into `cleanupCycle`. Do
not touch the audited surface (`Spec.lean`, `OpenVmSemantics.lean`, `MemoryBus.lean`,
`Leanr/Optimizer.lean`) or the glue in `Basic.lean`; correctness follows from the pass's own
`PassCorrect`. Build and verify with `lake build`.

When asked to improve the optimizer, use the `autoopt` skill.