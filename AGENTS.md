# Agent instructions

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
input is reproduced by the output. The precise relation is `refines` in `ApcOptimizer/Spec.lean`.

## Layout

The audited surface lives directly under `ApcOptimizer/`; everything under `ApcOptimizer/Implementation/` needs
no audit (its correctness is discharged by the theorems below and, for `BusFacts`, by
construction — a wrong fact would not compile), and `ApcOptimizer/Utils/` is tooling.

- `README.md` — A readme file for humans. Defines the auditing surface. Read it and any files mentioned there.
- `ApcOptimizer/Spec.lean` — the audited spec: `refines`, `optimizerMaintainsCorrectness`, the degree bound.
- `ApcOptimizer/OpenVmSemantics.lean`, `ApcOptimizer/MemoryBus.lean` — the audited OpenVM bus semantics and the
  memory-discipline utility they build on.
- `ApcOptimizer/Optimizer.lean` — the audited top: `optimizerWithBusFacts_maintainsCorrectness` (the
  master theorem, for all bus facts) plus its instances `simpleOptimizer_maintainsCorrectness` and the
  OpenVM `openVmOptimizer` (with `openVmOptimizer_maintainsCorrectness`).
- `ApcOptimizer/Implementation/OptimizerPasses/Basic.lean`, `FactPass.lean` — the framework: a `VerifiedPass` bundles its
  own `PassCorrect` proof, so a pass cannot be written without discharging it.
- `ApcOptimizer/Implementation/OptimizerPasses/*.lean` — one file per optimization pass.
- `ApcOptimizer/Implementation/Optimizer.lean` — assembles the passes into `optimizerWithBusFacts`.
  The pass sequence lives in three labelled lists — `preludePasses` (run once), `cleanupPasses`
  (iterated to a fixpoint), `codaPasses` (run once) — which are the single source of truth: both the
  optimizer (`pipeline` folds them) and the `profile` CLI command (`Main.lean`, which times them)
  consume the same lists, so they cannot drift apart. The cleanup cycle runs to a fixpoint via
  `iterateToFixpoint`, provably terminating on a lexicographic size measure, with no iteration count
  passed in.
- `ApcOptimizer/Implementation/BusFacts.lean`, `ApcOptimizer/Implementation/OpenVmFacts.lean` — the proven
  `BusFacts` (design + OpenVM instance); zero audit surface.
- `ApcOptimizer/Implementation/JsonParser.lean`, `Main.lean` — the powdr-export parser and the benchmark CLI (see
  `README.md`).
- `docs/design/architecture.md` — how the optimizer is built: the spec, the verified-pass
  framework, `BusFacts`, and the audited `admissible` predicate.

## Adding an optimization

Write a `VerifiedPass` in a new `ApcOptimizer/Implementation/OptimizerPasses/` file, import it in
`ApcOptimizer/Implementation/Optimizer.lean`, and add one `(name, pass.….guardDegree)` entry to the
`cleanupPasses` list. That is the only edit needed; the profiler picks up the new pass for free. Do
not touch the audited surface (`Spec.lean`, `OpenVmSemantics.lean`, `MemoryBus.lean`,
`ApcOptimizer/Optimizer.lean`) or the glue in `Basic.lean`; correctness follows from the pass's own
`PassCorrect`. Build and verify with `lake build`.

Effectiveness is measured along three axes (`ApcOptimizer/Utils/Size.lean`, reported by the CLI and the
benchmark), in priority order: **variable effectiveness > bus-interaction effectiveness >
algebraic-constraint effectiveness** (each is `count before / count after`). Optimize primarily
for fewer distinct variables; break ties, and pursue variable-neutral wins, by reducing bus
interactions and then constraints.

When asked to improve the optimizer, use the `autoopt` skill.

## Pushing work

- All commits have to compile without warnings.
- Changes should be committed in incremental commits if possible. Rebases are fine.
- The agent can always open a draft PR.
- Opening a PR triggers a CI run with benchmark results posted as a sticky comment. Agents may
  use this to run benchmarks (e.g. when they are on constrained environments).
- Agents should frequently check if there were any updates to main and rebase if needed, at least
  before they open / update a PR.
