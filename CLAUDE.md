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

- `README.md` — A readme file for humans. Defines the auditing surface. Read it and any files mentioned there.
- `Leanr/OptimizerPasses/Basic.lean`, `FactPass.lean` — the framework: a `VerifiedPass` bundles its
  own `PassCorrect` proof, so a pass cannot be written without discharging it.
- `Leanr/OptimizerPasses/*.lean` — one file per optimization pass.
- `Leanr/Optimizer.lean` — assembles the passes into `optimizer` (`cleanupCycle`), with the
  top-level `optimizer_maintainsCorrectness`.
- `Leanr/JsonParser.lean`, `Main.lean` — the powdr-export parser and the benchmark CLI (see
  `README.md`).
- `docs/design/architecture.md` — how the optimizer is built: the spec, the verified-pass
  framework, `BusFacts`, and the audited `admissible` predicate.

## Adding an optimization

Write a `VerifiedPass` in a new `Leanr/OptimizerPasses/` file, import it in `Leanr/Optimizer.lean`,
and `.andThen … |>.guardDegree` it into `cleanupCycle`. Do not touch `Spec.lean` or the glue in
`Basic.lean`; correctness follows from the pass's own `PassCorrect`. Build and verify with
`lake build`.

When asked to improve the optimizer, use the `autoopt` skill.