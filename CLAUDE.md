# Claude instructions

This repository is a Lean port of a circuit optimizer from
[powdr autoprecompiles](https://github.com/powdr-labs/powdr) (cf.
[`autoprecompiles/src/optimizer.rs`](https://github.com/powdr-labs/powdr/blob/main/autoprecompiles/src/optimizer.rs)).

## What a circuit is

Over a finite field, a circuit has **algebraic constraints** (expressions that must evaluate to
zero) and **bus interactions** (tuples sent to a global bus with a multiplicity; globally the bus
must balance). Buses are either **stateless lookups** (range/table checks — a chip sends with
multiplicity 0/1 and a table chip receives) or **stateful** (memory, execution bridge — they carry
state such as timestamp/PC). Two circuits are **equivalent** when each implies the other's
satisfiability *and* they have the same effect on stateful buses; an optimization must preserve
this.

## Vision

The optimizer should be AI-maintainable:

1. Specify circuit equivalence in Lean (the spec).
2. Specify circuit size.
3. Prove every optimization preserves the spec (starting from the trivial do-nothing optimizer).
4. Auto-merge PRs that keep the spec, still build, and reduce size on test cases.

## Layout

- `README.md` — A readme file for humans. Defines the auditing surface. Read it and any files mentioned there.
- `Leanr/OptimizerPasses/Basic.lean`, `FactPass.lean` — the framework: a `VerifiedPass` bundles its
  own `PassCorrect` proof, so a pass cannot be written without discharging it.
- `Leanr/OptimizerPasses/*.lean` — one file per optimization pass.
- `Leanr/Optimizer.lean` — assembles the passes into `optimizer` (`cleanupCycle`), with the
  top-level `optimizer_maintainsCorrectness`.
- `Leanr/JsonParser.lean`, `Main.lean` — the powdr-export parser and the benchmark CLI (see
  `README.md`).
- `docs/design/bus-knowledge.md` — design rationale for the bus-knowledge architecture (proven
  `BusFacts` + the audited `admissible` predicate).

## Adding an optimization

Write a `VerifiedPass` in a new `Leanr/OptimizerPasses/` file, import it in `Leanr/Optimizer.lean`,
and `.andThen … |>.guardDegree` it into `cleanupCycle`. Do not touch `Spec.lean` or the glue in
`Basic.lean`; correctness follows from the pass's own `PassCorrect`. Build and verify with
`lake build`.