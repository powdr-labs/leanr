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
- `ApcOptimizer/OpenVmSemantics.lean`, `ApcOptimizer/Sp1Semantics.lean`, `ApcOptimizer/MemoryBus.lean` — the audited
  OpenVM and SP1 bus semantics and the memory-discipline utility they build on. Auditing a VM's semantics is
  only needed if you use that VM; `MemoryBus.lean` (shared) carries the `direction`-parameterized memory discipline.
- `ApcOptimizer/Optimizer.lean` — the audited top: `optimizerWithBusFacts_maintainsCorrectness` (the
  master theorem, for all bus facts) plus its instances `simpleOptimizer_maintainsCorrectness`, the
  OpenVM `openVmOptimizer` (`openVmOptimizer_maintainsCorrectness`) and the SP1 `sp1Optimizer`
  (`sp1Optimizer_maintainsCorrectness`).
- `ApcOptimizer/Implementation/OptimizerPasses/Basic.lean`, `Pass.lean`, `FactPass.lean` — the framework: a
  pass bundles its own correctness proof, so a pass cannot be written without discharging it.
- `ApcOptimizer/Implementation/OptimizerPasses/*.lean` — one file per optimization pass (runtime
  definitions); its correctness proof and the wired pass live in the matching
  `OptimizerPasses/Proofs/*.lean` file.
- `ApcOptimizer/Implementation/Optimizer.lean` — assembles the passes into `optimizerWithBusFacts`.
  The pass sequence lives in three labelled lists — `preludePasses` (run once), `cleanupPasses`
  (iterated to a fixpoint), `codaPasses` (run once) — which are the single source of truth: both the
  optimizer (`pipeline` folds them) and the `profile` CLI command (`Main.lean`, which times them)
  consume the same lists, so they cannot drift apart. The cleanup cycle runs to a fixpoint via
  `iterateToFixpoint`, provably terminating on a lexicographic size measure, with no iteration count
  passed in.
- `ApcOptimizer/Implementation/BusFacts.lean`, `ApcOptimizer/Implementation/OpenVmFacts.lean`,
  `ApcOptimizer/Implementation/Sp1Facts.lean` — the proven `BusFacts` (design + OpenVM and SP1 instances);
  zero audit surface.
- `ApcOptimizer/Implementation/JsonParser.lean`, `Main.lean` — the powdr-export parser and the benchmark CLI (see
  `README.md`).
- `docs/design/architecture.md` — how the optimizer is built: the spec, the verified-pass
  framework, `BusFacts`, and the audited `admissible` predicate.

## Adding an optimization

Write a dense pass — a `DenseVerifiedPassW`, which bundles its own `DensePassCorrect` proof —
with its runtime definitions in a new `ApcOptimizer/Implementation/OptimizerPasses/` file and its
proof plus the wired pass in a matching `OptimizerPasses/Proofs/` file, import the latter in
`ApcOptimizer/Implementation/Optimizer.lean`, and add one `(name, pass)` entry to
the `cleanupPasses` list (the list applies the degree guard to every entry itself). Build the pass with `DenseVerifiedPassW.of` (registry unchanged) or, for
passes that mint fresh variables, `DenseVerifiedPassW.ofExtending`; see the worked examples
`Proofs/Gauss.lean`, `Proofs/DropPasses.lean`, `Proofs/CarryBranch.lean` / `Proofs/RangeBool.lean` and
`Proofs/Reencode.lean`. That one list entry is the only edit needed; the profiler picks up the new
pass for free. Do not touch the audited surface (`Spec.lean`, `OpenVmSemantics.lean`,
`Sp1Semantics.lean`, `MemoryBus.lean`, `ApcOptimizer/Optimizer.lean`) or the glue in `Basic.lean`;
correctness follows from the pass's own bundled proof. Build and verify with `lake build`.

Effectiveness is measured along three axes (`ApcOptimizer/Utils/Size.lean`, reported by the CLI and the
benchmark), in priority order: **variable effectiveness > bus-interaction effectiveness >
algebraic-constraint effectiveness** (each is `count before / count after`). Optimize primarily
for fewer distinct variables; break ties, and pursue variable-neutral wins, by reducing bus
interactions and then constraints.

When asked to improve the optimizer, use the `autoopt` skill.

## Comments

Comments under `ApcOptimizer/Implementation/` are read by agents, not auditors, and agents can
infer most things from the code — so keep them minimal and let the code speak:

- **Describe only the current state.** A comment is not a changelog: never narrate history or a
  change ("used to be X, now Y", "previously", "renamed from", "now also handles…").
- **Leave self-explanatory code uncommented.** If the code is easy to follow, don't comment it.
- **Reserve comments for non-obvious, important context** — an invariant, a subtle gate, why an
  ordering matters — never a restatement of what the next line plainly does.
- **Prefer references over prose.** Point to the relevant definition/theorem/file (e.g. "soundness
  in `Proofs/Gauss.lean`") instead of re-explaining it.
- **Every optimization pass keeps one concise human-readable comment** on its entry point saying
  what it does, ideally with a tiny example (e.g. "for a constraint like `x = 5`, infers the
  assignment `x := 5`").

Keep the implementation lean; don't let comments regrow.

## Pushing work

- All commits have to compile without warnings.
- Changes should be committed in incremental commits if possible. Rebases are fine.
- The agent can always open a draft PR.
- Opening a PR triggers a CI run with benchmark results posted as a sticky comment. Agents may
  use this to run benchmarks (e.g. when they are on constrained environments).
- Agents should frequently check if there were any updates to main and rebase if needed, at least
  before they open / update a PR.
