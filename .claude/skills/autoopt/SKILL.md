---
name: autoopt
description: Improve the leanr circuit optimizer — add a verified optimization pass, measure
  effectiveness on the benchmark set, keep the correctness proof intact, and log the result.
  Use when asked to make the optimizer more effective or to run an autoopt iteration.
---

# Improve the circuit optimizer

Maximize effectiveness (circuit-size reduction) on the benchmark set while keeping the optimizer
provably correct. At every commit the optimizer must have a correctness proof and `lake build`
must pass.

## Context

This is a recurring loop — skim the current architecture in `docs/design/architecture.md`, the
recent `docs/log.md` entries (`tail -100 docs/log.md`; earlier ones describe superseded designs),
and recent commits to see what has already been tried. Run a case with, e.g.:

```
lake exe leanr run OpenVmBenchmark/data/apc_001_pc0x4ecc54.json.gz
```

It reports vars/constraints/bus-interactions before/after and effectiveness (vars before / after).
Optimization is slow; sampling a few of the 100 cases per iteration is fine. You can use the `*.powdr_opt.*` files for inspiration of new ideas that are possible. For the full picture, `OpenVmBenchmark/benchmark.py` runs `leanr
compare` over all 100 cases in parallel (or `--n N` for the top N by cost; `--report out.html` for a
click-through comparison of the original / powdr / leanr circuits) and reports aggregate/geomean
effectiveness against powdr — this is the final evaluation. Report the result in the log.

## Rules

- **Do not change the audited surface** — `Leanr/Spec.lean`, `Leanr/OpenVM/Semantics.lean`, or
  `Leanr/MemoryBus.lean`.
- **No `sorry` / `admit` / `axiom` / `native_decide`** — enforced by CI
  (`Scripts/check-proof-integrity.sh`, runnable locally). If you cannot prove something, break it
  down or pick a simpler idea.
- **Every commit must `lake build`.**
- **Do not overfit.** Aim for a general algorithm that also works on a different VM with different
  bus semantics — not a transformation tuned to one circuit.

## How to add a pass

Write a `VerifiedPass` in a new `Leanr/OptimizerPasses/` file, import it in `Leanr/Optimizer.lean`,
and `.andThen … |>.guardDegree` it into `cleanupCycle`. See `CLAUDE.md` and
`docs/design/architecture.md` for the architecture; correctness follows from the pass's own
`PassCorrect`.

## Log

Append to `docs/log.md` on each commit: the idea, whether it worked, and the impact (which benchmark,
how effectiveness changed). Append-only.

## Ideas file

In each run, read and update `docs/ideas.md` with ideas for future passes. Whenever you come across an idea that doesn't fit in the current session, add it there. Remove implemented ideas.

## Looping

For one autoopt iteration go through the following steps (using different subagents):
- **Brainstorming**:
  - Read the log and ideas file.
  - Sample a few test cases from the benchmark, look at the current output of the optimizer and think if you can come up with a more efficient one for this specific circuit.
  - If you have several ideas, add them to the ideas file.
  - Out of all the ideas, pick the most promising one and proceed.
- **Implementation**: Implement the idea and measure the increase in effectiveness.
- **Evaluation**: If you succeed (= your optimization improves the benchmark + you can prove correctness), commit your changes and append to the log. If you fail, discard your changes and append to the log. Make sure the ideas does not contain ideas that have been implemented or are known to be impossible.
