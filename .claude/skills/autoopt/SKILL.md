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

This is a recurring loop — read `log.md` and recent commits first to see what has already been
tried. Run a case with, e.g.:

```
lake exe leanr run Leanr/OpenVM/Benchmark/apc_001_pc3647036.json.gz
```

It reports vars/constraints/bus-interactions before/after and effectiveness (vars before / after).
Optimization is slow; sampling a few of the 100 cases per iteration is fine. Ignore the
`*.powdr_opt.*` files. For the full picture, `Leanr/OpenVM/Benchmark/benchmark.py` runs `leanr
compare` over all 100 cases in parallel (or `--n N` for the top N by cost; `--report out.html` for a
click-through comparison of the original / powdr / leanr circuits) and reports aggregate/geomean
effectiveness against powdr — this is the final evaluation.

## Rules

- **Do not change the spec** — `Leanr/Spec.lean`, the bus semantics, or the snapshot test.
- **No `sorry` / `admit` / `axiom` / `native_decide`.** Before every commit run
  `grep -rn "sorry\|admit\|axiom\|native_decide" Leanr/`. If you cannot prove something, break it
  down or pick a simpler idea.
- **Every commit must `lake build`.**
- **Do not overfit.** Aim for a general algorithm that also works on a different VM with different
  bus semantics — not a transformation tuned to one circuit.

## How to add a pass

Write a `VerifiedPass` in a new `Leanr/OptimizerPasses/` file, import it in `Leanr/Optimizer.lean`,
and `.andThen … |>.guardDegree` it into `cleanupCycle`. See `CLAUDE.md` and
`docs/design/bus-knowledge.md` for the architecture; correctness follows from the pass's own
`PassCorrect`.

## Log

Append to `log.md` on each commit: the idea, whether it worked, and the impact (which benchmark,
how effectiveness changed). Append-only.

## Looping

For a sustained run, invoke this repeatedly — e.g. `/loop /autoopt`.
