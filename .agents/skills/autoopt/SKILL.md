---
name: autoopt
description: Improve apc-optimizer, the verified circuit optimizer.
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
lake exe apc-optimizer run Benchmarks/OpenVM/openvm-eth/apc_001_pc0x4ecc54.json.gz
lake exe apc-optimizer run Benchmarks/OpenVM/keccak/apc_001_pckeccak.json.gz
```

It reports before/after counts and three effectiveness factors — **variables**, **bus
interactions**, and **algebraic constraints** (each `before / after`; see `ApcOptimizer/Utils/Size.lean`).

**Priority: variable effectiveness > bus-interaction effectiveness > algebraic-constraint
effectiveness.** Optimize primarily for fewer distinct variables. When candidate passes are
otherwise comparable — or when a pass leaves the variable count unchanged — prefer the one that
removes more bus interactions, and then the one that removes more constraints. A pass that cuts
bus interactions or constraints without regressing variables is still an improvement worth
landing. Report all three factors in the log.

Optimization is slow; sampling a few cases per iteration might be fine. You can use the `*.powdr_opt.*` files for inspiration of new ideas that are possible. For the full picture, `Benchmarks/benchmark.py` runs `apc-optimizer compare` over all 100 cases in parallel (or `--n N` for the top N by cost; `--report out.html` for a
click-through comparison of the original / powdr / apc-optimizer circuits) and reports aggregate/geomean
effectiveness against powdr — this is the final evaluation. It runs the main `openvm-eth` benchmark
by default; a positional argument selects another set under `Benchmarks/<VM>/` (`--vm sp1` for SP1). Report the result
in the log.

## Rules

- **Do not change the audited surface** — `ApcOptimizer/Spec.lean`, `ApcOptimizer/OpenVmSemantics.lean`,
  `ApcOptimizer/MemoryBus.lean`, or the correctness theorems in `ApcOptimizer/Optimizer.lean`. All passes and
  the pipeline they compose into live under `ApcOptimizer/Implementation/`, which needs no audit.
- **No `sorry` / `admit` / `axiom` / `native_decide`** — enforced by CI
  (`Scripts/check-proof-integrity.sh`, runnable locally). If you cannot prove something, break it
  down or pick a simpler idea.
- **Every commit must `lake build`.**
- **Do not overfit.** Aim for a general algorithm. Do not do optimizations that only benefit a single test case. Also, the optimization should not be specific to the OpenVM semantics.

## How to add a pass

Write a `VerifiedPass` in a new `ApcOptimizer/Implementation/OptimizerPasses/` file, import it in
`ApcOptimizer/Implementation/Optimizer.lean`, and add one `(name, pass.….guardDegree)` entry to the
`cleanupPasses` list (the single pass-list both the optimizer and the profiler consume). See
`AGENTS.md` and `docs/design/architecture.md` for the architecture; correctness follows from the
pass's own `PassCorrect`.

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

## Idea guidelines

When generating ideas, consider the following:
- Think big: look for big improvements, don't get lost in ideas that improve a few test cases by a small amount.
- Beat powdr: There is no reason we should be less effective than powdr. Check out what powdr does and make sure we can do at least as well.
- Think from first principles: At the same time, don't just copy powdr. Think about what the spec allows and what is possible in general. We want the most optimal circuit optimizer possible.
- "Manually" optimize single test cases, detect patterns: Think hard about what kind of optimizations the Spec allows for on specific test cases and try to generalize what you found by optimizing manually.
- Prefer fewer, more general passes: Only add passes if you're adding a genuinely new optimization. If you can generalize or even combine existing passes, do that instead. That should help with maintainability and generalization.
