# Architecture

How the verified optimizer is put together. The audited surface is listed in the
[README](../../README.md); this document is the rationale behind it and the map for extending the
optimizer.

Files directly under `Leanr/` are audited (the spec, the OpenVM semantics, the memory-bus utility,
and the correctness theorems in `Leanr/Optimizer.lean`); everything under `Leanr/Implementation/` —
the passes, the pipeline that assembles them, the proven `BusFacts`, and the JSON parser — needs no
audit, and `Leanr/Utils/` is tooling.

## The spec (`Leanr/Spec.lean`, audited)

A `ConstraintSystem` is a list of algebraic constraints plus a list of bus interactions over
`Expression`s. The correctness relation is **`refines`**, deliberately asymmetric:

- **soundness** — `output.implies input`: every satisfying assignment of the output maps to one of
  the input with the same stateful side effects. Required for *all* assignments (a malicious prover
  may use any of them).
- **completeness** — `input.impliesAdmissible output`: every *admissible* (real-trace) satisfying
  assignment of the input is reproduced by the output. Only required for admissible assignments,
  and it *delivers* an admissible witness, which is what makes `refines` transitive (so passes
  compose).

Side effects are the messages on **stateful** buses, compared up to **net multiplicity** per
message (`≈`) — so an identical-payload send/receive pair cancels. `admissible` is an abstract
per-VM predicate (`BusSemantics.admissible`) over the active stateful messages; it is where the
"this is a real trace" assumption lives (see [Bus knowledge](#bus-knowledge) and the README's
assumptions). `optimizerMaintainsCorrectness` bundles `refines`, preservation of
`guaranteesInvariants`, and staying within the VM's degree bound.

## The framework (`Leanr/Implementation/OptimizerPasses/Basic.lean`, `FactPass.lean`)

A **`VerifiedPass`** maps a system to a new one *bundled with a `PassCorrect` proof* (`refines` +
invariant preservation) — so a pass cannot be written without discharging its obligations.

- `andThen` composes passes (correctness by `refines_trans`); `iterate`/`iterateStable` run to a
  fixpoint; the top-level `optimizer_maintainsCorrectness` is just a projection.
- `guardDegree` wraps each pass to fall back to its input if the output would exceed the degree
  bound — degree safety is compositional, with zero per-pass proof burden.
- `VerifiedPassW` is a pass that may additionally consult proven `BusFacts` (below).

## Bus knowledge

The semantics exposes bus tables only through the opaque `violatesConstraint`. Two channels give
passes usable knowledge:

- **`BusFacts` (`Leanr/Implementation/BusFacts.lean`) — proven, zero audit surface.** Each field (`slotBound`,
  `slotFun`, `neverViolates`, `memShape`) carries a soundness proof against the semantics, so a
  wrong fact simply will not compile. `BusFacts.trivial` claims nothing and recovers fact-free
  behavior. Example: the XOR functional dependence of the bitwise bus, or byte bounds on its
  operands.
- **`admissible` / `Leanr/MemoryBus.lean` — audited assumption.** The last-write-wins memory
  discipline: `admissibleMemoryBus` states that a send followed by a same-address receive (with no
  active same-address message between, **in list order**) carry equal payloads. This is a
  completeness-only assumption about real traces — the input must list memory interactions in
  timestamp order (see the README's assumptions). It is consumed by `busUnifyPass` to cancel
  send/receive pairs and chain accesses across instructions.

## OpenVM instantiation

`openVmBusSemantics` (`Leanr/OpenVmSemantics.lean`, audited) provides `isStateful`,
`violatesConstraint` (per-bus tables: range checkers, bitwise/XOR, PC lookup), `breaksInvariant`,
`admissible`, and the degree bound. `openVmFacts` (`Leanr/Implementation/OpenVmFacts.lean`) is the
proven `BusFacts` instance. Both are parameterized by the bus map, defaulting to `defaultBusMap`.

## The pipeline (`Leanr/Implementation/Optimizer.lean`, theorems in `Leanr/Optimizer.lean`)

`cleanupCycle` chains the passes — Gauss elimination, normalize, constant-fold, finite-domain
propagation (boolean/one-hot case analysis and bus-fact domains; prime `p` only), trivial /
zero-multiplicity / tautology drops, `busUnifyPass`, and re-encoding — each `guardDegree`-wrapped.
`pipelineIters` folds once, runs `cleanupCycle` to a fixpoint (`iterateStable`), then
monic-scales and folds. `optimizerWithBusFacts` takes a proven `BusFacts` instance; `optimizer` is
the trivial-facts instance (`BusFacts.trivial`). The audited `Leanr/Optimizer.lean` proves the
master theorem `optimizerWithBusFacts_maintainsCorrectness` (correctness for *every* choice of
facts) and derives its instances `optimizer_maintainsCorrectness` and the OpenVM `openVmOptimizer`
(with `openVmOptimizer_maintainsCorrectness`).

## Adding a pass

Write a `VerifiedPass` (or `VerifiedPassW`) in a new `Leanr/Implementation/OptimizerPasses/` file,
import it in `Leanr/Implementation/Optimizer.lean`, and `.andThen … |>.guardDegree` it into
`cleanupCycle`. Correctness follows from the pass's own `PassCorrect`; do not touch `Spec.lean`,
the audited `Leanr/Optimizer.lean`, or the `Basic.lean` glue. Build with `lake build`.
