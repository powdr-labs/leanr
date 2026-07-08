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
assumptions). `optimizerMaintainsCorrectness bs opt` bundles `refines`, preservation of
`guaranteesInvariants`, and staying within the VM's degree bound — for a *given* bus semantics
`bs` (quantify over `bs` for the "correct for every semantics" reading; fixing it lets a
semantics-specific optimizer be an instance).

## The framework (`Leanr/Implementation/OptimizerPasses/Basic.lean`, `FactPass.lean`)

A **`VerifiedPass`** maps a system to a new one *bundled with a `PassCorrect` proof* (`refines` +
invariant preservation) — so a pass cannot be written without discharging its obligations.

- `andThen` composes passes (correctness by `refines_trans`); `iterate`/`iterateStable` run to a
  fixpoint; the top-level `*_maintainsCorrectness` theorems are just projections.
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
monic-scales and folds. Applied to proven facts and an iteration bound, `optimizerWithBusFacts` is
a circuit-to-circuit map; `simpleOptimizer` is the trivial-facts instance (`BusFacts.trivial`). The
audited `Leanr/Optimizer.lean` proves the master theorem
`optimizerWithBusFacts_maintainsCorrectness` (correctness for *every* bus semantics, choice of
proven facts, and iteration count) and derives its instances `simpleOptimizer_maintainsCorrectness`
and the OpenVM `openVmOptimizer` (with
`openVmOptimizer_maintainsCorrectness`) as one-liners.

## Derived columns (witgen hints)

`ConstraintSystem` carries a `derivedColumns : List (DerivedVariable p)` field (defaulted to `[]`),
mirroring powdr's `SymbolicMachine.derived_columns`. A `DerivedVariable` is `{ isNew, name,
computation }`, and a `ComputationMethod` is `constant` / `quotientOrZero` (field-inverse quotient,
`0` on a zero divisor) / `ifEqZero` — reproducing powdr's `ComputationMethod` and its witgen
evaluator. These are **witness-generation hints, not constraints**: they are not checked by the
verifier and are deliberately kept out of `satisfies`/`refines`/`withinDegree`, all of which read
only `algebraicConstraints`/`busInteractions`. Consequently every existing pass proof is unaffected.

- **Correctness lives in `refines`.** `impliesAdmissible` (the completeness direction) now
  *assumes* `self.derivedConsistent env` and *delivers* a witness `env'` with
  `other.derivedConsistent env'`. This assume/deliver symmetry is what keeps the relation reflexive
  (`env' = env` re-delivers the assumption) and transitive (the middle witness carries the
  hypothesis the next step needs), so all pass composition (`refines_trans`) is unchanged. Soundness
  (`implies`) is deliberately left untouched: an adversarial output-satisfying assignment cannot be
  made hint-consistent, nor needs to be — hints are witgen instructions, not verifier constraints.
  `optimizerMaintainsCorrectness`'s fourth clause, `optimizerDerivedColumnsConsistent`, is the
  projection: for every admissible, satisfying, hint-consistent input there is an output-satisfying
  `env'` under which every emitted hint computes its assigned value.
- **Why this and not env-universal entailment.** `derivedColumnsEntailed` (every satisfying
  assignment makes the hints consistent) is kept as documentation but is *not* the guarantee: it
  fails for hints of *eliminated* variables, which are free in the output, so no output constraint
  pins them. Consistency under the *constructed completeness witness* is the right, provable notion —
  and is exactly what witgen needs (following the hints on a real trace yields a consistent
  assignment).
- **Emission.** The re-encoding pass (`Reencode.lean`) emits an `isNew = false` hint
  `QuotientOrZero(interpolation-over-fresh-bits, 1)` (= powdr's `ComputationMethod::expression`) for
  each group variable it eliminates, accumulating onto any hints already present. Its freshness
  certificate (`checkReencode`) requires the fresh bits to avoid the eliminated group vars and every
  existing derived column (name + computation), so accumulated hints transport across each step. The
  emitted-hint consistency is discharged from the pass's own forward witness.
- **Preservation.** Every *non-emitting* pass preserves derived columns unchanged. Because each
  such pass's completeness witness is `env' = env`, consistency transfers for free (the pass reuses
  its `derivedConsistent` hypothesis). This lets the emitting re-encoding pass stay inside the
  iterated cleanup cycle — so effectiveness (variables/bus/constraints) is byte-identical to the
  hint-free pipeline — while its hints survive verbatim to the optimizer output.
- **Serialization.** Parsing (`JsonParser.lean`) and serialization (`JsonSerializer.lean`) match
  powdr's serde exactly (3-tuple `[is_new, "name@id", method]`, externally-tagged `ComputationMethod`,
  field elements as bare numbers); a missing `derived_columns` key parses to `[]`.
- **Deferred.** Re-encoding does *not* yet emit `isNew = true` hints for the fresh bit columns it
  creates (witgen must compute those): the bit value is a function of the eliminated group values,
  expressible only via Lagrange interpolation over the non-boolean group-value domains (the existing
  `indicatorExpr` machinery is boolean-only) — a substantial addition left for later. Parser-provided
  *input* hints are dropped by substitution passes rather than rewritten under substitution (the
  benchmark inputs carry none); rewriting them is future work.

## Adding a pass

Write a `VerifiedPass` (or `VerifiedPassW`) in a new `Leanr/Implementation/OptimizerPasses/` file,
import it in `Leanr/Implementation/Optimizer.lean`, and `.andThen … |>.guardDegree` it into
`cleanupCycle`. Correctness follows from the pass's own `PassCorrect`; do not touch `Spec.lean`,
the audited `Leanr/Optimizer.lean`, or the `Basic.lean` glue. Build with `lake build`.
