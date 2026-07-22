# Architecture

How the verified optimizer is put together. The audited surface is listed in the
[README](../../README.md); this document is the rationale behind it and the map for extending the
optimizer.

Files directly under `ApcOptimizer/` are audited (the spec, the OpenVM semantics, the memory-bus utility,
and the correctness theorems in `ApcOptimizer/Optimizer.lean`); everything under `ApcOptimizer/Implementation/` —
the passes, the pipeline that assembles them, the proven `BusFacts`, and the JSON parser — needs no
audit, and `ApcOptimizer/Utils/` is tooling.

## The spec (`ApcOptimizer/Spec.lean`, audited)

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
assumptions).

**Derived variables.** The optimizer returns not just a circuit but a `Derivations` list — a
`ComputationMethod` (powdr's `Constant`/`QuotientOrZero`/`IfEqZero`, with an `eval`) for each
variable it introduces. The completeness direction (folded into `refines` / `impliesAdmissible`) is
strengthened accordingly: the reproduced witness must **`derivesWitness`** — every variable of the
output that carries a powdr ID is an input column present in the input with an unchanged value, and
every no-ID (derived) variable is computed by the method `Derivations` lists for it (`methodFor`,
its last entry — duplicates are allowed, the later one wins) reading only input columns. This is
exactly what lets witness generation extend an input trace to an output trace. (The requirement is
only demanded when the input's columns all carry powdr IDs — the intended shape of an exported
circuit; a variable with no powdr ID cannot be read from the input trace.)

`optimizerMaintainsCorrectness bs opt` bundles `refines`, preservation of
`guaranteesInvariants`, and staying within the VM's degree bound — for a *given* bus semantics
`bs` (quantify over `bs` for the "correct for every semantics" reading; fixing it lets a
semantics-specific optimizer be an instance).

## The framework (`ApcOptimizer/Implementation/OptimizerPasses/Basic.lean`, `Pass.lean`, `FactPass.lean`)

A **`DenseVerifiedPassW`** (`Pass.lean`) maps a registry + dense system to a new one *bundled with
a `PassCorrect` proof on the decode* (`refines` + invariant preservation) — so a pass cannot be
written without discharging its obligations. `Basic.lean` carries the `Variable`-level relation
glue (`PassCorrect` itself and its composition lemmas) that the dense results decode into.

- `andThen` composes passes (correctness by composing the per-pass `PassCorrect` proofs, with
  derivations concatenating); `denseIterateToFixpoint` runs a pass to a fixpoint, proven to
  terminate on the well-founded lexicographic size key (see the pipeline section); the top-level
  `*_maintainsCorrectness` theorems are just projections.
- `guardDegree` falls back to a pass's input if the output would exceed the degree bound; the
  pipeline's `guardAll` applies it to every stage-list entry, so degree safety is uniform with
  zero per-pass proof burden.
- `VerifiedPassW` (`FactPass.lean`) is the `Variable`-level pass type that may additionally
  consult proven `BusFacts` (below); the pipeline is its one inhabitant, wrapping the dense
  pipeline between one encode and one decode.

## Bus knowledge

The semantics exposes bus tables only through the opaque `violatesConstraint`. Two channels give
passes usable knowledge:

- **`BusFacts` (`ApcOptimizer/Implementation/BusFacts.lean`) — proven, zero audit surface.** Each field (`slotBound`,
  `slotFun`, `neverViolates`, `recvByteSlots`, `byteXorSpec`, `memShape`) carries a soundness proof
  against the semantics, so a wrong fact simply will not compile. `BusFacts.trivial` claims nothing
  and recovers fact-free behavior. Examples: the XOR functional dependence of the bitwise bus,
  byte bounds on its operands, or the byte bounds on the data limbs of a memory *receive*
  (`slotBound` is multiplicity-aware for exactly this). The byte-check and XOR passes consume the
  **VM-neutral** `byteXorSpec` descriptor — a layout-generic `(op, o₁, o₂, r)` decode/encode plus
  its `xorOp`/`pairOp` acceptance semantics — rather than any OpenVM-shaped payload, so the same
  passes fire on both the OpenVM bitwise-lookup bus and the SP1 byte-lookup bus.
- **`admissible` / `ApcOptimizer/MemoryBus.lean` — audited assumption.** The memory discipline:
  `admissibleMemoryBus` states that a `setNew` followed by a same-address `getPrevious` (with no
  active same-address message between, **in list order**) carry equal payloads. The `setNew`/`getPrevious`
  multiplicities are chosen per bus by `MemoryBusShape.direction` (via `setNewMult`) — `1`/`-1` for
  OpenVM (which sends the new record and receives the previous one), `-1`/`1` for SP1 (which sends the
  previous record and receives the new one). This is a completeness-only assumption about real traces —
  the input must list memory interactions in timestamp order (see the README's assumptions). It is
  consumed by `busUnifyPass` to cancel send/receive pairs and chain accesses across instructions.

## OpenVM instantiation

`openVmBusSemantics` (`ApcOptimizer/OpenVmSemantics.lean`, audited) provides `isStateful`,
`violatesConstraint` (per-bus tables: range checkers, bitwise/XOR, PC lookup), `breaksInvariant`,
`admissible`, and the degree bound. `openVmFacts` (`ApcOptimizer/Implementation/OpenVmFacts.lean`) is the
proven `BusFacts` instance. Both are parameterized by the bus map, defaulting to `defaultBusMap`.

## SP1 instantiation

`sp1BusSemantics` (`ApcOptimizer/Sp1Semantics.lean`, audited) is the analogous KoalaBear-field
instance: `isStateful`, `violatesConstraint` (the byte bus — AND/OR/XOR/U8Range/LTU/MSB/Range — plus
the 16-bit memory discipline and lookup arities), `breaksInvariant`, `admissible`, and SP1's degree
bound. SP1 sends the previous record and receives the new one, so its memory shapes carry
`direction := .sendThenReceive` (`setNewMult = -1`). `sp1Facts` (`ApcOptimizer/Implementation/Sp1Facts.lean`) is the
proven `BusFacts` instance: the execution bridge never violating, the x0 zero-cell, byte-operand slot
bounds, the byte-XOR functional dependence, the memory-unification discipline (`memShape` +
`admissible_sound`/`admissible_dropPair`), and the pair-cancellation `recvByteSlots` — carrying SP1's
16-bit (`2^16`) obligation on the memory data limbs via the VM-declared byte-slot bound.

## The pipeline (`ApcOptimizer/Implementation/Optimizer.lean`, theorems in `ApcOptimizer/Optimizer.lean`)

The pass sequence lives in three labelled lists — the **single source of truth**: `preludePasses`
(a constant-fold) run once, `cleanupPasses` iterated to a fixpoint, and `codaPasses`
(redundant-byte-drop, monic-scale, constant-fold) run once. `cleanupPasses` chains the passes —
Gauss elimination, normalize, constant-fold, finite-domain propagation (boolean/one-hot case
analysis and bus-fact domains; prime `p` only), trivial / zero-multiplicity / tautology drops,
`busUnifyPass`, and re-encoding — wrapped in the degree guard by `guardAll`. `pipeline` folds `preludePasses`, runs
the folded `cleanupPasses` cycle to a fixpoint (`denseIterateToFixpoint`), then folds `codaPasses`. The
`profile` CLI command (`Main.lean`) times those same three lists (stepping the passes in `IO`, which
the pure `pipeline` can't do), so the profiler cannot drift out of sync with the optimizer as passes
are added, removed, or reordered. The loop takes **no** iteration bound: it recurses while each cycle strictly lowers the
lexicographic size key `sizeKey = (distinct vars, bus interactions, constraints)` (variables most
significant, matching the effectiveness priority) and stops otherwise. That key is well-founded
(`sizeKey_wf`, the inverse image of `<` on `Nat ×ₗ Nat ×ₗ Nat`), so the loop is proven to terminate
with no cap a large basic block could exceed — the recursion is guarded by exactly the strict
decrease `decreasing_by` needs. Two free corollaries: the loop is size-monotone by construction
(`denseIterateToFixpoint_monotone` — the optimizer can only shrink the circuit), and correctness is the
usual `PassCorrect` composition (each kept cycle refines; stopping returns the input). Applied to
proven facts, `optimizerWithBusFacts` is a
circuit-to-circuit map; `simpleOptimizer` is the trivial-facts instance (`BusFacts.trivial`). The
audited `ApcOptimizer/Optimizer.lean` proves the master theorem
`optimizerWithBusFacts_maintainsCorrectness` (correctness for *every* bus semantics and choice of
proven facts) and derives its instances `simpleOptimizer_maintainsCorrectness`
and the OpenVM `openVmOptimizer` (with
`openVmOptimizer_maintainsCorrectness`) as one-liners.

## Adding a pass

Write a dense `DenseVerifiedPassW` — bundling its own `DensePassCorrect` proof — with runtime
definitions in a new `ApcOptimizer/Implementation/OptimizerPasses/` file and the proof plus wired
pass in a matching `OptimizerPasses/Proofs/` file, import the latter in
`ApcOptimizer/Implementation/Optimizer.lean`, and add one `(name, pass)` entry to the
`cleanupPasses` list (`guardAll` degree-guards every entry, so no per-pass guard is written). Build it with `DenseVerifiedPassW.of`, or `DenseVerifiedPassW.ofExtending` for
passes that mint fresh variables. Two common shapes skip the wiring entirely
(`Proofs/EntailedCheck.lean`): `DenseVerifiedPassW.ofCheckRules` builds an append-and-drop pass
from `DenseCheckRule`s — recognizers whose acceptance is exactly the vanishing of the emitted
constraint (`degenRange` is the worked example) — and `DenseVerifiedPassW.ofAddConstraints`
builds an append-only pass from an emitted-constraint list plus its containment/entailment
obligations (`oneHotAnnihilate`, `zeroRegister`, `xorEqExtract`). The pipeline encodes the system into the dense `VarId`
representation once at entry and decodes once at output; the `DensePassCorrect` is lifted to the
audited `Variable`-based `PassCorrect` at that boundary (`Bridge.lean`). Correctness follows from the
pass's own `DensePassCorrect`, and the profiler picks up the new pass for free since it consumes the
same list; do not touch `Spec.lean`, the audited `ApcOptimizer/Optimizer.lean`, or the `Basic.lean`
glue. Build with `lake build`.
