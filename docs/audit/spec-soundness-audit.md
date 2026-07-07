# Spec soundness audit — can a certified optimizer change side effects?

**Scope.** Look for a *soundness hole* in the audited spec: a way for a certified optimizer to
emit a circuit whose **stateful side effects** (memory / execution-bridge messages) differ from
the original's on a valid execution. A valid PoC would be an `optimizer` for which
`optimizerMaintainsCorrectness bs optimizer` is provable, yet which produces different side
effects.

**Files reviewed.** `Leanr/Spec.lean` (the definitions below), `Leanr/MemoryBus.lean`,
`Leanr/OpenVmSemantics.lean`, and the pass framework `Leanr/Implementation/OptimizerPasses/Basic.lean`
(the glue that turns a pass into a certified optimizer).

**Result.** No soundness hole was found. The `refines` relation pins the full stateful
side-effect behaviour (both messages *received* and *sent*) in both directions, so a certified
optimizer cannot change side effects on any valid execution. The residual trust is entirely in
(a) the `BusSemantics` instance faithfully modelling the VM and (b) the input assumptions already
documented in the `README`. These conclusions are backed by machine-checked extraction lemmas in
`Leanr/Audit/SoundnessExtraction.lean` (axiom-clean; builds with `lake build
Leanr.Audit.SoundnessExtraction`).

> Build note: the shipped `lean-toolchain` pinned `v4.30.0-rc1`, but the vendored `mathlib` /
> `batteries` under `.lake/packages` are built for `v4.28.0`. Under `v4.30.0-rc1` the project does
> not build (the dependencies fail to recompile). The toolchain was aligned to `v4.28.0`, which
> matches the vendored oleans, and the whole project then builds cleanly.

---

## 1. What the spec calls a "side effect"

`ConstraintSystem.sideEffects bs env` is the list of **stateful** bus interactions, each evaluated
to a `((busId, payload), multiplicity)` message:

```
sideEffects cs bs env =
  (cs.busInteractions.filter (bs.isStateful ·.busId)).map (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity))
```

Two side-effect states are compared by `≈` (`HasEquiv (BusState p)`): equal iff **every message
has the same net multiplicity** (`multiplicitySum`) in both. This is exactly the notion a global
bus argument cares about — a chip's externally visible effect is the net multiset of messages it
puts on each stateful bus.

Crucial observation: `sideEffects` records *all* stateful interactions — both the ones **received**
(inputs: memory reads, execution-bridge receive) and the ones **sent** (outputs: memory writes,
execution-bridge send). So `≈`-equality constrains inputs *and* outputs, i.e. the whole
input→output relation, not just the outputs.

## 2. What certification requires

`optimizerMaintainsCorrectness bs opt` requires, for every `cs`, that
`(opt cs).refines cs bs`, where

```
self.refines other := self.implies other ∧ other.impliesAdmissible self
```

* **Soundness** `(opt cs).implies cs`: for *every* satisfying `env` of `opt cs`, there is a
  satisfying `env'` of `cs` with `(opt cs).sideEffects env ≈ cs.sideEffects env'`.
* **Completeness** `cs.impliesAdmissible (opt cs)`: for every *admissible* (real-trace) satisfying
  `env` of `cs`, there is a satisfying **and admissible** `env'` of `opt cs` with
  `cs.sideEffects env ≈ (opt cs).sideEffects env'`.

`satisfies` enforces **all** algebraic constraints exactly (`c.eval env = 0`) plus
`violatesConstraint`. The pass framework's `PassCorrect` is *exactly* `refines ∧ invariant
preservation`, and passes compose by `refines_trans`; there is no weaker obligation a pass could
discharge instead.

## 3. Why side effects cannot change (the PoC search)

Suppose an attacker wants `opt` to compute a different memory write on some real input.

1. Take a real trace `env` of `cs`; it reads inputs (memory/execution-bridge **receives** `R`) and
   writes outputs (**sends** `W`). By completeness there is an admissible satisfying `env'` of
   `opt cs` with the *same* side effects, i.e. the same `R` **and** the same `W`. So `opt cs` must
   reproduce, not alter, the real behaviour.
2. Conversely, any satisfying `env` of `opt cs` producing receives `R'` and sends `W'` must, by
   soundness, be matched by a satisfying `env'` of `cs` with the same `R'` and `W'`. Because the
   *receives* `R'` are part of the matched side effects, `env'` feeds `cs` the same inputs; the
   original's algebraic constraints (modelled exactly by `satisfies`) then force the *sends*. So
   `opt cs` cannot pair inputs `R'` with an output `W'` that `cs` would not itself produce.

The would-be loophole — that `implies` only asks for the *existence* of a matching `env'`, with no
shared "input" variables between `env` and `env'` — is closed precisely because inputs are carried
as received side effects and matched by `≈`. There is nothing to permute.

Machine-checked in `Leanr/Audit/SoundnessExtraction.lean`:

* `certified_no_new_side_effects` — optimized ⊆ original (no invented behaviour);
* `certified_no_unrealizable_message` — the same, per message net multiplicity;
* `certified_realizes_real_traces` — real original ⊆ optimized (no dropped/altered real behaviour);
* `certified_preserves_invariants` — invariant preservation.

## 4. Framework and definitional checks (no bug found)

* `≈` is a genuine equivalence (`BusState.equiv_refl/symm/trans`) and `refines` is reflexive and
  transitive with the correct variance (`refines_trans` swaps the completeness witnesses
  correctly), so the per-pass proofs compose into a whole-optimizer proof soundly.
* `BusInteraction.eval` preserves `busId`, so `isStateful` (applied to the static `busId`) and the
  evaluated message agree; a stateful interaction cannot be "hidden" by evaluation.
* Direction is correct: certification asserts `(opt cs).refines cs` (optimized refines original),
  not the reverse.
* Making `opt cs` unsatisfiable to satisfy soundness vacuously is blocked by completeness (which
  demands a satisfying admissible witness of `opt cs` for every real trace of `cs`).
* `satisfies` models every algebraic constraint exactly; the master theorem
  `openVmOptimizer_maintainsCorrectness` is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## 5. Where the trust actually lives (out of scope of "the Spec", and already documented)

The abstract spec is sound *relative to the `BusSemantics` you give it*. The guarantee therefore
inherits these assumptions, all already called out in `README.md` / the source:

1. **`BusSemantics` must faithfully model the VM.** `sideEffects` only ranges over buses with
   `isStateful = true`; the shipped `openVmBusSemantics` marks memory and the execution bridge
   stateful (correct). A *wrong* semantics that, say, declared nothing stateful would make
   `sideEffects` empty and vacuously allow any change — but that is a wrong-semantics problem, not
   a Spec hole, and is exactly why `OpenVmSemantics.lean` is on the audit surface.
2. **Documented semantic approximations are completeness-side, and never touch stateful side
   effects.** The `pcLookup` `violates` check is arity-only (`OpenVmSemantics.lean`, marked
   `ISSUE`) and the execution bridge is admitted as a memory bus with partial completeness
   (`memShapeOf`). PC lookups and range checks are **stateless**, so they are not side effects; the
   documented risk is loss of completeness (mitigated by the "PC lookups pinned" input
   assumption), not a change of side effects.
3. **Input assumptions (README).** Memory / execution-bridge interactions are listed in
   chronological order (used by `admissible` in `MemoryBus.lean`); the input guarantees invariants
   and respects the degree bound; PC lookup fields are pinned to constants. These are preconditions
   the exporter must meet; violating them can break completeness or the memory invariant, and are
   the auditor's responsibility to confirm on the input circuits.

## 6. Conclusion

No optimizer that changes stateful side effects on a valid execution can satisfy
`optimizerMaintainsCorrectness` for the shipped OpenVM semantics: `refines` pins the full
input→output side-effect relation both ways, and this is verified in
`Leanr/Audit/SoundnessExtraction.lean`. The remaining trust surface is the faithfulness of the
`BusSemantics` instance and the documented input assumptions — not a hole in the spec's
definitions.
