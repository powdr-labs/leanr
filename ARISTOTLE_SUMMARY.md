# Summary of changes for run a7ec1800-1523-43ca-be77-434ef1c65e08
## Audit result: no soundness hole found in the Spec

I searched `Leanr/Spec.lean` (plus the supporting `Leanr/MemoryBus.lean`, `Leanr/OpenVmSemantics.lean`, and the pass-composition glue in `Leanr/Implementation/OptimizerPasses/Basic.lean`) for a way a *certified* optimizer could emit a circuit with different stateful side effects (memory / execution-bridge messages) from the original — i.e. a PoC optimizer for which `optimizerMaintainsCorrectness` is provable yet whose side effects differ on a valid execution. I found none, and I backed the conclusion with machine-checked lemmas.

### Why there is no hole
`refines` pins the full stateful side-effect relation in both directions:
- **Soundness** (`(opt cs).implies cs`): every satisfying assignment of the optimized circuit is matched by a satisfying assignment of the original with `≈`-equal side effects — the optimizer cannot invent behaviour.
- **Completeness** (`cs.impliesAdmissible (opt cs)`): every real (admissible) trace of the original is reproduced with equal side effects — no real behaviour is dropped or altered.

The subtle loophole one might expect — that `implies` only asks for *existence* of a matching assignment, with no shared "input" variables — is closed because `sideEffects` records the messages *received* (inputs: memory reads / execution-bridge receive) as well as those *sent* (outputs). Since `≈` matches both, inputs are pinned and the original's exactly-modelled algebraic constraints then force the outputs. There is nothing to permute. I also checked the framework mechanics: `≈` is a genuine equivalence, `refines` is reflexive/transitive with correct variance (so per-pass proofs compose soundly), `PassCorrect` is exactly `refines ∧ invariant-preservation` (no weaker obligation), evaluation preserves `busId`, the certified direction is `(opt cs).refines cs`, and vacuous satisfaction is blocked by completeness.

### Where trust actually lives (documented, not spec holes)
The guarantee is relative to the `BusSemantics` you supply. It inherits assumptions already called out in the README/source: the `BusSemantics` must faithfully mark stateful buses (the shipped OpenVM instance correctly marks memory + execution bridge); the documented `pcLookup`/execution-bridge approximations are stateless and completeness-side (they never change side effects); and the input assumptions (chronological ordering, input guarantees invariants, PC lookups pinned) are exporter preconditions. None of these let a certified optimizer change stateful side effects on a valid trace.

### Deliverables (committed and pushed)
- `Leanr/Audit/SoundnessExtraction.lean` — axiom-clean, `sorry`-free lemmas extracting the guarantees from `optimizerMaintainsCorrectness`: `certified_no_new_side_effects`, `certified_no_unrealizable_message`, `certified_realizes_real_traces`, `certified_preserves_invariants`. (Not part of the audited surface; imported by nothing that matters for correctness.)
- `docs/audit/spec-soundness-audit.md` — the full analysis and the attempted-PoC reasoning.

### Build fix
The project as shipped did not build here: `lean-toolchain` pinned `v4.30.0-rc1`, but the vendored `mathlib`/`batteries` under `.lake/packages` are built for `v4.28.0`. I aligned `lean-toolchain` to `v4.28.0` (matching the vendored oleans); the whole project then builds cleanly (`lake build`), and I confirmed the master theorem `openVmOptimizer_maintainsCorrectness` is axiom-clean.