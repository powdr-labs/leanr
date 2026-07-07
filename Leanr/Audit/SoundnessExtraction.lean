import Leanr.Spec

/-!
# Soundness audit: what certification actually guarantees about side effects

This file is **not** part of the audited surface and is imported by nothing that matters for
correctness. It exists to make the audit conclusion machine-checked: it *extracts*, from the
spec's `optimizerMaintainsCorrectness`, the precise operational guarantees about the **stateful
side effects** (`ConstraintSystem.sideEffects`) of a certified optimizer.

The question under audit was: *can a certified optimizer emit a circuit whose side effects
differ from the original's?* These lemmas answer "no", in both directions:

* `certified_no_new_side_effects` — every satisfying assignment of the optimized circuit is
  matched by a satisfying assignment of the *original* with `≈`-equal side effects. So the
  optimizer can never *invent* a stateful behaviour (a memory / execution-bridge message net
  multiplicity) that the original could not already produce.
* `certified_no_unrealizable_message` — the same, message by message: the net multiplicity of
  every bus message the optimized circuit sends is reproduced by some satisfying assignment of
  the original.
* `certified_realizes_real_traces` — every *admissible* (real-trace) satisfying assignment of
  the original is reproduced, with `≈`-equal side effects, by an admissible satisfying assignment
  of the optimized circuit. So no real behaviour is dropped or altered.

Together these say the certified optimizer preserves the stateful side-effect *relation* exactly
(soundness: optimized ⊆ original; completeness: real original ⊆ optimized). Note that
`ConstraintSystem.sideEffects` records **both** the messages *received* (inputs, e.g. memory
reads / execution-bridge receive) and those *sent* (outputs, e.g. memory writes), so `≈`-equality
pins the full input→output behaviour, not just the outputs.

These are direct consequences of the definitions, which is exactly the point: the guarantee is
built into `refines`, with no extra hypotheses smuggled in.
-/

set_option autoImplicit false

variable {p : ℕ}
variable {bs : BusSemantics p} {opt : ConstraintSystem p → ConstraintSystem p}

/-- **Soundness extraction.** A certified optimizer never makes the optimized circuit exhibit a
    stateful side-effect state that the original could not also exhibit. -/
theorem certified_no_new_side_effects
    (hcorrect : optimizerMaintainsCorrectness bs opt)
    (cs : ConstraintSystem p) (env : String → ZMod p)
    (hsat : (opt cs).satisfies bs env) :
    ∃ env', cs.satisfies bs env' ∧ (opt cs).sideEffects bs env ≈ cs.sideEffects bs env' :=
  (hcorrect.1 cs).1.1 env hsat

/-- **Per-message soundness.** The optimized circuit cannot send any bus message with a net
    multiplicity unattainable by the original. -/
theorem certified_no_unrealizable_message
    (hcorrect : optimizerMaintainsCorrectness bs opt)
    (cs : ConstraintSystem p) (env : String → ZMod p)
    (hsat : (opt cs).satisfies bs env) (m : BusMessage p) :
    ∃ env', cs.satisfies bs env' ∧
      multiplicitySum m ((opt cs).sideEffects bs env)
        = multiplicitySum m (cs.sideEffects bs env') := by
  obtain ⟨env', hsat', hequiv⟩ := certified_no_new_side_effects hcorrect cs env hsat
  exact ⟨env', hsat', hequiv m⟩

/-- **Completeness extraction.** Every real (admissible) trace of the original is reproduced,
    with identical side effects, by an admissible satisfying assignment of the optimized circuit. -/
theorem certified_realizes_real_traces
    (hcorrect : optimizerMaintainsCorrectness bs opt)
    (cs : ConstraintSystem p) (env : String → ZMod p)
    (hadm : cs.admissible bs env) (hsat : cs.satisfies bs env) :
    ∃ env', (opt cs).satisfies bs env' ∧ (opt cs).admissible bs env' ∧
      cs.sideEffects bs env ≈ (opt cs).sideEffects bs env' :=
  (hcorrect.1 cs).1.2 env hadm hsat

/-- **Invariant preservation extraction.** If the original guarantees the VM's invariants, so
    does the optimized circuit. -/
theorem certified_preserves_invariants
    (hcorrect : optimizerMaintainsCorrectness bs opt)
    (cs : ConstraintSystem p) (hinv : cs.guaranteesInvariants bs) :
    (opt cs).guaranteesInvariants bs :=
  (hcorrect.1 cs).2 hinv
