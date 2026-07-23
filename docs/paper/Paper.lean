import VersoManual

import ApcOptimizer.Spec
import ApcOptimizer.Optimizer

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

-- Render signatures even where a field/theorem carries no docstring: for the audited theorems the
-- signature *is* the statement we want to show, and we do not add prose to the audited source.
set_option verso.docstring.allowMissing true

#doc (Manual) "apc-optimizer: A Verified Constraint-System Optimizer" =>
%%%
authors := ["The apc-optimizer authors"]
shortTitle := "apc-optimizer"
%%%

This document is generated from the audited Lean source. Every formal statement shown below is
spliced directly from the compiled definition — so what you read here is, by construction, the
artifact that is verified, not a transcription of it.

`apc-optimizer` is a verified optimizer for the constraint systems (circuits) that powdr's
autoprecompiles pipeline emits for zkVMs. It is a drop-in replacement for powdr's
`optimize`, and it comes with a machine-checked proof that it preserves a precise notion of
circuit equivalence. The purpose of this document is to make that notion, and the guarantee that
rests on it, legible to an auditor: the audited surface is small, and this is a guided reading of
it.

# Circuits

A circuit is a list of algebraic constraints together with a list of bus interactions, both over
arithmetic expressions in a finite field.

An {deftech}_expression_ is a constant, a variable, or a sum or product of expressions:

{docstring Expression}

Expressions are evaluated under an {deftech}_environment_ assigning a field element to every
variable:

{docstring Expression.eval}

A {deftech}_bus interaction_ sends a tuple (the payload) to a global bus with a multiplicity. Bus
interactions are how a chip talks to the rest of the system — range checks, lookups, memory, the
execution bridge.

{docstring BusInteraction}

Putting the two together, a {deftech}_constraint system_ is a single chip: its algebraic
constraints and its bus interactions.

{docstring ConstraintSystem}

# Bus semantics

The meaning of a bus is not baked into the circuit; it is supplied separately by the zkVM's
{deftech}_bus semantics_. This is the interface an auditor reviews once per VM, and it is
deliberately abstract: the optimizer is proven correct against *any* semantics of this shape, and a
particular VM (OpenVM, SP1) is one instance.

{docstring BusSemantics}

The `admissible` field is where the "this is a real trace" assumption lives. Soundness is required
for *every* assignment (a malicious prover may pick any), but completeness — that the optimizer
does not throw away good traces — is only required for assignments the semantics deems admissible.
For memory buses this encodes the memory discipline; see the memory-bus utility in the audited
`MemoryBus.lean`.

# The correctness relation

The heart of the specification is what it means for an optimized circuit to be a faithful
replacement for its input. The relation is deliberately *asymmetric*, split into soundness and
completeness.

## What a circuit does

Two notions pin down the observable behavior of a circuit under an environment.

A circuit is {deftech}_satisfied_ when every algebraic constraint vanishes and no active bus
interaction violates a constraint in another chip:

{docstring ConstraintSystem.satisfies}

Its {deftech}_side effects_ are the messages it puts on the *stateful* buses (memory, execution
bridge) — this is the behavior that must be preserved, and it is compared up to net multiplicity,
so an identical-payload send/receive pair cancels.

{docstring ConstraintSystem.sideEffects}

## Soundness

Soundness is the direction that protects against a cheating prover: *anything the optimized circuit
accepts, the original would have accepted too, with the same effect on the rest of the system.*

{docstring ConstraintSystem.isSoundReplacementOf}

## Completeness

Completeness is the direction that protects against a useless optimizer that accepts nothing: *every
real (admissible) trace of the input is reproduced by the output.* Crucially, it is constructive —
the optimizer ships a list of {deftech}_derivations_ (computation methods for the columns it
introduced), and completeness demands that witness generation, run on the input trace, actually
produces a satisfying output trace.

{docstring ConstraintSystem.isCompleteReplacementOf}

# The theorem

An optimizer is {deftech}_correct_ for a given bus semantics and degree bound when, on every input,
its output is both a sound and a complete replacement, and it never exceeds the degree bound:

{docstring Optimizer.isCorrect}

The master theorem states that the optimizer is correct for *every* bus semantics and *every* choice
of proven bus facts:

{docstring optimizerWithBusFacts_maintainsCorrectness}

The optimizers actually shipped are instances of it. The fact-free optimizer, usable with any VM:

{docstring simpleOptimizer_maintainsCorrectness}

And the OpenVM-specialized optimizer that the CLI runs:

{docstring ApcOptimizer.OpenVM.openVmOptimizer_maintainsCorrectness}
