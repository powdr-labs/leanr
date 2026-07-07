import Leanr.Implementation.Optimizer
import Leanr.Implementation.OpenVmFacts

set_option autoImplicit false

/-! # The optimizers and their correctness (audited)

This is the audited top of the optimizer. Everything it *builds on* — the pipeline, the passes,
the proven `BusFacts` — lives under `Leanr/Implementation/` and needs no audit; what an auditor
reviews here are the optimizer definitions and, above all, the *statements* of the correctness
theorems, read against the spec (`Leanr/Spec.lean`) and the bus semantics
(`Leanr/OpenVmSemantics.lean`). `lake build` checks the proofs.

The file has two sections — first the optimizers, then their correctness. All three correctness
results are instances of a single `optimizerMaintainsCorrectness bs opt` statement (for bus
semantics `bs`: the circuit-to-circuit map `opt` refines its input, preserves invariants, and
respects the degree bound). -/

variable {p : ℕ}

/-! ## The optimizers

`optimizerWithBusFacts` (the fact-aware pipeline) is defined in `Leanr/Implementation/`. Applied
to proven `BusFacts` and an iteration bound it is a circuit-to-circuit map; the two optimizers
below instantiate it. -/

/-- The fact-free optimizer for a bus semantics `bs`: the pipeline with no bus knowledge
    (`BusFacts.trivial`). -/
def simpleOptimizer (bs : BusSemantics p) : ConstraintSystem p → ConstraintSystem p :=
  optimizerWithBusFacts (BusFacts.trivial bs) 32

namespace Leanr.OpenVM

/-- The optimizer the `leanr` CLI runs on OpenVM circuits: `optimizerWithBusFacts` at the OpenVM
    bus semantics and its proven `BusFacts`. `busMap` selects the bus layout (default:
    `defaultBusMap`); `iters` bounds the cleanup cycles. -/
def openVmOptimizer (busMap : BusMap := defaultBusMap) (iters : Nat := 32) :
    ConstraintSystem babyBear → ConstraintSystem babyBear :=
  optimizerWithBusFacts (openVmFacts babyBear busMap) iters

end Leanr.OpenVM

/-! ## Correctness

Each theorem is an instance of `optimizerMaintainsCorrectness bs opt`. The master theorem does the
work; the fact-free and OpenVM optimizers fall out of it as one-liners. -/

/-- **Master correctness theorem.** For any bus semantics `bs`, any proven `BusFacts` for it, and
    any cleanup-cycle bound `iters`, the fact-aware pipeline maintains correctness. The two
    optimizers below are instances; because `BusFacts p bs` bundles each claim with its soundness
    proof, no choice of facts can break correctness. -/
theorem optimizerWithBusFacts_maintainsCorrectness (bs : BusSemantics p) (facts : BusFacts p bs)
    (iters : Nat) :
    optimizerMaintainsCorrectness bs (optimizerWithBusFacts facts iters) :=
  ⟨fun cs => optimizerWithBusFacts_correct facts iters cs,
   fun cs => optimizerWithBusFacts_respectsDegree facts iters cs⟩

/-- The fact-free `simpleOptimizer` maintains correctness, for every bus semantics: the
    trivial-facts instance of the master theorem (`BusFacts.trivial` claims nothing). -/
theorem simpleOptimizer_maintainsCorrectness (bs : BusSemantics p) :
    optimizerMaintainsCorrectness bs (simpleOptimizer bs) :=
  optimizerWithBusFacts_maintainsCorrectness bs (BusFacts.trivial bs) 32

namespace Leanr.OpenVM

/-- `openVmOptimizer` maintains correctness w.r.t. the OpenVM semantics, for every bus map and
    iteration count: the instance of the master theorem at `openVmFacts`. Those facts are proven
    sound by construction (`openVmFacts : BusFacts …`), so no extra audit is needed. -/
theorem openVmOptimizer_maintainsCorrectness (busMap : BusMap) (iters : Nat) :
    optimizerMaintainsCorrectness (openVmBusSemantics babyBear busMap)
      (openVmOptimizer busMap iters) :=
  optimizerWithBusFacts_maintainsCorrectness (openVmBusSemantics babyBear busMap)
    (openVmFacts babyBear busMap) iters

end Leanr.OpenVM
