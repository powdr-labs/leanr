import ApcOptimizer.Implementation.Optimizer
import ApcOptimizer.Implementation.OpenVmFacts

set_option autoImplicit false

/-! # The optimizers and their correctness (audited) -/

variable {p : ℕ}

/-! ## The optimizers

    Three optimizers are available:
    - `optimizerWithBusFacts facts`: This is the most general optimizer. It consumes a `BusFacts` instance
      with *proven* properties of the bus semantics.
    - `simpleOptimizer bs`: A specialization with `BusFacts.trivial bs` (no bus knowledge). This is the optimizer for
      a new VM with no proven bus facts. It will likely be less effective than the fact-aware optimizer.
    - `openVmOptimizer busMap`: A specialization for the OpenVM semantics. -/

/-- Optimizer which does not use any bus facts. Works with any VM, but is less effective. Returns
    the optimized system together with the `Derivations` for its newly-introduced columns. -/
def simpleOptimizer (bs : BusSemantics p) : ConstraintSystem p → ConstraintSystem p × Derivations p :=
  optimizerWithBusFacts (BusFacts.trivial bs)

namespace ApcOptimizer.OpenVM

/-- Optimizer specialized for the OpenVM semantics. -/
def openVmOptimizer (busMap : BusMap := defaultBusMap) :
    ConstraintSystem babyBear → ConstraintSystem babyBear × Derivations babyBear :=
  optimizerWithBusFacts (openVmFacts babyBear busMap)

end ApcOptimizer.OpenVM

/-! ## Correctness

    In the following theorems, we establish that the optimizers maintain correctness. -/

theorem optimizerWithBusFacts_maintainsCorrectness (bs : BusSemantics p) (facts : BusFacts p bs) :
    Optimizer.isCorrect (optimizerWithBusFacts facts) bs :=
  ⟨fun cs => optimizerWithBusFacts_correct facts cs,
   fun cs => optimizerWithBusFacts_respectsDegree facts cs⟩

theorem simpleOptimizer_maintainsCorrectness (bs : BusSemantics p) :
    Optimizer.isCorrect (simpleOptimizer bs) bs :=
  optimizerWithBusFacts_maintainsCorrectness bs (BusFacts.trivial bs)

namespace ApcOptimizer.OpenVM

theorem openVmOptimizer_maintainsCorrectness (busMap : BusMap) :
    Optimizer.isCorrect (openVmOptimizer busMap)
      (openVmBusSemantics babyBear busMap) :=
  optimizerWithBusFacts_maintainsCorrectness (openVmBusSemantics babyBear busMap)
    (openVmFacts babyBear busMap)

end ApcOptimizer.OpenVM
