import ApcOptimizer.Implementation.Optimizer
import ApcOptimizer.Implementation.OpenVmFacts
import ApcOptimizer.Implementation.Sp1Facts

set_option autoImplicit false

/-! # The optimizers and their correctness (audited) -/

variable {p : ℕ}

/-! ## The optimizers

    Three optimizers are available, each taking the zkVM's degree bound `b` as a parameter:
    - `optimizerWithBusFacts b facts`: This is the most general optimizer. It consumes a `BusFacts`
      instance with *proven* properties of the bus semantics.
    - `simpleOptimizer bs b`: A specialization with `BusFacts.trivial bs` (no bus knowledge). This is
      the optimizer for a new VM with no proven bus facts. It will likely be less effective than the
      fact-aware optimizer.
    - `openVmOptimizer busMap`: A specialization for the OpenVM semantics (degree bound defaulting to
      `OpenVM.defaultDegreeBound`). -/

/-- Optimizer which does not use any bus facts. Works with any VM, but is less effective. Returns
    the optimized system together with the `Derivations` for its newly-introduced columns. -/
def simpleOptimizer (bs : BusSemantics p) (b : DegreeBound) :
    ConstraintSystem p → ConstraintSystem p × Derivations p :=
  optimizerWithBusFacts b (BusFacts.trivial bs)

namespace ApcOptimizer.OpenVM

/-- Optimizer specialized for the OpenVM semantics. -/
def openVmOptimizer (busMap : BusMap := defaultBusMap) (b : DegreeBound := defaultDegreeBound) :
    ConstraintSystem babyBear → ConstraintSystem babyBear × Derivations babyBear :=
  optimizerWithBusFacts b (openVmFacts babyBear busMap)

end ApcOptimizer.OpenVM

namespace ApcOptimizer.SP1

/-- Optimizer specialized for the SP1 semantics. -/
def sp1Optimizer (busMap : BusMap := defaultBusMap) (b : DegreeBound := defaultDegreeBound) :
    ConstraintSystem koalaBear → ConstraintSystem koalaBear × Derivations koalaBear :=
  optimizerWithBusFacts b (sp1Facts koalaBear busMap)

end ApcOptimizer.SP1

/-! ## Correctness

    In the following theorems, we establish that the optimizers maintain correctness. -/

theorem optimizerWithBusFacts_maintainsCorrectness (bs : BusSemantics p) (b : DegreeBound)
    (facts : BusFacts p bs) :
    Optimizer.isCorrect (optimizerWithBusFacts b facts) bs b :=
  ⟨fun cs => optimizerWithBusFacts_correct b facts cs,
   fun cs => optimizerWithBusFacts_respectsDegree b facts cs⟩

theorem simpleOptimizer_maintainsCorrectness (bs : BusSemantics p) (b : DegreeBound) :
    Optimizer.isCorrect (simpleOptimizer bs b) bs b :=
  optimizerWithBusFacts_maintainsCorrectness bs b (BusFacts.trivial bs)

namespace ApcOptimizer.OpenVM

theorem openVmOptimizer_maintainsCorrectness (busMap : BusMap) (b : DegreeBound) :
    Optimizer.isCorrect (openVmOptimizer busMap b)
      (openVmBusSemantics babyBear busMap) b :=
  optimizerWithBusFacts_maintainsCorrectness (openVmBusSemantics babyBear busMap) b
    (openVmFacts babyBear busMap)

end ApcOptimizer.OpenVM

namespace ApcOptimizer.SP1

theorem sp1Optimizer_maintainsCorrectness (busMap : BusMap) (b : DegreeBound) :
    Optimizer.isCorrect (sp1Optimizer busMap b)
      (sp1BusSemantics koalaBear busMap) b :=
  optimizerWithBusFacts_maintainsCorrectness (sp1BusSemantics koalaBear busMap) b
    (sp1Facts koalaBear busMap)

end ApcOptimizer.SP1
