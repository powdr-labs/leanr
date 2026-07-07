import Leanr.Implementation.Optimizer
import Leanr.Implementation.OpenVmFacts

set_option autoImplicit false

/-! # The optimizers and their correctness (audited) -/

variable {p : ℕ}

/-! ## The optimizers

    Three optimizers are available:
    - `optimizerWithBusFacts facts iters`: This is the most general optimizer. It consumes a `BusFacts` instance
      with *proven* properties of the bus semantics.
    - `simpleOptimizer bs`: A specialization with `BusFacts.trivial bs` (no bus knowledge). This is the optimizer for
      a new VM with no proven bus facts. It will likely be less effective than the fact-aware optimizer.
    - `openVmOptimizer busMap iters`: A specialization for the OpenVM semantics. -/

/-- Optimizer which does not use any bus facts. Works with any VM, but is less effective. -/
def simpleOptimizer (bs : BusSemantics p) (iters : Nat := 32) : ConstraintSystem p → ConstraintSystem p :=
  optimizerWithBusFacts (BusFacts.trivial bs) iters

namespace Leanr.OpenVM

/-- Optimizer specialized for the OpenVM semantics. -/
def openVmOptimizer (busMap : BusMap := defaultBusMap) (iters : Nat := 32) :
    ConstraintSystem babyBear → ConstraintSystem babyBear :=
  optimizerWithBusFacts (openVmFacts babyBear busMap) iters

end Leanr.OpenVM

/-! ## Correctness

    In the following theorems, we establish that the optimizers maintain correctness. -/

theorem optimizerWithBusFacts_maintainsCorrectness (bs : BusSemantics p) (facts : BusFacts p bs)
    (iters : Nat) :
    optimizerMaintainsCorrectness bs (optimizerWithBusFacts facts iters) :=
  ⟨fun cs => optimizerWithBusFacts_correct facts iters cs,
   fun cs => optimizerWithBusFacts_respectsDegree facts iters cs,
   fun cs => optimizerWithBusFacts_preservesDerived facts iters cs⟩

theorem simpleOptimizer_maintainsCorrectness (bs : BusSemantics p) (iters : Nat) :
    optimizerMaintainsCorrectness bs (simpleOptimizer bs iters) :=
  optimizerWithBusFacts_maintainsCorrectness bs (BusFacts.trivial bs) iters

namespace Leanr.OpenVM

theorem openVmOptimizer_maintainsCorrectness (busMap : BusMap) (iters : Nat) :
    optimizerMaintainsCorrectness (openVmBusSemantics babyBear busMap)
      (openVmOptimizer busMap iters) :=
  optimizerWithBusFacts_maintainsCorrectness (openVmBusSemantics babyBear busMap)
    (openVmFacts babyBear busMap) iters

end Leanr.OpenVM
