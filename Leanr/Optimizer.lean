import Leanr.Implementation.Optimizer
import Leanr.Implementation.OpenVmFacts

set_option autoImplicit false

/-! # Proofs of optimizer correctness (audited) -/

variable {p : ℕ}

/-- **Master correctness theorem.** Given a rule `facts` that picks a proven `BusFacts` instance
    for each bus semantics, the fact-aware pipeline run with those facts maintains correctness:
    its output refines the input, preserves invariants, and stays within the degree bound — for
    every constraint system and every bus semantics. Every concrete optimizer below is an
    instance of this one statement; because `BusFacts p bs` bundles each claim with its soundness
    proof, no choice of `facts` can break correctness. -/
theorem optimizerWithBusFacts_maintainsCorrectness
    (facts : (bs : BusSemantics p) → BusFacts p bs) :
    optimizerMaintainsCorrectness (p := p)
      (fun cs bs => optimizerWithBusFacts cs bs (facts bs)) :=
  ⟨fun cs bs => optimizerWithBusFacts_correct cs bs (facts bs),
   fun cs bs h => optimizerWithBusFacts_respectsDegree cs bs (facts bs) (h := h)⟩

/-- The fact-free `optimizer` maintains correctness: the trivial-facts instance of the master
    theorem (`BusFacts.trivial` claims nothing). -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) optimizer :=
  optimizerWithBusFacts_maintainsCorrectness fun bs => BusFacts.trivial bs

namespace Leanr.OpenVM

/-- The concrete optimizer the `leanr` CLI runs on OpenVM circuits: the fact-aware pipeline
    (`optimizerWithBusFacts`) instantiated with the OpenVM bus semantics and its proven
    `BusFacts`. `busMap` selects the bus layout (default: `defaultBusMap`); `iters` bounds the
    cleanup cycles. -/
def openVmOptimizer (cs : ConstraintSystem babyBear) (busMap : BusMap := defaultBusMap)
    (iters : Nat := 32) : ConstraintSystem babyBear :=
  optimizerWithBusFacts cs (openVmBusSemantics babyBear busMap) (openVmFacts babyBear busMap) iters

/-- `openVmOptimizer` maintains correctness: for every input circuit, bus map, and iteration
    bound, the output refines the input under the OpenVM semantics, preserves invariants, and
    stays within the degree bound. Immediate from `optimizerWithBusFacts_maintainsCorrectness` —
    the OpenVM facts are proven sound by construction (`openVmFacts : BusFacts …`), so no extra
    audit is needed. -/
theorem openVmOptimizer_maintainsCorrectness (cs : ConstraintSystem babyBear)
    (busMap : BusMap) (iters : Nat) :
    ((openVmOptimizer cs busMap iters).refines cs (openVmBusSemantics babyBear busMap)) ∧
      (cs.guaranteesInvariants (openVmBusSemantics babyBear busMap) →
        (openVmOptimizer cs busMap iters).guaranteesInvariants
          (openVmBusSemantics babyBear busMap)) ∧
      (cs.withinDegree (openVmBusSemantics babyBear busMap).degreeBound →
        (openVmOptimizer cs busMap iters).withinDegree
          (openVmBusSemantics babyBear busMap).degreeBound) :=
  ⟨(optimizerWithBusFacts_correct cs (openVmBusSemantics babyBear busMap)
      (openVmFacts babyBear busMap) iters).1,
   (optimizerWithBusFacts_correct cs (openVmBusSemantics babyBear busMap)
      (openVmFacts babyBear busMap) iters).2,
   optimizerWithBusFacts_respectsDegree cs (openVmBusSemantics babyBear busMap)
      (openVmFacts babyBear busMap) iters⟩

end Leanr.OpenVM
