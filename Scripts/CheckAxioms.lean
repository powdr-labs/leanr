import Leanr.Optimizer

/-! CI helper: print the axiom dependencies of the top-level correctness theorems.
    `Scripts/check-proof-integrity.sh` asserts the output mentions no forbidden axiom
    (`sorryAx`, `native_decide`'s `ofReduceBool`, …) — i.e. the proofs are fully checked
    and rest only on Lean's three standard axioms. -/

-- The master theorem: the fact-aware optimizer is correct for every choice of proven bus facts.
#print axioms optimizerWithBusFacts_maintainsCorrectness
-- Its two instances: the fact-free optimizer, and the concrete OpenVM optimizer the CLI runs.
#print axioms optimizer_maintainsCorrectness
#print axioms Leanr.OpenVM.openVmOptimizer_maintainsCorrectness
