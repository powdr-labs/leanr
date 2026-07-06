import Leanr.Optimizer

/-! CI helper: print the axiom dependencies of the top-level correctness theorems.
    `Scripts/check-proof-integrity.sh` asserts the output mentions no forbidden axiom
    (`sorryAx`, `native_decide`'s `ofReduceBool`, …) — i.e. the proofs are fully checked
    and rest only on Lean's three standard axioms. -/

#print axioms optimizer_maintainsCorrectness
#print axioms optimizer_respectsDegreeBound
