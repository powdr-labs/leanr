import Leanr.OpenVM.Snapshot

/-!
# Concrete correctness of the optimizer on the snapshot circuit

The snapshot test (`Leanr/OpenVM/Snapshot.lean`) measures *effectiveness* (the shrink factor). This
file records the *correctness* side for the very same machine: the optimizer's output on the OpenVM
ADD-immediate is provably equivalent to the input, and preserves invariants — a direct instance of
the general `optimizer_maintainsCorrectness`.

Note there is **no** `Fact (Nat.Prime babyBear)` in sight: the optimizer is correct over *any*
modulus — a strictly stronger guarantee than the prime-field setting. The one pass that needs
field structure (finite-domain propagation) *decides* `p.Prime` at runtime, carries the fact
locally, and is the identity for composite `p`, so no primality hypothesis ever reaches the
statements here (checked: both theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace Leanr.OpenVM.Snapshot

open Leanr.OpenVM

/-- The optimized ADD-immediate circuit is equivalent to the input under the OpenVM bus semantics. -/
theorem addiOptimized_equivalent :
    addiOptimized.equivalentTo addiInput (openVmBusSemantics babyBear) :=
  (optimizerWith_correct addiInput (openVmBusSemantics babyBear) (openVmFacts babyBear)).1

/-- If the input circuit guarantees the system invariants, so does the optimized circuit. -/
theorem addiOptimized_preservesInvariants
    (h : addiInput.guaranteesInvariants (openVmBusSemantics babyBear)) :
    addiOptimized.guaranteesInvariants (openVmBusSemantics babyBear) :=
  (optimizerWith_correct addiInput (openVmBusSemantics babyBear) (openVmFacts babyBear)).2 h

end Leanr.OpenVM.Snapshot
