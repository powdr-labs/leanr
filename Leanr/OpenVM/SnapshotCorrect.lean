import Leanr.OpenVM.Snapshot

/-!
# Concrete correctness of the optimizer on the snapshot circuit

The snapshot test (`Leanr/OpenVM/Snapshot.lean`) measures *effectiveness* (the shrink factor). This
file records the *correctness* side for the very same machine: the optimizer's output on the OpenVM
ADD-immediate is provably equivalent to the input, and preserves invariants — a direct instance of
the general `optimizer_maintainsCorrectness`.

Note there is **no** `Fact (Nat.Prime babyBear)` in sight: every optimization pass is field-agnostic
(it uses only commutative-ring identities), so the optimizer is correct over *any* modulus — a
strictly stronger guarantee than the prime-field setting. Primality is available (`Nat.Prime
babyBear` is provable by `norm_num`) should a future prime-field-specific pass require it.
-/

namespace Leanr.OpenVM.Snapshot

open Leanr.OpenVM

/-- The optimized ADD-immediate circuit is equivalent to the input under the OpenVM bus semantics. -/
theorem addiOptimized_equivalent :
    addiOptimized.equivalentTo addiInput (openVmBusSemantics babyBear) :=
  (optimizer_maintainsCorrectness addiInput (openVmBusSemantics babyBear)).1

/-- If the input circuit guarantees the system invariants, so does the optimized circuit. -/
theorem addiOptimized_preservesInvariants
    (h : addiInput.guaranteesInvariants (openVmBusSemantics babyBear)) :
    addiOptimized.guaranteesInvariants (openVmBusSemantics babyBear) :=
  (optimizer_maintainsCorrectness addiInput (openVmBusSemantics babyBear)).2 h

end Leanr.OpenVM.Snapshot
