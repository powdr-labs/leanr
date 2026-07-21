set_option autoImplicit false

/-! # Search / enumeration budget constants

Representation-independent (`Nat`) runtime work caps and gates, re-homed here from the reference
`OldVariableBased/` passes so the dense passes and their proofs can consume them without importing
the reference passes; each reference pass imports them back. Moving a plain `Nat` constant cannot
change behaviour — the same literal is shared, so every reference-vs-dense decision it gates is
unchanged. Each constant keeps its original (root-namespace) fully-qualified name. -/

/-! ## Deep byte-justification budgets (`OldVariableBased/BusPairCancel.lean`) -/

/-- Cap on the number of enumerated flag assignments per deep-justification attempt. -/
def maxDeepPoints : Nat := 64

/-- Cap on a single enumerated variable's domain size in the deep justification. -/
def maxDeepDomain : Nat := 4

/-- Cap on the number of candidate defining constraints tried per deep justification. -/
def maxDeepConstraints : Nat := 4

/-- Cap on a candidate constraint's number of distinct other variables (wider constraints
    cannot collapse to the ≤2-term linear shapes `pointByteOk` accepts anyway). -/
def maxDeepVars : Nat := 8

/-- Reduction fuel: how many checked forms one basis justification may subtract. -/
def basisFuel : Nat := 3

/-! ## Enumeration work caps (`OldVariableBased/DomainBatch.lean`, `.../DomainFold.lean`) -/

/-- Work cap for one joint enumeration: box size × number of covered targets. -/
def maxEnumWork : Nat := 524288

/-- Systems with at least this many algebraic constraints use the inverted index; smaller ones use
    the direct per-target `coveredCsOf` scan (see the section comment). Purely a runtime gate —
    both paths compute the identical fold. -/
def domainFoldIndexThreshold : Nat := 8192
