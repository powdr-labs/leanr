set_option autoImplicit false

/-! # Search / enumeration budget constants

Representation-independent (`Nat`) runtime work caps and gates consumed by the dense passes and
their proofs. -/

/-! ## Deep byte-justification budgets -/

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

/-! ## Enumeration work caps (`DomainBatch` / `DomainFold`) -/

/-- Work cap for one joint enumeration: box size × number of covered targets. -/
def maxEnumWork : Nat := 524288

/-- Systems with at least this many algebraic constraints use the inverted index; smaller ones use
    the direct per-target `coveredCsOf` scan. Purely a runtime gate — both paths compute the
    identical fold. -/
def domainFoldIndexThreshold : Nat := 8192

/-- Systems with at least this many bus interactions use the slot-0-indexed representative store in
    `densePdDropSet`; smaller ones scan the per-class representative list directly (the index's
    per-interaction map overhead outweighs the scan at fixture scale). Purely a runtime gate — both
    paths propose the identical drop set. -/
def pointwiseDupDropIndexThreshold : Nat := 4096
