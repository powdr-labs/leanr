import ApcOptimizer.Implementation.Dense.Registry
import ApcOptimizer.Implementation.Dense.Encoding
import ApcOptimizer.Implementation.Dense.Measure
import ApcOptimizer.Implementation.Dense.Pass
import ApcOptimizer.Implementation.Dense.Adapter

/-! # Dense `VarId` internal representation — umbrella import (Task 3)

Imports every implementation-only dense module so that a plain `lake build` compiles them all,
even those not yet wired into a scheduled pass (e.g. shared expression ops awaiting their consumer).
`Implementation/Optimizer.lean` imports this, keeping the whole dense layer in the default build
graph. -/
