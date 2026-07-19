import ApcOptimizer.Implementation.Dense.Registry
import ApcOptimizer.Implementation.Dense.Encoding
import ApcOptimizer.Implementation.Dense.Measure
import ApcOptimizer.Implementation.Dense.Pass
import ApcOptimizer.Implementation.Dense.ExprOps
import ApcOptimizer.Implementation.Dense.Adapter
import ApcOptimizer.Implementation.Dense.Bridge
import ApcOptimizer.Implementation.Dense.Subst
import ApcOptimizer.Implementation.Dense.SubstMap
import ApcOptimizer.Implementation.Dense.Affine
import ApcOptimizer.Implementation.Dense.Rewrite
import ApcOptimizer.Implementation.Dense.DropPasses
import ApcOptimizer.Implementation.Dense.Normalize
import ApcOptimizer.Implementation.Dense.Dedup
import ApcOptimizer.Implementation.Dense.DigitFold
import ApcOptimizer.Implementation.Dense.Gauss
import ApcOptimizer.Implementation.Dense.DomainBatch
import ApcOptimizer.Implementation.Dense.DomainBatchNative
import ApcOptimizer.Implementation.Dense.DomainBatchNativeProof
import ApcOptimizer.Implementation.Dense.OneHotAnnihilate
import ApcOptimizer.Implementation.Dense.ZeroRegister
import ApcOptimizer.Implementation.Dense.CarryBranch
import ApcOptimizer.Implementation.Dense.ZeroWidthRange
import ApcOptimizer.Implementation.Dense.DomainFold
import ApcOptimizer.Implementation.Dense.DomainFoldNative
import ApcOptimizer.Implementation.Dense.DomainFoldNativeProof
import ApcOptimizer.Implementation.Dense.AddrDiseq
import ApcOptimizer.Implementation.Dense.AddrDiseqProof
import ApcOptimizer.Implementation.Dense.BusUnifyNative
import ApcOptimizer.Implementation.Dense.BusUnifyNativeProof
import ApcOptimizer.Implementation.Dense.RootPairUnifyNative
import ApcOptimizer.Implementation.Dense.RootPairUnifyNativeProof
import ApcOptimizer.Implementation.Dense.FlagUnifyNative
import ApcOptimizer.Implementation.Dense.FlagUnifyNativeProof
import ApcOptimizer.Implementation.Dense.FlagFoldDropsNative
import ApcOptimizer.Implementation.Dense.FlagFoldDropsNativeProof
import ApcOptimizer.Implementation.Dense.FxSubstNative

/-! # Dense `VarId` internal representation — umbrella import (Task 3)

Imports every implementation-only dense module so that a plain `lake build` compiles them all,
even those not yet wired into a scheduled pass (e.g. shared expression ops awaiting their consumer).
`Implementation/Optimizer.lean` imports this, keeping the whole dense layer in the default build
graph. -/
