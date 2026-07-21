import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ConstantFold

/-! `ConstantFold` has a native dense `VarId` port — `denseConstantFoldPass` (native
`DensePassCorrect` proof) in `ExprOps.lean`. This wrapper re-exports the audited `Variable`-based
semantics (the spec of record) from `OldVariableBased/`. -/
