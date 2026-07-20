import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroMultBus

/-! `ZeroMultBus` has a native dense `VarId` port — `denseZeroMultBusDropPass` (native
`DensePassCorrect` proof) in `DropPassesProof.lean`, keyed on the dense recognizers in
`DropPasses.lean`. This wrapper re-exports the audited `Variable`-based semantics (the spec of
record) from `OldVariableBased/`. -/
