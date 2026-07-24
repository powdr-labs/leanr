import ApcOptimizer.Implementation.OptimizerPasses.Registry

set_option autoImplicit false

/-! # Per-variable item index

Maps each variable to the items mentioning it (`denseVarBucket`), uncapped and order-preserving so
a lookup returns exactly the same list a `filter (mentions x)` would. Shared by
`RedundantByteDrop.lean` (operand justification) and `RootPairUnify.lean` (per-variable bound
lookups); the soundness/exactness lemmas live with their consumers. -/

namespace ApcOptimizer.Dense

/-- Record `a` under each variable in `vs` (prepending, so a right-to-left build keeps source
    order). -/
def denseVarBucketAdd {α : Type} (m : Std.HashMap VarId (List α)) (vs : List VarId) (a : α) :
    Std.HashMap VarId (List α) :=
  vs.foldl (fun m x => m.insert x (a :: m.getD x [])) m

/-- Index each item under every variable it mentions (via `varsOf`), keeping source order. -/
def denseVarBucket {α : Type} (varsOf : α → List VarId) (items : List α) :
    Std.HashMap VarId (List α) :=
  items.foldr (fun a m => denseVarBucketAdd m ((varsOf a).eraseDups) a) ∅

/-- Look up the items indexed under `x`. -/
def denseVarBucketLookup {α : Type} (I : Std.HashMap VarId (List α)) (x : VarId) : List α :=
  I.getD x []

end ApcOptimizer.Dense
