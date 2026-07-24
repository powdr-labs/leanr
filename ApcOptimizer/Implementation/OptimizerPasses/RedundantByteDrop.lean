import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify

set_option autoImplicit false

/-! # Dense redundant byte-check removal

Runtime recognizer and transform for `redundantByteDrop`; the pass is wrapped in
`Proofs/RedundantByteDrop.lean`. Unlike `denseSvCheck?` (`ByteCheckPack.lean`), the recognizer here
ignores the dropped check's own multiplicity, returns a *list* of justified operands, and also
recognizes the packed-pair shape. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## A generic uncapped per-variable bucket index

`denseByteJustifiedW` needs, per operand variable, the constraints mentioning it (`candsOf`) and the
base interactions bounding it (`wits`). Computing those by filtering the whole system on every
operand query is O(system) per query. We instead build, once per pass, a per-variable index mapping
each variable to the items mentioning it, and feed those lookups to `denseByteJustifiedW`. Uncapped
and order-preserving so a lookup returns exactly the same list a `filter (mentions x)` would. -/

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

/-- The operands whose byte-ness *implies* this interaction's acceptance (at any multiplicity):
    the checked operands of any fold-recognized shape, packed pair included (`denseByteShape?`);
    `none` otherwise. -/
def denseByteCheckOperands? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (List (DenseExpr p)) :=
  (denseByteShape? denseCmpFolded bs facts bi).map fun (sh, _, o1, o2) => sh.operands o1 o2

/-- The justification base: the interactions this pass can never drop (not recognized as byte
    checks). Justifying only against these makes the drop non-circular. -/
def denseByteDropBase (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseByteCheckOperands? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized byte check whose operands are all byte-justified through the
    prebuilt per-variable indexes `domCs`/`candsOf` (constraints) and `wits` (base interactions).
    Consumes `denseByteJustifiedW`, so the O(system) per-operand scans in `denseByteJustified` become
    per-variable bucket lookups. -/
def denseByteDropKeepW (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (candsOf : VarId → List (DenseExpr p))
    (wits : VarId → List (BusInteraction (DenseExpr p)))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseByteCheckOperands? bs facts bi with
  | some ops =>
    !(ops.all (fun e =>
      denseByteJustifiedW 256 pw.isPrime domCs candsOf bs facts wits (fun _ => []) e))
  | none => true

/-- Drops a byte-check interaction when all its operands are already proven to be bytes elsewhere —
    from the constraints and the un-droppable base interactions — so the check is redundant
    (`denseRedundantByteDropPass`). The domain/candidate/witness structures are built once per
    invocation (per-variable bucket indexes) and shared across every operand query. -/
def denseRedundantByteDropF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let base := denseByteDropBase bs facts d
  let domCs := d.algebraicConstraints.filter DenseExpr.isSingleVar
  let candsIdx := denseVarBucket DenseExpr.vars d.algebraicConstraints
  let witsIdx := denseVarBucket denseBIVars base
  d.filterBus (denseByteDropKeepW pw bs facts domCs
    (denseVarBucketLookup candsIdx) (denseVarBucketLookup witsIdx))

end ApcOptimizer.Dense
