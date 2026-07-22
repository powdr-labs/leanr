import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify

set_option autoImplicit false

/-! # Hash index and entailed-equality maps for `busPairCancel`

Per-invocation hash-indexing and entailed-equality machinery for `busPairCancel`:
`densePayloadHash`/`denseAddrHash`/`denseRecvIndexAll` (the once-per-invocation receive-candidate
hash index), `DenseVarCsIdx` (the per-variable candidate-constraint index), `DenseEqConstraintMap`
(the normalized-constraint hash index), and `densePayloadEntailedEq` (the `Thunk`-forced slot-wise
entailed-equality check they feed). This file is **impl-only**: `DenseVarCsIdx` and
`DenseEqConstraintMap` are plain `Std.HashMap`-wrapping structures; no soundness lemma is stated
here (that lives in `BusPairCancelIndexProof.lean`).

## Reuse

* `DenseExpr.bHash` (`Dedup.lean`) is the structural hash (`mixHash 11/13/17/19` recursion, a
  `VarId` leaf) used unqualified for `densePayloadHash`/`denseAddrHash`/`DenseEqConstraintMap`'s
  bucket key — no new hash function is introduced.
* `denseMultConst` (`BusUnify.lean`, itself `bi.multiplicity.constValue?`) is reused unqualified in
  `denseRecvIndexAll`.
* `DenseExpr.normalize` (`Normalize.lean`) is reused unqualified in
  `DenseEqConstraintMap.addAll`/`densePayloadEntailedEq`.
* `maxDeepConstraints` (`SearchBudgets.lean`) is a plain `Nat` literal, reused unqualified.
* `denseEqExpr` (`BusUnify.lean`) computes `e - e'`; `densePayloadEntailedEq` below calls it for
  every slot-wise difference it checks.

## Fold-direction fidelity (`denseRecvIndexAll`) — load-bearing

`denseRecvIndexAll` folds `arr.toList.zipIdx` with `List.foldr`, and each step *prepends* the
current index onto whatever bucket already holds (`m.insert h (bij.2 :: m.getD h [])`). Under
`foldr`, the rightmost (highest-index) element is folded first against the empty map (innermost
application), and each subsequent, lower-index step prepends its own index in front of what the
higher indices already produced — so the final bucket lists hold **ascending** positions.
`firstMatchAt` (elsewhere) picks the first `i < j` match by scanning a bucket in list order, so this
ascending order is behavior, not incidental: flipping to `foldl` would silently reverse bucket
order.

## `Thunk` forcing fidelity (`densePayloadEntailedEq`)

`M` (the `EqConstraintMap`, a `Thunk`) is forced only when the first `||` disjunct
(`decide (e = e')`, plain syntactic equality) is `false` — Lean's `||`/`&&` on `Bool` are
short-circuiting, so a fully syntactically-identical payload pair never evaluates `M.get` at all.
`densePayloadEntailedEq` keeps that exact `Bool`/`Thunk` shape and disjunct order
(`decide (e = e') || M.get.test … || M.get.test …`), so the short-circuit/forcing discipline
matters: `M` is never `.get`-projected to a plain value ahead of the disjunction, and no branch is
reordered. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ### Hash-indexed receive lookup -/

/-- Structural hash of a payload (order-sensitive). -/
def densePayloadHash (pl : List (DenseExpr p)) : UInt64 :=
  pl.foldl (fun h e => mixHash h e.bHash) 7

/-- Structural hash of the address slots of a payload (order-sensitive over
    `shape.addressFields`) — the receive-index key for entailed payload matching: value slots may
    differ syntactically, addresses must not. -/
def denseAddrHash (shape : MemoryBusShape) (pl : List (DenseExpr p)) : UInt64 :=
  shape.addressFields.foldl (fun h slot => mixHash h ((pl[slot]?).elim 5 DenseExpr.bHash)) 7

/-- Positions (ascending — see the module header) of the candidate receives (the `getPrevious`,
    multiplicity `-shape.setNewMult`) on **every** memory-shaped bus, keyed by the bus id mixed
    with the payload hash — one build serves the whole sweep. In the cycle (`aggressive = false`)
    the payload part of the key is the exact payload hash; in the coda (`aggressive = true`) it is
    the address-slot hash `denseAddrHash`. -/
def denseRecvIndexAll {bs : BusSemantics p} (facts : BusFacts p bs) (aggressive : Bool)
    (arr : Array (BusInteraction (DenseExpr p))) :
    Std.HashMap UInt64 (List Nat) :=
  (arr.toList.zipIdx).foldr (fun bij m =>
    match facts.memShape bij.1.busId with
    | some shape =>
      if decide (denseMultConst bij.1 = some (-shape.setNewMult)) then
        let h := mixHash (hash bij.1.busId)
          (if aggressive then denseAddrHash shape bij.1.payload else densePayloadHash bij.1.payload)
        m.insert h (bij.2 :: m.getD h [])
      else m
    | none => m) ∅

/-! ### The per-invocation candidate-constraint index -/

/-- A per-variable candidate-constraint index: for each variable, the constraints (in traversal
    order) known to mention it. Plain data — no soundness field. -/
structure DenseVarCsIdx (p : ℕ) where
  map : Std.HashMap VarId (List (DenseExpr p))

namespace DenseVarCsIdx

/-- The empty index. -/
def empty : DenseVarCsIdx p where
  map := ∅

/-- Append `c` at the end of `x`'s bucket (so buckets stay in traversal order), capped at
    `maxDeepConstraints`. -/
def insertC (I : DenseVarCsIdx p) (x : VarId) (c : DenseExpr p) : DenseVarCsIdx p :=
  match I.map[x]? with
  | none => { map := I.map.insert x [c] }
  | some old =>
    if old.length < maxDeepConstraints then { map := I.map.insert x (old ++ [c]) }
    else I

/-- Record `c` under each of its variables. -/
def addConstraint (I : DenseVarCsIdx p) (c : DenseExpr p) : DenseVarCsIdx p :=
  c.vars.dedup.foldl (fun I x => I.insertC x c) I

/-- Fold `addConstraint` over a constraint list. -/
def addAll : DenseVarCsIdx p → List (DenseExpr p) → DenseVarCsIdx p
  | I, [] => I
  | I, c :: rest => addAll (I.addConstraint c) rest

/-- Build the index from scratch. -/
def build (constraints : List (DenseExpr p)) : DenseVarCsIdx p :=
  addAll empty constraints

/-- The constraints recorded under `x`. -/
def lookup (I : DenseVarCsIdx p) (x : VarId) : List (DenseExpr p) :=
  (I.map[x]?).getD []

end DenseVarCsIdx

/-! ### Constraint-entailed payload matching -/

/-- A hash index of normalized constraints, bucketed by `DenseExpr.bHash` of the *normalized*
    form. Plain data — no soundness field. -/
structure DenseEqConstraintMap (p : ℕ) where
  map : Std.HashMap UInt64 (List (DenseExpr p))

namespace DenseEqConstraintMap

/-- The empty map. -/
def empty : DenseEqConstraintMap p where
  map := ∅

/-- Prepend a normalized form to its hash bucket. -/
def insertNorm (M : DenseEqConstraintMap p) (n : DenseExpr p) : DenseEqConstraintMap p where
  map := M.map.insert n.bHash (n :: (M.map[n.bHash]?).getD [])

/-- Fold the normalizations of `pending` into the map. -/
def addAll : DenseEqConstraintMap p → List (DenseExpr p) → DenseEqConstraintMap p
  | M, [] => M
  | M, c :: rest => addAll (M.insertNorm c.normalize) rest

/-- Build the map for a constraint list. -/
def build (constraints : List (DenseExpr p)) : DenseEqConstraintMap p :=
  addAll empty constraints

/-- Is (the normalized) `d` one of the normalized constraints? -/
def test (M : DenseEqConstraintMap p) (d : DenseExpr p) : Bool :=
  match M.map[d.bHash]? with
  | some ns => ns.any (fun n => decide (n = d))
  | none => false

end DenseEqConstraintMap

/-! ### Constraint-entailed payload matching (the `Thunk`-forced check) -/

/-- Slot-wise payload match with the entailed-equality escape hatch: each slot pair is
    syntactically equal, or its (normalized) difference — in either orientation — is a normalized
    constraint. `M` (a `Thunk`) is forced only at the first syntactic mismatch (see the module
    header). -/
def densePayloadEntailedEq (M : Thunk (DenseEqConstraintMap p)) :
    List (DenseExpr p) → List (DenseExpr p) → Bool
  | [], [] => true
  | e :: es, e' :: es' =>
    (decide (e = e') || M.get.test (denseEqExpr e e').normalize
      || M.get.test (denseEqExpr e' e).normalize) && densePayloadEntailedEq M es es'
  | _, _ => false

end ApcOptimizer.Dense
