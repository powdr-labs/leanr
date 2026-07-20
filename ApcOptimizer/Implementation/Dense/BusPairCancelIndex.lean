import ApcOptimizer.Implementation.Dense.BusPairCancelJustify
import ApcOptimizer.Implementation.Dense.BusUnifyNative

set_option autoImplicit false

/-! # Dense hash index + entailed-equality maps for `busPairCancel` (Task 3, chunk C3 — impl)

Dense, `VarId`-native transliteration of the per-invocation hash-indexing and entailed-equality
machinery of `OptimizerPasses/BusPairCancel.lean` (:1214-1489): `payloadHash`/`addrHash`/
`recvIndexAll` (the once-per-invocation receive-candidate hash index), `VarCsIdx` (the
per-variable candidate-constraint index), `EqConstraintMap` (the normalized-constraint hash
index), and `payloadEntailedEq` (the `Thunk`-forced slot-wise entailed-equality check they feed).
This file is **impl-only**: the proof-carrying spec structures (`VarCsIdx`, `EqConstraintMap`)
become plain `Std.HashMap`-wrapping structures with their `sound` fields (and the `constraints`
index parameter that exists only to state `sound`) dropped; no `lookup_mem`/`test_sound`/
`payloadEntailedEq_sound` lemma is ported.

## Reuse map (not re-derived)

* `Expression.structHash` (`BusUnify.lean:14`) → `DenseExpr.bHash` (`Dense/Dedup.lean:241`),
  already established as the dense structural-hash mirror (identical `mixHash 11/13/17/19`
  recursion, a `VarId` leaf instead of a `Variable`'s `(name, powdrId?)` pair) by
  `Dense/BusUnifyNative.lean`'s own header. Reused unqualified here for `densePayloadHash`/
  `denseAddrHash`/`DenseEqConstraintMap`'s bucket key — no new hash function is introduced.
* `multConst` (`MemoryUnify.lean:300`) → `denseMultConst` (`Dense/BusUnifyNative.lean:50`, itself
  `bi.multiplicity.constValue?`), reused unqualified in `denseRecvIndexAll`.
* `Expression.normalize` (`Normalize.lean:306`) → `DenseExpr.normalize` (`Dense/Normalize.lean:47`,
  already ported and wired for the `normalize` cleanup pass), reused unqualified in
  `DenseEqConstraintMap.addAll`/`densePayloadEntailedEq`.
* `maxDeepConstraints` (`BusPairCancel.lean:57`) is a plain `Nat` literal, reused unqualified —
  same precedent as `BusPairCancelJustify.lean`'s header for `maxDeepPoints`/`maxDeepDomain`/
  `maxDeepVars`.

## Flagged deviation: `diffE` has NO new dense counterpart

`diffE e e' := .add e (.mul (.const (-1)) e')` (`BusPairCancel.lean:1448`) is textually identical
(up to bound-variable names) to `MemoryUnify.eqExpr e2 e1 := .add e2 (.mul (.const (-1)) e1)`
(`MemoryUnify.lean:78`, with `e := e2`, `e' := e1`) — the spec itself duplicates `eqExpr` under a
local name here, exactly as `Expression.containsVar` duplicates `Expression.mentions` (flagged in
the `BusPairCancelJustify.lean` header for the same reason). Its dense mirror `denseEqExpr`
(`Dense/BusUnifyNative.lean:47`) is therefore reused directly: `denseEqExpr e e'` computes exactly
`diffE e e'`. No `denseDiffE` definition is introduced; `densePayloadEntailedEq` below calls
`denseEqExpr` everywhere the spec calls `diffE`.

## Fold-direction fidelity (`denseRecvIndexAll`) — CRITICAL

`recvIndexAll` folds `arr.toList.zipIdx` with `List.foldr`, and each step *prepends* the current
index onto whatever bucket already holds (`m.insert h (bij.2 :: m.getD h [])`). Under `foldr`, the
rightmost (highest-index) element is folded first against the empty map (innermost application),
and each subsequent, lower-index step prepends its own index in front of what the higher indices
already produced — so the final bucket lists hold **ascending** positions. `firstMatchAt` (a later
chunk) picks the first `i < j` match by scanning a bucket in list order, so this ascending order is
behavior, not incidental. `denseRecvIndexAll` below preserves the identical `foldr` + prepend
structure, unqualified, so its buckets are ascending too — flipping to `foldl` (also plausible at
first glance, since both produce *some* hash map) would silently reverse bucket order and is
exactly the kind of divergence this chunk must not introduce.

## `Thunk` forcing fidelity (`densePayloadEntailedEq`)

The spec forces `M.get` (the `EqConstraintMap`) only when the first `||` disjunct
(`decide (e = e')`, plain syntactic equality) is `false` — Lean's `||`/`&&` on `Bool` are
short-circuiting, so a fully syntactically-identical payload pair never evaluates `M.get` at all.
`densePayloadEntailedEq` keeps the exact same `Bool`/`Thunk` shape and disjunct order
(`decide (e = e') || M.get.test … || M.get.test …`), so the short-circuit/forcing discipline
transfers unchanged: `M` is never `.get`-projected to a plain value ahead of the disjunction, and
no branch is reordered. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ### Hash-indexed receive lookup -/

/-- Structural hash of a payload (order-sensitive). Mirrors `payloadHash`
    (`BusPairCancel.lean:1226`). -/
def densePayloadHash (pl : List (DenseExpr p)) : UInt64 :=
  pl.foldl (fun h e => mixHash h e.bHash) 7

/-- Structural hash of the address slots of a payload (order-sensitive over
    `shape.addressFields`) — the receive-index key for entailed payload matching: value slots may
    differ syntactically, addresses must not. Mirrors `addrHash` (`BusPairCancel.lean:1232`). -/
def denseAddrHash (shape : MemoryBusShape) (pl : List (DenseExpr p)) : UInt64 :=
  shape.addressFields.foldl (fun h slot => mixHash h ((pl[slot]?).elim 5 DenseExpr.bHash)) 7

/-- Positions (ascending — see the module header) of the candidate receives (the `getPrevious`,
    multiplicity `-shape.setNewMult`) on **every** memory-shaped bus, keyed by the bus id mixed
    with the payload hash — one build serves the whole sweep. In the cycle (`aggressive = false`)
    the payload part of the key is the exact payload hash; in the coda (`aggressive = true`) it is
    the address-slot hash `denseAddrHash`. Mirrors `recvIndexAll` (`BusPairCancel.lean:1247`). -/
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

/-- Data-only mirror of `VarCsIdx` (`BusPairCancel.lean:1278`): the `sound` proof field is dropped,
    and the `constraints` index parameter (which exists only to state `sound`) is dropped with
    it. -/
structure DenseVarCsIdx (p : ℕ) where
  map : Std.HashMap VarId (List (DenseExpr p))

namespace DenseVarCsIdx

/-- Mirrors `VarCsIdx.empty` (`BusPairCancel.lean:1287`). -/
def empty : DenseVarCsIdx p where
  map := ∅

/-- Append `c` at the end of `x`'s bucket (so buckets stay in traversal order), capped. Mirrors
    `VarCsIdx.insertC` (`BusPairCancel.lean:1295`). -/
def insertC (I : DenseVarCsIdx p) (x : VarId) (c : DenseExpr p) : DenseVarCsIdx p :=
  match I.map[x]? with
  | none => { map := I.map.insert x [c] }
  | some old =>
    if old.length < maxDeepConstraints then { map := I.map.insert x (old ++ [c]) }
    else I

/-- Record `c` under each of its variables. Mirrors `VarCsIdx.addConstraint`
    (`BusPairCancel.lean:1329`). -/
def addConstraint (I : DenseVarCsIdx p) (c : DenseExpr p) : DenseVarCsIdx p :=
  c.vars.dedup.foldl (fun I x => I.insertC x c) I

/-- Mirrors `VarCsIdx.addAll` (`BusPairCancel.lean:1333`). -/
def addAll : DenseVarCsIdx p → List (DenseExpr p) → DenseVarCsIdx p
  | I, [] => I
  | I, c :: rest => addAll (I.addConstraint c) rest

/-- Mirrors `VarCsIdx.build` (`BusPairCancel.lean:1340`). -/
def build (constraints : List (DenseExpr p)) : DenseVarCsIdx p :=
  addAll empty constraints

/-- Mirrors `VarCsIdx.lookup` (`BusPairCancel.lean:1343`). -/
def lookup (I : DenseVarCsIdx p) (x : VarId) : List (DenseExpr p) :=
  (I.map[x]?).getD []

end DenseVarCsIdx

/-! ### Constraint-entailed payload matching -/

/-- Data-only mirror of `EqConstraintMap` (`BusPairCancel.lean:1375`): the `sound` proof field and
    the `constraints` index parameter are dropped. Bucketed by `DenseExpr.bHash` (the established
    `structHash → bHash` mapping — see the module header) of the *normalized* form. -/
structure DenseEqConstraintMap (p : ℕ) where
  map : Std.HashMap UInt64 (List (DenseExpr p))

namespace DenseEqConstraintMap

/-- Mirrors `EqConstraintMap.empty` (`BusPairCancel.lean:1384`). -/
def empty : DenseEqConstraintMap p where
  map := ∅

/-- Prepend a normalized form to its hash bucket. Mirrors `EqConstraintMap.insertNorm`
    (`BusPairCancel.lean:1392`). -/
def insertNorm (M : DenseEqConstraintMap p) (n : DenseExpr p) : DenseEqConstraintMap p where
  map := M.map.insert n.bHash (n :: (M.map[n.bHash]?).getD [])

/-- Fold the normalizations of `pending` into the map. Mirrors `EqConstraintMap.addAll`
    (`BusPairCancel.lean:1413`). -/
def addAll : DenseEqConstraintMap p → List (DenseExpr p) → DenseEqConstraintMap p
  | M, [] => M
  | M, c :: rest => addAll (M.insertNorm c.normalize) rest

/-- Build the map for a constraint list. Mirrors `EqConstraintMap.build`
    (`BusPairCancel.lean:1421`). -/
def build (constraints : List (DenseExpr p)) : DenseEqConstraintMap p :=
  addAll empty constraints

/-- Is (the normalized) `d` one of the normalized constraints? Mirrors `EqConstraintMap.test`
    (`BusPairCancel.lean:1425`). -/
def test (M : DenseEqConstraintMap p) (d : DenseExpr p) : Bool :=
  match M.map[d.bHash]? with
  | some ns => ns.any (fun n => decide (n = d))
  | none => false

end DenseEqConstraintMap

/-! ### Constraint-entailed payload matching (the `Thunk`-forced check) -/

/-- Slot-wise payload match with the entailed-equality escape hatch: each slot pair is
    syntactically equal, or its (normalized) difference — in either orientation — is a normalized
    constraint. `M` (a `Thunk`) is forced only at the first syntactic mismatch (see the module
    header). `diffE`'s dense mirror is `denseEqExpr` — no new definition, see the module header.
    Mirrors `payloadEntailedEq` (`BusPairCancel.lean:1458`). -/
def densePayloadEntailedEq (M : Thunk (DenseEqConstraintMap p)) :
    List (DenseExpr p) → List (DenseExpr p) → Bool
  | [], [] => true
  | e :: es, e' :: es' =>
    (decide (e = e') || M.get.test (denseEqExpr e e').normalize
      || M.get.test (denseEqExpr e' e).normalize) && densePayloadEntailedEq M es es'
  | _, _ => false

end ApcOptimizer.Dense
