import ApcOptimizer.Implementation.Dense.AddrDiseq
import ApcOptimizer.Implementation.Dense.Dedup
import ApcOptimizer.Implementation.Dense.DropPasses

set_option autoImplicit false

/-! # Dense unified consecutive-match bus unification (Task 3, busUnify cluster, chunk M2 — impl)

Dense, `VarId`-native transliteration of `OptimizerPasses/BusUnify.lean`'s **runtime** definitions
(`Expression.structHash`, `addrConstsNeq`, `checkPair`, `SplitCand`, `findConsumer`,
`candidateSplits`, `collectForBus`, `collectAllBuses`, `busUnifyPass`). This file is **impl-only**:
no theorem/lemma from the spec file is ported, and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper
is built here — the top-level transform `denseBusUnifyF` is shaped exactly like the `denseF`
argument `DenseVerifiedPassW.ofNative` (`Dense/Bridge.lean`) expects, so the prover wraps it
directly.

Three notes on how spec pieces map here:

* **`structHash` reuse.** The spec `Expression.structHash` and `Dense/Dedup.lean`'s
  `DenseExpr.bHash` already have the *identical* recursion structure (`mixHash 11/13/17/19` on
  `const`/`var`/`add`/`mul`); the only difference is the leaf case, which hashes the `VarId`
  directly instead of a `Variable`'s `(name, powdrId?)` pair. Since this hash only gates a
  bucket-dedup prefilter ahead of an exact structural check (hash values may legitimately differ
  from the spec's), reusing `DenseExpr.bHash` as-is is a direct reuse, not a re-derivation — no new
  `structHash` def is introduced.
* **MemoryUnify companions.** `checkPair`/`findConsumer`/`memEqConstraints`'s ingredients
  `eqExpr`/`multConst`/`addrConstsEq` are owned by `OptimizerPasses/MemoryUnify.lean`, which has no
  dense port yet (only its `BoundsMap` machinery has been mirrored piecemeal, inside
  `Dense/DigitFold.lean`, for a different pass). They are transliterated locally below (`denseEqExpr`
  /`denseMultConst`/`denseAddrConstsEq`/`denseMemEqConstraints`) as the minimal slice `busUnify`
  needs; a future dense `MemoryUnify`/`busPairCancel` port should reuse these, not re-derive them.
* **Proof-witness drops.** Every spec `dif`/`Subtype` that exists only to carry a witness back to
  `checkPair_sound`/`collectForBus`'s own subtype proof (the split-equation proofs in `SplitCand`/
  `findConsumer`/`candidateSplits`, and the `cs`/`bs`/`hp1`/`hshape` threading in `collectForBus`
  that is otherwise unused by its computed value) is dropped, keeping the identical decidable
  condition/control flow as a plain `if`/plain data shape — the M1 (`Dense/AddrDiseq.lean`)
  precedent. `collectAllBuses` keeps `facts` because it makes a *real* runtime call
  (`facts.memShape busId`) that decides which candidates get enumerated at all. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## MemoryUnify companions (the minimal slice `busUnify` needs) -/

/-- `e₂ - e₁` as a dense expression. Mirrors `eqExpr` (`OptimizerPasses/MemoryUnify.lean`). -/
def denseEqExpr (e2 e1 : DenseExpr p) : DenseExpr p := .add e2 (.mul (.const (-1)) e1)

/-- Constant multiplicity of a dense interaction. Mirrors `multConst`. -/
def denseMultConst (bi : BusInteraction (DenseExpr p)) : Option (ZMod p) :=
  bi.multiplicity.constValue?

/-- Do the two sends carry equal constant address entries? Mirrors `addrConstsEq`. -/
def denseAddrConstsEq (shape : MemoryBusShape) (S S' : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.all (fun slot =>
    match S.payload[slot]?, S'.payload[slot]? with
    | some e, some e' =>
      decide (e = e') ||
      (match e.constValue?, e'.constValue? with
       | some c, some c' => c = c'
       | _, _ => false)
    | _, _ => false)

/-- The entailed conclusions: slot-wise equality of the receive's and the send's payloads,
    excluding the (constant, already-equal) address slots. Mirrors `memEqConstraints`. -/
def denseMemEqConstraints (shape : MemoryBusShape) (S Rt : BusInteraction (DenseExpr p)) :
    List (DenseExpr p) :=
  ((List.range S.payload.length).filter (fun i => decide (i ∉ shape.addressFields))).map
    (fun i => denseEqExpr ((Rt.payload[i]?).getD (.const 0)) ((S.payload[i]?).getD (.const 0)))

/-! ## Address inequality (companion to `denseAddrConstsEq`) -/

/-- Some address slot carries provably-different constants: the two interactions provably have
    different addresses. Mirrors `addrConstsNeq`. -/
def denseAddrConstsNeq (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' =>
      (match e.constValue?, e'.constValue? with
       | some c, some c' => decide (c ≠ c')
       | _, _ => false)
    | _, _ => false)

/-! ## The checked pair -/

/-- A checked consecutive send→receive pair on bus `busId`: `S` a constant send, `R` a constant
    receive, same constant address, and every `mid` message provably inactive or of a different
    address. Mirrors `checkPair`; the split equation the enumerator (`denseCandidateSplits`)
    produces by construction is no longer carried (no proof to re-verify it against). -/
def denseCheckPair (shape : MemoryBusShape) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (S : BusInteraction (DenseExpr p))
    (mid : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p)) : Bool :=
  decide (denseMultConst S = some shape.setNewMult) &&
    decide (denseMultConst R = some (-shape.setNewMult)) &&
  denseAddrConstsEq shape S R &&
  mid.all (fun m => denseAddrConstsNeq shape S m || denseAddrAffineNeq shape S m
    || denseAddrTwoRootNeq shape T S m || denseAddrNonzeroNeq shape nw S m
    || decide (denseMultConst m = some 0))

/-! ## The pass -/

/-- One `(pre, S, mid, R, post)` candidate (data only — mirrors `SplitCand`, dropping the
    list-recomposition proof `L = pre ++ S :: mid ++ R :: post`; that proof is over data, not a
    wrapped closure, so the dense enumerator just returns the plain tuple). -/
abbrev DenseSplitCand (p : ℕ) :=
  List (BusInteraction (DenseExpr p)) × BusInteraction (DenseExpr p)
    × List (BusInteraction (DenseExpr p)) × BusInteraction (DenseExpr p)
    × List (BusInteraction (DenseExpr p))

/-- Scan forward from a send `S` for its consumer: the first same-address receive, with every
    message before it excludable (different address, or inactive). Returns `(mid, R, post)` on
    success, `none` if a possibly-same-address active non-receive blocks the window. Mirrors
    `findConsumer`, dropping the recomposition-proof `Subtype` it returned. -/
def denseFindConsumer (shape : MemoryBusShape) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (S : BusInteraction (DenseExpr p)) :
    (revMid rest : List (BusInteraction (DenseExpr p))) →
    Option (List (BusInteraction (DenseExpr p)) × BusInteraction (DenseExpr p)
      × List (BusInteraction (DenseExpr p)))
  | _, [] => none
  | revMid, r :: rest =>
      if decide (denseMultConst r = some (-shape.setNewMult)) && denseAddrConstsEq shape S r then
        some (revMid.reverse, r, rest)
      else if denseAddrConstsNeq shape S r || denseAddrAffineNeq shape S r
          || denseAddrTwoRootNeq shape T S r || denseAddrNonzeroNeq shape nw S r
          || decide (denseMultConst r = some 0) then
        denseFindConsumer shape T nw S (r :: revMid) rest
      else none

/-- One candidate per active send `S`, pairing it with its consumer receive (`denseFindConsumer`).
    Linear in the number of sends × scan length, so no O(n²) blow-up on large buses. Mirrors
    `candidateSplits`, dropping the whole-list `L`/`hinv` parameters (proof-only: they existed only
    to state the split equation `SplitCand` carried). -/
def denseCandidateSplits (shape : MemoryBusShape) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p) :
    (revPre rest : List (BusInteraction (DenseExpr p))) → List (DenseSplitCand p)
  | _, [] => []
  | revPre, S :: rest =>
      (if decide (denseMultConst S = some shape.setNewMult) then
        match denseFindConsumer shape T nw S [] rest with
        | some (mid, R, post) => [(revPre.reverse, S, mid, R, post)]
        | none => []
       else []) ++ denseCandidateSplits shape T nw (S :: revPre) rest

/-- Collect the entailed equalities for one bus. Mirrors `collectForBus`, dropping its
    `cs`/`bs`/`facts`/`hp1`/`hshape` parameters: none of them are read by the computed value (only
    by the subtype proof `collectForBus` carried), so `shape`/`T`/`nw`/the candidate list are all
    that remain. `pre`/`post` are similarly proof-only in the spec (only used inside its `by`
    block, via `checkPair_sound`), so they are discarded here too. -/
def denseCollectForBus (shape : MemoryBusShape) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p) :
    List (DenseSplitCand p) → List (DenseExpr p)
  | [] => []
  | (_pre, S, mid, R, _post) :: rest =>
    let acc := denseCollectForBus shape T nw rest
    if denseCheckPair shape T nw S mid R = true then
      denseMemEqConstraints shape S R ++ acc
    else acc

/-- Collect over every declared bus. Mirrors `collectAllBuses`, dropping the proof-only `hp1`; it
    keeps `facts` (unlike `denseCollectForBus`), since `facts.memShape busId` is a real runtime call
    here that decides whether — and with what `shape` — a bus's candidates get enumerated at all. -/
def denseCollectAllBuses (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p) :
    List Nat → List (DenseExpr p)
  | [] => []
  | busId :: rest =>
    let acc := denseCollectAllBuses d bs facts T nw rest
    match facts.memShape busId with
    | some shape =>
      let eqs := denseCollectForBus shape T nw
        (denseCandidateSplits shape T nw [] (d.busInteractions.filter (fun bi => bi.busId = busId)))
      eqs ++ acc
    | none => acc

/-- The unified bus-unification pass's runtime transform: add the entailed consecutive
    send→receive slot equalities for every declared memory / execution-bridge bus (skipping
    equations already present or trivially zero). Mirrors `busUnifyPass`'s computed output
    (dropping its `PassCorrect` term); shaped as `(bs) → (facts) → (d) → out`, matching the `denseF`
    argument `DenseVerifiedPassW.ofNative` expects (`Dense/Bridge.lean`), so the prover can wrap it
    directly (with `fun _ _ _ => ([] : DenseDerivations p)` for the no-derivations side). -/
def denseBusUnifyF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    -- precompute the per-variable two-root data once (memoized `denseTwoRootOf?`), so the
    -- address-disequality certificate is a constant-time hash lookup per candidate pair
    let T := DenseTwoRootMap.build d.algebraicConstraints
    -- reciprocal (nonzero-witness) forms, for the register-vs-RAM address-disequality certificate
    let nw := DenseNonzeroWits.build d.algebraicConstraints
    let eqs := denseCollectAllBuses d bs facts T nw
      ((d.busInteractions.map (fun bi => bi.busId)).dedup)
    -- keep only equalities over existing columns, so the pass introduces no new variable
    let dVarSet := Std.HashSet.ofList d.occ
    -- the already-present test is a per-equality deep structural scan; bucket the constraints by
    -- structural hash once (reusing `DenseExpr.bHash`) and compare within the bucket
    let dHashes : Std.HashMap UInt64 (List (DenseExpr p)) :=
      d.algebraicConstraints.foldl (fun m c =>
        let h := c.bHash
        m.insert h (c :: m.getD h [])) ∅
    let containsC : DenseExpr p → Bool := fun c =>
      (dHashes.getD c.bHash []).any (fun c' => c' == c)
    let new := eqs.filter
      (fun c => !c.normalize.fold.isConstZero && !containsC c
        && c.vars.all (fun z => dVarSet.contains z))
    if new.isEmpty then d
    else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
