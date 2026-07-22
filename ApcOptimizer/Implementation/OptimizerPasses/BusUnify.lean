import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses

set_option autoImplicit false

/-! # Dense unified consecutive-match bus unification (Task 3, busUnify cluster, chunk M2 — impl)

Dense, `VarId`-native transliteration of `OptimizerPasses/BusUnify.lean`'s **runtime** definitions
(`Expression.structHash`, `addrConstsNeq`, `checkPair`, `SplitCand`, `findConsumer`,
`candidateSplits`, `collectForBus`, `collectAllBuses`, `busUnifyPass`). This file is **impl-only**:
no theorem/lemma from the spec file is ported, and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper
is built here — the top-level transform `denseBusUnifyF` is shaped exactly like the `denseF`
argument `DenseVerifiedPassW.of` (`Dense/Bridge.lean`) expects, so the prover wraps it
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
    address. Mirrors `checkPair`; the split equation the enumerator (`denseCandidateSplitsSweep`)
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

/-! ## The consumer sweep (#165 delta, chunk C1)

Dense, `VarId`-native mirror of the single-sweep consumer-finding infra that replaced the per-send
`findConsumer` scan (`OptimizerPasses/BusUnify.lean:230-436`, doc comment there for the full
rationale). This is the enumerator `denseCollectAllBuses` now consumes (the old per-send
`findConsumer`/`candidateSplits` transliterations were deleted with the #165 flip).

Every spec proof witness that exists only to state the split equation the enumerator recovers
(`OpenRec.hi`/`hsplit`, `SplitCand`'s `Subtype` proof, `sweepGo`'s `hsplit`/`hj`, `emitCand`'s
`hj`/`hnow`) is dropped, matching the plain-data `DenseSplitCand`/dropped-`Subtype` pattern: the
runtime control flow and position arithmetic are otherwise identical. -/

/-- One message tested against one open window. Mirrors `StepRes`. -/
inductive DenseStepRes
  | consumer
  | excluded
  | blocker

/-- The two-root / nonzero-witness certificate tables are passed as `Thunk`s so an invocation that
    never reaches the expensive arms (every pair decided by the constant or affine certificate — the
    common case) never builds them. Mirrors `stepTest`, using the same certificate calls and call
    order (`denseCheckPair`'s `mid` arms) that `denseCheckPair` re-verifies. -/
def denseStepTest (shape : MemoryBusShape) (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p))
    (S m : BusInteraction (DenseExpr p)) : DenseStepRes :=
  if decide (denseMultConst m = some (-shape.setNewMult)) && denseAddrConstsEq shape S m then .consumer
  else if denseAddrConstsNeq shape S m || denseAddrAffineNeq shape S m
      || denseAddrTwoRootNeq shape T.get S m || denseAddrNonzeroNeq shape nw.get S m
      || decide (denseMultConst m = some 0) then .excluded
  else .blocker

/-- A canonical address key. Mirrors `AddrKey`. -/
structure DenseAddrKey (p : ℕ) where
  exprs : List (DenseExpr p)
deriving DecidableEq

instance : Hashable (DenseAddrKey p) :=
  ⟨fun k => k.exprs.foldl (fun h e => mixHash h e.bHash) 7⟩

/-- The canonical key of an interaction's address slots, `none` if a slot is missing (such a message
    never `denseAddrConstsEq`-matches anything, so it can neither open a window nor consume one).
    Mirrors `addrKey?`. -/
def denseAddrKey? (shape : MemoryBusShape) (bi : BusInteraction (DenseExpr p)) :
    Option (DenseAddrKey p) :=
  (shape.addressFields.foldr (fun slot acc =>
    match acc, bi.payload[slot]? with
    | some ks, some e =>
      match e.constValue? with
      | some c => some (.const c :: ks)
      | none => some (e :: ks)
    | _, _ => none) (some [])).map DenseAddrKey.mk

/-- Whether every component of a canonical key is a literal constant. Mirrors `AddrKey.allConst`. -/
def DenseAddrKey.allConst (k : DenseAddrKey p) : Bool :=
  k.exprs.all fun e => match e with
    | .const _ => true
    | _ => false

/-- An open send window: the send, its split context, and its position `i` (data only — mirrors
    `OpenRec`, dropping its `hi`/`hsplit` proof fields and its list-index parameter `L`; the prover
    reconstructs the split-equation invariant externally, as with `DenseSplitCand` above). -/
structure DenseOpenRec (p : ℕ) where
  revPre : List (BusInteraction (DenseExpr p))
  S : BusInteraction (DenseExpr p)
  restAfter : List (BusInteraction (DenseExpr p))
  i : Nat

/-- Assemble the split candidate for a consumed window, tagged with its send position. `mid` is
    recovered positionally from the send's stored suffix (`take (j−i−1)`), the identical position
    arithmetic `emitCand`/`split_of_positions` compute — only the recomposition-proof witness is
    dropped, guarded by the same `w.i < j` test as a plain `if` (not the spec's proof-extracting
    `dif`). Mirrors `emitCand`. -/
def denseEmitCand (w : DenseOpenRec p) (j : Nat) (R : BusInteraction (DenseExpr p))
    (post : List (BusInteraction (DenseExpr p))) : Option (Nat × DenseSplitCand p) :=
  if w.i < j then
    some (w.i, (w.revPre.reverse, w.S, w.restAfter.take (j - w.i - 1), R, post))
  else none

/-- The sweep: one pass over the bus's interaction list, windows keyed as described above. `acc`
    collects `(sendPosition, candidate)` pairs (order restored by the caller's sort). Mirrors
    `sweepGo`, dropping its `L`/`hsplit`/`hj` proof-only parameters; the `j` position counter and
    `acc` are kept as plain data, and every phase's control flow, binder shape, and evaluation order
    matches the spec verbatim. -/
def denseSweepGo (shape : MemoryBusShape) (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p)) :
    (revSeen rest : List (BusInteraction (DenseExpr p))) → (j : Nat) →
    (constOpen : Std.HashMap (DenseAddrKey p) (DenseOpenRec p)) →
    (symOpen : List (DenseOpenRec p)) →
    (acc : List (Nat × DenseSplitCand p)) →
    List (Nat × DenseSplitCand p)
  | _, [], _, _, _, acc => acc
  | revSeen, m :: rest', j, constOpen, symOpen, acc =>
    let mKey? := denseAddrKey? shape m
    let mAllConst := match mKey? with
      | some k => k.allConst
      | none => false
    -- (1) constant-keyed windows: an all-constant message only meets the window at its own key
    --     (it is `denseAddrConstsNeq`-excluded at every other constant key); a symbolic-address
    --     message meets every one.
    let (constOpen, acc) :=
      if mAllConst then
        match mKey? with
        | some k =>
          match constOpen[k]? with
          | some w =>
            match denseStepTest shape T nw w.S m with
            | .consumer =>
              (constOpen.erase k,
               match denseEmitCand w j m rest' with
               | some c => c :: acc
               | none => acc)
            | .excluded => (constOpen, acc)
            | .blocker => (constOpen.erase k, acc)
          | none => (constOpen, acc)
        | none => (constOpen, acc)
      else
        let (drops, acc) := constOpen.toList.foldl (init := (([] : List (DenseAddrKey p)), acc))
          fun (ds, a) kw =>
            match denseStepTest shape T nw kw.2.S m with
            | .consumer =>
              (kw.1 :: ds,
               match denseEmitCand kw.2 j m rest' with
               | some c => c :: a
               | none => a)
            | .excluded => (ds, a)
            | .blocker => (kw.1 :: ds, a)
        (drops.foldl (·.erase ·) constOpen, acc)
    -- (2) symbolic-keyed windows are tested literally against every message.
    let (symOpen, acc) :=
      if symOpen.isEmpty then (symOpen, acc) else
      symOpen.foldr (init := (([] : List (DenseOpenRec p)), acc)) fun w (so, a) =>
        match denseStepTest shape T nw w.S m with
        | .consumer =>
          (so,
           match denseEmitCand w j m rest' with
           | some c => c :: a
           | none => a)
        | .excluded => (w :: so, a)
        | .blocker => (so, a)
    -- (3) a send opens its window. A same-key window that survived (1) as *excluded* moves to
    --     the literally-tested side list, so no window the per-send scans had is lost.
    let (constOpen, symOpen) :=
      if decide (denseMultConst m = some shape.setNewMult) then
        match mKey? with
        | some k =>
          let w : DenseOpenRec p := ⟨revSeen, m, rest', j⟩
          if k.allConst then
            match constOpen[k]? with
            | some old => (constOpen.insert k w, old :: symOpen)
            | none => (constOpen.insert k w, symOpen)
          else (constOpen, w :: symOpen)
        | none => (constOpen, symOpen)
      else (constOpen, symOpen)
    denseSweepGo shape T nw (m :: revSeen) rest' (j + 1) constOpen symOpen acc

/-- All consumer candidates of one bus, in send-position order — the same list a per-send
    forward scan would produce, computed by a single sweep. Mirrors the new spec `candidateSplits`.
    Consumed by `denseCollectAllBuses` below. -/
def denseCandidateSplitsSweep (shape : MemoryBusShape) (T : Thunk (DenseTwoRootMap p))
    (nw : Thunk (DenseNonzeroWits p)) (L : List (BusInteraction (DenseExpr p))) :
    List (DenseSplitCand p) :=
  ((denseSweepGo shape T nw [] L 0 ∅ [] []).mergeSort
    (fun a b => decide (a.1 ≤ b.1))).map (·.2)

/-- Collect the entailed equalities for one bus. Mirrors `collectForBus`, dropping its
    `cs`/`bs`/`facts`/`hp1`/`hshape` parameters: none of them are read by the computed value (only
    by the subtype proof `collectForBus` carried), so `shape`/`T`/`nw`/the candidate list are all
    that remain. `pre`/`post` are similarly proof-only in the spec (only used inside its `by`
    block, via `checkPair_sound`), so they are discarded here too. The certificate tables are
    `Thunk`s (as in the spec), forced only at the `denseCheckPair … T.get nw.get` call. -/
def denseCollectForBus (shape : MemoryBusShape) (T : Thunk (DenseTwoRootMap p))
    (nw : Thunk (DenseNonzeroWits p)) :
    List (DenseSplitCand p) → List (DenseExpr p)
  | [] => []
  | (_pre, S, mid, R, _post) :: rest =>
    let acc := denseCollectForBus shape T nw rest
    if denseCheckPair shape T.get nw.get S mid R = true then
      denseMemEqConstraints shape S R ++ acc
    else acc

/-- Collect over every declared bus. Mirrors `collectAllBuses`, dropping the proof-only `hp1`; it
    keeps `facts` (unlike `denseCollectForBus`), since `facts.memShape busId` is a real runtime call
    here that decides whether — and with what `shape` — a bus's candidates get enumerated at all.
    Candidates come from the single-sweep `denseCandidateSplitsSweep` (the #165 flip). -/
def denseCollectAllBuses (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p)) :
    List Nat → List (DenseExpr p)
  | [] => []
  | busId :: rest =>
    let acc := denseCollectAllBuses d bs facts T nw rest
    match facts.memShape busId with
    | some shape =>
      let eqs := denseCollectForBus shape T nw
        (denseCandidateSplitsSweep shape T nw (d.busInteractions.filter (fun bi => bi.busId = busId)))
      eqs ++ acc
    | none => acc

/-- The unified bus-unification pass's runtime transform: add the entailed consecutive
    send→receive slot equalities for every declared memory / execution-bridge bus (skipping
    equations already present or trivially zero). Mirrors `busUnifyPass`'s computed output
    (dropping its `PassCorrect` term); shaped as `(bs) → (facts) → (d) → out`, matching the `denseF`
    argument `DenseVerifiedPassW.of` expects (`Dense/Bridge.lean`), so the prover can wrap it
    directly (with `fun _ _ _ => ([] : DenseDerivations p)` for the no-derivations side). -/
def denseBusUnifyF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    -- the per-variable two-root data and the reciprocal nonzero-witness forms back the two
    -- expensive address-disequality certificates. Both are `Thunk`ed (as in the spec): they are
    -- built only if some window test reaches those arms — an invocation whose pairs are all decided
    -- by the constant/affine certificates never pays the builds.
    let T : Thunk (DenseTwoRootMap p) :=
      Thunk.mk fun _ => DenseTwoRootMap.build d.algebraicConstraints
    let nw : Thunk (DenseNonzeroWits p) :=
      Thunk.mk fun _ => DenseNonzeroWits.build d.algebraicConstraints
    let eqs := denseCollectAllBuses d bs facts T nw
      ((d.busInteractions.map (fun bi => bi.busId)).dedup)
    -- Nothing collected (the common late-cycle case): skip the filter-table build outright.
    if eqs.isEmpty then d
    else
      -- The "no new variable" side condition holds **by construction** — every equality's variables
      -- come from payload slots of `d`'s own interactions (`denseMemEqConstraints_vars`, carried
      -- through `denseCollectAllBuses_vars`) — so the old per-variable membership scan over the
      -- whole occurrence list is gone, with the filter provably unchanged.
      -- The already-present test is a per-equality deep structural scan; bucket the constraints by
      -- structural hash once (reusing `DenseExpr.bHash`) and compare within the bucket.
      let dHashes : Std.HashMap UInt64 (List (DenseExpr p)) :=
        d.algebraicConstraints.foldl (fun m c =>
          let h := c.bHash
          m.insert h (c :: m.getD h [])) ∅
      let containsC : DenseExpr p → Bool := fun c =>
        (dHashes.getD c.bHash []).any (fun c' => c' == c)
      let new := eqs.filter
        (fun c => !c.normalize.fold.isConstZero && !containsC c)
      if new.isEmpty then d
      else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
