import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelIndex

set_option autoImplicit false

/-! # Dense region tests + emitted-check acceptance for `busPairCancel` (Task 3, chunk C5 — impl)

Dense, `VarId`-native transliteration of the *region tests + emitted checks* slice of
`OptimizerPasses/BusPairCancel.lean` (:1731-2104): `firstMatchAt` (:1736), `midRefuted` (:1779),
`preRefuted` (:1786), `provRecv` (:1828), `shieldScan`/`shieldOk` (:1848/:1861), `mkByteCheck`
(`OptimizerPasses/BytePack.lean:17`, no existing dense port — see below), `emitOk` (:1920),
`unjustifiedSlots` (:2020), `checkCancel` (:2035). This is **impl-only**: no `_sound`/`_spec`
lemma is ported (`firstMatchAt_spec`, `midRefuted_sound`, `preRefuted_sound`, `provRecv_sound`,
`shieldScan_hasRecv`, `shieldOk_sound`, `emitOk_sound`, `checkCancel_sound` are all proof, left for
the prover), and no theorem is stated here.

## Reuse map (not re-derived)

* `EqConstraintMap p constraints` / `payloadEntailedEq` → `DenseEqConstraintMap p` /
  `densePayloadEntailedEq` (`Dense/BusPairCancelIndex.lean`, chunk C3).
* `AddrCerts p constraints` (`tworoot`/`nonzero` fields) → `DenseAddrCerts p`
  (`Dense/AddrDiseq.lean`, chunk M1).
* `addrConstsNeq`/`addrConstsEq` → `denseAddrConstsNeq`/`denseAddrConstsEq`, `multConst` →
  `denseMultConst` (all `Dense/BusUnifyNative.lean`, chunk M2).
* `addrAffineNeq`/`addrTwoRootNeq`/`addrNonzeroNeq` → `denseAddrAffineNeq`/`denseAddrTwoRootNeq`/
  `denseAddrNonzeroNeq` (`Dense/AddrDiseq.lean`, chunk M1).
* `byteJustifiedW`/`recvSlotsJustified` → `denseByteJustifiedW`/`denseRecvSlotsJustified`
  (`Dense/BusPairCancelJustify.lean`, chunks C1a-c).
* `Expression.constValue?` → `DenseExpr.constValue?` (`Dense/DropPasses.lean`).
* `facts.memShape`/`facts.slotBound`/`facts.recvByteSlots`/`facts.byteXorSpec` and `ByteXorSpec`
  itself (`Implementation/BusFacts.lean`) are representation-independent (`Nat`/`ZMod p`-valued, or
  polymorphic `{α : Type}` in the `ByteXorSpec.encode`/`decode` case) and are consulted directly,
  unqualified, exactly as the spec does — no dense wrapper is introduced or needed.

## Flagged deviation 1: dropped index-typed implicit parameters

The spec's `firstMatchAt`/`midRefuted`/`preRefuted`/`shieldScan`/`shieldOk`/`checkCancel` all carry
an implicit `{constraints : List (Expression p)}` (or, for `checkCancel`, `{all : List
(Expression p)}`) whose *sole* purpose is indexing the proof-carrying `EqConstraintMap p
constraints` / `AddrCerts p constraints` types so their own (unported) `sound` fields typecheck.
Since chunk C3/M1 already established `DenseEqConstraintMap p` / `DenseAddrCerts p` as **plain**
(non-indexed) structures — the established "proof-carrying spec struct → plain dense runtime
state" pattern — threading a matching implicit list argument here would be dead weight with
nothing to index: the dense definitions below simply drop that implicit parameter, exactly as
`Dense/BusPairCancelCore.lean`'s `denseDropPair_correct` (chunk C2) already does for the same
reason (it drops `AddrCerts`'s index for its `T` argument). No control flow, order, or decision
changes; only a vestigial type-index parameter with no dense counterpart to name disappears.

## Flagged deviation 2: `denseMkByteCheck` — a new shared helper, no existing bytePack port

`mkByteCheck` is owned by `OptimizerPasses/BytePack.lean`, which has **no** dense port yet (per the
task queue, `bytePack` is a separate, not-yet-started pass). `busPairCancel`'s `emitOk`/`checkCancel`
need `mkByteCheck`'s *shape* (not the function itself — `emitOk` only recognizes an already-built
check syntactically) to state its own soundness (`emitOk_sound` proves `ck = mkByteCheck spec
ck.busId o1`, a proof-only fact, not needed by the impl below) — but `checkCancel`'s caller
(`mkDropResult`, a later chunk) *does* call `mkByteCheck` at runtime to build an emitted check, so a
dense mirror is required now, in this chunk, transliterated fresh (mirroring `mkByteCheck`'s exact
payload shape `spec.encode (.const spec.xorOp) e e (.const 0)`, multiplicity `.const 1`). **Flagged
for the future `bytePack` port: reuse `denseMkByteCheck` below rather than re-deriving it** — the
same precedent `Dense/BusPairCancelJustify.lean`'s header set for `DenseExpr.singleVarAux`/
`isSingleVar` (defined once, in the consumer that needed them first, for later reuse). `ByteXorSpec`
itself needs no dense counterpart: `encode`/`decode` are declared `{α : Type} → …`, so they apply to
`DenseExpr p` exactly as they apply to `Expression p`, unqualified.

## `Thunk` forcing fidelity (`denseMidRefuted`/`densePreRefuted`/`denseShieldScan`)

`midRefuted`'s five `||` disjuncts are, in order: bus mismatch, zero-multiplicity, `addrConstsNeq`,
`addrAffineNeq`, `addrTwoRootNeq T.get.tworoot`, `addrNonzeroNeq T.get.nonzero` — `T.get` (forcing
the memoized two-root/nonzero-witness tables) is textually the **last two** disjuncts, so `||`'s
short-circuit means `T` is never forced when any cheaper refutation already succeeds.
`denseMidRefuted` below preserves the identical five-way `||` chain in the identical order, so `T`
is forced at exactly the same two (last) positions, no earlier. `densePreRefuted` calls
`denseMidRefuted` first (same short-circuit inherited) before its own `multConst`-vs-`setNewMult`
check. `denseShieldScan`'s right-to-left fold calls `densePreRefuted` (and hence, transitively,
`denseMidRefuted`) once per list element, in the same position within the pair `(hasRecvSoFar, ok)`
construction — no reordering, no eager forcing introduced. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ### The receive-candidate scan -/

/-- The first indexed position strictly after `i` on `busId` whose payload matches `S.payload`,
    among positions that are still **live** (positions ascending; the hash bucket pre-filters, the
    liveness bit and the bus-id check and the slot-wise entailed comparison decide). A tombstoned
    position is skipped exactly as if it were absent, so the receive chosen is the first live match
    — the same one the old compact-array scan chose. Mirrors `firstMatchAt`
    (`OptimizerPasses/BusPairCancel.lean:1736`). -/
def denseFirstMatchAt (M : Thunk (DenseEqConstraintMap p)) (arr : Array (BusInteraction (DenseExpr p)))
    (alive : Array Bool)
    (busId : Nat) (S : BusInteraction (DenseExpr p)) (i : Nat) : List Nat → Option Nat
  | [] => none
  | j :: rest =>
    if decide (i < j) && alive[j]?.getD false then
      match arr[j]? with
      | some R =>
        if decide (R.busId = busId) && densePayloadEntailedEq M S.payload R.payload then some j
        else denseFirstMatchAt M arr alive busId S i rest
      | none => denseFirstMatchAt M arr alive busId S i rest
    else denseFirstMatchAt M arr alive busId S i rest

/-! ### Between-region and before-region address-disequality refutation -/

/-- Refute `m` as an active same-address message on `busId` (the "between" region test). The
    two-root address-disequality (`denseAddrTwoRootNeq`) lets this step over interleaved
    other-pointer heap accesses whose addresses are pointer *expressions* rather than constants —
    the enabler for interior-pair telescoping on the heap. Mirrors `midRefuted`
    (`OptimizerPasses/BusPairCancel.lean:1779`). -/
def denseMidRefuted (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  decide (m.busId ≠ busId) || decide (denseMultConst m = some 0) || denseAddrConstsNeq shape S m
    || denseAddrAffineNeq shape S m || denseAddrTwoRootNeq shape T.get.tworoot S m
    || denseAddrNonzeroNeq shape T.get.nonzero S m

/-- Refute `m` as an active same-address *send* on `busId` (the "before" region test: earliest-send).
    Mirrors `preRefuted` (`OptimizerPasses/BusPairCancel.lean:1786`). -/
def densePreRefuted (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  denseMidRefuted shape T busId S m ||
    (match denseMultConst m with | some c => decide (c ≠ shape.setNewMult) | none => false)

/-- `m` is a *provable* active same-address receive on `busId`: on-bus, constant `-1`
    multiplicity, and a constant address equal to `S`'s. Mirrors `provRecv`
    (`OptimizerPasses/BusPairCancel.lean:1828`). -/
def denseProvRecv (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (DenseExpr p)) : Bool :=
  decide (m.busId = busId) && denseAddrConstsEq shape S m &&
    decide (denseMultConst m = some (-shape.setNewMult))

/-! ### The before-region shield scan -/

/-- Single right-to-left pass returning `(hasRecvSoFar, ok)`: `hasRecvSoFar` is whether the tail
    processed so far (everything to the right) contains a provable active same-address receive; `ok`
    is whether every not-`densePreRefuted` message so far is followed by such a receive. O(n).
    Mirrors `shieldScan` (`OptimizerPasses/BusPairCancel.lean:1848`). -/
def denseShieldScan (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) :
    List (BusInteraction (DenseExpr p)) → Bool × Bool
  | [] => (false, true)
  | m0 :: rest =>
    let r := denseShieldScan shape T busId S rest
    (r.1 || denseProvRecv shape busId S m0, r.2 && (densePreRefuted shape T busId S m0 || r.1))

/-- The *shield* check on the before-region: every message that is **not** provably a
    non-(active-same-address-send) (`¬densePreRefuted`) is followed by a provable active
    same-address receive (`denseProvRecv`). Computed in one O(n) pass (`denseShieldScan`). Mirrors
    `shieldOk` (`OptimizerPasses/BusPairCancel.lean:1861`). -/
def denseShieldOk (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) (l : List (BusInteraction (DenseExpr p))) : Bool :=
  (denseShieldScan shape T busId S l).2

/-! ### Emitted byte checks (`mkByteCheck` — see the module header, flagged deviation 2) -/

/-- Single-value byte check on `e`, emitted through `spec` (multiplicity `1`). Fresh transliteration
    of `mkByteCheck` (`OptimizerPasses/BytePack.lean:17`) — no existing dense port; see the module
    header for why this chunk defines it, and the flag for the future `bytePack` port to reuse it. -/
def denseMkByteCheck (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.xorOp) e e (.const 0) }

/-- Packed pair byte check on `(e₁, e₂)`, emitted through `spec` (multiplicity `1`). Fresh
    transliteration of `mkBytePair` (`OptimizerPasses/BytePack.lean:23`), placed next to
    `denseMkByteCheck` above for the same reason (no existing dense port; see the module header) —
    this is the builder the `bytePack` port (`OptimizerPasses/ByteCheckPack.lean`) reuses to emit its
    packed pair check, rather than re-deriving it there. -/
def denseMkBytePair (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.pairOp) e₁ e₂ (.const 0) }

/-- Certificate that an emitted check is a faithful carrier of `R`'s byte obligation: it sits on
    a `byteXorSpec` bus (byte bound `256`), has multiplicity 1 and a self-check payload decoding to
    `(xorOp, e, e, 0)` where `e` is one of `R`'s declared byte-slot entries whose byte-ness `R`'s
    own accepted receive implies (a `slotBound` of at most 256 at that slot, at multiplicity `-1`,
    against `R`'s own constant pattern). Mirrors `emitOk`
    (`OptimizerPasses/BusPairCancel.lean:1920`). -/
def denseEmitOk (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat) (shape : MemoryBusShape)
    (slots : List Nat) (R ck : BusInteraction (DenseExpr p)) : Bool :=
  match facts.byteXorSpec ck.busId with
  | none => false
  | some spec =>
    decide (spec.bound = 256) &&
    decide (ck.multiplicity = (.const 1 : DenseExpr p)) &&
    (match spec.decode ck.payload with
     | some (op, o1, o2, r) =>
       decide (op = (.const spec.xorOp : DenseExpr p)) && decide (o1 = o2) &&
       decide (r = (.const 0 : DenseExpr p)) &&
       slots.any (fun slot =>
         decide (R.payload[slot]? = some o1) &&
         (match facts.slotBound busId (-shape.setNewMult) (R.payload.map DenseExpr.constValue?) slot with
          | some b => decide (b ≤ 256)
          | none => false))
     | none => false)

/-! ### The per-candidate acceptance test -/

/-- The declared byte slots of `R` whose payload entries the witnesses do not justify. Mirrors
    `unjustifiedSlots` (`OptimizerPasses/BusPairCancel.lean:2020`). -/
def denseUnjustifiedSlots (bound : Nat) (deep : Bool) (domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : List Nat :=
  slots.filter (fun slot =>
    match R.payload[slot]? with
    | some e => !denseByteJustifiedW bound deep domCs candsOf bs facts wits fwits e
    | none => false)

/-- The per-candidate certificate: address/multiplicity/payload of the pair, the emitted
    checks' certificates, plus the byte justification of the dropped receive's declared byte
    slots through the witness lookup `wits`. The split equation, the between-region refutation
    and the before-region shield are *not* re-checked here — the scan established them already
    and supplies them to the prover's correctness lemma as hypotheses. The justification scan is the
    last conjunct, so it only runs for candidates that already match. Mirrors `checkCancel`
    (`OptimizerPasses/BusPairCancel.lean:2035`; the implicit index parameter `{all : List
    (Expression p)}` is dropped — see the module header, flagged deviation 1). -/
def denseCheckCancel (deep : Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (M : Thunk (DenseEqConstraintMap p))
    (domCs : List (DenseExpr p)) (candsOf : VarId → List (DenseExpr p))
    (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (busId : Nat) (shape : MemoryBusShape) (slots : List Nat) (bound : Nat)
    (S R : BusInteraction (DenseExpr p))
    (checks : List (BusInteraction (DenseExpr p))) : Bool :=
  decide (S.busId = busId) && decide (R.busId = busId) &&
  decide (denseMultConst S = some shape.setNewMult) &&
    decide (denseMultConst R = some (-shape.setNewMult)) &&
  densePayloadEntailedEq M S.payload R.payload &&
  checks.all (denseEmitOk bs facts busId shape slots R) &&
  denseRecvSlotsJustified bound deep domCs candsOf bs facts wits fwits slots R

end ApcOptimizer.Dense
