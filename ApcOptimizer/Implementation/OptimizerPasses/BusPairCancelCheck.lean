import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelIndex

set_option autoImplicit false

/-! # Dense region tests + emitted-check acceptance for `busPairCancel`

The region tests and emitted-check acceptance for `busPairCancel`: the receive-candidate scan
(`denseFirstMatchAt`), the between-region and before-region address-disequality refutation
(`denseMidRefuted`/`densePreRefuted`/`denseProvRecv`), the before-region shield scan
(`denseShieldScan`/`denseShieldOk`), the emitted byte checks (`denseMkByteCheck`/`denseMkBytePair`,
`denseEmitOk`), and the per-candidate acceptance test (`denseUnjustifiedSlots`/`denseCheckCancel`).
This is **impl-only**: it carries no correctness proof here.

## Notes

* `DenseEqConstraintMap p`/`densePayloadEntailedEq` (`Dense/BusPairCancelIndex.lean`) and
  `DenseAddrCerts p` (`Dense/AddrDiseq.lean`) are **plain** (non-indexed) structures, so the
  definitions below carry no index-typed parameter for them — there is nothing dense to index.
* `denseAddrConstsNeq`/`denseAddrConstsEq`, `denseMultConst` (`Dense/BusUnifyNative.lean`),
  `denseAddrAffineNeq`/`denseAddrTwoRootNeq`/`denseAddrNonzeroNeq` (`Dense/AddrDiseq.lean`), and
  `denseByteJustifiedW`/`denseRecvSlotsJustified` (`Dense/BusPairCancelJustify.lean`) are all reused
  from their defining files.
* `facts.memShape`/`facts.slotBound`/`facts.recvByteSlots`/`facts.byteXorSpec` and `ByteXorSpec`
  itself (`Implementation/BusFacts.lean`) are representation-independent (`Nat`/`ZMod p`-valued, or
  polymorphic `{α : Type}` in the `ByteXorSpec.encode`/`decode` case) and are consulted directly,
  unqualified — no dense wrapper is introduced or needed.
* `denseMkByteCheck`/`denseMkBytePair` build the two emitted-check payload shapes (a single-value
  byte check and a packed pair byte check); `denseMkBytePair` is reused by `ByteCheckPack.lean` to
  emit its packed pair check rather than re-deriving it there.

## `Thunk` forcing

`denseMidRefuted`'s five `||` disjuncts are, in order: bus mismatch, zero-multiplicity,
`denseAddrConstsNeq`, `denseAddrAffineNeq`, `denseAddrTwoRootNeq T.get.tworoot`,
`denseAddrNonzeroNeq T.get.nonzero` — `T.get` (forcing the memoized two-root/nonzero-witness
tables) is textually the **last two** disjuncts, so `||`'s short-circuit means `T` is never forced
when any cheaper refutation already succeeds. `densePreRefuted` calls `denseMidRefuted` first (same
short-circuit inherited) before its own `multConst`-vs-`setNewMult` check. `denseShieldScan`'s
right-to-left fold calls `densePreRefuted` (and hence, transitively, `denseMidRefuted`) once per
list element, in the same position within the pair `(hasRecvSoFar, ok)` construction — no
reordering, no eager forcing introduced. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ### The receive-candidate scan -/

/-- The first indexed position strictly after `i` on `busId` whose payload matches `S.payload`,
    among positions that are still **live** (positions ascending; the hash bucket pre-filters, the
    liveness bit and the bus-id check and the slot-wise entailed comparison decide). A tombstoned
    position is skipped exactly as if it were absent, so the receive chosen is the first live
    match. -/
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
    the enabler for interior-pair telescoping on the heap. -/
def denseMidRefuted (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  decide (m.busId ≠ busId) || decide (denseMultConst m = some 0) || denseAddrConstsNeq shape S m
    || denseAddrAffineNeq shape S m || denseAddrTwoRootNeq shape T.get.tworoot S m
    || denseAddrNonzeroNeq shape T.get.nonzero S m

/-- Refute `m` as an active same-address *send* on `busId` (the "before" region test:
    earliest-send). -/
def densePreRefuted (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  denseMidRefuted shape T busId S m ||
    (match denseMultConst m with | some c => decide (c ≠ shape.setNewMult) | none => false)

/-- `m` is a *provable* active same-address receive on `busId`: on-bus, constant `-1`
    multiplicity, and a constant address equal to `S`'s. -/
def denseProvRecv (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (DenseExpr p)) : Bool :=
  decide (m.busId = busId) && denseAddrConstsEq shape S m &&
    decide (denseMultConst m = some (-shape.setNewMult))

/-! ### The before-region shield scan -/

/-- Single right-to-left pass returning `(hasRecvSoFar, ok)`: `hasRecvSoFar` is whether the tail
    processed so far (everything to the right) contains a provable active same-address receive; `ok`
    is whether every not-`densePreRefuted` message so far is followed by such a receive. O(n). -/
def denseShieldScan (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) :
    List (BusInteraction (DenseExpr p)) → Bool × Bool
  | [] => (false, true)
  | m0 :: rest =>
    let r := denseShieldScan shape T busId S rest
    (r.1 || denseProvRecv shape busId S m0, r.2 && (densePreRefuted shape T busId S m0 || r.1))

/-- The *shield* check on the before-region: every message that is **not** provably a
    non-(active-same-address-send) (`¬densePreRefuted`) is followed by a provable active
    same-address receive (`denseProvRecv`). Computed in one O(n) pass (`denseShieldScan`). -/
def denseShieldOk (shape : MemoryBusShape) (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) (l : List (BusInteraction (DenseExpr p))) : Bool :=
  (denseShieldScan shape T busId S l).2

/-! ### Emitted byte checks -/

/-- Single-value byte check on `e`, emitted through `spec` (multiplicity `1`). -/
def denseMkByteCheck (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.xorOp) e e (.const 0) }

/-- Packed pair byte check on `(e₁, e₂)`, emitted through `spec` (multiplicity `1`); the builder
    `ByteCheckPack.lean` reuses to emit its packed pair check, rather than re-deriving it there. -/
def denseMkBytePair (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.pairOp) e₁ e₂ (.const 0) }

/-- Certificate that an emitted check is a faithful carrier of `R`'s byte obligation: it sits on
    a `byteXorSpec` bus (byte bound `256`), has multiplicity 1 and a self-check payload decoding to
    `(xorOp, e, e, 0)` where `e` is one of `R`'s declared byte-slot entries whose byte-ness `R`'s
    own accepted receive implies (a `slotBound` of at most 256 at that slot, at multiplicity `-1`,
    against `R`'s own constant pattern). -/
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

/-- The declared byte slots of `R` whose payload entries the witnesses do not justify. -/
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
    and supplies them to the correctness proof as hypotheses. The justification scan is the last
    conjunct, so it only runs for candidates that already match. -/
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
