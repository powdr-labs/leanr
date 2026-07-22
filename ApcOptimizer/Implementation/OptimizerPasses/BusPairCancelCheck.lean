import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelIndex

set_option autoImplicit false

/-! # Dense region tests + emitted-check acceptance for `busPairCancel`

The receive scan (`denseFirstMatchAt`), address-disequality refutation
(`denseMidRefuted`/`densePreRefuted`/`denseProvRecv`), the shield scan (`denseShieldOk`), emitted
byte checks (`denseMkByteCheck`/`denseMkBytePair`), and the per-candidate acceptance test
(`denseCheckCancel`). Impl-only; soundness in `BusPairCancelCheckProof.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The first indexed position after `i` on `busId` whose payload matches `S.payload` among still
    **live** positions (ascending); tombstoned positions are skipped, so it is the first live match. -/
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

/-- Refute `m` as an active same-address message on `busId` (the "between" region test). The two-root
    disequality (`denseAddrTwoRootNeq`) lets it step over interleaved accesses whose addresses are
    pointer expressions rather than constants. -/
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

/-- Single-value byte check on `e`, emitted through `spec` (multiplicity `1`). -/
def denseMkByteCheck (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.xorOp) e e (.const 0) }

/-- Packed pair byte check on `(e₁, e₂)`, emitted through `spec` (multiplicity `1`). -/
def denseMkBytePair (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.pairOp) e₁ e₂ (.const 0) }

/-- Certificate that an emitted check faithfully carries `R`'s byte obligation: on a `byteXorSpec`
    bus (bound `256`), multiplicity 1, self-check payload `(xorOp, e, e, 0)` for an `e` that is a
    declared byte slot of `R`. -/
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

/-- The declared byte slots of `R` whose payload entries the witnesses do not justify. -/
def denseUnjustifiedSlots (bound : Nat) (deep : Bool) (domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : List Nat :=
  slots.filter (fun slot =>
    match R.payload[slot]? with
    | some e => !denseByteJustifiedW bound deep domCs candsOf bs facts wits fwits e
    | none => false)

/-- The per-candidate certificate: bus/multiplicity/payload of the pair, the emitted checks'
    certificates, and byte justification of `R`'s declared slots. The split equation and region
    tests are not re-checked here (the scan established them); the justification scan is last, so it
    only runs for already-matching candidates. -/
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
