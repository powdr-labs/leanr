import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense tuple-range packing

Runtime recognizers, partner scans, and drain for `tupleRange`; the pass is wrapped in
`TupleRangeProof.lean`. The partner scans return the `pre`/`mid`/`post` split directly, so the
split equation holds by construction, available to the prover as a loop invariant. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The two message shapes being packed and unpacked -/

/-- Range check `[y, b]` (multiplicity `1`) on a variable-range-checker bus. -/
def denseRangeCheck1 (busId : Nat) (y b : DenseExpr p) : BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1, payload := [y, b] }

/-- Tuple check `[x, y]` (multiplicity `1`). -/
def denseTupleCheck (busId : Nat) (x y : DenseExpr p) : BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1, payload := [x, y] }

/-! ## Recognizing a candidate half of a pack -/

/-- If `bi` is a single-value byte check (decoded op `= xorOp`, `o₁ = o₂`, result `0`, multiplicity
    `1`) on a `byteXorSpec` bus with byte bound `256`, return the bus spec and checked value. -/
def denseMatchByteSingle (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (ByteXorSpec p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
          if bi.multiplicity = DenseExpr.const 1 ∧ op = DenseExpr.const spec.xorOp
              ∧ o1 = o2 ∧ r = DenseExpr.const 0
          then some (spec, o1) else none
      | none => none
    else none

/-- If `bi` is a range check `[y, b]` (multiplicity `1`, constant supported width, exact size
    `2 ^ b = s2`) on a `varRangeBus`, return `(y, b)`. -/
def denseMatchRangeCheck (bs : BusSemantics p) (facts : BusFacts p bs) (s2 : Nat)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p × ZMod p) :=
  if facts.varRangeBus bi.busId then
    match bi.multiplicity, bi.payload with
    | .const c, [y, .const b] =>
        if decide (c = 1) && decide (b.val ≤ 17) && decide (2 ^ b.val = s2)
        then some (y, b) else none
    | _, _ => none
  else none

/-- The declared tuple buses with a byte-sized first slot, probed over a bounded id range (the
    target bus typically carries no interaction in the input circuit, so its id cannot be read off
    `d`). -/
def denseTupleBusCandidates (bs : BusSemantics p) (facts : BusFacts p bs) (maxId : Nat) :
    List (Nat × Nat × Nat) :=
  (List.range maxId).filterMap (fun k =>
    match facts.tupleRangeBus k with
    | some (s1, s2) => if s1 = 256 then some (k, s1, s2) else none
    | none => none)

/-! ## Forward partner scans -/

/-- Scan for the next exact-size range check, returning the interior `mid`, the checked value `y`
    with its width witness `b`, and the remainder `post`. -/
def denseFindRangePartner (bs : BusSemantics p) (facts : BusFacts p bs) (s2 : Nat) :
    List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p)) →
    Option (List (BusInteraction (DenseExpr p)) × DenseExpr p × ZMod p ×
      List (BusInteraction (DenseExpr p)))
  | _, [] => none
  | revMid, b :: rest =>
    match denseMatchRangeCheck bs facts s2 b with
    | some (y, bw) => some (revMid.reverse, y, bw, rest)
    | none => denseFindRangePartner bs facts s2 (b :: revMid) rest

/-- Scan for the next single-value byte check, returning the interior `mid`, the recognized spec
    and checked value `x`, and the remainder `post`. -/
def denseFindBytePartner (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p)) →
    Option (List (BusInteraction (DenseExpr p)) × ByteXorSpec p × DenseExpr p ×
      List (BusInteraction (DenseExpr p)))
  | _, [] => none
  | revMid, b :: rest =>
    match denseMatchByteSingle bs facts b with
    | some (spec, x) => some (revMid.reverse, spec, x, rest)
    | none => denseFindBytePartner bs facts (b :: revMid) rest

/-- Fused scan for the first packable pair for a tuple bus with second-slot size `s2`: a byte check
    with an exact-width range check partner, in either order, returned as the packed values `x`
    (byte) and `y` (range) with the surrounding `pre`/`mid`/`post` split. -/
def denseFindTuplePack (bs : BusSemantics p) (facts : BusFacts p bs) (s2 : Nat)
    (revPre : List (BusInteraction (DenseExpr p))) :
    List (BusInteraction (DenseExpr p)) →
    Option (List (BusInteraction (DenseExpr p)) × DenseExpr p ×
      List (BusInteraction (DenseExpr p)) × DenseExpr p × List (BusInteraction (DenseExpr p)))
  | [] => none
  | a :: rest =>
    match denseMatchByteSingle bs facts a with
    | some (_spec, x) =>
      match denseFindRangePartner bs facts s2 [] rest with
      | some (mid, y, _b, post) => some (revPre.reverse, x, mid, y, post)
      | none => denseFindTuplePack bs facts s2 (a :: revPre) rest
    | none =>
      match denseMatchRangeCheck bs facts s2 a with
      | some (y, _b) =>
        match denseFindBytePartner bs facts [] rest with
        | some (mid, _spec, x, post) => some (revPre.reverse, x, mid, y, post)
        | none => denseFindTuplePack bs facts s2 (a :: revPre) rest
      | none => denseFindTuplePack bs facts s2 (a :: revPre) rest

/-! ## The pass: try every candidate tuple bus, drain every packable pair -/

/-- Try each candidate tuple bus in order: the first bus with a packable pair wins. -/
def denseTryTupleBuses (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) :
    List (Nat × Nat × Nat) →
    Option (Nat × List (BusInteraction (DenseExpr p)) × DenseExpr p ×
      List (BusInteraction (DenseExpr p)) × DenseExpr p ×
      List (BusInteraction (DenseExpr p)))
  | [] => none
  | (trBus, _s1, s2) :: rest =>
    match denseFindTuplePack bs facts s2 [] bis with
    | some (pre, x, mid, y, post) => some (trBus, pre, x, mid, y, post)
    | none => denseTryTupleBuses bs facts bis rest

/-- Drain every packable pair: pack the first (bus-major, then position-major) pair, recompute the
    candidate buses on the shrunken list, repeat. Fuel-bounded; each pack drops the list length by
    one, so fuel = interaction-list length suffices. -/
def denseDrainTuplePacks (bs : BusSemantics p) (facts : BusFacts p bs) :
    Nat → List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p))
  | 0, bis => bis
  | fuel + 1, bis =>
    let maxId := (bis.map (fun bi => bi.busId)).foldl max 0 + 65
    match denseTryTupleBuses bs facts bis (denseTupleBusCandidates bs facts maxId) with
    | some (trBus, pre, x, mid, y, post) =>
      denseDrainTuplePacks bs facts fuel (pre ++ denseTupleCheck trBus x y :: mid ++ post)
    | none => bis

/-- Packs a single-value byte check on `x` and an exact-width range check `[y, b]` into one tuple
    check `[x, y]` on a tuple-range bus (`x < 256 ∧ y < 2^b`), draining every packable pair in one
    invocation (`denseTupleRangePass`). -/
def denseTupleRangeF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    { d with busInteractions :=
        denseDrainTuplePacks bs facts d.busInteractions.length d.busInteractions }
  else d

end ApcOptimizer.Dense
