import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense tuple-range packing

Recognizes byte checks (`denseMatchByteSingle`) and range checks (`denseMatchRangeCheck`) on the
relevant buses, scans for a packable pair of them (`denseFindRangePartner`/`denseFindBytePartner`/
`denseFindTuplePack`), tries every candidate tuple bus in turn (`denseTryTupleBuses`), and drains
every packable pair (`denseDrainTuplePacks`) into the pass transform `denseTupleRangeF`. This file
is **impl-only**: it carries no `DensePassCorrect`/`DenseVerifiedPassW` proof obligation here. The
runtime transform `denseTupleRangeF` is unconditional in `p`, gated only by a `(1 : ZMod p) ≠ 0`
self-check, and consumes `facts` directly with no fresh variables, so it can be wrapped with
`DenseVerifiedPassW.of`.

## Notes

* `denseMkByteCheck` (`BusPairCancelCheck.lean`) is **not used here**: `denseMatchByteSingle`/
  `denseMatchRangeCheck` only *recognize* an already-built check syntactically (they never emit
  one), and the packed output is a *different* bus message (`[x, y]` on the tuple-range bus, built
  fresh below as `denseTupleCheck`), not a rebuilt byte check.
* `ByteXorSpec`/`BusFacts.byteXorSpec`/`BusFacts.varRangeBus`/`BusFacts.tupleRangeBus` are
  representation-independent (`Nat`/`ZMod p`-valued, or `{α : Type} → …` for `decode`), so they are
  consulted directly, unqualified.
* `DecidableEq (DenseExpr p)` (derived on the inductive, `Encoding.lean:33`) is what
  `denseMatchByteSingle`/`denseMatchRangeCheck` use everywhere they decide payload-slot equalities.

## Partner scans: plain `List` splits

`denseFindRangePartner`/`denseFindBytePartner` and `denseFindTuplePack` scan plain `List`s and
return the split directly as `pre`/`mid`/`post` sublists — the split equation is then true by
construction of the traversal, available for the prover to state as a loop invariant. At each
position, left to right, a byte check is tried first (looking strictly rightward for the first
exact-width range check partner via `denseFindRangePartner`); failing that, a range check is tried
(looking strictly rightward for the first byte check partner via `denseFindBytePartner`); failing
both, the scan moves to the next position.

Two further points on how the packed output is built:

* `denseTryTupleBuses` calls straight into the scan for every candidate bus with no re-check of the
  bus's shape: every element of `denseTupleBusCandidates`'s output already satisfies the tuple-bus
  shape by construction (`denseTupleBusCandidates` only ever emits `(k, s1, s2)` after checking
  exactly this).
* The packed output `denseTupleCheck trBus x y` needs **no** `ByteXorSpec` to build — it is the
  plain 2-ary message `[x, y]`. So `denseFindTuplePack` only needs `x`/`y` at its own return
  boundary and discards the byte bus's `spec`/the range check's width witness `b : ZMod p` with an
  underscore once matched — the `spec`/`b` data itself is still threaded one level deeper, in
  `denseFindRangePartner`/`denseFindBytePartner`'s own return tuples, for the prover's convenience
  (a bound name rather than a re-derived existential). -/

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

/-- Fused scan for the first packable pair for a tuple bus with second-slot size `s2`: at each
    position, left to right, a byte check first looks rightward for the first exact-width range
    check (`denseFindRangePartner`); failing that, a range check looks rightward for the first byte
    check (`denseFindBytePartner`); failing both, move on. Returns the packed values `x` (byte) and
    `y` (range) with the surrounding `pre`/`mid`/`post` split — `x`/`y` are all `denseTupleCheck`
    needs to build the replacement, in either orientation. -/
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
    candidate buses on the shrunken list, repeat. One invocation replaces the enclosing per-pair
    fixpoint. Fuel-bounded structural recursion, fuel initialized to the interaction-list length at
    the call site (`denseTupleRangeF`): each successful pack strictly drops that list's length by
    one, so the fuel is never actually exhausted before `denseTryTupleBuses` reports `none`. -/
def denseDrainTuplePacks (bs : BusSemantics p) (facts : BusFacts p bs) :
    Nat → List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p))
  | 0, bis => bis
  | fuel + 1, bis =>
    let maxId := (bis.map (fun bi => bi.busId)).foldl max 0 + 65
    match denseTryTupleBuses bs facts bis (denseTupleBusCandidates bs facts maxId) with
    | some (trBus, pre, x, mid, y, post) =>
      denseDrainTuplePacks bs facts fuel (pre ++ denseTupleCheck trBus x y :: mid ++ post)
    | none => bis

/-- The dense pack-until-drained transform (`of` shape: registry unchanged, no fresh
    variables). VM-neutral: with a trivial `BusFacts`, `tupleRangeBus` is `none` everywhere, so
    `denseTupleBusCandidates` is always `[]` and the drain is the identity in its first step. This
    pass needs no outer `iterateToFixpoint` wrapper; the single internal drain call already
    exhausts every packable pair. -/
def denseTupleRangeF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    { d with busInteractions :=
        denseDrainTuplePacks bs facts d.busInteractions.length d.busInteractions }
  else d

end ApcOptimizer.Dense
