import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense tuple-range packing (Task 3 — impl)

Dense, `VarId`-native transliteration of the reference `TupleRange` pass's *runtime* definitions
(`rangeCheck1` :32, `tupleCheck` :36, `matchByteSingle` :207, `matchRangeCheck` :222,
`tupleBusCandidates` :235, `findRangeIdx` :304, `findByteIdx` :320, `findTuplePackIdx` :422,
`tryTupleBuses` :510, `drainTuplePacks` :528, and the pass `tupleRangePass` :542). This file is
**impl-only**: no theorem/lemma from the spec file is ported (`rangeCheck1_eval`, `tupleCheck_eval`,
`mergeStateless2_correct`, `tupleKey`, `matchByteSingle_eq`, `matchRangeCheck_eq`,
`packByteFirst_correct`, `packRangeFirst_correct`, and the two accept certificates baked into
`findTuplePackIdx`'s `PassCorrect` term are all proof-side, the prover's job), and no
`DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the runtime transform
`denseTupleRangeF` is shaped like `denseByteCheckPackF`/`denseSplitBytePairF` (unconditional in `p`,
gated only by the same `(1 : ZMod p) ≠ 0` self-check as the spec pass, consuming `facts` directly
with no fresh variables), so the prover wraps it with `DenseVerifiedPassW.ofNative`.

## Reuse map (not re-derived)

* `denseMkByteCheck` (`BusPairCancelCheck.lean`) is the dense `mkByteCheck`
  (`OptimizerPasses/BytePack.lean:17`) — **not used here**: `matchByteSingle`/`matchRangeCheck`
  only *recognize* an already-built check syntactically (they never emit one), and the packed
  output `tupleCheck` is a *different* bus message (`[x, y]` on the tuple-range bus, built fresh
  below as `denseTupleCheck`), not a rebuilt byte check. Recorded here only to note the check was
  made — reuse is n/a for this pass.
* `ByteXorSpec`/`BusFacts.byteXorSpec`/`BusFacts.varRangeBus`/`BusFacts.tupleRangeBus` are
  representation-independent (`Nat`/`ZMod p`-valued, or `{α : Type} → …` for `decode`), so they are
  consulted directly, unqualified, exactly as the spec does.
* `DecidableEq (DenseExpr p)` (derived on the inductive, `Encoding.lean:33`) stands in for
  `DecidableEq (Expression p)` everywhere `matchByteSingle`/`matchRangeCheck` decide payload-slot
  equalities.

## Flagged deviation: `findRangeIdx`/`findByteIdx`/`findTuplePackIdx` go from `Array`+index+`PSigma`
to plain `List` splits

The reference threads an `Array (BusInteraction (Expression p))`, dependent-pair (`PSigma`)
witnesses of "position `j ≥ i` with a match, plus a proof `j < arr.size`", and (at the accepted
candidate) an `arr[j]?`/`Array.getElem?_eq_getElem` re-derivation of the matched interaction `R` —
all of it existing *solely* to feed `split_of_extracts` so the **proof** obligation
(`cs.busInteractions = pre ++ a :: mid ++ b :: post`) is available for `packByteFirst_correct`/
`packRangeFirst_correct`. This is exactly the pattern flagged and dropped once already in this
port set (`BusPairCancelCheck.lean`'s "Flagged deviation 1", and, in the same drain-pass family,
`ByteCheckPack.lean`'s `denseFindSecond`/`denseFindGo`, whose *own reference* is already the
list-splitting shape below — no `Array`/`PSigma` at all). Below, `denseFindRangePartner`/
`denseFindBytePartner` (mirroring `findRangeIdx`/`findByteIdx`) and `denseFindTuplePack` (mirroring
`findTuplePackIdx`) scan plain `List`s and return the split directly as `pre`/`mid`/`post` sublists
— the split equation is then true by construction of the traversal (no `Array.extract`/`getElem?`
re-derivation needed), left for the prover to state as a loop invariant exactly as
`denseFindGo_split` does for `ByteCheckPack.lean`. **No selection, control-flow, or order change**:
at each position, left to right, a byte check is tried first (looking strictly rightward for the
first exact-width range check partner via `denseFindRangePartner`); failing that, a range check is
tried (looking strictly rightward for the first byte check partner via `denseFindBytePartner`);
failing both, the scan moves to the next position — the identical two-recognizer, two-orientation,
first-match order the reference's `i`/`i+1`-indexed `findTuplePackIdx` walks.

Two further, smaller instances of the same "drop proof-only scaffolding, keep the decision" pattern:

* `denseTryTupleBuses` drops the reference `tryTupleBuses`'s `if h : facts.tupleRangeBus trBus =
  some (s1, s2) ∧ s1 = 256 then … else …` re-`decide` before calling into the scan: every element of
  `tupleBusCandidates`'s output already satisfies this by construction (`tupleBusCandidates` only
  ever emits `(k, s1, s2)` after checking exactly this), so the guard is always true at runtime — the
  same "always-true `dite`, kept only so the proof has the hypothesis in scope" pattern
  `ByteCheckPack.lean`'s `denseFindGo` already drops for its own split-equation `dite`.
* The packed output `tupleCheck trBus x y` (unlike `ByteCheckPack.lean`'s `mkBytePair spec busId e₁
  e₂`) needs **no** `ByteXorSpec` to build — it is the plain 2-ary message `[x, y]`. So, unlike
  `denseFindGo`, which must carry `busId`/`spec` all the way out to build its output,
  `denseFindTuplePack` only needs `x`/`y` at its own return boundary and discards the byte bus's
  `spec`/the range check's width witness `b : ZMod p` with an underscore once matched (exactly as
  `denseFindGo` already discards `denseFindSecond`'s matched interaction with `_b`) — the
  `spec`/`b` data itself is still threaded one level deeper, in `denseFindRangePartner`/
  `denseFindBytePartner`'s own return tuples, for the prover's convenience (a bound name rather
  than a re-derived existential), mirroring `findRangeIdx`/`findByteIdx`'s own carried `b`/`spec`
  fields. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The two message shapes being packed and unpacked -/

/-- Range check `[y, b]` (multiplicity `1`) on a variable-range-checker bus. Mirrors `rangeCheck1`
   . -/
def denseRangeCheck1 (busId : Nat) (y b : DenseExpr p) : BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1, payload := [y, b] }

/-- Tuple check `[x, y]` (multiplicity `1`). Mirrors `tupleCheck`
   . -/
def denseTupleCheck (busId : Nat) (x y : DenseExpr p) : BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1, payload := [x, y] }

/-! ## Recognizing a candidate half of a pack -/

/-- If `bi` is a single-value byte check (decoded op `= xorOp`, `o₁ = o₂`, result `0`, multiplicity
    `1`) on a `byteXorSpec` bus with byte bound `256`, return the bus spec and checked value.
    Mirrors `matchByteSingle`. -/
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
    `2 ^ b = s2`) on a `varRangeBus`, return `(y, b)`. Mirrors `matchRangeCheck`
   . -/
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
    `d`). Mirrors `tupleBusCandidates`. -/
def denseTupleBusCandidates (bs : BusSemantics p) (facts : BusFacts p bs) (maxId : Nat) :
    List (Nat × Nat × Nat) :=
  (List.range maxId).filterMap (fun k =>
    match facts.tupleRangeBus k with
    | some (s1, s2) => if s1 = 256 then some (k, s1, s2) else none
    | none => none)

/-! ## Forward partner scans (list-based — see the module header's flagged deviation) -/

/-- Scan for the next exact-size range check, returning the interior `mid`, the checked value `y`
    with its width witness `b`, and the remainder `post`. Mirrors `findRangeIdx`
   , dropping the `Array`+index+`PSigma` scaffolding (see
    the module header). -/
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
    and checked value `x`, and the remainder `post`. Mirrors `findByteIdx`
   , dropping the `Array`+index+`PSigma` scaffolding (see
    the module header). -/
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
    needs to build the replacement, in either orientation. Mirrors `findTuplePackIdx`
   , same two-recognizer, two-orientation, first-match
    order; dropping the `Array`+index+`PSigma` scaffolding (see the module header). -/
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

/-- Try each candidate tuple bus in order: the first bus with a packable pair wins. Mirrors
    `tryTupleBuses`, dropping the redundant re-`decide` of
    `facts.tupleRangeBus trBus = some (s1, s2) ∧ s1 = 256` (see the module header). -/
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
    one, so the fuel is never actually exhausted before `denseTryTupleBuses` reports `none` — the
    same fuel-for-termination shape as `ByteCheckPack.lean`'s `denseDrainBytePacks`, standing in for
    the reference `drainTuplePacks`'s well-founded
    recursion on the strictly-dropping interaction count. -/
def denseDrainTuplePacks (bs : BusSemantics p) (facts : BusFacts p bs) :
    Nat → List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p))
  | 0, bis => bis
  | fuel + 1, bis =>
    let maxId := (bis.map (fun bi => bi.busId)).foldl max 0 + 65
    match denseTryTupleBuses bs facts bis (denseTupleBusCandidates bs facts maxId) with
    | some (trBus, pre, x, mid, y, post) =>
      denseDrainTuplePacks bs facts fuel (pre ++ denseTupleCheck trBus x y :: mid ++ post)
    | none => bis

/-- The dense pack-until-drained transform (`ofNative` shape: registry unchanged, no fresh
    variables). Mirrors `tupleRangePass`'s `hp1` self-gate
    (VM-neutral: with a trivial `BusFacts`, `tupleRangeBus` is `none` everywhere, so
    `denseTupleBusCandidates` is always `[]` and the drain is the identity in its first step)
    composed with the single internal-drain call (see `denseDrainTuplePacks`'s doc comment) — this
    pass needs no outer `iterateToFixpoint` wrapper, matching the schedule docstring. -/
def denseTupleRangeF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    { d with busInteractions :=
        denseDrainTuplePacks bs facts d.busInteractions.length d.busInteractions }
  else d

end ApcOptimizer.Dense
