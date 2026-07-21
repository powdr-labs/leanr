import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense byte-check pair splitting (Task 3 — impl)

Dense, `VarId`-native transliteration of `OldVariableBased/SplitBytePair.lean`'s *runtime*
definitions (`asBytePair`, `splitOne`, and the pass's computed output). This file is **impl-only**:
no theorem/lemma from the spec file is ported (`asBytePair_eq`, `splitOne_P`,
`forall_P_flatMap`, `splitOne_filter_stateful`, `filter_stateful_flatMap`, `splitOne_map_filter`,
`map_filter_flatMap`, `splitOne_vars`, `splitOne_breaksInvariant`, and the pass's `hp1`-gated
`PassCorrect` proof are all proof-side, the prover's job), and no `DenseVerifiedPassW`/
`DensePassCorrect` wrapper is built here — the runtime transform `denseSplitBytePairF` is shaped
like `denseByteCheckPackF` (`ByteCheckPack.lean`): unconditional in `p` (gated only by the same
`(1 : ZMod p) ≠ 0` self-check as the spec pass), consuming `facts` directly with no fresh
variables, so the prover wraps it directly with `DenseVerifiedPassW.ofNative`.

## Reuse map (not re-derived)

* `denseMkByteCheck` (`BusPairCancelCheck.lean`) is the dense `mkByteCheck` (`BytePack.lean:17`),
  reused unchanged as the emitter for each of the two split singles — exactly as the spec `splitOne`
  reuses `mkByteCheck`.
* `ByteXorSpec`/`BusFacts.byteXorSpec`/`spec.decode` are representation-independent (their
  signatures only mention `Nat`/`ZMod p`/payload lists, never `Variable`/`Expression`), so
  `denseAsBytePair` consults them unqualified, exactly as the spec `asBytePair` does.

## Ordering note (byte-identity-critical)

`denseSplitOne` emits the split pair in the exact order `[denseMkByteCheck spec busId a,
denseMkByteCheck spec busId b]` — same operand order (`a` then `b`, the pair's own decode order)
as the spec's `[mkByteCheck spec busId a, mkByteCheck spec busId b]`. `denseSplitBytePairF`
`flatMap`s `denseSplitOne` over `d.busInteractions` in original list order, exactly as the spec
pass `flatMap`s `splitOne` over `cs.busInteractions`: every untouched interaction keeps its position
and every split pair is emitted in place of the one packed interaction it replaces, singles in
decode order. No representation-forced reordering is possible here — `List` traversal order is the
same regardless of whether the payload/multiplicity carry `Expression`/`Variable` or `DenseExpr`/
`VarId`, so this port needs no divergence from the reference's order at all. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognize a packed pair byte check (decoded op `= pairOp`, result `0`, multiplicity `1`) on a
    `byteXorSpec` bus, returning `(busId, spec, a, b)`. Mirrors `asBytePair`
    (`OldVariableBased/SplitBytePair.lean:42`). -/
def denseAsBytePair (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    Option (Nat × ByteXorSpec p × DenseExpr p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | some (op, o1, o2, r) =>
        if bi.multiplicity = DenseExpr.const 1 ∧ op = DenseExpr.const spec.pairOp
            ∧ r = DenseExpr.const 0 then some (bi.busId, spec, o1, o2) else none
    | none => none

/-- Split one interaction: a recognized packed pair becomes its two single-value checks (in
    decode order `a` then `b`); anything else passes through unchanged. Mirrors `splitOne`
    (`OldVariableBased/SplitBytePair.lean:82`). -/
def denseSplitOne (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : List (BusInteraction (DenseExpr p)) :=
  match denseAsBytePair bs facts bi with
  | some (busId, spec, a, b) => [denseMkByteCheck spec busId a, denseMkByteCheck spec busId b]
  | none => [bi]

/-- The runtime transform: explode every packed pair byte check into its two single-value checks,
    in place, preserving the order of every other interaction. Mirrors `splitBytePairPass`'s
    (`OldVariableBased/SplitBytePair.lean:241`) `hp1` self-gate (VM-neutral: with a trivial
    `BusFacts`, `byteXorSpec` is `none` everywhere, so `denseAsBytePair` never fires and the
    `flatMap` is the identity up to `[bi]`-singleton unwrapping) composed with its computed output
    (dropping the `PassCorrect` term). -/
def denseSplitBytePairF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    { d with busInteractions := d.busInteractions.flatMap (denseSplitOne bs facts) }
  else d

end ApcOptimizer.Dense
