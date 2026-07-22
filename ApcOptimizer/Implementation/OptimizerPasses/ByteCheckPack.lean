import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense generalized single-value byte-check packing

Runtime content for `byteCheckPack`: `denseComplExpr`, `denseIsByteCompl`, `denseSvCheck?`,
`denseFindSecond`, and the fused scan `denseFindGo`, from which `denseByteCheckPackPass`
(`ByteCheckPackProof.lean`) is assembled. The `"bytePack"`/`"bytePackLate"` labels
(`Implementation/Optimizer.lean`) each run that pass through an outer `iterateToFixpoint`. This
file is **impl-only**: it carries no soundness lemma, and no theorem is stated here.

## Reuse map

* `denseMkBytePair` (`BusPairCancelCheck.lean`, placed next to `denseMkByteCheck`).
* `DenseExpr.normalize` (`Normalize.lean`).
* `DenseExpr.constValue?` (`DropPasses.lean`).
* `DecidableEq (DenseExpr p)` (derived directly on the inductive, `Encoding.lean`) and the generic
  derived `DecidableEq (BusInteraction α)` instance applied at `α := DenseExpr p`.
  `facts.byteXorSpec`/`ByteXorSpec.decode`/`encode` are representation-independent
  (`{α : Type} → …`) and are consulted unqualified.

## `denseFindGo`'s positional split

`denseFindGo` returns the positionally-split pack data directly:
`(busId, spec, pre, eA, mid, eB, post)` with `pre = revPre.reverse`. The **selection** — first `a`
with `denseSvCheck? = some eA`; first `b` strictly after `a` on the same bus with
`denseSvCheck? = some eB` (`denseFindSecond`); `a`'s `byteXorSpec` bus-fact lookup and its
`bound = 256` gate — determines the pair chosen, with no re-verification of the split. `busId`
(`= a.busId`, needed by `denseMkBytePair` at the call site) is carried explicitly as the tuple's
first component. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Recognizing the NOT-form complement -/

/-- `255 − e` as a dense expression. -/
def denseComplExpr (e : DenseExpr p) : DenseExpr p := .add (.const 255) (.mul (.const (-1)) e)

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment? Decided by folding
    `b − (255 − a)` to a constant and checking it is `0`. -/
def denseIsByteCompl (a b : DenseExpr p) : Bool :=
  (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).normalize.constValue? == some 0

/-! ## Recognizing a single-value byte check in any encoding -/

/-- The value byte-checked by a multiplicity-1 single-value byte check, recognized through the
    VM-neutral `byteXorSpec` (byte bound `256`, decoded op `= xorOp`): the self-check (`o₁ = o₂`,
    `r = 0`), the two XOR-with-zero mirrors (`o₂ = 0, o₁ = r` / `o₁ = 0, o₂ = r`), and the two NOT
    (XOR-with-255) forms (`o₂ = 255, r = 255 − o₁` / `o₁ = 255, r = 255 − o₂`, when `256 ≤ p`) all
    return the checked operand; `none` otherwise. Seven branches, checked in order: self-check, two
    XOR-with-zero mirrors, two NOT-form mirrors (each gated `256 ≤ p`), then the OR-identity mirror
    pair, gated in order by `bound = 256`, then multiplicity/op, then each shape. -/
def denseSvCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | none => none
      | some (op, o1, o2, r) =>
        if bi.multiplicity = DenseExpr.const 1 ∧ op = DenseExpr.const spec.xorOp then
          if o1 = o2 ∧ r = DenseExpr.const 0 then some o1
          else if o2 = DenseExpr.const 0 ∧ o1 = r then some o1
          else if o1 = DenseExpr.const 0 ∧ o2 = r then some o2
          else if decide (256 ≤ p) ∧ o2 = DenseExpr.const 255 ∧ denseIsByteCompl o1 r = true then
            some o1
          else if decide (256 ≤ p) ∧ o1 = DenseExpr.const 255 ∧ denseIsByteCompl o2 r = true then
            some o2
          else none
        else if bi.multiplicity = DenseExpr.const 1 ∧
            spec.orOp.any (fun oop => op == DenseExpr.const oop) = true then
          -- OR identity (`x | 0 = x`): the interaction is exactly a byte check on the survivor.
          if o2 = DenseExpr.const 0 ∧ o1 = r then some o1
          else if o1 = DenseExpr.const 0 ∧ o2 = r then some o2
          else none
        else none
    else none

/-! ## The pass: find and pack one pair, draining to a fixpoint in one call -/

/-- Scan for the next single-value byte check on `busId`, returning the interior `mid`, the
    interaction `b`, its checked value `eB`, and the remainder `post`. -/
def denseFindSecond (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat) :
    List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p)) →
    Option (List (BusInteraction (DenseExpr p)) × BusInteraction (DenseExpr p) ×
      DenseExpr p × List (BusInteraction (DenseExpr p)))
  | _, [] => none
  | revMid, b :: rest =>
    match denseSvCheck? bs facts b with
    | some eB => if decide (b.busId = busId) then some (revMid.reverse, b, eB, rest)
                 else denseFindSecond bs facts busId (b :: revMid) rest
    | none => denseFindSecond bs facts busId (b :: revMid) rest

/-- Fused scan for the first packable pair, returning plain positionally-split pack data — see the
    module header for why `busId` is carried explicitly. Selection order: first `a` with a
    recognized single-value check, then the first same-bus match after it (`denseFindSecond`), then
    `a`'s `byteXorSpec` bus fact and its `bound = 256` gate. -/
def denseFindGo (bs : BusSemantics p) (facts : BusFacts p bs)
    (revPre : List (BusInteraction (DenseExpr p))) :
    List (BusInteraction (DenseExpr p)) →
    Option (Nat × ByteXorSpec p × List (BusInteraction (DenseExpr p)) × DenseExpr p ×
      List (BusInteraction (DenseExpr p)) × DenseExpr p × List (BusInteraction (DenseExpr p)))
  | [] => none
  | a :: rest =>
    match denseSvCheck? bs facts a with
    | some eA =>
      match denseFindSecond bs facts a.busId [] rest with
      | some (mid, _b, eB, post) =>
        match facts.byteXorSpec a.busId with
        | some spec =>
          if decide (spec.bound = 256) then
            some (a.busId, spec, revPre.reverse, eA, mid, eB, post)
          else denseFindGo bs facts (a :: revPre) rest
        | none => denseFindGo bs facts (a :: revPre) rest
      | none => denseFindGo bs facts (a :: revPre) rest
    | none => denseFindGo bs facts (a :: revPre) rest

end ApcOptimizer.Dense
