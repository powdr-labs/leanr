import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense single-value byte-check packing

Runtime recognizers and the pair-finding scan for `byteCheckPack`; the pass is assembled in
`Proofs/ByteCheckPack.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `255 − e` as a dense expression. -/
def denseComplExpr (e : DenseExpr p) : DenseExpr p := .add (.const 255) (.mul (.const (-1)) e)

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment? -/
def denseIsByteCompl (a b : DenseExpr p) : Bool :=
  (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).normalize.constValue? == some 0

/-- The value byte-checked by a multiplicity-1 single-value byte check, recognized through the
    VM-neutral `byteXorSpec` (byte bound `256`): the self-check `[x, x, 0]`, the two XOR-with-zero
    mirrors, the two NOT/XOR-255 forms (gated `256 ≤ p`), and the OR-identity mirrors; `none`
    otherwise. -/
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

/-- Fused scan for the first packable pair `denseByteCheckPackPass` fuses: two single-value byte
    checks on the same byte-XOR bus, e.g. `x < 256` and `y < 256` merged into one `[x, y]` pair
    check. Returns the positional split `(busId, spec, pre, eA, mid, eB, post)`. -/
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
