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

/-- The byte-check shapes recognizable on a `byteXorSpec` bus, by decoded payload
    `(op, o₁, o₂, r)`: the XOR self-check `[x, x, 0]`, the XOR-with-zero and NOT/XOR-255 mirrors
    (the latter gated `256 ≤ p`), the OR-identity (`x | 0 = x`) mirrors, and the packed pair. -/
inductive DenseByteShape
  | selfCheck | xorZeroL | xorZeroR | not255L | not255R | orIdL | orIdR | pair

/-- The decoded operands a shape byte-checks (`…L` checks `o₁`, `…R` checks `o₂`). -/
def DenseByteShape.operands (sh : DenseByteShape) (o1 o2 : DenseExpr p) : List (DenseExpr p) :=
  match sh with
  | .selfCheck => [o1] | .xorZeroL => [o1] | .xorZeroR => [o2] | .not255L => [o1]
  | .not255R => [o2] | .orIdL => [o1] | .orIdR => [o2] | .pair => [o1, o2]

/-- Structural constant test: `e` is literally `const c`. -/
def denseCmpStructural (e : DenseExpr p) (c : ZMod p) : Bool := e == DenseExpr.const c

/-- Folded constant test: `e` constant-folds to `c`. -/
def denseCmpFolded (e : DenseExpr p) (c : ZMod p) : Bool := e.constValue? == some c

/-- Classify a byte check through the VM-neutral `byteXorSpec` (byte bound `256`), testing
    constant slots with `cmp`: the recognized `DenseByteShape` with the spec and decoded operands,
    or `none`. Sound for any `cmp` whose hits pin evaluation (`denseByteShape?_sound`,
    `Proofs/ByteCheckPack.lean`). -/
def denseByteShape? (cmp : DenseExpr p → ZMod p → Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p)) :
    Option (DenseByteShape × ByteXorSpec p × DenseExpr p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | none => none
      | some (op, o1, o2, r) =>
        if cmp op spec.xorOp then
          if o1 == o2 && cmp r 0 then some (.selfCheck, spec, o1, o2)
          else if cmp o2 0 && o1 == r then some (.xorZeroL, spec, o1, o2)
          else if cmp o1 0 && o2 == r then some (.xorZeroR, spec, o1, o2)
          else if decide (256 ≤ p) && cmp o2 255 && denseIsByteCompl o1 r then
            some (.not255L, spec, o1, o2)
          else if decide (256 ≤ p) && cmp o1 255 && denseIsByteCompl o2 r then
            some (.not255R, spec, o1, o2)
          else none
        else if spec.orOp.any (fun oop => cmp op oop) then
          if cmp o2 0 && o1 == r then some (.orIdL, spec, o1, o2)
          else if cmp o1 0 && o2 == r then some (.orIdR, spec, o1, o2)
          else none
        else if cmp op spec.pairOp && cmp r 0 then some (.pair, spec, o1, o2)
        else none
    else none

/-- The value byte-checked by a multiplicity-1 single-value byte check: the operand of a
    structurally recognized single-operand shape (`denseByteShape?`), e.g. `x` for the XOR
    self-check `[x, x, 0]`; `none` otherwise. -/
def denseSvCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  if bi.multiplicity = DenseExpr.const 1 then
    match denseByteShape? denseCmpStructural bs facts bi with
    | some (sh, _, o1, o2) =>
      match sh.operands o1 o2 with
      | [e] => some e
      | _ => none
    | none => none
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
