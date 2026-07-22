import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify

set_option autoImplicit false

/-! # Dense redundant byte-check removal

Recognizes byte-check bus interactions whose operands are already byte-justified elsewhere in the
system, and drops them. No `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the
runtime transform `denseRedundantByteDropF` is shaped exactly like `denseSubsumedCheckDropF`
(`SubsumedCheck.lean`): a `PrimeWitness`-threading, unconditional-in-`p` filter, wrapped directly
with `DenseVerifiedPassW.of`.

## Reuse map (not re-derived)

* `denseComplExpr`/`denseIsByteCompl` (`ByteCheckPack.lean`) are reused unchanged rather than
  redeclared here, since the dense side keeps one shared `ApcOptimizer.Dense` namespace.
* `denseByteJustified` (`BusPairCancelJustify.lean`) is reused unchanged; it internally threads the
  plain full-scan witness lookup (`fun _ => rest`) and disables the basis-reduction arm
  (`fwits := fun _ => []`).
* `DenseExpr.constValue?` (`DropPasses.lean`).
* `DenseConstraintSystem.filterBus` (`Rewrite.lean`) is what the pass's `.out` is built from.
* `BusFacts`/`BusSemantics`/`ByteXorSpec` are representation-independent (`decode`/`encode` are
  `{α : Type} → …`), consulted unqualified.

## `byteCheckOperands?` is not `denseSvCheck?`

`ByteCheckPack.lean`'s `denseSvCheck?` looks similar (same `byteXorSpec` recognition tower) but is a
genuinely different function, so it is defined separately here as `denseByteCheckOperands?` rather
than reused: it drops `denseSvCheck?`'s multiplicity-`1` gate (this pass justifies an interaction's
*acceptance* regardless of the dropped check's own multiplicity — soundness never reads it),
returns a *list* of justified operands (one for the XOR/OR-identity shapes, two for the
packed-pair shape) instead of a single expression, and adds the packed-pair (`pairOp`, `r = 0`)
recognition branch that `denseSvCheck?` has no use for. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Recognizing pure byte-check interactions -/

/-- The operands whose byte-ness *implies* this interaction's acceptance (for any multiplicity),
    recognized through the VM-neutral `byteXorSpec` (byte bound `256`). Decoding to
    `(op, o₁, o₂, r)`: for `op = xorOp` the self-check `o₁ = o₂`, `r = 0` (`[x, x, 0]`), the two
    XOR-with-zero mirrors (`o₂ = 0, o₁ = r` / `o₁ = 0, o₂ = r`), and the two NOT forms
    (`o₂ = 255, r = 255 − o₁` / `o₁ = 255, r = 255 − o₂`, when `256 ≤ p`); for the OR-identity op(s)
    the same zero mirrors; for `op = pairOp` the packed pair `r = 0`. `none` otherwise. Gates on
    `bound = 256` before decoding, then checks each shape in order, using the same `==`/`&&` (Bool)
    recognition style throughout (not `denseSvCheck?`'s `=`/`∧` style). -/
def denseByteCheckOperands? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (List (DenseExpr p)) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | none => none
      | some (op, o1, o2, r) =>
        if op.constValue? == some spec.xorOp then
          if o1 == o2 && r.constValue? == some 0 then some [o1]
          else if o2.constValue? == some 0 && o1 == r then some [o1]
          else if o1.constValue? == some 0 && o2 == r then some [o2]
          else if decide (256 ≤ p) && o2.constValue? == some 255 && denseIsByteCompl o1 r then
            some [o1]
          else if decide (256 ≤ p) && o1.constValue? == some 255 && denseIsByteCompl o2 r then
            some [o2]
          else none
        else if spec.orOp.any (fun oop => op.constValue? == some oop) then
          -- OR identity (`x | 0 = x`): exactly a byte check on the survivor.
          if o2.constValue? == some 0 && o1 == r then some [o1]
          else if o1.constValue? == some 0 && o2 == r then some [o2]
          else none
        else if op.constValue? == some spec.pairOp && r.constValue? == some 0 then some [o1, o2]
        else none
    else none

/-! ## The pass -/

/-- The justification base: the interactions this pass can never drop (not recognized as byte
    checks). Justifying only against these makes the drop non-circular. -/
def denseByteDropBase (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseByteCheckOperands? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized byte check whose operands are all byte-justified from the
    constraints and the justification base. -/
def denseByteDropKeep (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (all : List (DenseExpr p)) (rest : List (BusInteraction (DenseExpr p)))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseByteCheckOperands? bs facts bi with
  | some ops => !(ops.all (fun e => denseByteJustified 256 pw.isPrime all bs facts rest e))
  | none => true

/-- Drop every stateless byte-check interaction whose operands are all byte-justified from the
    parts of the system this pass can never remove. -/
def denseRedundantByteDropF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseByteDropKeep pw bs facts d.algebraicConstraints (denseByteDropBase bs facts d))

end ApcOptimizer.Dense
