import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.RedundantByteDrop
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify

set_option autoImplicit false

/-! # Dense redundant byte-check removal (Task 3 — impl)

Dense, `VarId`-native transliteration of `OldVariableBased/RedundantByteDrop.lean`'s *runtime*
definitions (`byteCheckOperands?` :88, `byteDropBase` :245, `byteDropKeep` :251, and
`redundantByteDropPass`'s computed output :260). This file is **impl-only**: no `_sound`/soundness
lemma is ported (`isByteCompl_sound`, `byteCheckOperands?_stateless`, `byteCheckOperands?_accepted`,
and the pass's `filterBusEntailed_correct`-built `PassCorrect` term are all proof-side, the
prover's job), and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the runtime
transform `denseRedundantByteDropF` is shaped exactly like `denseSubsumedCheckDropF`
(`SubsumedCheck.lean`): a `PrimeWitness`-threading, unconditional-in-`p` filter, so the prover wraps
it directly with `DenseVerifiedPassW.ofNative`.

## Reuse map (not re-derived)

* `denseComplExpr`/`denseIsByteCompl` (`ByteCheckPack.lean`) are *exactly* the `complExpr`/
  `isByteCompl` this pass's own reference file redefines at `RedundantByteDrop.lean:46,52` (a
  byte-for-byte duplicate of `ByteCheckPack.lean`'s copy — the two spec files each keep a private
  copy under their own namespace). The dense side has one shared `ApcOptimizer.Dense` namespace, so
  the existing `ByteCheckPack.lean` copy is reused unchanged rather than re-declared here.
* `denseByteJustified` (`BusPairCancelJustify.lean`) is *exactly* the `byteJustified` this pass's
  `byteDropKeep` calls (`BusPairCancel.lean:744`) — its doc comment already names this very pass as
  its consumer ("used by the coda's `RedundantByteDrop`"). Reused unchanged; it internally threads
  the plain full-scan witness lookup (`fun _ => rest`) and disables the basis-reduction arm
  (`fwits := fun _ => []`), exactly as the spec `byteJustified` does.
* `DenseExpr.constValue?` (`DropPasses.lean`) is the dense `Expression.constValue?`.
* `DenseConstraintSystem.filterBus` (`Rewrite.lean`) is the dense `ConstraintSystem.filterBus` the
  pass's `.out` is built from.
* `BusFacts`/`BusSemantics`/`ByteXorSpec` are representation-independent (`decode`/`encode` are
  `{α : Type} → …`), consulted unqualified exactly as the spec does.

## `byteCheckOperands?` is not `denseSvCheck?`

`ByteCheckPack.lean`'s `denseSvCheck?` looks similar (same `byteXorSpec` recognition tower) but is a
genuinely different function, so it is transliterated locally here as `denseByteCheckOperands?`
rather than reused: it drops `denseSvCheck?`'s multiplicity-`1` gate (this pass justifies an
interaction's *acceptance* regardless of the dropped check's own multiplicity — soundness never
reads it), returns a *list* of justified operands (one for the XOR/OR-identity shapes, two for the
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
    the same zero mirrors; for `op = pairOp` the packed pair `r = 0`. `none` otherwise. Mirrors
    `byteCheckOperands?` (`OldVariableBased/RedundantByteDrop.lean:88`), same gate order (`bound =
    256`, then decode, then each shape in the same order) and the same `==`/`&&` (Bool) recognition
    style as the reference (not `denseSvCheck?`'s `=`/`∧` style). -/
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
    checks). Justifying only against these makes the drop non-circular. Mirrors `byteDropBase`
    (`OldVariableBased/RedundantByteDrop.lean:245`). -/
def denseByteDropBase (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (denseByteCheckOperands? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized byte check whose operands are all byte-justified from the
    constraints and the justification base. Mirrors `byteDropKeep`
    (`OldVariableBased/RedundantByteDrop.lean:251`). -/
def denseByteDropKeep (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (all : List (DenseExpr p)) (rest : List (BusInteraction (DenseExpr p)))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseByteCheckOperands? bs facts bi with
  | some ops => !(ops.all (fun e => denseByteJustified 256 pw.isPrime all bs facts rest e))
  | none => true

/-- Drop every stateless byte-check interaction whose operands are all byte-justified from the
    parts of the system this pass can never remove. Mirrors `redundantByteDropPass`'s computed
    output (`OldVariableBased/RedundantByteDrop.lean:260`), dropping its `PassCorrect` term. -/
def denseRedundantByteDropF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseByteDropKeep pw bs facts d.algebraicConstraints (denseByteDropBase bs facts d))

end ApcOptimizer.Dense
