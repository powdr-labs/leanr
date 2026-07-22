import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense generalized single-value byte-check packing (Task 3, chunk BP-I1 — impl)

Dense, `VarId`-native transliteration of the reference `ByteCheckPack` pass's *runtime* content:
`complExpr` (:37), `isByteCompl` (:42), `svCheck?` (:63), `findSecond` (:231), `findGo` (:268), and
the pass `byteCheckPackPass` (:315), which the `"bytePack"`/`"bytePackLate"` labels
(`Implementation/Optimizer.lean`) each run through an outer `iterateToFixpoint`. This is
**impl-only** (chunk BP-I1 of the port): no `_sound` lemma is ported (`isByteCompl_sound`,
`svCheck?_sound`, `findSecond_sound`, and `findGo`'s inline `mergeStateless2_correct` obligation are
all proof, left for the prover), and no theorem is stated here; nothing is wired into the
`denseImpl` selector.

## Reuse map

* `mkBytePair` → `denseMkBytePair` (`BusPairCancelCheck.lean`, placed next to `denseMkByteCheck` per
  its module header's flag for this very port).
* `Expression.normalize` → `DenseExpr.normalize` (`Normalize.lean:54`).
* `Expression.constValue?` → `DenseExpr.constValue?` (`DropPasses.lean:64`).
* `DecidableEq (Expression p)`/`DecidableEq (BusInteraction (Expression p))` (from
  `deriving instance` in `FactPass.lean`) → `DecidableEq (DenseExpr p)` (derived directly on the
  inductive, `Encoding.lean:33`) and the generic derived `DecidableEq (BusInteraction α)` instance
  applied at `α := DenseExpr p`. `facts.byteXorSpec`/`ByteXorSpec.decode`/`encode` are
  representation-independent (`{α : Type} → …`) and are consulted unqualified, exactly as the spec
  does.

## `denseFindGo`'s positional split (no re-`decide`)

The spec `findGo` returns an `Option (PassResult cs bs)`: at the chosen candidate it checks (via a
`dite`) that `cs.busInteractions = revPre.reverse ++ a :: mid ++ b :: post` — an O(n) equation that,
given how `revPre`/`mid`/`post` were threaded by the scan itself, always holds at runtime; the
`dite` exists only so the *proof* obligation (`mergeStateless2_correct`'s hypotheses) has that
equation available, not because the scan could ever produce a wrong split. `denseFindGo` below drops
the `cs`/`hp1` parameters (unused by the scan's own selection decisions — only by the spec's
`PassResult` construction) and the re-`decide`, returning the positionally-split pack data directly:
`(busId, spec, pre, eA, mid, eB, post)` with `pre = revPre.reverse`. The **selection** — first `a`
with `denseSvCheck? = some eA`; first `b` strictly after `a` on the same bus with
`denseSvCheck? = some eB` (`denseFindSecond`); `a`'s `byteXorSpec` bus-fact lookup and its `bound =
256` gate — is mirrored in the exact same order as the spec, so the pair chosen is identical to what
the spec would choose against the same input list; only the re-verification of the (trivially true)
split equation is dropped. `busId` (`= a.busId`, needed by `denseMkBytePair` at the call site but not
part of the spec's own six informally-named return components `spec, pre, eA, mid, eB, post`) is
carried explicitly as the tuple's first component — a data-completeness addition, not a selection or
control-flow change; **flagged for the prover**, who reconstructs the split equation
`d.busInteractions = pre ++ a :: mid ++ b :: post` as a loop invariant of the scan rather than
re-deciding it. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Recognizing the NOT-form complement -/

/-- `255 − e` as a dense expression. Mirrors `complExpr`
   . -/
def denseComplExpr (e : DenseExpr p) : DenseExpr p := .add (.const 255) (.mul (.const (-1)) e)

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment? Decided by folding
    `b − (255 − a)` to a constant and checking it is `0`. Mirrors `isByteCompl`
   . -/
def denseIsByteCompl (a b : DenseExpr p) : Bool :=
  (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).normalize.constValue? == some 0

/-! ## Recognizing a single-value byte check in any encoding -/

/-- The value byte-checked by a multiplicity-1 single-value byte check, recognized through the
    VM-neutral `byteXorSpec` (byte bound `256`, decoded op `= xorOp`): the self-check (`o₁ = o₂`,
    `r = 0`), the two XOR-with-zero mirrors (`o₂ = 0, o₁ = r` / `o₁ = 0, o₂ = r`), and the two NOT
    (XOR-with-255) forms (`o₂ = 255, r = 255 − o₁` / `o₁ = 255, r = 255 − o₂`, when `256 ≤ p`) all
    return the checked operand; `none` otherwise. Mirrors `svCheck?`
   , same 7 branches in the same order (self-check, two
    XOR-with-zero mirrors, two NOT-form mirrors — each gated `256 ≤ p` — then the OR-identity mirror
    pair), and the same gate order (`bound = 256`, then multiplicity/op, then each shape). -/
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
    interaction `b`, its checked value `eB`, and the remainder `post`. Mirrors `findSecond`
   . -/
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

/-- Fused scan for the first packable pair, returning plain positionally-split pack data instead of
    a `PassResult` — see the module header for why the split equation needs no re-`decide` here and
    why `busId` is carried explicitly. Mirrors `findGo`
   , same selection order: first `a` with a recognized
    single-value check, then the first same-bus match after it (`denseFindSecond`), then `a`'s
    `byteXorSpec` bus fact and its `bound = 256` gate. -/
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
