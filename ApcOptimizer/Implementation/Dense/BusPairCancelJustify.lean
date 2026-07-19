import ApcOptimizer.Implementation.Dense.RootPairUnifyNative
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancel

set_option autoImplicit false

/-! # Dense byte-justification certificates for `busPairCancel` (Task 3, chunk C1a — impl)

Dense, `VarId`-native transliteration of the *deep byte justification* tower at the top of
`OptimizerPasses/BusPairCancel.lean` (`Expression.containsVar`/`singleVarAux`/`isSingleVar`,
`pointByteOk`, `deepByteVars`, `deepEnumDoms`, `deepBoundOk`, `deepByteJustified`, `exprPointByte`,
`domainByteJustified`). This is a pure **leaf** chunk: no bus-pair scan, no loop, no pass — just the
per-slot byte-justification certificates later `busPairCancel` chunks (C1b onward) will call. This
file is **impl-only**: no `_sound` lemma is ported and no theorem is stated (definitions only).

## Constants

`maxDeepPoints`/`maxDeepDomain`/`maxDeepConstraints`/`maxDeepVars` are reused **directly, unqualified**
from the spec file (`OptimizerPasses/BusPairCancel.lean`): they are plain `Nat` literals, wholly
representation-independent (they cap enumeration/candidate counts, never touch `Variable`/`VarId`),
so mirroring them under a new name here would just be a duplicate binding to the same value — the
established precedent for such spec constants (e.g. `maxDomainBound`/`maxEnumSize`/`maxEnumWork`,
reused unqualified throughout `Dense/DomainBatch.lean`/`Dense/DomainFold.lean`).

## Reuse map (not re-derived)

`denseLinearize`/`DenseLinExpr.norm` (`Dense/Affine.lean`/`Dense/Normalize.lean`), `denseFindVarBound`
(`Dense/RootPairUnifyNative.lean`), `denseFindDomainAlg`/`denseAssignments` (`Dense/DomainFold.lean`),
`denseEnvOfFast` (`Dense/DomainBatch.lean`), `DenseExpr.constValue?` (`Dense/DropPasses.lean`),
`DenseExpr.fold` (`Dense/ExprOps.lean`), `DenseExpr.substF` (`Dense/SubstMap.lean`), `DenseExpr.vars`
(`Dense/Encoding.lean`) — all pulled in transitively through the single `Dense.RootPairUnifyNative`
import (its own reuse-map anchor for this cluster; later chunks of this pass should likewise import
it rather than re-deriving any of the above). `denseInteractionBound`/`denseVarSlot`
(`Dense/DigitFold.lean`) are **not used by this chunk** (nothing here reads a bus interaction's payload
slots directly — that is `denseFindVarBound`'s job, already ported) but are transitively imported and
listed for later chunks' benefit.

## Flagged deviation: `Expression.containsVar` has NO new dense counterpart here

`Expression.containsVar` (`BusPairCancel.lean:65`) is structurally **identical** to
`Expression.mentions` (`Gauss.lean:38`) — same recursion, same leaf case (`y == x`) — just declared
under a different name local to this pass file. Its dense mirror already exists, reused unchanged
elsewhere in the dense layer: `DenseExpr.mentions` (`Dense/SubstMap.lean:192`). Introducing a second,
byte-identical `DenseExpr.containsVar` definition here would be a pure duplicate, not a port, so this
file does **not** define one. **Later chunks that need `containsVar`'s dense counterpart (e.g. the
`byteJustifiedW`-style per-variable candidate filter, `all.filter (Expression.containsVar x)`) must
call `DenseExpr.mentions x` directly** — flagged loudly here since the spec name has no matching dense
declaration to grep for.

`Expression.singleVarAux`/`Expression.isSingleVar` have no existing dense analogue (verified: no
`singleVarAux`/`isSingleVar` in any `Dense/*.lean` file prior to this one; `denseSingleVarCs`
(`Dense/FlagFoldDropsNative.lean`) is a different, unrelated concept — the *list* of constraints with
exactly one distinct variable via `c.vars.eraseDups.length == 1`, not this expression-level "is a
single-variable expression" allocation-free walk) — so they are transliterated fresh below, under
`DenseExpr.singleVarAux`/`DenseExpr.isSingleVar` (method-style, mirroring the spec's `Expression.`
dot-notation), exactly as spec structures them. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `DenseExpr.singleVarAux`/`isSingleVar` (fresh port — see the module header) -/

/-- The expression's single distinct variable: `some (some v)` when exactly `v` occurs, `some none`
    when no variable occurs, `none` when several distinct variables occur. Cheap pre-filter for the
    constraints `denseFindDomainAlg` can actually derive a domain from. Mirrors `Expression.singleVarAux`
    (`BusPairCancel.lean:74`). -/
def DenseExpr.singleVarAux : DenseExpr p → Option (Option VarId)
  | .const _ => some none
  | .var y => some (some y)
  | .add a b | .mul a b =>
    match a.singleVarAux, b.singleVarAux with
    | some none, r => r
    | r, some none => r
    | some (some u), some (some v) => if u == v then some (some u) else none
    | _, _ => none

/-- Is the expression a single-variable expression (exactly one distinct variable)? Mirrors
    `Expression.isSingleVar` (`BusPairCancel.lean:85`). -/
def DenseExpr.isSingleVar (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some _) => true
  | _ => false

/-! ## The deep enumeration certificate chain -/

/-- Per-point core of the deep justification. The point `pt` fixes the enumerable variables `keys`
    of the constraint `c`; after substituting and folding, the constraint must be linear and — once
    normalized — either pin `x` to a re-checked byte constant, or equate `x` (coefficient-for-
    coefficient, no constant) to a single variable in `byteVars` (the precomputed byte-bounded
    variables — so the per-point work is allocation-light and scans nothing). Mirrors `pointByteOk`
    (`BusPairCancel.lean:96`). -/
def densePointByteOk (x : VarId) (c : DenseExpr p) (byteVars : List VarId)
    (keys : List VarId) (pt : List (VarId × ZMod p)) : Bool :=
  match denseLinearize ((c.substF (fun v =>
      if keys.contains v then some (.const (denseEnvOfFast pt v)) else none)).fold) with
  | none => false
  | some l =>
    let ln := DenseLinExpr.norm l
    match ln.terms with
    | [(v, a)] =>
      -- `x` is pinned to the (re-checked) root; it must be a byte
      decide (v = x) && decide (a ≠ 0) &&
        decide (a * (-(a⁻¹ * ln.const)) + ln.const = 0) &&
        decide ((-(a⁻¹ * ln.const) : ZMod p).val < 256)
    | [(v1, a1), (v2, a2)] =>
      -- `x = other` (opposite coefficients, no constant); the other side is byte-bounded
      decide (ln.const = 0) &&
      (if v1 = x then
        decide (a2 = -a1) && decide (a1 ≠ 0) && byteVars.contains v2
       else if v2 = x then
        decide (a1 = -a2) && decide (a2 ≠ 0) && byteVars.contains v1
       else false)
    | _ => false

/-- The variables of `c` (other than `x`) with a proven byte bound from the remaining interactions —
    computed once per candidate, not once per enumeration point. Mirrors `deepByteVars`
    (`BusPairCancel.lean:128`). -/
def denseDeepByteVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) (c : DenseExpr p) :
    List VarId :=
  (c.vars.eraseDups.filter (fun v => v ≠ x)).filter (fun v =>
    match denseFindVarBound bs facts (wits v) v with
    | some b => decide (b ≤ 256)
    | none => false)

/-- The variables of `c` other than `x` that carry a small proven *constraint-derived* finite domain
    (selector flags) — the candidates for enumeration in the deep justification. Mirrors
    `deepEnumDoms` (`BusPairCancel.lean:143`). -/
def denseDeepEnumDoms (domCs : List (DenseExpr p)) (x : VarId) (c : DenseExpr p) :
    List (VarId × List (ZMod p)) :=
  (c.vars.eraseDups.filter (fun v => v ≠ x)).filterMap (fun v =>
    match denseFindDomainAlg domCs v with
    | some d => if d.length ≤ maxDeepDomain then some (v, d) else none
    | none => none)

/-- Deep byte bound for `x` from one constraint `c`: enumerate the small proven finite domains of
    `c`'s other variables (e.g. one-hot selector flags) and require `densePointByteOk` at every
    point. Mirrors `deepBoundOk` (`BusPairCancel.lean:154`). -/
def denseDeepBoundOk (domCs : List (DenseExpr p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) (c : DenseExpr p) :
    Bool :=
  let enum := denseDeepEnumDoms domCs x c
  if (c.vars.eraseDups.filter (fun v => v ≠ x)).length ≤ maxDeepVars &&
      (enum.map (fun vd => vd.2.length)).prod ≤ maxDeepPoints then
    (denseAssignments enum).all
      (densePointByteOk x c (denseDeepByteVars bs facts wits x c) (enum.map Prod.fst))
  else false

/-- Deep byte justification for `x`: one of the first `maxDeepConstraints` constraints mentioning `x`
    (the caller passes them as `cands`) pins it via `denseDeepBoundOk`. Mirrors `deepByteJustified`
    (`BusPairCancel.lean:168`). -/
def denseDeepByteJustified (domCs cands : List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) : Bool :=
  (cands.take maxDeepConstraints).any (fun c => denseDeepBoundOk domCs bs facts wits x c)

/-! ## Affine bound propagation for byte-domain expressions -/

/-- Evaluate the single-variable expression `e` with its variable fixed to `d` and check the result
    is a byte constant. Mirrors `exprPointByte` (`BusPairCancel.lean:339`). -/
def denseExprPointByte (e : DenseExpr p) (x : VarId) (d : ZMod p) : Bool :=
  match (e.substF (fun v => if v = x then some (.const d) else none)).fold.constValue? with
  | some c => decide (c.val < 256)
  | none => false

/-- Is `e` a byte because its single variable `x` ranges over a small constraint-derived finite
    domain at every point of which `e` evaluates to a byte? Mirrors `domainByteJustified`
    (`BusPairCancel.lean:348`). -/
def denseDomainByteJustified (domCs : List (DenseExpr p)) (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some x) =>
    match denseFindDomainAlg domCs x with
    | some d => decide (d.length ≤ maxDeepDomain) && d.all (denseExprPointByte e x)
    | none => false
  | _ => false

end ApcOptimizer.Dense
