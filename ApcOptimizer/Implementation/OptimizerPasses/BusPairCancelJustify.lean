import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.BusPairCancel

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
  (c.vars.dedup.filter (fun v => v ≠ x)).filter (fun v =>
    match denseFindVarBound bs facts (wits v) v with
    | some b => decide (b ≤ 256)
    | none => false)

/-- The variables of `c` other than `x` that carry a small proven *constraint-derived* finite domain
    (selector flags) — the candidates for enumeration in the deep justification. Mirrors
    `deepEnumDoms` (`BusPairCancel.lean:143`). -/
def denseDeepEnumDoms (domCs : List (DenseExpr p)) (x : VarId) (c : DenseExpr p) :
    List (VarId × List (ZMod p)) :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filterMap (fun v =>
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
  if (c.vars.dedup.filter (fun v => v ≠ x)).length ≤ maxDeepVars &&
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

/-! ## Affine bound propagation through a linearized form (Task 3, chunk C1b — impl)

Dense, `VarId`-native transliteration of the *affine* justification tier
(`BusPairCancel.lean:401-489`): `linTermsNatBound`/`LinExpr.natBound`/`affineJustified`. Reuses
`denseLinearize`/`DenseLinExpr.norm` (already imported transitively — see the C1a header). -/

/-- Natural upper bound of a term list `Σ cᵥ·v` under per-variable value bounds `bnd` (`bnd v`
    bounds `(denv v).val` strictly): `Σ cᵥ.val·(bnd v − 1)`; `none` if any variable is unbounded.
    Mirrors `linTermsNatBound` (`BusPairCancel.lean:413`). -/
def denseLinTermsNatBound (bnd : VarId → Option Nat) : List (VarId × ZMod p) → Option Nat
  | [] => some 0
  | (v, c) :: rest =>
    match bnd v, denseLinTermsNatBound bnd rest with
    | some b, some acc => some (c.val * (b - 1) + acc)
    | _, _ => none

/-- Natural upper bound of `L.eval`: `L.const.val + Σ cᵥ.val·(bnd v − 1)`. Mirrors
    `LinExpr.natBound` (`BusPairCancel.lean:421`). -/
def DenseLinExpr.natBound (bnd : VarId → Option Nat) (L : DenseLinExpr p) : Option Nat :=
  (denseLinTermsNatBound bnd L.terms).map (fun s => L.const.val + s)

/-- Affine byte/limb justification: `e` linearizes to a form whose per-variable-bounded natural
    value is `< bound` (and `< p`, so it does not wrap). Mirrors `affineJustified`
    (`BusPairCancel.lean:483`). -/
def denseAffineJustified (bound : Nat) (bnd : VarId → Option Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L =>
    match L.natBound bnd with
    | some M => decide (M < bound) && decide (M < p)
    | none => false
  | none => false

/-! ## Basis justification (Task 3, chunk C1b — impl)

Dense, `VarId`-native transliteration of the *basis* justification tier
(`BusPairCancel.lean:506-706`): `formBoundAt`/`basisReduceGo`/`basisJustified`. `basisFuel`
(`BusPairCancel.lean:580`) is a plain `Nat` literal, wholly representation-independent, so it is
reused unqualified below — same precedent as `maxDeepPoints` in the C1a header.

### `IntervalForce.srep` reuse (no dense counterpart needed)

`IntervalForce.srep` (`OptimizerPasses/IntervalForce.lean:50`, already transitively imported
through `OptimizerPasses.BusPairCancel`, which imports `OptimizerPasses.IntervalForce`) is
`fun c : ZMod p => if c.val ≤ (p - 1) / 2 then (c.val : Int) else (c.val : Int) - p` — a plain
`ZMod p → Int` function with no `Variable`/`Expression`/`VarId`/`DenseExpr` anywhere in its
signature or body. It is representation-independent data, so `basisReduceGo`'s dense mirror below
calls it exactly unqualified, exactly as it calls `p` itself. -/

/-- The linearized (merged) form and bound of payload slot `i` of `bi`, when the multiplicity is
    a nonzero constant and the slot carries a `slotBound`. Mirrors `formBoundAt`
    (`BusPairCancel.lean:521`). -/
def denseFormBoundAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : Nat) : Option (DenseLinExpr p × Nat) :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match bi.payload[i]?,
            facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
      | some e, some B =>
        match denseLinearize e with
        | some L => some (L.norm, B)
        | none => none
      | _, _ => none

/-- Fuel-bounded basis reduction: is `L`'s value provably `< bound − used` using per-variable
    bounds (`bnd`, the finish arm) after subtracting positive integer multiples of range-checked
    slot forms from `fwits` (each step accounts its form's worst case against `used`)? Structural
    recursion on `fuel` preserved exactly (same recursion shape as spec). Mirrors `basisReduceGo`
    (`BusPairCancel.lean:585`). -/
def denseBasisReduceGo (bound : Nat) (bnd : VarId → Option Nat) {bs : BusSemantics p}
    (facts : BusFacts p bs) (fwits : VarId → List (BusInteraction (DenseExpr p))) :
    Nat → Nat → DenseLinExpr p → Bool
  | 0, _, _ => false
  | fuel + 1, used, L =>
    (match L.natBound bnd with
     | some M => decide (used + M < bound) && decide (used + M < p)
     | none => false) ||
    (L.terms.map Prod.fst).any (fun v =>
      (fwits v).any (fun bi =>
        (List.range bi.payload.length).any (fun i =>
          match denseFormBoundAt facts bi i with
          | none => false
          | some (Lf, Bf) =>
            let cF := IntervalForce.srep (Lf.coeff v)
            let μi := IntervalForce.srep (L.coeff v) / cF
            if cF ≠ 0 ∧ 0 < μi ∧ cF * μi = IntervalForce.srep (L.coeff v) then
              denseBasisReduceGo bound bnd facts fwits fuel (used + μi.toNat * (Bf - 1))
                ((L.add (Lf.scale (-(μi.toNat : ZMod p)))).norm)
            else false)))

/-- Basis justification: `e` linearizes to a form the fuel-bounded reduction proves `< bound`.
    Mirrors `basisJustified` (`BusPairCancel.lean:681`). -/
def denseBasisJustified (bound : Nat) (bnd : VarId → Option Nat) {bs : BusSemantics p}
    (facts : BusFacts p bs) (fwits : VarId → List (BusInteraction (DenseExpr p)))
    (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L => denseBasisReduceGo bound bnd facts fwits basisFuel 0 L.norm
  | none => false

/-! ## The byte-justification dispatcher (Task 3, chunk C1c — impl)

Dense, `VarId`-native transliteration of the top of the byte-justification tower
(`BusPairCancel.lean:707-869`): `byteJustifiedW`/`byteJustified`/`recvSlotsJustified`. These tie
together the leaf certificates from C1a (`denseDeepByteJustified`/`denseDomainByteJustified`) and
C1b (`denseAffineJustified`/`denseBasisJustified`) via a fixed-order, short-circuiting
disjunction — the alternative order and the `||`/`&&` short-circuiting are preserved exactly, and
each `match`/`if` mirrors the spec's `dif`/`match` one for one. `Expression.isSingleVar`'s dense
counterpart is `DenseExpr.isSingleVar` (C1a); `Expression.containsVar`'s is `DenseExpr.mentions`
(reused unchanged from `Dense/SubstMap.lean`, flagged already in the C1a module header — no new
declaration needed here either). No `_sound` lemma is ported (impl-only chunk). -/

/-- Is `e` provably a byte under every assignment satisfying the remaining system? Either a
    constant `< bound`, a variable with a proven bus-fact bound `≤ bound` derived from the
    remaining interactions, or — when `deep` is set — a variable a constraint pins to a byte on
    every point of its selector flags' finite domains (`denseDeepByteJustified`), or a
    single-variable expression whose variable's finite domain makes `e` a byte at every point
    (`denseDomainByteJustified`), or an affine recomposition of bounded limbs
    (`denseAffineJustified`), or a basis reduction against range-checked slot forms from the
    second witness lookup `fwits` (`denseBasisJustified`).

    Parameterized form: the remaining interactions are consulted through the witness lookup
    `wits` (see `denseDeepByteVars`), the single-variable constraints `domCs` and the
    per-variable candidate constraints `candsOf` are precomputed by the caller. Mirrors
    `byteJustifiedW` (`BusPairCancel.lean:722`). -/
def denseByteJustifiedW (bound : Nat) (deep : Bool) (domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (e : DenseExpr p) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < bound)
  | none =>
    (match e with
     | .var x =>
       (match denseFindVarBound bs facts (wits x) x with
        | some b => decide (b ≤ bound)
        | none => false) ||
       (deep && decide (256 ≤ bound) &&
         denseDeepByteJustified domCs (candsOf x) bs facts wits x)
     | _ => false) ||
    (deep && decide (256 ≤ bound) && denseDomainByteJustified domCs e) ||
    denseAffineJustified bound (fun x => denseFindVarBound bs facts (wits x) x) e ||
    denseBasisJustified bound (fun x => denseFindVarBound bs facts (wits x) x) facts fwits e

/-- The plain full-scan form (used by the coda's `RedundantByteDrop`): witness lookup and
    precomputed constraint lists instantiated with the naive per-query filters. The basis arm is
    disabled (`fwits = []`): feeding the whole region would rescan it per queried variable, and
    the byte-level drops it serves don't need range-checked forms. Mirrors `byteJustified`
    (`BusPairCancel.lean:744`). -/
def denseByteJustified (bound : Nat) (deep : Bool) (all : List (DenseExpr p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (DenseExpr p))) (e : DenseExpr p) : Bool :=
  denseByteJustifiedW bound deep (all.filter DenseExpr.isSingleVar)
    (fun x => all.filter (DenseExpr.mentions x)) bs facts (fun _ => rest) (fun _ => []) e

/-- Are all of `R`'s payload entries at the declared byte slots justified (through the witness
    lookup `wits` and precomputed `domCs`/`candsOf`, see `denseByteJustifiedW`)? Mirrors
    `recvSlotsJustified` (`BusPairCancel.lean:833`). -/
def denseRecvSlotsJustified (bound : Nat) (deep : Bool) (domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : Bool :=
  slots.all (fun slot =>
    match R.payload[slot]? with
    | some e => denseByteJustifiedW bound deep domCs candsOf bs facts wits fwits e
    | none => true)

end ApcOptimizer.Dense
