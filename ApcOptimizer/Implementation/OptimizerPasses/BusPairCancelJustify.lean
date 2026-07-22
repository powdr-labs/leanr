import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.ListSplit
import ApcOptimizer.Implementation.OptimizerPasses.SearchBudgets

set_option autoImplicit false

/-! # Dense byte-justification certificates for `busPairCancel`

Runtime-only certificates for deciding whether an expression is provably a byte (`< 256`) or
otherwise bounded, used by the byte-justified drops inside `busPairCancel`. This is a pure **leaf**
file: no bus-pair scan, no loop, no pass — just the per-slot byte-justification certificates later
files build on. It is **impl-only**: it carries no soundness lemma and states no theorem
(definitions only).

## Constants

`maxDeepPoints`/`maxDeepDomain`/`maxDeepConstraints`/`maxDeepVars` come from the shared budget home
`SearchBudgets.lean`, reused unqualified: they are plain `Nat` literals that only cap
enumeration/candidate counts.

## Reuse map

`denseLinearize`/`DenseLinExpr.norm` (`Affine.lean`/`Normalize.lean`), `denseFindVarBound`
(`RootPairUnify.lean`), `denseFindDomainAlg`/`denseAssignments` (`DomainFold.lean`),
`denseEnvOfFast` (`DomainBatch.lean`), `DenseExpr.constValue?` (`DropPasses.lean`),
`DenseExpr.fold` (`ExprOps.lean`), `DenseExpr.substF` (`SubstMap.lean`), `DenseExpr.vars`
(`Encoding.lean`) are all pulled in transitively through the `RootPairUnify` import.
`denseInteractionBound`/`denseVarSlot` (`DigitFold.lean`) are not used here (nothing here reads a
bus interaction's payload slots directly — that is `denseFindVarBound`'s job) but are transitively
imported.

`DenseExpr.mentions` (`SubstMap.lean`) is the occurrence check used below; there is no separate
`containsVar`-named definition. `DenseExpr.singleVarAux`/`DenseExpr.isSingleVar` (defined below)
recognise a single-variable expression: `denseSingleVarCs` (`FlagFoldDrops.lean`) is a different,
unrelated concept — the *list* of constraints with exactly one distinct variable via
`c.vars.eraseDups.length == 1`, not this expression-level walk. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `DenseExpr.singleVarAux`/`isSingleVar` -/

/-- The expression's single distinct variable: `some (some v)` when exactly `v` occurs, `some none`
    when no variable occurs, `none` when several distinct variables occur. Cheap pre-filter for the
    constraints `denseFindDomainAlg` can actually derive a domain from. -/
def DenseExpr.singleVarAux : DenseExpr p → Option (Option VarId)
  | .const _ => some none
  | .var y => some (some y)
  | .add a b | .mul a b =>
    match a.singleVarAux, b.singleVarAux with
    | some none, r => r
    | r, some none => r
    | some (some u), some (some v) => if u == v then some (some u) else none
    | _, _ => none

/-- Is the expression a single-variable expression (exactly one distinct variable)? -/
def DenseExpr.isSingleVar (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some _) => true
  | _ => false

/-! ## The deep enumeration certificate chain -/

/-- Per-point core of the deep justification. The point `pt` fixes the enumerable variables `keys`
    of the constraint `c`; after substituting and folding, the constraint must be linear and — once
    normalized — either pin `x` to a re-checked byte constant, or equate `x` (coefficient-for-
    coefficient, no constant) to a single variable in `byteVars` (the precomputed byte-bounded
    variables — so the per-point work is allocation-light and scans nothing). -/
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
    computed once per candidate, not once per enumeration point. -/
def denseDeepByteVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) (c : DenseExpr p) :
    List VarId :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filter (fun v =>
    match denseFindVarBound bs facts (wits v) v with
    | some b => decide (b ≤ 256)
    | none => false)

/-- The variables of `c` other than `x` that carry a small proven *constraint-derived* finite domain
    (selector flags) — the candidates for enumeration in the deep justification. -/
def denseDeepEnumDoms (domCs : List (DenseExpr p)) (x : VarId) (c : DenseExpr p) :
    List (VarId × List (ZMod p)) :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filterMap (fun v =>
    match denseFindDomainAlg domCs v with
    | some d => if d.length ≤ maxDeepDomain then some (v, d) else none
    | none => none)

/-- Deep byte bound for `x` from one constraint `c`: enumerate the small proven finite domains of
    `c`'s other variables (e.g. one-hot selector flags) and require `densePointByteOk` at every
    point. -/
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
    (the caller passes them as `cands`) pins it via `denseDeepBoundOk`. -/
def denseDeepByteJustified (domCs cands : List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) : Bool :=
  (cands.take maxDeepConstraints).any (fun c => denseDeepBoundOk domCs bs facts wits x c)

/-! ## Affine bound propagation for byte-domain expressions -/

/-- Evaluate the single-variable expression `e` with its variable fixed to `d` and check the result
    is a byte constant. -/
def denseExprPointByte (e : DenseExpr p) (x : VarId) (d : ZMod p) : Bool :=
  match (e.substF (fun v => if v = x then some (.const d) else none)).fold.constValue? with
  | some c => decide (c.val < 256)
  | none => false

/-- Is `e` a byte because its single variable `x` ranges over a small constraint-derived finite
    domain at every point of which `e` evaluates to a byte? -/
def denseDomainByteJustified (domCs : List (DenseExpr p)) (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some x) =>
    match denseFindDomainAlg domCs x with
    | some d => decide (d.length ≤ maxDeepDomain) && d.all (denseExprPointByte e x)
    | none => false
  | _ => false

/-! ## Affine bound propagation through a linearized form

The affine justification tier: reuses `denseLinearize`/`DenseLinExpr.norm` (imported transitively,
see the reuse map above). -/

/-- Natural upper bound of a term list `Σ cᵥ·v` under per-variable value bounds `bnd` (`bnd v`
    bounds `(denv v).val` strictly): `Σ cᵥ.val·(bnd v − 1)`; `none` if any variable is unbounded. -/
def denseLinTermsNatBound (bnd : VarId → Option Nat) : List (VarId × ZMod p) → Option Nat
  | [] => some 0
  | (v, c) :: rest =>
    match bnd v, denseLinTermsNatBound bnd rest with
    | some b, some acc => some (c.val * (b - 1) + acc)
    | _, _ => none

/-- Natural upper bound of `L.eval`: `L.const.val + Σ cᵥ.val·(bnd v − 1)`. -/
def DenseLinExpr.natBound (bnd : VarId → Option Nat) (L : DenseLinExpr p) : Option Nat :=
  (denseLinTermsNatBound bnd L.terms).map (fun s => L.const.val + s)

/-- Affine byte/limb justification: `e` linearizes to a form whose per-variable-bounded natural
    value is `< bound` (and `< p`, so it does not wrap). -/
def denseAffineJustified (bound : Nat) (bnd : VarId → Option Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L =>
    match L.natBound bnd with
    | some M => decide (M < bound) && decide (M < p)
    | none => false
  | none => false

/-! ## Basis justification

The basis justification tier. `basisFuel` (`SearchBudgets.lean`) is a plain `Nat` literal, reused
unqualified below.

### `IntervalForce.srep`

`IntervalForce.srep` (`IntervalForce.lean`, imported above) is
`fun c : ZMod p => if c.val ≤ (p - 1) / 2 then (c.val : Int) else (c.val : Int) - p` — a plain
`ZMod p → Int` function with no `VarId`/`DenseExpr` anywhere in its signature or body, called
unqualified below by `denseBasisReduceGo`, exactly as it calls `p` itself. -/

/-- The linearized (merged) form and bound of payload slot `i` of `bi`, when the multiplicity is
    a nonzero constant and the slot carries a `slotBound`. -/
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
    slot forms from `fwits` (each step accounts its form's worst case against `used`)? The
    recursion is structural on `fuel`. -/
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

/-- Basis justification: `e` linearizes to a form the fuel-bounded reduction proves `< bound`. -/
def denseBasisJustified (bound : Nat) (bnd : VarId → Option Nat) {bs : BusSemantics p}
    (facts : BusFacts p bs) (fwits : VarId → List (BusInteraction (DenseExpr p)))
    (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L => denseBasisReduceGo bound bnd facts fwits basisFuel 0 L.norm
  | none => false

/-! ## The byte-justification dispatcher

The top of the byte-justification tower: `denseByteJustifiedW`/`denseByteJustified`/
`denseRecvSlotsJustified`. These tie together the leaf certificates above
(`denseDeepByteJustified`/`denseDomainByteJustified`) and the affine/basis tier
(`denseAffineJustified`/`denseBasisJustified`) via a fixed-order, short-circuiting disjunction. No
soundness lemma is stated here (impl-only). -/

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
    per-variable candidate constraints `candsOf` are precomputed by the caller. -/
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
    the byte-level drops it serves don't need range-checked forms. -/
def denseByteJustified (bound : Nat) (deep : Bool) (all : List (DenseExpr p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (DenseExpr p))) (e : DenseExpr p) : Bool :=
  denseByteJustifiedW bound deep (all.filter DenseExpr.isSingleVar)
    (fun x => all.filter (DenseExpr.mentions x)) bs facts (fun _ => rest) (fun _ => []) e

/-- Are all of `R`'s payload entries at the declared byte slots justified (through the witness
    lookup `wits` and precomputed `domCs`/`candsOf`, see `denseByteJustifiedW`)? -/
def denseRecvSlotsJustified (bound : Nat) (deep : Bool) (domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : Bool :=
  slots.all (fun slot =>
    match R.payload[slot]? with
    | some e => denseByteJustifiedW bound deep domCs candsOf bs facts wits fwits e
    | none => true)

end ApcOptimizer.Dense
