import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.SeqzCollapse
import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse

set_option autoImplicit false

/-! # Collapsing the `sltu x, 1` (seqz) gadget — dense `VarId` port (impl-only)

Dense, `VarId`-native transliteration of `OldVariableBased/SeqzCollapse.lean`'s *runtime*
definitions: the expression templates (`eM1`/`e0`/`e1`/`e2`/`sExpr`/`markerSum`/`krExpr`/`twoRExpr`/
`diffInner`/`diffInner0`/`clusterConstraints`/`clusterBus`/`boolConstraint`/`sumExpr4`/
`newConstraints`/`invMethod`), the recognizer (`matchMarkerSum`/`matchNegVar`/`matchE11`/
`matchPrefixVar`/`Roles`/`Roles.witnesses`/`Roles.inv`/`pureInCluster`/`extractRoles`/
`collapsedSystem`/`rolesValid`), and the scanning driver (`tryList`, `seqzCollapsePass`'s computed
output). This file is **impl-only**: no theorem/lemma from the spec file is ported (`clusterEval_iff`,
`setFive`/`setFive_free`/`setFive_at3`/`setFive_at2`/`setFive_at1`/`setFive_at0`/`setFive_atd`,
`bus_accepts_byte_zero`, `bus_byte_of_accepts`, `seqzCollapse_correct`, and every `ZMod p`-value-level
lemma (`neg_byte_val_big` … `seqz_forward`/`seqz_reconstruct`) are all proof-side, the prover's job),
and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here.

## Shape: a registry-extending native transform

Like `Reencode`/`HintCollapse`, this pass mints a fresh derived witness (the reciprocal hint `inv`
of the is-zero gadget), so it is shaped for the registry-extending builder — the prover wires it with
`DenseVerifiedPassW.ofNativeExtending (denseSeqzCollapseF) …`
(`transform : VarRegistry → (bs) → BusFacts p bs → DenseConstraintSystem p → VarRegistry ×
DenseConstraintSystem p × DenseDerivations p`, `Reencode.lean`/`HintCollapse.lean`'s own shape).
Still out of scope: the correctness theorems and the `ofNativeExtending` call itself.

## Where the fresh variable is minted, and the freshness-decision mechanism

The spec's `Roles.inv` (`OldVariableBased/SeqzCollapse.lean:533`) is a pure getter,
`⟨"seqzinv#" ++ r.dv.name, none⟩`, readable off any recognised `Roles` value without side effects
(a spec `Variable` needs no registration). `rolesValid` (`:591`) gates on `decide (r.inv ∉ cs.vars)`
before `tryList` (`:1101`) ever uses `r.inv` as a fresh column. The dense port mirrors this exactly
with the `Reencode`/`HintCollapse` established mechanism (see their headers): `denseSeqzInvVar reg r`
computes the *candidate* `Variable` — `⟨"seqzinv#" ++ (reg.resolve r.dv).name, none⟩` — by resolving
`r.dv`'s `VarId` back to the `Variable` it was originally registered for (so the name is byte-identical
to what the spec's `r.dv.name` would read directly off the same source expression); `denseIsFresh`
(`HintCollapse.lean`, reused unchanged — see its header for the mechanism: an `reg.idOf?` prefilter
composed with a linear scan of `d.occ`, the dense analogue of `cs.vars`) tests it exactly as
`rolesValid` does. The candidate is registered (`reg.register`) only on `denseSeqzTryList`'s accepting
branch, exactly mirroring `HintCollapse`'s own choice (not the spec's *construction* point, which is
unconditional but free since `Variable` carries no persistent identity) — registering-and-discarding a
`VarId` for every rejected candidate would needlessly inflate the registry for the run's remaining
lifetime, while an unregistered candidate is invisible to every downstream decision exactly as an
unreferenced spec `Variable` is.

## `BoundsMap.build` is recomputed per accepted candidate — mirrored, not hoisted

The spec's `tryList` (`:1091`) calls `BoundsMap.build facts` *inside* the `some r` branch, once per
`extractRoles`-recognised candidate that also has a `byteXorSpec` (i.e. potentially more than once
per pass invocation, since the scan keeps trying further bus interactions until `rolesValid`
succeeds). It is **not** hoisted above the scan. `BoundsMap p (collapsedSystem cs r spec) bs`'s
`build` folds only over `(collapsedSystem cs r spec).busInteractions`, which — by `collapsedSystem`'s
own definition (`:566`) — is exactly `cs.busInteractions.filter (fun bi => decide (bi ≠ bus))`, a
value that does *not* depend on the (not-yet-registered) `inv` variable. `denseSeqzTryList` below
reproduces this precisely: it computes `denseBuild bs facts (d.busInteractions.filter (fun bi' =>
decide (bi' ≠ bus)))` fresh, inside the `some r` branch, on every accepted-extraction candidate — no
memoisation across candidates, matching the spec's own (non-hoisted) cost profile exactly. This lets
freshness-checking and the byte-bound map both be computed *before* any registration, so `inv` is
still minted only on the final accepting branch (see above).

## No `PrimeWitness` — the spec re-decides primality per candidate, and so does this port

Unlike `HintCollapse`/`MonicScale`/`SplitBytePair`/`IdentitySubst`, the spec's `rolesValid`
(`:576`–`593`) inlines `decide (Nat.Prime p) && decide (1024 ≤ p) && …` as part of its `Bool` chain,
called once per `extractRoles`-recognised candidate — there is no outer `[Fact p.Prime]` or
`PrimeWitness` gate on `seqzCollapsePass` (`:1109`) or `tryList` (`:1091`) the way there is on
`hintCollapsePass`/`monicScalePass`'s callers. `denseSeqzRolesValid` below inlines the same
`decide (Nat.Prime p) && decide (1024 ≤ p)` verbatim, at the same call frequency. This *is* the
reference's own re-decide-per-candidate cost profile (flagged, not "fixed" — introducing a
`PrimeWitness` here would be exactly the kind of unrequested "improvement" the port must not make).

## Reuse map (not re-derived)

* `denseBuild` (`DigitFold.lean`) is the dense fact-derived bounds map, playing the role of
  `BoundsMap.build facts`'s `.map` field (see above for why it is recomputed the same way, not
  memoised).
* `reg.isInput` (`Bridge.lean`) is `x.powdrId?.isSome` transported through the registry, in place of
  the spec's direct `Variable.powdrId?.isSome` reads (`rolesValid`'s last conjunct).
* `DenseExpr.mentions` (`SubstMap.lean`) is `Expression.mentions`, reused unchanged by
  `denseSeqzPureInCluster`.
* `denseIsFresh` (`HintCollapse.lean`) is the freshness-prefilter mechanism, reused unchanged (see
  above) rather than re-derived, exactly as the "reuse, don't re-derive" convention of every other
  landed dense pass file.
* `DecidableEq (DenseExpr p)`/`DecidableEq (BusInteraction (DenseExpr p))` (`Encoding.lean`'s
  `deriving`, `FactPass.lean`'s `deriving instance … for BusInteraction`) back every structural
  equality test below (`matchE11`/`matchPrefixVar`'s `lhs = …`, `pureInCluster`'s `bi = bus`,
  `rolesValid`'s `.contains`/`.Nodup`), exactly as the spec's own `DecidableEq (Expression p)`/
  `DecidableEq (BusInteraction (Expression p))` (also from `FactPass.lean`'s `deriving instance`)
  back the same tests there.

## Ordering note (no representation-forced divergence)

Nothing here ever sorts or iterates by variable *name*: `extractRoles` matches syntactic shapes in
the constraint list's given order (`List.findSome?`, first match wins, exactly as the spec), and
`tryList`/`denseSeqzTryList` scan `busInteractions` in original list order, first accepted candidate
wins. `VarId` has the same `BEq`/`Hashable`/`DecidableEq` shape `Variable` does, so every `.contains`/
`.Nodup`/`decide (· = ·)` test carries over with no reordering. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Expression templates for the recognised gadget

Mirrors `OldVariableBased/SeqzCollapse.lean:44`–`123`. Names are prefixed `denseSeqz` (rather than
just `dense`) since the reference's own names (`e0`, `markerSum`, `boolConstraint`, `sumExpr4`, …) are
short enough to plausibly collide with other dense pass files sharing this flat namespace — indeed
`denseBoolConstraint`/`denseTryList` are already taken by `Reencode.lean`/`HintCollapse.lean`. -/

/-- `-1` as a dense constant. Mirrors `eM1` (`:44`). -/
def denseSeqzEM1 : DenseExpr p := .const (-1)
/-- `0` as a dense constant. Mirrors `e0` (`:46`). -/
def denseSeqzE0 : DenseExpr p := .const 0
/-- `1` as a dense constant. Mirrors `e1` (`:48`). -/
def denseSeqzE1 : DenseExpr p := .const 1
/-- `2` as a dense constant. Mirrors `e2` (`:50`). -/
def denseSeqzE2 : DenseExpr p := .const 2

/-- The partial marker sums `sₖ = -1 + mₖ + … + m₃` (`s3` is `-1 + m3`), nested left. Mirrors
    `sExpr` (`:53`). -/
def denseSeqzSExpr (m3 m2 m1 m0 : VarId) : Nat → DenseExpr p
  | 0 => .add (.add (.add (.add denseSeqzEM1 (.var m3)) (.var m2)) (.var m1)) (.var m0)
  | 1 => .add (.add (.add denseSeqzEM1 (.var m3)) (.var m2)) (.var m1)
  | 2 => .add (.add denseSeqzEM1 (.var m3)) (.var m2)
  | _ => .add denseSeqzEM1 (.var m3)

/-- The marker sum `Σ mₖ = ((m3 + m2) + m1) + m0` (no `-1`), the bus multiplicity. Mirrors
    `markerSum` (`:60`). -/
def denseSeqzMarkerSum (m3 m2 m1 m0 : VarId) : DenseExpr p :=
  .add (.add (.add (.var m3) (.var m2)) (.var m1)) (.var m0)

/-- `K + R`, the "sign" factor of the prefix constraints. Mirrors `krExpr` (`:64`). -/
def denseSeqzKrExpr (K : ZMod p) (R : VarId) : DenseExpr p := .add (.const K) (.var R)

/-- `-1 + 2·R`, the `2·cmp − 1` sign selector of the diff constraints. Mirrors `twoRExpr` (`:67`). -/
def denseSeqzTwoRExpr (R : VarId) : DenseExpr p := .add denseSeqzEM1 (.mul denseSeqzE2 (.var R))

/-- Diff-definition inner term for limbs 1..3: `dv + (-1)·((-1·aᵢ)·(2R−1))`. Mirrors `diffInner`
    (`:70`). -/
def denseSeqzDiffInner (dv ai R : VarId) : DenseExpr p :=
  .add (.var dv) (.mul denseSeqzEM1 (.mul (.mul denseSeqzEM1 (.var ai)) (denseSeqzTwoRExpr R)))

/-- Diff-definition inner term for limb 0: `dv + (-1)·((1 + (-1·a0))·(2R−1))`. Mirrors `diffInner0`
    (`:74`). -/
def denseSeqzDiffInner0 (dv a0 R : VarId) : DenseExpr p :=
  .add (.var dv)
    (.mul denseSeqzEM1 (.mul (.add denseSeqzE1 (.mul denseSeqzEM1 (.var a0))) (denseSeqzTwoRExpr R)))

/-- The 14 algebraic constraints of the gadget, in machine order (limb 3 → 0, then the two
    marker-sum constraints). Mirrors `clusterConstraints` (`:79`). -/
def denseSeqzClusterConstraints (m3 m2 m1 m0 dv R a3 a2 a1 a0 : VarId) (K : ZMod p) :
    List (DenseExpr p) :=
  [ -- limb 3
    .mul (.var m3) (.add denseSeqzEM1 (.var m3)),
    .mul (denseSeqzSExpr m3 m2 m1 m0 3) (.mul (.var a3) (denseSeqzKrExpr K R)),
    .mul (.var m3) (denseSeqzDiffInner dv a3 R),
    -- limb 2
    .mul (.var m2) (.add denseSeqzEM1 (.var m2)),
    .mul (denseSeqzSExpr m3 m2 m1 m0 2) (.mul (.var a2) (denseSeqzKrExpr K R)),
    .mul (.var m2) (denseSeqzDiffInner dv a2 R),
    -- limb 1
    .mul (.var m1) (.add denseSeqzEM1 (.var m1)),
    .mul (denseSeqzSExpr m3 m2 m1 m0 1) (.mul (.var a1) (denseSeqzKrExpr K R)),
    .mul (.var m1) (denseSeqzDiffInner dv a1 R),
    -- limb 0 (comparand digit is 1, so the operand is `a0 - 1`)
    .mul (.var m0) (.add denseSeqzEM1 (.var m0)),
    .mul (denseSeqzSExpr m3 m2 m1 m0 0) (.mul (.add denseSeqzEM1 (.var a0)) (denseSeqzKrExpr K R)),
    .mul (.var m0) (denseSeqzDiffInner0 dv a0 R),
    -- marker-sum booleanity and the "no marker ⇒ cmp = 0" constraint
    .mul (denseSeqzMarkerSum m3 m2 m1 m0) (denseSeqzSExpr m3 m2 m1 m0 0),
    .mul (denseSeqzSExpr m3 m2 m1 m0 0) (.var R) ]

/-- The gadget's range-check bus interaction: `mult = Σ mₖ`, a byte pair-check on `dv − 1` emitted
    through the bus's `ByteXorSpec` (`spec.encode pairOp (dv − 1) 0 0`). Mirrors `clusterBus`
    (`:104`). -/
def denseSeqzClusterBus (busId : Nat) (m3 m2 m1 m0 dv : VarId) (spec : ByteXorSpec p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := denseSeqzMarkerSum m3 m2 m1 m0,
    payload := spec.encode (.const spec.pairOp) (.add denseSeqzEM1 (.var dv)) denseSeqzE0
      denseSeqzE0 }

/-- The result's booleanity constraint `R·(R − 1)` (kept, not part of the cluster). Mirrors
    `boolConstraint` (`:110`). -/
def denseSeqzBoolConstraint (R : VarId) : DenseExpr p := .mul (.var R) (.add denseSeqzEM1 (.var R))

/-- `S = a0 + a1 + a2 + a3`, the limb sum. Mirrors `sumExpr4` (`:113`). -/
def denseSeqzSumExpr4 (a0 a1 a2 a3 : VarId) : DenseExpr p :=
  .add (.add (.add (.var a0) (.var a1)) (.var a2)) (.var a3)

/-- The two is-zero constraints replacing the cluster: `R·S` and `inv·S + (R − 1)`. Mirrors
    `newConstraints` (`:117`). -/
def denseSeqzNewConstraints (R a0 a1 a2 a3 inv : VarId) : List (DenseExpr p) :=
  [ .mul (.var R) (denseSeqzSumExpr4 a0 a1 a2 a3),
    .add (.mul (.var inv) (denseSeqzSumExpr4 a0 a1 a2 a3)) (.add (.var R) denseSeqzEM1) ]

/-- The derivation for `inv`: `QuotientOrZero(1 − R, S)`. Mirrors `invMethod` (`:122`). -/
def denseSeqzInvMethod (R a0 a1 a2 a3 : VarId) : DenseComputationMethod p :=
  .quotientOrZero (.add denseSeqzE1 (.mul denseSeqzEM1 (.var R))) (denseSeqzSumExpr4 a0 a1 a2 a3)

/-! ## Role extraction (recogniser)

Mirrors `OldVariableBased/SeqzCollapse.lean:494`–`593`. -/

/-- Match the bus multiplicity `((m3 + m2) + m1) + m0`. Mirrors `matchMarkerSum` (`:494`). -/
def denseSeqzMatchMarkerSum : DenseExpr p → Option (VarId × VarId × VarId × VarId)
  | .add (.add (.add (.var m3) (.var m2)) (.var m1)) (.var m0) => some (m3, m2, m1, m0)
  | _ => none

/-- Match `-1 + x` (a variable), returning `x`. Mirrors `matchNegVar` (`:499`). -/
def denseSeqzMatchNegVar : DenseExpr p → Option VarId
  | .add (.const c) (.var x) => if c = (-1 : ZMod p) then some x else none
  | _ => none

/-- Match constraint E11 `s0 · ((-1 + a0)·(K + R))`, returning `(a0, K, R)`. Mirrors `matchE11`
    (`:504`). -/
def denseSeqzMatchE11 (s0 : DenseExpr p) : DenseExpr p → Option (VarId × ZMod p × VarId)
  | .mul lhs (.mul (.add (.const c) (.var a0)) (.add (.const k) (.var r))) =>
      if lhs = s0 ∧ c = (-1 : ZMod p) then some (a0, k, r) else none
  | _ => none

/-- Match a prefix constraint `prefixE · (aᵢ · KR)`, returning `aᵢ`. Mirrors `matchPrefixVar`
    (`:510`). -/
def denseSeqzMatchPrefixVar (prefixE kr : DenseExpr p) : DenseExpr p → Option VarId
  | .mul lhs (.mul (.var ai) rhs) => if lhs = prefixE ∧ rhs = kr then some ai else none
  | _ => none

/-- All the recognised roles of a gadget instance. Mirrors `Roles` (`:515`). -/
structure DenseSeqzRoles (p : ℕ) where
  m3 : VarId
  m2 : VarId
  m1 : VarId
  m0 : VarId
  dv : VarId
  R : VarId
  a3 : VarId
  a2 : VarId
  a1 : VarId
  a0 : VarId
  K : ZMod p
  busId : Nat

/-- The private witnesses of a gadget instance (dropped by the collapse). Mirrors `Roles.witnesses`
    (`:530`). -/
def DenseSeqzRoles.witnesses (r : DenseSeqzRoles p) : List VarId := [r.m3, r.m2, r.m1, r.m0, r.dv]

/-- The fresh `inv` variable *candidate* for a gadget instance: resolve `r.dv` back to the `Variable`
    it was registered for and prepend the same tag the spec uses. Mirrors `Roles.inv` (`:533`),
    threading `reg` through since a `VarId` alone carries no display name (see the module header for
    why this reproduces the spec's `r.dv.name` byte-identically). -/
def denseSeqzInvVar (reg : VarRegistry) (r : DenseSeqzRoles p) : Variable :=
  ⟨"seqzinv#" ++ (reg.resolve r.dv).name, none⟩

/-- Does variable `w` occur only inside the recognised cluster (the 14 constraints + the bus)?
    Decided with `DenseExpr.mentions`. Mirrors `pureInCluster` (`:537`). -/
def denseSeqzPureInCluster (d : DenseConstraintSystem p) (cluster : List (DenseExpr p))
    (bus : BusInteraction (DenseExpr p)) (w : VarId) : Bool :=
  (d.algebraicConstraints.all (fun c => cluster.contains c || !(c.mentions w))) &&
  (d.busInteractions.all (fun bi => decide (bi = bus) ||
    (!(bi.multiplicity.mentions w) && bi.payload.all (fun e => !(e.mentions w)))))

/-- Extract the gadget roles from a candidate range-check bus interaction and the constraint list.
    Returns `none` unless every template constraint is present in exact form. Mirrors `extractRoles`
    (`:545`). -/
def denseSeqzExtractRoles (d : DenseConstraintSystem p) (bi : BusInteraction (DenseExpr p)) :
    Option (DenseSeqzRoles p) := do
  guard (bi.payload.length = 4)
  let dvArg ← bi.payload[0]?
  let dv ← denseSeqzMatchNegVar dvArg
  guard (bi.payload[1]? = some denseSeqzE0 ∧ bi.payload[2]? = some denseSeqzE0 ∧
    bi.payload[3]? = some denseSeqzE0)
  let (m3, m2, m1, m0) ← denseSeqzMatchMarkerSum bi.multiplicity
  let s0 : DenseExpr p := denseSeqzSExpr m3 m2 m1 m0 0
  let (a0, K, R) ← d.algebraicConstraints.findSome? (denseSeqzMatchE11 s0)
  let kr : DenseExpr p := denseSeqzKrExpr K R
  let a3 ← d.algebraicConstraints.findSome?
    (denseSeqzMatchPrefixVar (denseSeqzSExpr m3 m2 m1 m0 3) kr)
  let a2 ← d.algebraicConstraints.findSome?
    (denseSeqzMatchPrefixVar (denseSeqzSExpr m3 m2 m1 m0 2) kr)
  let a1 ← d.algebraicConstraints.findSome?
    (denseSeqzMatchPrefixVar (denseSeqzSExpr m3 m2 m1 m0 1) kr)
  pure { m3, m2, m1, m0, dv, R, a3, a2, a1, a0, K, busId := bi.busId }

/-- The collapsed output system: drop the cluster constraints and range bus, add the is-zero
    constraints with the (already-registered) fresh witness `invId`. Mirrors `collapsedSystem`
    (`:562`); `r.inv` becomes the explicit `invId` parameter since minting it is the caller's job
    (`denseSeqzTryList`, only on the accepting branch — see the module header). -/
def denseSeqzCollapsedSystem (d : DenseConstraintSystem p) (r : DenseSeqzRoles p) (invId : VarId)
    (spec : ByteXorSpec p) : DenseConstraintSystem p :=
  let cluster := denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K
  let bus := denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec
  { algebraicConstraints :=
      d.algebraicConstraints.filter (fun c => !cluster.contains c)
        ++ denseSeqzNewConstraints r.R r.a0 r.a1 r.a2 r.a3 invId,
    busInteractions := d.busInteractions.filter (fun bi => decide (bi ≠ bus)) }

/-- All checks that must pass for the collapse to be sound: field size and primality (re-decided
    here, at the same call frequency as the spec — see the module header), constants, template
    presence, result booleanity (kept), purity/distinctness of the witnesses, byte bounds on the
    limbs (via the fact-derived bounds map `Bm`, built over the *output* bus interactions — see the
    module header), and `inv` freshness. Mirrors `rolesValid` (`:576`); `bs` is dropped (unused by
    the spec's own computation, only threading `Bm`'s dependent type there), `reg` is added (needed
    to resolve `r.dv`'s name for `denseSeqzInvVar` and to test `isInput`/freshness — see the module
    header). -/
def denseSeqzRolesValid (reg : VarRegistry) (d : DenseConstraintSystem p) (r : DenseSeqzRoles p)
    (spec : ByteXorSpec p) (Bm : Std.HashMap VarId Nat) : Bool :=
  let cluster := denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K
  let bus := denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec
  decide (Nat.Prime p) && decide (1024 ≤ p) && decide (2 * r.K + 1 = 0) &&
  decide (spec.bound = 256) &&
  d.busInteractions.contains bus &&
  cluster.all (fun c => d.algebraicConstraints.contains c) &&
  d.algebraicConstraints.contains (denseSeqzBoolConstraint r.R) &&
  (!cluster.contains (denseSeqzBoolConstraint r.R)) &&
  r.witnesses.all (fun w => denseSeqzPureInCluster d cluster bus w) &&
  [r.a0, r.a1, r.a2, r.a3].all (fun a =>
    match Bm[a]? with | some b => decide (b ≤ 256) | none => false) &&
  decide ([r.R, r.a0, r.a1, r.a2, r.a3, r.m3, r.m2, r.m1, r.m0, r.dv].Nodup) &&
  denseIsFresh reg d (denseSeqzInvVar reg r) &&
  [r.R, r.a0, r.a1, r.a2, r.a3].all (fun v => reg.isInput v)

/-! ## The scanning driver -/

/-- Scan the bus interactions for the first collapsible gadget, registering the fresh `inv` witness
    only on the accepting branch. Mirrors `tryList` (`:1091`); the fact-derived bounds map `Bm` is
    (re)built inside the `some r` branch on every accepted-extraction candidate, exactly matching the
    spec's own non-hoisted `BoundsMap.build facts` call (see the module header). -/
def denseSeqzTryList (reg : VarRegistry) (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) →
      Option (VarRegistry × DenseConstraintSystem p × DenseDerivations p)
  | [] => none
  | bi :: rest =>
    match denseSeqzExtractRoles d bi with
    | none => denseSeqzTryList reg d bs facts rest
    | some r =>
      match facts.byteXorSpec r.busId with
      | some spec =>
        let bus := denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec
        let Bm : Std.HashMap VarId Nat :=
          denseBuild bs facts (d.busInteractions.filter (fun bi' => decide (bi' ≠ bus)))
        if denseSeqzRolesValid reg d r spec Bm = true then
          let (reg1, invId) := reg.register (denseSeqzInvVar reg r)
          some (reg1, denseSeqzCollapsedSystem d r invId spec,
            [(invId, denseSeqzInvMethod r.R r.a0 r.a1 r.a2 r.a3)])
        else denseSeqzTryList reg d bs facts rest
      | none => denseSeqzTryList reg d bs facts rest

/-! ## The pass, as a registry-extending native transform -/

/-- The seqz-collapse transform, shaped for `DenseVerifiedPassW.ofNativeExtending` (the prover wires
    it with `DenseVerifiedPassW.ofNativeExtending denseSeqzCollapseF …`). Mirrors `seqzCollapsePass`
    (`:1109`): scan for the first recognised gadget, replacing it by the is-zero gadget (dropping the
    four `diff_marker`s and `diff_val`, minting one `QuotientOrZero` witness); identity when none is
    found. -/
def denseSeqzCollapseF (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  (denseSeqzTryList reg d bs facts d.busInteractions).getD (reg, d, [])

end ApcOptimizer.Dense
