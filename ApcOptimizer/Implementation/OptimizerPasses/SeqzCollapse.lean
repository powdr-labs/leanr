import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse

set_option autoImplicit false

/-! # Collapsing the `sltu x, 1` (seqz) gadget — dense `VarId` port (impl-only)

Dense `VarId` definitions for the seqz-collapse pass: the expression templates
(`eM1`/`e0`/`e1`/`e2`/`sExpr`/`markerSum`/`krExpr`/`twoRExpr`/
`diffInner`/`diffInner0`/`clusterConstraints`/`clusterBus`/`boolConstraint`/`sumExpr4`/
`newConstraints`/`invMethod`), the recognizer (`matchMarkerSum`/`matchNegVar`/`matchE11`/
`matchPrefixVar`/`Roles`/`Roles.witnesses`/`Roles.inv`/`pureInCluster`/`extractRoles`/
`collapsedSystem`/`rolesValid`), and the scanning driver (`tryList`, `seqzCollapsePass`'s computed
output). This file is **impl-only**: no correctness theorem is stated here, and no
`DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here.

## Shape: a registry-extending transform

Like `Reencode`/`HintCollapse`, this pass mints a fresh derived witness (the reciprocal hint `inv`
of the is-zero gadget), so it is shaped for the registry-extending builder — the prover wires it with
`DenseVerifiedPassW.ofExtending (denseSeqzCollapseF) …`
(`transform : VarRegistry → (bs) → BusFacts p bs → DenseConstraintSystem p → VarRegistry ×
DenseConstraintSystem p × DenseDerivations p`, `Reencode.lean`/`HintCollapse.lean`'s own shape).
Still out of scope: the correctness theorems and the `ofExtending` call itself.

## Where the fresh variable is minted, and the freshness-decision mechanism

`denseSeqzInvVar reg r` computes the *candidate* name for the fresh `inv` witness —
`⟨"seqzinv#" ++ (reg.resolve r.dv).name, none⟩` — by resolving `r.dv`'s `VarId` back to the display
name it was registered under. `denseIsFresh` (`HintCollapse.lean`, reused unchanged — see its header
for the mechanism: an `reg.idOf?` prefilter composed with a linear scan of `d.occ`) tests whether that
candidate name is already in use, and `denseSeqzRolesValid` requires it to be fresh. The candidate is
registered (`reg.register`) only on `denseSeqzTryList`'s accepting branch: registering-and-discarding a
`VarId` for every rejected candidate would needlessly inflate the registry for the run's remaining
lifetime, while an unregistered candidate is invisible to every downstream decision.

## `denseBuild` is recomputed per accepted candidate, not hoisted

`denseSeqzTryList` calls `denseBuild bs facts (…)` *inside* the `some r` branch, once per
`extractRoles`-recognised candidate that also has a `byteXorSpec` — potentially more than once
per pass invocation, since the scan keeps trying further bus interactions until `denseSeqzRolesValid`
succeeds. It is **not** hoisted above the scan: the filtered bus-interaction list it folds over does
not depend on the (not-yet-registered) `inv` variable, but the recomputation on every accepted
candidate is deliberate and preserved rather than memoised across candidates. This lets
freshness-checking and the byte-bound map both be computed *before* any registration, so `inv` is
still minted only on the final accepting branch (see above).

## No `PrimeWitness` — primality is re-decided per candidate

Unlike `HintCollapse`/`MonicScale`/`SplitBytePair`/`IdentitySubst`, `denseSeqzRolesValid` inlines
`decide (Nat.Prime p) && decide (1024 ≤ p)` directly in its `Bool` chain, rather than being gated by
an outer `[Fact p.Prime]`/`PrimeWitness` on its caller; there is no such gate on
`denseSeqzTryList`/`denseSeqzCollapseF`. Primality is therefore re-decided once per
`extractRoles`-recognised candidate, at the same frequency as every other check in
`denseSeqzRolesValid`; introducing a `PrimeWitness` here would change this cost profile and is out of
scope.

## Reuse map

* `denseBuild` (`DigitFold.lean`) is the fact-derived byte-bounds map used by
  `denseSeqzRolesValid`/`denseSeqzTryList` (see above for why it is recomputed per candidate rather
  than memoised).
* `reg.isInput` (`Bridge.lean`) tests `x.powdrId?.isSome` through the registry.
* `DenseExpr.mentions` (`SubstMap.lean`) is reused unchanged by `denseSeqzPureInCluster`.
* `denseIsFresh` (`HintCollapse.lean`) is the freshness-prefilter mechanism, reused unchanged rather
  than re-derived here.
* `DecidableEq (DenseExpr p)`/`DecidableEq (BusInteraction (DenseExpr p))` (`Encoding.lean`'s
  `deriving`, `FactPass.lean`'s `deriving instance … for BusInteraction`) back every structural
  equality test below (`matchE11`/`matchPrefixVar`'s `lhs = …`, `pureInCluster`'s `bi = bus`,
  `rolesValid`'s `.contains`/`.Nodup`).

## Ordering note

Nothing here ever sorts or iterates by variable *name*: `denseSeqzExtractRoles` matches syntactic
shapes in the constraint list's given order (`List.findSome?`, first match wins), and
`denseSeqzTryList` scans `busInteractions` in original list order, first accepted candidate wins.
`VarId`'s `BEq`/`Hashable`/`DecidableEq` instances make every `.contains`/`.Nodup`/`decide (· = ·)`
test below a straightforward equality check with no reordering. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Expression templates for the recognised gadget

Names are prefixed `denseSeqz` (rather than just `dense`) since short names like `e0`, `markerSum`,
`boolConstraint`, `sumExpr4` would plausibly collide with other dense pass files sharing this flat
namespace — indeed `denseBoolConstraint`/`denseTryList` are already taken by
`Reencode.lean`/`HintCollapse.lean`. -/

/-- `-1` as a dense constant. -/
def denseSeqzEM1 : DenseExpr p := .const (-1)
/-- `0` as a dense constant. -/
def denseSeqzE0 : DenseExpr p := .const 0
/-- `1` as a dense constant. -/
def denseSeqzE1 : DenseExpr p := .const 1
/-- `2` as a dense constant. -/
def denseSeqzE2 : DenseExpr p := .const 2

/-- The partial marker sums `sₖ = -1 + mₖ + … + m₃` (`s3` is `-1 + m3`), nested left. -/
def denseSeqzSExpr (m3 m2 m1 m0 : VarId) : Nat → DenseExpr p
  | 0 => .add (.add (.add (.add denseSeqzEM1 (.var m3)) (.var m2)) (.var m1)) (.var m0)
  | 1 => .add (.add (.add denseSeqzEM1 (.var m3)) (.var m2)) (.var m1)
  | 2 => .add (.add denseSeqzEM1 (.var m3)) (.var m2)
  | _ => .add denseSeqzEM1 (.var m3)

/-- The marker sum `Σ mₖ = ((m3 + m2) + m1) + m0` (no `-1`), the bus multiplicity. -/
def denseSeqzMarkerSum (m3 m2 m1 m0 : VarId) : DenseExpr p :=
  .add (.add (.add (.var m3) (.var m2)) (.var m1)) (.var m0)

/-- `K + R`, the "sign" factor of the prefix constraints. -/
def denseSeqzKrExpr (K : ZMod p) (R : VarId) : DenseExpr p := .add (.const K) (.var R)

/-- `-1 + 2·R`, the `2·cmp − 1` sign selector of the diff constraints. -/
def denseSeqzTwoRExpr (R : VarId) : DenseExpr p := .add denseSeqzEM1 (.mul denseSeqzE2 (.var R))

/-- Diff-definition inner term for limbs 1..3: `dv + (-1)·((-1·aᵢ)·(2R−1))`. -/
def denseSeqzDiffInner (dv ai R : VarId) : DenseExpr p :=
  .add (.var dv) (.mul denseSeqzEM1 (.mul (.mul denseSeqzEM1 (.var ai)) (denseSeqzTwoRExpr R)))

/-- Diff-definition inner term for limb 0: `dv + (-1)·((1 + (-1·a0))·(2R−1))`. -/
def denseSeqzDiffInner0 (dv a0 R : VarId) : DenseExpr p :=
  .add (.var dv)
    (.mul denseSeqzEM1 (.mul (.add denseSeqzE1 (.mul denseSeqzEM1 (.var a0))) (denseSeqzTwoRExpr R)))

/-- The 14 algebraic constraints of the gadget, in machine order (limb 3 → 0, then the two
    marker-sum constraints). -/
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
    through the bus's `ByteXorSpec` (`spec.encode pairOp (dv − 1) 0 0`). -/
def denseSeqzClusterBus (busId : Nat) (m3 m2 m1 m0 dv : VarId) (spec : ByteXorSpec p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := denseSeqzMarkerSum m3 m2 m1 m0,
    payload := spec.encode (.const spec.pairOp) (.add denseSeqzEM1 (.var dv)) denseSeqzE0
      denseSeqzE0 }

/-- The result's booleanity constraint `R·(R − 1)` (kept, not part of the cluster). -/
def denseSeqzBoolConstraint (R : VarId) : DenseExpr p := .mul (.var R) (.add denseSeqzEM1 (.var R))

/-- `S = a0 + a1 + a2 + a3`, the limb sum. -/
def denseSeqzSumExpr4 (a0 a1 a2 a3 : VarId) : DenseExpr p :=
  .add (.add (.add (.var a0) (.var a1)) (.var a2)) (.var a3)

/-- The two is-zero constraints replacing the cluster: `R·S` and `inv·S + (R − 1)`. -/
def denseSeqzNewConstraints (R a0 a1 a2 a3 inv : VarId) : List (DenseExpr p) :=
  [ .mul (.var R) (denseSeqzSumExpr4 a0 a1 a2 a3),
    .add (.mul (.var inv) (denseSeqzSumExpr4 a0 a1 a2 a3)) (.add (.var R) denseSeqzEM1) ]

/-- The derivation for `inv`: `QuotientOrZero(1 − R, S)`. -/
def denseSeqzInvMethod (R a0 a1 a2 a3 : VarId) : DenseComputationMethod p :=
  .quotientOrZero (.add denseSeqzE1 (.mul denseSeqzEM1 (.var R))) (denseSeqzSumExpr4 a0 a1 a2 a3)

/-! ## Role extraction (recogniser)

Pattern-matches the constraint list and a candidate bus interaction against the gadget's expected
shapes to recover its role variables. -/

/-- Match the bus multiplicity `((m3 + m2) + m1) + m0`. -/
def denseSeqzMatchMarkerSum : DenseExpr p → Option (VarId × VarId × VarId × VarId)
  | .add (.add (.add (.var m3) (.var m2)) (.var m1)) (.var m0) => some (m3, m2, m1, m0)
  | _ => none

/-- Match `-1 + x` (a variable), returning `x`. -/
def denseSeqzMatchNegVar : DenseExpr p → Option VarId
  | .add (.const c) (.var x) => if c = (-1 : ZMod p) then some x else none
  | _ => none

/-- Match constraint E11 `s0 · ((-1 + a0)·(K + R))`, returning `(a0, K, R)`. -/
def denseSeqzMatchE11 (s0 : DenseExpr p) : DenseExpr p → Option (VarId × ZMod p × VarId)
  | .mul lhs (.mul (.add (.const c) (.var a0)) (.add (.const k) (.var r))) =>
      if lhs = s0 ∧ c = (-1 : ZMod p) then some (a0, k, r) else none
  | _ => none

/-- Match a prefix constraint `prefixE · (aᵢ · KR)`, returning `aᵢ`. -/
def denseSeqzMatchPrefixVar (prefixE kr : DenseExpr p) : DenseExpr p → Option VarId
  | .mul lhs (.mul (.var ai) rhs) => if lhs = prefixE ∧ rhs = kr then some ai else none
  | _ => none

/-- All the recognised roles of a gadget instance. -/
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

/-- The private witnesses of a gadget instance (dropped by the collapse). -/
def DenseSeqzRoles.witnesses (r : DenseSeqzRoles p) : List VarId := [r.m3, r.m2, r.m1, r.m0, r.dv]

/-- The fresh `inv` variable *candidate* for a gadget instance: `reg.resolve r.dv` recovers the
    display name that `dv`'s `VarId` was registered under, and `"seqzinv#"` is prepended to form the
    candidate name. `reg` is threaded through since a `VarId` alone carries no display name. -/
def denseSeqzInvVar (reg : VarRegistry) (r : DenseSeqzRoles p) : Variable :=
  ⟨"seqzinv#" ++ (reg.resolve r.dv).name, none⟩

/-- Does variable `w` occur only inside the recognised cluster (the 14 constraints + the bus)?
    Decided with `DenseExpr.mentions`. -/
def denseSeqzPureInCluster (d : DenseConstraintSystem p) (cluster : List (DenseExpr p))
    (bus : BusInteraction (DenseExpr p)) (w : VarId) : Bool :=
  (d.algebraicConstraints.all (fun c => cluster.contains c || !(c.mentions w))) &&
  (d.busInteractions.all (fun bi => decide (bi = bus) ||
    (!(bi.multiplicity.mentions w) && bi.payload.all (fun e => !(e.mentions w)))))

/-- Extract the gadget roles from a candidate range-check bus interaction and the constraint list.
    Returns `none` unless every template constraint is present in exact form. -/
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
    constraints with the (already-registered) fresh witness `invId`, passed in explicitly since
    minting it is the caller's job (`denseSeqzTryList`, only on the accepting branch — see the
    module header). -/
def denseSeqzCollapsedSystem (d : DenseConstraintSystem p) (r : DenseSeqzRoles p) (invId : VarId)
    (spec : ByteXorSpec p) : DenseConstraintSystem p :=
  let cluster := denseSeqzClusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K
  let bus := denseSeqzClusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv spec
  { algebraicConstraints :=
      d.algebraicConstraints.filter (fun c => !cluster.contains c)
        ++ denseSeqzNewConstraints r.R r.a0 r.a1 r.a2 r.a3 invId,
    busInteractions := d.busInteractions.filter (fun bi => decide (bi ≠ bus)) }

/-- All checks that must pass for the collapse to be sound: field size and primality (re-decided
    here, per candidate — see the module header), constants, template presence, result booleanity
    (kept), purity/distinctness of the witnesses, byte bounds on the limbs (via the fact-derived
    bounds map `Bm`, built over the *output* bus interactions — see the module header), and `inv`
    freshness. `reg` resolves `r.dv`'s name for `denseSeqzInvVar` and tests `isInput`/freshness. -/
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
    only on the accepting branch. The fact-derived bounds map `Bm` is (re)built inside the `some r`
    branch on every accepted-extraction candidate rather than hoisted above the scan (see the module
    header). -/
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

/-! ## The pass, as a registry-extending transform -/

/-- The seqz-collapse transform, shaped for `DenseVerifiedPassW.ofExtending` (the prover wires
    it with `DenseVerifiedPassW.ofExtending denseSeqzCollapseF …`): scan for the first recognised
    gadget, replacing it by the is-zero gadget (dropping the four `diff_marker`s and `diff_val`,
    minting one `QuotientOrZero` witness); identity when none is found. -/
def denseSeqzCollapseF (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  (denseSeqzTryList reg d bs facts d.busInteractions).getD (reg, d, [])

end ApcOptimizer.Dense
