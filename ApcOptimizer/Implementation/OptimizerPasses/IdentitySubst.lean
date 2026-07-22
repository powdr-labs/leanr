import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Dense late identity-result substitution

Dense `VarId` definitions for the identity-substitution pass's *runtime*
definitions (`asVar`, `orIdentityOperand`, `identityPairAt`, `identityPairs`, `firstWins`,
`resolveGo`, `identityMap`, `identityFm`, and `identitySubstStep`'s computed output). This file is
**impl-only**: no correctness theorem is stated here, and no
`DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the runtime transform
`denseIdentitySubstF` is shaped like `denseSplitBytePairF` (`SplitBytePair.lean`): unconditional in
`p` (gated only by the same `(1 : ZMod p) ≠ 0` self-check as its sibling passes), so the prover
wraps it directly with `DenseVerifiedPassW.of` and applies the already-landed
`denseIterateToFixpoint` (`Pass.lean`) to reach the scheduled fixpoint pass.

## Reuse map

* `DenseExpr.substF`/`DenseConstraintSystem.substF` (`SubstMap.lean`) are reused unchanged as the
  batch substitution applied once by `denseIdentitySubstF`.
* `ByteXorSpec`/`BusFacts.byteXorSpec`/`spec.decode`/`spec.orOp` are representation-independent
  (their signatures only mention `Nat`/`ZMod p`/payload lists, never `Variable`/`Expression`), so
  `denseIdentityPairAt` consults them unqualified (the same reuse `SplitBytePair.lean`'s
  `denseAsBytePair` documents).
* `firstWins`/`resolveGo`/`identityMap`/`identityFm` have no existing dense counterpart elsewhere
  (they are bespoke to this pass, not shared machinery like `Solved`/`FUData`), so they are
  defined locally below.

## Ordering note

`denseIdentityPairs` is `d.busInteractions.filterMap denseIdentityPairAt`, `denseFirstWins` folds
that list left-to-right keeping the first pair per key, and `denseIdentityMap` builds
`Std.HashMap VarId VarId` from it — none of this ever sorts or iterates by variable *name*: it
folds `d.busInteractions` in original list order and keys the `Std.HashMap VarId VarId` by first
occurrence, plain hash-map point lookups only, no key enumeration. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The `VarId` of a bare-variable dense expression, else `none`. -/
def denseAsVar (e : DenseExpr p) : Option VarId :=
  match e with | .var v => some v | _ => none

/-- The operand `VarId` of an OR-identity `(op, o1, o2, r)`: the non-zero operand when the other is
    the constant `0` (so `r = o1 | o2` collapses to that operand). -/
def denseOrIdentityOperand (o1 o2 : DenseExpr p) : Option VarId :=
  if o2 = DenseExpr.const 0 then denseAsVar o1
  else if o1 = DenseExpr.const 0 then denseAsVar o2
  else none

/-- The `(result, operand)` pair of an OR-identity interaction decoding to `(orOp, o1, o2, result)`
    where one operand is `0` and the surviving operand is a bare variable distinct from the result. -/
def denseIdentityPairAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (VarId × VarId) :=
  match facts.byteXorSpec bi.busId with
  | some spec =>
    match spec.orOp with
    | some oop =>
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        match r with
        | .var rv =>
          if bi.multiplicity = DenseExpr.const 1 ∧ op = DenseExpr.const oop then
            match denseOrIdentityOperand o1 o2 with
            | some o1v => if rv = o1v then none else some (rv, o1v)
            | none => none
          else none
        | _ => none
      | none => none
    | none => none
  | none => none

/-- All recognised `(result, operand)` identity pairs in the system, computed once. Hoisting this
    out of the per-variable lookup below keeps the substitution — which calls the map once per
    variable occurrence — from re-`filterMap`ping (and re-decoding) every bus interaction on each
    visit; the lookup becomes a linear scan of this (small) list instead. -/
def denseIdentityPairs {bs : BusSemantics p} (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (VarId × VarId) :=
  d.busInteractions.filterMap (denseIdentityPairAt facts)

/-- First-wins key→value map of a pair list: the value stored for `y` is the first pair keyed `y`,
    exactly the `filterMap … |>.head?` semantics, at one hash lookup per query. -/
def denseFirstWins : List (VarId × VarId) → Std.HashMap VarId VarId → Std.HashMap VarId VarId
  | [], m => m
  | pr :: rest, m => denseFirstWins rest (if m.contains pr.1 then m else m.insert pr.1 pr.2)

/-- Resolve a mapped variable through operand→operand chains, fuel-bounded (a cycle burns fuel and
    stops harmlessly — the fixpoint wrapper then discards the resulting no-op). Compressing the
    chains lets one substitution collapse a whole chain, so the fixpoint converges in ~2
    iterations instead of one per link. -/
def denseResolveGo (m : Std.HashMap VarId VarId) : Nat → VarId → VarId
  | 0, v => v
  | fuel + 1, v =>
    match m[v]? with
    | some w => denseResolveGo m fuel w
    | none => v

/-- The mapped pairs, with the operand side path-compressed. -/
def denseIdentityMap {bs : BusSemantics p} (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    Std.HashMap VarId VarId :=
  denseFirstWins (denseIdentityPairs facts d) ∅

/-- The identity substitution over a prebuilt map: `result ↦ operand` (first per key), the operand
    resolved through chains (`denseResolveGo`). The map is a **parameter**, computed once by the
    pass body — a def-local `let … ; fun y => …` would be re-evaluated per query by arity
    expansion, rebuilding the pair list on every variable occurrence. -/
def denseIdentityFm (m : Std.HashMap VarId VarId) (fuel : Nat) : VarId → Option (DenseExpr p) :=
  fun y => m[y]?.map (fun w => DenseExpr.var (denseResolveGo m fuel w))

/-- The pass step's computed output: batch-substitute every OR-identity result by its operand. When
    the system has no recognised identities — e.g. any OpenVM circuit, whose bitwise bus declares no
    `orOp` — the `[]` branch returns it unchanged, skipping the whole-system `substF` traversal
    (which would be a no-op but still walks every expression). This keeps the pass ~free wherever it
    finds nothing to do. -/
def denseIdentitySubstF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  match denseIdentityPairs facts d with
  | [] => d
  | _ :: _ =>
    if (1 : ZMod p) ≠ 0 then
      -- Bind the map (and its fuel) here, fully applied — see `denseIdentityFm` on why the map
      -- must not live behind the substitution closure's missing argument.
      let m := denseIdentityMap facts d
      d.substF (denseIdentityFm m m.size)
    else d

end ApcOptimizer.Dense
