import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.DisconnectedComponent
import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Disconnected-component removal — dense `VarId` port (impl-only)

Dense, `VarId`-native transliteration of the *runtime* definitions of
`OptimizerPasses/OldVariableBased/DisconnectedComponent.lean` (`Variable`/`Expression`-based). A
*disconnected component* is a set of algebraic constraints and stateless bus interactions whose
variables never touch any **stateful** bus interaction. The pass finds such a component by
connectivity from the stateful buses, tries the all-zero witness, and drops the component only if
the witness provably certifies it (the same run-time re-check `guardDegree` uses).

Only the connectivity search's *representation* changes: `Variable`→`VarId`, `Expression`→
`DenseExpr`, `BusInteraction.vars`→`denseBIVars`, `Std.HashMap Variable`/`Std.HashSet Variable`→
their `VarId`-keyed twins, `Std.HashSet Nat`/`Array (List Variable)` unchanged in shape. Control
flow, candidate/traversal order, the co-occurrence graph, the seeds, the per-component certification,
and the final re-checked partition are all preserved verbatim.

This is **impl-only**: the correctness argument (`dropComponent_correct`) and the run-time re-check
that discharges it are native-proved in `DisconnectedComponentProof.lean`. Nothing here states or
proves anything beyond the runtime computation.

## The one non-transliteration: a terminating closure

The spec's `bfsClosure` is a `partial def` (correctness never depends on it — the pass re-checks the
partition it induces). New `partial def`s are forbidden on this branch, so `denseBfsClosure` runs the
**same** algorithm — same visited `HashSet`, same worklist stack, same group-processed `HashSet`,
same per-step work (one `v2g` lookup, one `filter`, two `foldl`s) — driven by an explicit `fuel`
counter.

**Fuel adequacy.** Each recursion pops exactly one stack element, so the number of recursion steps
equals `|seed|` plus the total pushed. A group `g` first enters some `gids` in exactly one step
(afterwards it is in `procGroups`, so the `filter` skips it) — but within that step it can appear in
`gids` with multiplicity, because `v2g[x]` lists `g` once per occurrence of `x` in item `g` (e.g. a
constraint `x*x` records `g` twice for `x`). So `g`'s vars are pushed `μ_g · groups[g].length` times,
where `μ_g ≤ groups[g].length` is that trigger multiplicity; total pushes
`≤ Σ_g groups[g].length² = denseClosureFuel`. Hence `steps ≤ |seed| + denseClosureFuel`, and
`denseConnBad` seeds each closure with `seed.length + denseClosureFuel groups + 1` — an upper bound
that guarantees no truncation. The bound is computed **once**, `O(edges)`. The fuel is only a cap:
the stack empties at the true step count (≈ `2·edges` in practice), well before the fuel is spent,
so unused fuel costs nothing and the runtime complexity is exactly the spec's `bfsClosure` (identical
algorithm, identical per-step work). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The co-occurrence graph -/

/-- The co-occurrence graph of the dense system: for each item (constraint, then interaction) its
    list of `VarId`s (`groups`), and a map from each `VarId` to the indices of the items it occurs in
    (`v2g`). Dense mirror of `buildGraph`. -/
def denseBuildGraph (d : DenseConstraintSystem p) :
    Array (List VarId) × Std.HashMap VarId (List Nat) :=
  let groups : Array (List VarId) :=
    (d.algebraicConstraints.map DenseExpr.vars ++
      d.busInteractions.map denseBIVars).toArray
  let v2g : Std.HashMap VarId (List Nat) :=
    (List.range groups.size).foldl
      (fun mp i => (groups.getD i []).foldl (fun mp x => mp.insert x (i :: mp.getD x [])) mp) ∅
  (groups, v2g)

/-- A safe upper bound on the closure's push count, `Σ_g groups[g].length²` (see the module header):
    a group's vars are pushed `μ_g · groups[g].length ≤ groups[g].length²` times. The fuel budget's
    dominant term, computed once per pass in `O(edges)` (each `groups[g].length` is walked once, then
    squared) — the same order as the graph build. -/
def denseClosureFuel (groups : Array (List VarId)) : Nat :=
  groups.foldl (fun a g => a + g.length * g.length) 0

/-! ## The terminating closure -/

/-- Variables reachable from a seed via co-occurrence in a constraint or interaction. Dense,
    fuel-driven mirror of the spec's `partial def bfsClosure`; the algorithm and per-step work are
    identical (see the module header for the fuel-adequacy argument). Correctness never depends on
    this result — the pass re-checks the partition it induces. -/
def denseBfsClosure (groups : Array (List VarId)) (v2g : Std.HashMap VarId (List Nat))
    (visited : Std.HashSet VarId) (procGroups : Std.HashSet Nat) (stack : List VarId)
    (fuel : Nat) : Std.HashSet VarId :=
  match fuel with
  | 0 => visited
  | fuel + 1 =>
    match stack with
    | [] => visited
    | x :: rest =>
      if visited.contains x then denseBfsClosure groups v2g visited procGroups rest fuel
      else
        let gids := (v2g.getD x []).filter (fun g => !procGroups.contains g)
        let procGroups := gids.foldl (fun s g => s.insert g) procGroups
        let newVars := gids.foldl (fun acc g => groups.getD g [] ++ acc) rest
        denseBfsClosure groups v2g (visited.insert x) procGroups newVars fuel

/-! ## Keep predicates -/

/-- Keep a constraint unless *all* of its variables are removable (and it has at least one). Dense
    mirror of `keepConWith`. -/
def denseKeepConWith (remV : VarId → Bool) (c : DenseExpr p) : Bool :=
  c.vars.isEmpty || !(c.vars.all remV)

/-- Keep an interaction if it is stateful or has a non-removable variable (or no variables). Dense
    mirror of `keepBiWith`. -/
def denseKeepBiWith (bs : BusSemantics p) (remV : VarId → Bool)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  bs.isStateful bi.busId || (denseBIVars bi).isEmpty || !((denseBIVars bi).all remV)

/-! ## Computing the removable set

`denseConnBad` returns the two reachable sets as **data** (a pair), not a `VarId → Bool` predicate:
a def whose result type is a function is eta-expanded to maximal arity, which would re-run the
graph build and both closures on *every* `remV x` application (the `lean-arity-expansion-trap`). The
`remV` predicate is instead built once, at the single use site in `denseDisconnectedF`, capturing
the already-computed sets. The spec pass keeps `conn`/`bad` as `let`s inside its (data-returning)
pass body for exactly this reason. -/

/-- The two reachable sets the pass computes: `conn` (variables connected to a stateful bus
    interaction) and `bad` (the co-occurrence closure of any disconnected item the all-zero witness
    fails on). Dense mirror of the spec pass's `conn`/`disc`/`badSeeds`/`bad` computation. Returns
    data — the `remV` predicate is derived at the use site. Treated **opaquely** by the correctness
    proof (which re-checks the partition the derived `remV` induces). -/
def denseConnBad (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    Std.HashSet VarId × Std.HashSet VarId :=
  let (groups, v2g) := denseBuildGraph d
  let e := denseClosureFuel groups
  -- variables connected to a stateful bus interaction
  let connSeed : List VarId :=
    d.busInteractions.foldl (fun acc bi =>
      if bs.isStateful bi.busId then denseBIVars bi ++ acc else acc) []
  let conn := denseBfsClosure groups v2g ∅ ∅ connSeed (connSeed.length + e + 1)
  let disc : VarId → Bool := fun x => !conn.contains x
  -- variables of a disconnected item the all-zero witness fails on: keep its whole component
  let badSeeds : List VarId :=
    d.algebraicConstraints.foldl (fun acc c =>
        if !c.vars.isEmpty && c.vars.all disc && !decide (c.eval (fun _ => 0) = 0)
        then c.vars ++ acc else acc)
      (d.busInteractions.foldl (fun acc bi =>
        if !bs.isStateful bi.busId && !(denseBIVars bi).isEmpty && (denseBIVars bi).all disc
            && bs.violatesConstraint (denseBIEval bi (fun _ => 0))
        then denseBIVars bi ++ acc else acc) [])
  let bad := denseBfsClosure groups v2g ∅ ∅ badSeeds (badSeeds.length + e + 1)
  (conn, bad)

/-! ## The guarded drop -/

/-- The run-time re-check: the induced partition is a genuine drop, the all-zero witness satisfies
    every removed constraint and non-violates every removed interaction, and every kept item uses
    only non-removable variables. Dense mirror of the spec pass's `hchk` formula, stated for an
    arbitrary `remV`. -/
def denseDropCheck (bs : BusSemantics p) (d : DenseConstraintSystem p) (remV : VarId → Bool) : Bool :=
  (d.algebraicConstraints.any (fun c => !denseKeepConWith remV c) ||
    d.busInteractions.any (fun bi => !denseKeepBiWith bs remV bi)) &&
  d.algebraicConstraints.all (fun c => denseKeepConWith remV c || decide (c.eval (fun _ => 0) = 0)) &&
  d.busInteractions.all (fun bi =>
    denseKeepBiWith bs remV bi || !bs.violatesConstraint (denseBIEval bi (fun _ => 0))) &&
  d.algebraicConstraints.all (fun c =>
    !denseKeepConWith remV c || c.vars.all (fun x => !remV x)) &&
  d.busInteractions.all (fun bi =>
    !denseKeepBiWith bs remV bi || (denseBIVars bi).all (fun x => !remV x))

/-- Drop the removable component if the re-check passes; otherwise the identity. Stated for an
    arbitrary `remV` so the correctness proof is generic in the connectivity search (mirrors how the
    spec's `dropComponent_correct` is generic in `remV`/`keepCon`/`keepBi`). -/
def denseDropGuarded (bs : BusSemantics p) (d : DenseConstraintSystem p) (remV : VarId → Bool) :
    DenseConstraintSystem p :=
  if denseDropCheck bs d remV then
    { algebraicConstraints := d.algebraicConstraints.filter (denseKeepConWith remV),
      busInteractions := d.busInteractions.filter (denseKeepBiWith bs remV) }
  else d

/-- The dense disconnected-component transform: compute the reachable sets once, derive the
    removable predicate as a closure over them, then run the guarded drop. Dense mirror of
    `disconnectedComponentPass`'s data. Returns data (a `DenseConstraintSystem`), so the `let cb`
    runs once per invocation — the `remV` closure captures it, never recomputes it. -/
def denseDisconnectedF (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  let cb := denseConnBad bs d
  denseDropGuarded bs d (fun x => !cb.1.contains x && !cb.2.contains x)

end ApcOptimizer.Dense
