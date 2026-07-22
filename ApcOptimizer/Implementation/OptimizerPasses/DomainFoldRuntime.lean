import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchRuntime

set_option autoImplicit false

/-! # Dense `domainFold`, with compiled value-only evaluation

The two hot evaluators — `denseGroupSurvivorsEV` (the group's survivor filter) and
`denseConstOnSurvsV` (the constant-on-survivors check that drives the fold) — evaluate every
candidate through the compile-once/eval-per-point `IExpr` machinery (`DomainBatch.lean`),
value-only (`List (ZMod p)` points, no `VarId` travels with a point at all): the group's covered
constraints are compiled once per target (`denseCompileEs`) and every enumerated point is checked by
index, with the ring operations hoisted out of the `ZMod p` instances once. `denseConstOnSurvsV`
gets the same treatment at per-node granularity: every `e` passed to it already satisfies
`e.varsIn xs` (checked by its caller, `denseFoldRewriteGoV`, right before calling it), so compiling
`e` once per call before evaluating it against every survivor is the value-only analogue of the same
compile-once/eval-per-point hoisting `denseGroupSurvivorsEV` uses.

## Candidate group order

Candidate fold-target groups (`denseTargetsV`) are sorted by `VarId.index` (`compare a.index
b.index`) — the natural dense order, with no name resolution needed and no `VarRegistry` threaded
into this pass at all. A different (but still valid, un-dominated) candidate group order can accept
a different — still correct — set of folds, which can cascade through the cleanup fixpoint into a
different, still correct, final system.

## Hoisted `let`s avoiding redundant recomputation

Three values below are deliberately bound once, outside any per-element closure, rather than
recomputed on each use — the "Lean arity-expansion trap" (a `def`/computed value called from inside
a per-element closure re-runs per element unless explicitly hoisted to a `let` outside it):

* `denseFoldLoopV` binds the whole step's result once (`let r := denseFoldStepV d fidx xs`), so the
  covered-index scan, domain lookup, survivor enumeration, gate, and (on an accepted fold) the whole
  rewrite each run once per target, not twice.
* `denseFoldStepWithV` binds the group's survivor list once (`let survsV := …`), so the group's
  domain enumeration and covered-constraint filter run once per target, not three times.
* `denseTargetsV` binds `denseSvSet d` once, outside the `filterMap`, so the single-variable-check
  set is built once rather than once per candidate constraint (an `O(#targets × #constraints)`
  blow-up otherwise).

## What is reused unchanged

Everything not on the per-point/per-candidate-node evaluation path is reused from `DomainFold.lean`
and `DomainBatch.lean`/`DomainBatchRuntime.lean`:

* `denseFindDomainAlg`/`denseGroupDoms` (the group's per-variable root-list domains; already
  variable-free `List (ZMod p)` results);
* `denseCoveredBy`/`denseCoveredCsOf` (the covered-constraint predicate/filter);
* `DenseFoldIdx`/`.mk'`/`.refresh` and `denseCoveredIdx` (the prebuilt covered-constraint index and
  its order-restoring scan) — neither carries a survivor representation;
* `denseSvSet` (already `VarId`-native);
* `denseCompileE`/`denseCompileEs`/`IExpr`/`denseVarIx` (the positional compiler, `DomainBatch.lean`)
  and `denseIExprEvalWithV`/`denseEnvOfKeysV`/`denseLookupIxV` (the value-only evaluator,
  `DomainBatchRuntime.lean`) — reused exactly as `domainBatch`'s box scan uses them, since `IExpr`
  is already variable-free and the compiled term is identical regardless of point representation;
* `dedupHash`/`List.mergeSort` (generic, `ListSplit.lean`).

No pipeline wiring and no correctness theorems here: every definition below is runtime-only. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Value-only eager enumeration of a group's domain

`domainFold`'s domains are already concrete `List (ZMod p)` root lists (from `denseFindDomainAlg`/
`denseRootsIn`), not the symbolic `FiniteDomain` `domainBatch`'s box scan lazily streams, so they
are enumerated eagerly via `denseAssignmentsV`/`filter`, with no early exit, dropping the key from
every point (nothing on this path ever reads a key from a point once the compiled `IExpr`s take
over). -/

/-- The Cartesian product of the group's per-variable domain values, value-only: every point is a
    `List (ZMod p)` in the same (compile-time-fixed) key order as the input domain list. -/
def denseAssignmentsV : List (List (ZMod p)) → List (List (ZMod p))
  | [] => [[]]
  | d :: rest => (denseAssignmentsV rest).flatMap (fun a => d.map (fun v => v :: a))

/-! ## The group's survivor filter, compiled once per target -/

/-- All the group's covered constraints zero at a value-only point, ring operations hoisted out of
    the instances once by the caller. -/
def denseSurvZeroCWV (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWithV add mul pt ie = 0))

/-- The surviving group values, value-only: the group's covered constraints `es` are compiled once
    to positional `IExpr`s over the group's key list `xs` (`denseGroupDoms es xs = some doms`
    always yields `doms.map Prod.fst = xs`, see `denseGroupDoms_fst`), and every enumerated point
    (`domVals`, the domains in the same `xs` order) is checked by index, no per-variable env scan.
    Falls back to the direct (uncompiled) filter only if compilation fails — dead for a covered set
    (every leaf is a group variable, hence in `xs`), kept for totality. -/
def denseGroupSurvivorsEV (es : List (DenseExpr p)) (xs : List VarId)
    (domVals : List (List (ZMod p))) : List (List (ZMod p)) :=
  match denseCompileEs xs es with
  | some ces =>
    let addI : Add (ZMod p) := inferInstance
    let mulI : Mul (ZMod p) := inferInstance
    (denseAssignmentsV domVals).filter (denseSurvZeroCWV addI.add mulI.mul ces)
  | none =>
    (denseAssignmentsV domVals).filter
      (fun a => es.all (fun c => decide (c.eval (denseEnvOfKeysV xs a) = 0)))

/-! ## `constOnSurvs`, compiled per candidate node (see the module header) -/

/-- `some c` if `e` evaluates to the same constant `c` on every (value-only) survivor, else `none`.
    `e` is compiled once, against the group's key list `xs`, to a positional `IExpr` (dead-fallback
    otherwise, see the module header — every `e` reaching this call already has `e.varsIn xs`), and
    every survivor is checked by index with the ring operations hoisted once — the same
    compile-once/eval-per-point treatment `denseGroupSurvivorsEV` gets, applied at the finer
    per-node granularity this needs. -/
def denseConstOnSurvsV (xs : List VarId) (survsV : List (List (ZMod p))) (e : DenseExpr p) :
    Option (ZMod p) :=
  match survsV with
  | [] => none
  | s₀ :: rest =>
    match denseCompileE xs e with
    | some ie =>
      let addI : Add (ZMod p) := inferInstance
      let mulI : Mul (ZMod p) := inferInstance
      let v₀ := denseIExprEvalWithV addI.add mulI.mul s₀ ie
      if (s₀ :: rest).all (fun s => decide (denseIExprEvalWithV addI.add mulI.mul s ie = v₀))
      then some v₀ else none
    | none =>
      let v₀ := e.eval (denseEnvOfKeysV xs s₀)
      if (s₀ :: rest).all (fun s => decide (e.eval (denseEnvOfKeysV xs s) = v₀))
      then some v₀ else none

/-! ## The dense fold rewrite, value-only -/

/-- The recursive fold core, value-only survivors: replace every maximal wholly-in-group
    subexpression that is constant on the survivors by that constant; recurse otherwise. -/
def denseFoldRewriteGoV (xs : List VarId) (survsV : List (List (ZMod p))) :
    DenseExpr p → DenseExpr p
  | .const c => .const c
  | .var y => .var y
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then
        match denseConstOnSurvsV xs survsV (.add a b) with
        | some c => .const c
        | none => .add (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)
      else .add (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then
        match denseConstOnSurvsV xs survsV (.mul a b) with
        | some c => .const c
        | none => .mul (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)
      else .mul (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)

/-- The fold rewrite, gated. -/
def denseFoldRewriteV (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs || e.hasConstFoldableNode then denseFoldRewriteGoV xs survsV e else e

/-! ## The folded output -/

/-- Fold every non-covered constraint and every bus interaction; keep the covered (domain-pinning)
    constraints verbatim. -/
def denseFoldOutV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map (denseFoldRewriteV xs survsV)
        ++ denseCoveredCsOf d xs,
    busInteractions := d.busInteractions.map
      (fun bi => { bi with
        multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
        payload := bi.payload.map (denseFoldRewriteV xs survsV) }) }

/-! ## The no-op gates, value-only -/

/-- Does this expression have a maximal wholly-in-group subexpression that folds to a constant
    (value-only survivors)? Purely an efficiency gate. -/
def DenseExpr.hasFoldableV (xs : List VarId) (survsV : List (List (ZMod p))) : DenseExpr p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b =>
      ((DenseExpr.add a b).varsInF xs && (denseConstOnSurvsV xs survsV (.add a b)).isSome) ||
        a.hasFoldableV xs survsV || b.hasFoldableV xs survsV
  | .mul a b =>
      ((DenseExpr.mul a b).varsInF xs && (denseConstOnSurvsV xs survsV (.mul a b)).isSome) ||
        a.hasFoldableV xs survsV || b.hasFoldableV xs survsV

/-- Does the fold change anything in the system? The no-op gate of the direct (unindexed) path, with
    the non-covered constraints (`csRest`, the `denseCoveredBy` complement) precomputed by the
    caller: the direct path partitions the constraint list once per target, so the gate does not
    re-evaluate `denseCoveredBy` per constraint. Purely an efficiency gate. -/
def denseSystemHasFoldableWV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) (csRest : List (DenseExpr p)) : Bool :=
  csRest.any (fun c => c.hasFoldableV xs survsV) ||
    d.busInteractions.any (fun bi =>
      bi.multiplicity.hasFoldableV xs survsV || bi.payload.any (fun e => e.hasFoldableV xs survsV))

/-- The index-local form of the direct-path gate `denseSystemHasFoldableWV` (value-only survivors):
    scan only the items sharing a variable with `xs` through the prebuilt inverted indexes — a plain
    two-bucket scan, with no const-foldable-item caches. Used by the indexed path. -/
def denseSystemHasFoldableIdxV (fidx : DenseFoldIdx p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : Bool :=
  (((xs.flatMap (fun v => fidx.idx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arr.size then
      let c := fidx.arr[i]
      !denseCoveredBy xs c && c.hasFoldableV xs survsV
    else false)) ||
  (((xs.flatMap (fun v => fidx.bisIdx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arrBis.size then
      let bi := fidx.arrBis[i]
      bi.multiplicity.hasFoldableV xs survsV || bi.payload.any (fun e => e.hasFoldableV xs survsV)
    else false))

/-! ## The direct (unindexed) fold loop

For systems smaller than `domainFoldIndexThreshold`. One `partition` per target computes the covered
set `es` and its complement `csRest` together and threads both in; the no-op gate scans `csRest`
without a second `denseCoveredBy` sweep, and the survivor list is bound once (`survsV`) — see the
module header's second hoisted `let`. -/

/-- One checked fold for a candidate group, given the covered set `es = denseCoveredCsOf d xs` and
    its complement `csRest` (the non-covered constraints, feeding the no-op gate without a second
    `denseCoveredBy` sweep). -/
def denseFoldStepWithV (d : DenseConstraintSystem p) (xs : List VarId)
    (es : List (DenseExpr p)) (csRest : List (DenseExpr p)) :
    DenseConstraintSystem p :=
  match denseGroupDoms es xs with
  | none => d
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableWV d xs survsV csRest then
        denseFoldOutV d xs survsV
      else d
    else d

/-- The direct fold loop: one `partition` per target computes the covered set `es` and its complement
    `csRest` together, no index and no second `denseCoveredBy` sweep for the gate. -/
def denseFoldLoopDirectV : List (List VarId) → DenseConstraintSystem p → DenseConstraintSystem p
  | [], d => d
  | xs :: rest, d =>
    match d.algebraicConstraints.partition (denseCoveredBy xs) with
    | (es, csRest) => denseFoldLoopDirectV rest (denseFoldStepWithV d xs es csRest)

/-! ## The index-preserving indexed-path rewrite

The direct path keeps the `anyVarIn xs || hasConstFoldableNode` gate (`denseFoldRewriteV` above);
the indexed path uses its own `anyVarIn`-only gate feeding an *order- and length-preserving*
in-place fold (an `if`-`then`-`else` `.map`, not a filter-then-append reshuffle) — which is what
lets `DenseFoldIdx.refresh` keep both inverted indexes **without any rebuild** across an accepted
fold (positions never move). `denseFoldOutIdxV` then computes that same in-place fold *sparsely*,
touching only the bucketed candidate positions.

The four defs below implement that indexed-path shape and are wired below: `denseFoldStepV`
computes an accepted fold via `denseFoldOutIdxV` (provably `denseFoldOutInPlaceV`) and refreshes the
index without rebuilding. -/

/-- The indexed-path fold rewrite, gated by `anyVarIn` alone: an expression sharing no variable with
    the group is returned untouched (the same object) — what lets `denseFoldOutIdxV` below skip such
    expressions without even reaching them. Wraps the same `denseFoldRewriteGoV` recursion
    `denseFoldRewriteV` above uses, only with the `hasConstFoldableNode` half of the gate dropped
    (that half is direct-path-only, per the section note above). -/
def denseFoldRewriteIdxV (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs then denseFoldRewriteGoV xs survsV e else e

/-- The in-place fold, order- and length-preserving: fold every non-covered constraint and every bus
    interaction *in place*; keep the covered (domain-pinning) constraints verbatim, also in place.
    Positions never move and rewrites only ever shrink an expression's variable set — unlike
    `denseFoldOutV` above (which filters the non-covered constraints out, folds them, then appends
    the covered ones back), this is what lets an accepted fold refresh the inverted index without
    any rebuild. Bus interaction expressions are rewritten field-by-field, the same inline shape
    `denseFoldOutV` above uses. -/
def denseFoldOutInPlaceV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map
      (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c),
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
      payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }) }

/-- The deduplicating position set of every bucket entry for a variable of `xs` — the positions an
    accepted fold can possibly touch. Same shape already inlined once per side inside
    `denseSystemHasFoldableIdxV` above; this is the reusable standalone form `denseFoldOutIdxV`
    below needs. -/
def denseTouchedSet (idx : DenseCovIndex) (xs : List VarId) : Std.HashSet Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])).foldl (·.insert ·) ∅

/-- `denseFoldOutInPlaceV`, computed sparsely through the index: only candidate positions (bucketed
    under a variable of `xs`) are rewritten; all others are passed through by position, unchanged.
    `touchedCs`/`touchedBis` are each bound **once**, outside both `.map` closures — inlining either
    call into its closure would rebuild the whole `HashSet` per element, the same arity-expansion
    trap the module header's hoisted `let`s guard against. -/
def denseFoldOutIdxV (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  let touchedCs : Std.HashSet Nat := denseTouchedSet fidx.idx xs
  let touchedBis : Std.HashSet Nat := denseTouchedSet fidx.bisIdx xs
  { algebraicConstraints := d.algebraicConstraints.zipIdx.map (fun ci =>
      if touchedCs.contains ci.2 then
        (if denseCoveredBy xs ci.1 then ci.1 else denseFoldRewriteIdxV xs survsV ci.1)
      else ci.1),
    busInteractions := d.busInteractions.zipIdx.map (fun bii =>
      if touchedBis.contains bii.2 then
        { bii.1 with
          multiplicity := denseFoldRewriteIdxV xs survsV bii.1.multiplicity,
          payload := bii.1.payload.map (denseFoldRewriteIdxV xs survsV) }
      else bii.1) }

/-! ## The indexed fold loop

For systems at least `domainFoldIndexThreshold` large. The covered set is served from the prebuilt
`DenseFoldIdx` and refreshed (no rebuild) only on an accepted fold — see `DomainFold.lean`'s module
header for the rationale. The single-evaluation `let` for the whole step's result is what makes the
indexed loop run each `denseFoldStepV` exactly once per target. -/

/-- One checked fold for a candidate group, served from the prebuilt covered-constraint index. An
    accepted fold is computed sparsely (`denseFoldOutIdxV`, provably the in-place fold) and bound
    **once** as `ro` (the arity trap), then the index is **refreshed without any rebuild**
    (`fidx.refresh`, keeping both bucket maps, re-materialising only the item arrays). -/
def denseFoldStepV (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    DenseConstraintSystem p × DenseFoldIdx p :=
  let es := denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs
  match denseGroupDoms es xs with
  | none => (d, fidx)
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableIdxV fidx xs survsV then
        let ro := denseFoldOutIdxV d fidx xs survsV
        (ro, fidx.refresh ro)
      else (d, fidx)
    else (d, fidx)

/-- Process the candidate groups sequentially, threading and refreshing the index. The whole step's
    result is bound once (`r`) and both its output and its refreshed index are read from that single
    binding (see the module header). -/
def denseFoldLoopV : List (List VarId) → DenseConstraintSystem p → DenseFoldIdx p →
    DenseConstraintSystem p
  | [], d, _ => d
  | xs :: rest, d, fidx =>
    let r := denseFoldStepV d fidx xs
    denseFoldLoopV rest r.1 r.2

/-! ## The candidate group list

The candidate group order (`VarId`-order `mergeSort`, see the module header) and the `svSet`
hoisted-`let` (bound once, outside the `filterMap`, see the module header) both live here. -/

/-- The candidate fold targets: every constraint's 2–8-distinct-variable group, every variable of
    which has some single-variable constraint somewhere (`denseSvSet`, bound **once**), sorted by
    `VarId.index` (the natural dense order, no name resolution — same `mergeSort`/`dedupHash`
    structure and stability as any other order would give) and deduplicated. -/
def denseTargetsV (d : DenseConstraintSystem p) : List (List VarId) :=
  let svSet := denseSvSet d
  dedupHash (d.algebraicConstraints.filterMap (fun c =>
    let vs := HashedDedup.hashedDedup (hash ·) c.vars
    if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
      some (vs.mergeSort (fun a b => compare a.index b.index != .gt))
    else none))

/-! ## The pass -/

/-- The dense domain-constant folding transform, no `VarRegistry` needed (see the module header).
    Prime `p` only; identity otherwise. Systems at least `domainFoldIndexThreshold` large use the
    indexed loop; smaller ones use the direct loop — both compute the identical fold. -/
def denseDomainFoldFV (pw : PrimeWitness p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let targets := denseTargetsV d
    if domainFoldIndexThreshold ≤ d.algebraicConstraints.length then
      denseFoldLoopV targets d (DenseFoldIdx.mk' d)
    else denseFoldLoopDirectV targets d
  else d

end ApcOptimizer.Dense
