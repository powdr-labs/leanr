import ApcOptimizer.Implementation.Dense.DomainFold
import ApcOptimizer.Implementation.Dense.DomainBatchNative

set_option autoImplicit false

/-! # Dense `domainFold`, rebuilt with compiled value-only evaluation (Task 3 — perf fix)

The committed `Dense/DomainFold.lean` port is byte-identical to the spec pass but **+27% slower**
on `apc_037` (`denseDomainFoldPass`, commit `6511a2a`). Its two hot evaluators,
`denseGroupSurvivorsE` (the group's survivor filter) and `denseConstOnSurvs` (the constant-on-
survivors check that drives the fold), evaluate every candidate with the *slow* `DenseExpr.eval`
(re-derives the `CommRing (ZMod p)` operation chain at every `add`/`mul` node) against
`denseEnvOfFast`, an assoc-list env keyed by `VarId` (a linear key scan per variable lookup, per
node, per survivor). The **spec** pass this ports (`OptimizerPasses/DomainFold.lean`, current
version, which already carries upstream's #127 constant-on-survivors hoist) evaluates both through
the `domainBatch`/`reencode` compile-once machinery instead: `groupSurvivorsE` compiles its group's
covered constraints to positional `IExpr`s **once per target** (`compileEs`) and evaluates every
enumerated point by index, with the ring operations hoisted out of the `ZMod p` instances once
(`survZeroCW`) — see `Reencode.lean`'s `groupSurvivorsE`/`groupSurvivorsE_eq`. This file rebuilds
exactly that hot slice **value-only** (`List (ZMod p)` points, no `VarId` travels with a point at
all — one step further than the spec's own `List (Variable × ZMod p)` point, which is already
positionally accessed via `lookupIx` and never actually needs its keys), reusing
`Dense/DomainBatchNative.lean`'s value-only compile/eval engine
(`denseCompileE(s)`, `denseIExprEvalWithV`, `denseEnvOfKeysV`) exactly as that module built it for
`domainBatch`'s box scan. `constOnSurvs` gets the **same** treatment for consistency and to remove
its own per-node ring-op-reconstruction + linear-scan cost, even though the *current* spec text only
hoists it via `evalFast` (no `compileE`): every `e` passed to `constOnSurvs` already satisfies
`e.varsIn xs` (checked by its caller, `foldRewriteGo`, right before calling it), so `e`'s variables
are always a subset of the same `xs`/`keys` the group's domains are enumerated over, and compiling
`e` once per call (mirroring `compileEs`'s per-target compile, at per-node granularity) before
evaluating it against every survivor is the direct value-only analogue of the same compile-once/
eval-per-point hoisting.

## The one authorized divergence

`Dense/DomainFold.lean`'s target list was built by resolving every `VarId` back to its `Variable`
merely to reuse `Variable`'s `compare` for the `mergeSort` that canonicalises each candidate group
(`denseTargets`, `compare (reg.resolve a) (reg.resolve b)`). Per `VarId.md`/`VarIdAddendum.md` and
the user's explicit decision, **this is dropped**: `denseTargetsV` below sorts by `compare a.index
b.index` (the natural `VarId`-native order), with the identical `mergeSort`/`dedupHash` structure
and stability. No `VarRegistry` is threaded into this pass at all any more (`denseDomainFoldFV` takes
no `reg`) — the wiring/`DenseVerifiedPassW` layer the prover builds still needs `reg` to invoke
`decodeCS`/state coverage, but the pass's own algorithm no longer resolves an ID to a `Variable`
anywhere. **Downstream output may legitimately differ from the reference on this pass**: a
different (but still valid, un-dominated) candidate group order can accept a different — still
correct — set of folds, which can cascade through the cleanup fixpoint into a different, still
correct, final system. The prover should compare against the reference and attribute any count
difference to this authorized reordering, not treat it as a regression.

## Structural fixes recovered from the spec (not new algorithm, restored fidelity)

Three more spots where the *old* dense port (`Dense/DomainFold.lean`) dropped a `let`-binding the
spec has, each turning a single computation into a repeated one — restored here, since "reuse the
existing algorithm" means reusing the spec's actual sharing, not the old port's accidental
re-derivation of it:

* `denseFoldLoop` called `(denseFoldStep d fidx xs).1` and `.2` as two **separate** calls (no `let`),
  so the entire indexed fold step — covered-index scan, domain lookup, survivor enumeration, gate,
  and (on an accepted fold) the whole rewrite — ran **twice** per target. The spec's `foldLoop` binds
  `let r1 := foldStep bs cs fidx xs` once. `denseFoldLoopV` below does the same
  (`let r := denseFoldStepV d fidx xs`).
* `denseFoldStepWith` wrote `denseGroupSurvivorsE es doms` **three times** in its guard/output
  (`1 ≤ … .length`, `denseSystemHasFoldable …`, `denseFoldOut …`) with no `let`, so the group's
  domain enumeration and covered-constraint filter ran three times per target. The spec's
  `foldStepWith` binds `let survs := groupSurvivorsE es doms` once. `denseFoldStepWithV` binds
  `survsV` once, matching it.
* `denseTargets` called `(denseSvSet d).contains ·` — a fresh call to `denseSvSet d`, which folds
  over **every** algebraic constraint to build a `HashSet` — inside the `filterMap` closure run once
  per candidate constraint, rebuilding the whole set from scratch for every 2–8-variable group
  candidate (an `O(#targets × #constraints)` blow-up). The spec binds
  `let svSet := cs.algebraicConstraints.foldl …` once, **before** the `filterMap`, and the closure
  only reads the captured `svSet`. `denseTargetsV` does the same (`let svSet := denseSvSet d`, bound
  once, outside the `filterMap`).

None of these three change the *result*; they were unauthorized re-derivations of a value the spec
computes once (the "Lean arity-expansion trap" — a `def`/computed value called from inside a
per-element closure re-runs per element unless explicitly hoisted to a `let` outside it), not
algorithmic divergences. Restoring them is part of "mirror the spec exactly" (the spec's `let`
structure *is* part of the algorithm being ported), not a new optimization.

## What is reused unchanged

Everything not on the per-point/per-candidate-node evaluation path is reused verbatim from
`Dense/DomainFold.lean` (old, untouched — this file does not edit it) and
`Dense/DomainBatchNative.lean`/`Dense/DomainBatch.lean`:

* `denseFindDomainAlg`/`denseGroupDoms` (the group's per-variable root-list domains; already
  variable-free `List (ZMod p)` results, no port needed);
* `denseCoveredBy`/`denseCoveredCsOf` (the covered-constraint predicate/filter);
* `DenseFoldIdx`/`.mk'`/`.refresh` and `denseCoveredIdx` (the prebuilt covered-constraint index and
  its order-restoring scan) — untouched, since neither carries a survivor representation;
* `denseSvSet` (already `VarId`-native, no `Variable` resolution inside it — only its *caller* in the
  old port re-invoked it wrongly, fixed above);
* `denseCompileE`/`denseCompileEs`/`IExpr`/`denseVarIx` (the positional compiler, `Dense/DomainBatch.lean`)
  and `denseIExprEvalWithV`/`denseEnvOfKeysV`/`denseLookupIxV` (the value-only evaluator,
  `Dense/DomainBatchNative.lean`) — reused exactly as domainBatch's box scan uses them, since `IExpr`
  is already variable-free and the compiled term is identical regardless of point representation;
* `dedupHash`/`List.mergeSort` (generic, `OptimizerPasses/Reencode.lean`).

No pipeline wiring and no correctness theorems here (the prover's job, per the Task 3 native-proof
architecture): every definition below is runtime-only. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Value-only eager enumeration of a group's domain

`domainFold`'s domains are already concrete `List (ZMod p)` root lists (from `denseFindDomainAlg`/
`denseRootsIn`), not the symbolic `FiniteDomain` `domainBatch`'s box scan lazily streams — the spec
pass enumerates them eagerly via `assignments`/`filter`, with no early exit, so this rebuild keeps
that same eager shape (mirrors `assignments`/`denseAssignments`), only dropping the key from every
point (mirrors `Dense/DomainBatchNative.lean`'s value-only rebuild rationale: nothing on this path
ever reads a key from a point once the compiled `IExpr`s take over). -/

/-- The Cartesian product of the group's per-variable domain values, value-only: every point is a
    `List (ZMod p)` in the same (compile-time-fixed) key order as the input domain list — mirrors
    `assignments`/`denseAssignments` with the key dropped from every entry. -/
def denseAssignmentsV : List (List (ZMod p)) → List (List (ZMod p))
  | [] => [[]]
  | d :: rest => (denseAssignmentsV rest).flatMap (fun a => d.map (fun v => v :: a))

/-! ## The group's survivor filter, compiled once per target (mirrors `groupSurvivorsE`) -/

/-- All the group's covered constraints zero at a value-only point, ring operations hoisted out of
    the instances once by the caller (mirrors `survZeroCW`). -/
def denseSurvZeroCWV (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWithV add mul pt ie = 0))

/-- The surviving group values, value-only: the group's covered constraints `es` are compiled once
    to positional `IExpr`s over the group's key list `xs` (mirrors `groupSurvivorsE`'s
    `compileEs (doms.map Prod.fst) es` — here simply `xs`, since `denseGroupDoms es xs = some doms`
    always yields `doms.map Prod.fst = xs`, see `denseGroupDoms_fst` in `Dense/DomainFold.lean`), and
    every enumerated point (`domVals`, the domains in the same `xs` order) is checked by index, no
    per-variable env scan. Falls back to the direct (uncompiled) filter only if compilation fails —
    dead for a covered set (every leaf is a group variable, hence in `xs`), kept for totality exactly
    as `groupSurvivorsE`/`denseCompiledSurvV` keep their fallback arms. -/
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

/-- `some c` if `e` evaluates to the same constant `c` on every (value-only) survivor, else `none`
    (mirrors `constOnSurvs`/`denseConstOnSurvs`). `e` is compiled once, against the group's key list
    `xs`, to a positional `IExpr` (dead-fallback otherwise, see the module header — every `e` reaching
    this call already has `e.varsIn xs`), and every survivor is checked by index with the ring
    operations hoisted once — the same compile-once/eval-per-point treatment `groupSurvivorsE` gets,
    applied at the finer per-node granularity `constOnSurvs` needs. -/
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

/-! ## The dense fold rewrite, value-only (mirrors `foldRewriteGo`/`denseFoldRewriteGo`) -/

/-- The recursive fold core, value-only survivors (mirrors `foldRewriteGo`/`denseFoldRewriteGo`):
    replace every maximal wholly-in-group subexpression that is constant on the survivors by that
    constant; recurse otherwise. -/
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

/-- The fold rewrite, gated (mirrors `foldRewrite`/`denseFoldRewrite`). -/
def denseFoldRewriteV (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs || e.hasConstFoldableNode then denseFoldRewriteGoV xs survsV e else e

/-! ## The folded output (mirrors `foldOut`/`denseFoldOut`) -/

/-- Fold every non-covered constraint and every bus interaction; keep the covered (domain-pinning)
    constraints verbatim (mirrors `foldOut`/`denseFoldOut`). -/
def denseFoldOutV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map (denseFoldRewriteV xs survsV)
        ++ denseCoveredCsOf d xs,
    busInteractions := d.busInteractions.map
      (fun bi => { bi with
        multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
        payload := bi.payload.map (denseFoldRewriteV xs survsV) }) }

/-! ## The no-op gates, value-only (mirrors `Expression.hasFoldable`/`systemHasFoldable`) -/

/-- Does this expression have a maximal wholly-in-group subexpression that folds to a constant?
    (mirrors `Expression.hasFoldable`/`DenseExpr.hasFoldable`, value-only survivors). Purely an
    efficiency gate. -/
def DenseExpr.hasFoldableV (xs : List VarId) (survsV : List (List (ZMod p))) : DenseExpr p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b =>
      ((DenseExpr.add a b).varsInF xs && (denseConstOnSurvsV xs survsV (.add a b)).isSome) ||
        a.hasFoldableV xs survsV || b.hasFoldableV xs survsV
  | .mul a b =>
      ((DenseExpr.mul a b).varsInF xs && (denseConstOnSurvsV xs survsV (.mul a b)).isSome) ||
        a.hasFoldableV xs survsV || b.hasFoldableV xs survsV

/-- Does the fold change anything in the system? (mirrors `systemHasFoldable`/`denseSystemHasFoldable`,
    value-only survivors). Used by the direct (unindexed) path. -/
def denseSystemHasFoldableV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : Bool :=
  d.algebraicConstraints.any (fun c => !denseCoveredBy xs c && c.hasFoldableV xs survsV) ||
    d.busInteractions.any (fun bi =>
      bi.multiplicity.hasFoldableV xs survsV || bi.payload.any (fun e => e.hasFoldableV xs survsV))

/-- The index-local form of `denseSystemHasFoldableV` (mirrors `systemHasFoldableIdx`/
    `denseSystemHasFoldableIdx`, value-only survivors): scan only the items sharing a variable with
    `xs` through the prebuilt inverted indexes, plus the precomputed const-foldable items when
    disjoint from `xs`. Used by the indexed path. -/
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
    else false)) ||
  (fidx.cfCs.any (fun c => !c.anyVarIn xs)) ||
  (fidx.cfBis.any (fun bi =>
    !(bi.multiplicity.anyVarIn xs || bi.payload.any (fun e => e.anyVarIn xs))))

/-! ## The direct (unindexed) fold loop (mirrors `foldStepWith`/`foldLoopDirect`)

For systems smaller than `domainFoldIndexThreshold`. The covered set is computed once per target and
threaded in as `es` (mirrors the spec exactly); the survivor list is bound once (`survsV`) — see the
module header's second restored `let`. -/

/-- One checked fold for a candidate group, given the covered set `es = denseCoveredCsOf d xs`
    (mirrors `foldStepWith`/`denseFoldStepWith`). -/
def denseFoldStepWithV (d : DenseConstraintSystem p) (xs : List VarId) (es : List (DenseExpr p)) :
    DenseConstraintSystem p :=
  match denseGroupDoms es xs with
  | none => d
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableV d xs survsV then
        denseFoldOutV d xs survsV
      else d
    else d

/-- The direct fold loop: recompute `denseCoveredCsOf d xs` per target, no index (mirrors
    `foldLoopDirect`/`denseFoldLoopDirect`). -/
def denseFoldLoopDirectV : List (List VarId) → DenseConstraintSystem p → DenseConstraintSystem p
  | [], d => d
  | xs :: rest, d => denseFoldLoopDirectV rest (denseFoldStepWithV d xs (denseCoveredCsOf d xs))

/-! ## The indexed fold loop (mirrors `foldStep`/`foldLoop`)

For systems at least `domainFoldIndexThreshold` large. The covered set is served from the prebuilt
`DenseFoldIdx` and rebuilt only on an accepted fold — see `Dense/DomainFold.lean`'s module header for
the rationale, unchanged here. The single-evaluation `let` for the whole step's result (restored,
see the module header's first fix) is what makes the indexed loop run each `denseFoldStepV` exactly
once per target. -/

/-- One checked fold for a candidate group (mirrors `foldStep`/`denseFoldStep`), served from the
    prebuilt covered-constraint index and refreshed only on an accepted fold. -/
def denseFoldStepV (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    DenseConstraintSystem p × DenseFoldIdx p :=
  let es := denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs
  match denseGroupDoms es xs with
  | none => (d, fidx)
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableIdxV fidx xs survsV then
        let ro := denseFoldOutV d xs survsV
        (ro, fidx.refresh ro)
      else (d, fidx)
    else (d, fidx)

/-- Process the candidate groups sequentially, threading and refreshing the index (mirrors
    `foldLoop`/`denseFoldLoop`). The whole step's result is bound once (`r`) and both its output and
    its refreshed index are read from that single binding — restoring the spec's `let r1 :=
    foldStep …` sharing that the old dense port's two separate `.1`/`.2` calls dropped (see the
    module header). -/
def denseFoldLoopV : List (List VarId) → DenseConstraintSystem p → DenseFoldIdx p →
    DenseConstraintSystem p
  | [], d, _ => d
  | xs :: rest, d, fidx =>
    let r := denseFoldStepV d fidx xs
    denseFoldLoopV rest r.1 r.2

/-! ## The candidate group list (mirrors the spec pass's inline `svSet`/`targets`)

The one authorized divergence (`VarId`-order `mergeSort`, see the module header) and the third
restored `let` (`svSet` bound once, outside the `filterMap`, see the module header) both live here. -/

/-- The candidate fold targets: every constraint's 2–8-distinct-variable group, every variable of
    which has some single-variable constraint somewhere (`denseSvSet`, bound **once** — the restored
    fix), sorted by `VarId.index` (**the authorized divergence**: the reference sorts by the resolved
    `Variable`'s order to canonicalise each group before dedup; here the natural dense order is used
    instead — same `mergeSort`/`dedupHash` structure and stability, no `Variable` resolution) and
    deduplicated (mirrors the spec pass's inline `svSet`/`targets`, and `denseTargets` in
    `Dense/DomainFold.lean`, minus the `VarRegistry` it threaded only for the sort key). -/
def denseTargetsV (d : DenseConstraintSystem p) : List (List VarId) :=
  let svSet := denseSvSet d
  dedupHash (d.algebraicConstraints.filterMap (fun c =>
    let vs := c.vars.dedup
    if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
      some (vs.mergeSort (fun a b => compare a.index b.index != .gt))
    else none))

/-! ## The index-preserving indexed-path rewrite (mirrors #165's `foldRewrite`/`foldOut`/`touchedSet`/
`foldOutIdx`, `OptimizerPasses/DomainFold.lean:121,374-378,887,899`)

Upstream #165 split what used to be one gate into two: the **direct** path keeps the historical
`anyVarIn xs || hasConstFoldableNode` gate under a new name, `foldRewriteC` — that is exactly
`denseFoldRewriteV` above, untouched, still wired as the direct-path/C twin. The **indexed** path
now gets its own `anyVarIn`-only gate, `foldRewrite`, feeding an *order- and length-preserving*
in-place `foldOut` (an `if`-`then`-`else` `.map`, not the old filter-then-append reshuffle
`denseFoldOutV` above still performs) — which is what lets `FoldIdx.refresh` keep both inverted
indexes **without any rebuild** across an accepted fold (positions never move). `foldOutIdx` then
computes that same in-place fold *sparsely*, touching only the bucketed candidate positions.

The four defs below are the dense twins of that new indexed-path shape. They are pure additions:
nothing here is called by `denseFoldStepV`/`denseFoldLoopV`/`denseDomainFoldFV` yet (those still run
the pre-#165 shape via `denseFoldOutV`/`denseFoldRewriteV`) — the wiring swap is a later chunk. -/

/-- The indexed-path fold rewrite, gated by `anyVarIn` alone (mirrors NEW spec `foldRewrite`,
    `DomainFold.lean:121`): an expression sharing no variable with the group is returned untouched
    (the same object) — what lets `denseFoldOutIdxV` below skip such expressions without even
    reaching them (mirrors `foldRewrite_eq_self`). Wraps the same `denseFoldRewriteGoV` recursion
    `denseFoldRewriteV` above uses, only with the `hasConstFoldableNode` half of the gate dropped
    (that half is now direct-path-only, per the section note above). -/
def denseFoldRewriteIdxV (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs then denseFoldRewriteGoV xs survsV e else e

/-- The in-place fold, order- and length-preserving (mirrors NEW spec `foldOut`,
    `DomainFold.lean:374-378`): fold every non-covered constraint and every bus interaction *in
    place*; keep the covered (domain-pinning) constraints verbatim, also in place. Positions never
    move and rewrites only ever shrink an expression's variable set — unlike `denseFoldOutV` above
    (which filters the non-covered constraints out, folds them, then appends the covered ones back,
    the pre-#165 shape), this is what lets an accepted fold refresh the inverted index without any
    rebuild. Bus interaction expressions are rewritten field-by-field (no dense `BusInteraction.mapExpr`
    exists, same inline shape `denseFoldOutV` already uses above). -/
def denseFoldOutInPlaceV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map
      (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c),
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
      payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }) }

/-- The deduplicating position set of every bucket entry for a variable of `xs` (mirrors
    `touchedSet`, `DomainFold.lean:887`) — the positions an accepted fold can possibly touch. Same
    shape already inlined once per side inside `denseSystemHasFoldableIdxV` above; this is the
    reusable standalone form `foldOutIdx`'s dense twin below needs. -/
def denseTouchedSet (idx : DenseCovIndex) (xs : List VarId) : Std.HashSet Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])).foldl (·.insert ·) ∅

/-- `denseFoldOutInPlaceV`, computed sparsely through the index (mirrors `foldOutIdx`,
    `DomainFold.lean:899`): only candidate positions (bucketed under a variable of `xs`) are
    rewritten; all others are passed through by position, unchanged. `touchedCs`/`touchedBis` are
    each bound **once**, outside both `.map` closures (mirrors the spec's own `let touchedCs := …`/
    `let touchedBis := …` at `DomainFold.lean:901-902` — inlining either call into its closure would
    rebuild the whole `HashSet` per element, the same arity-expansion trap the module header's three
    restored `let`s above guard against). -/
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

/-! ## The pass -/

/-- The dense domain-constant folding transform (mirrors `domainFoldPass`/`denseDomainFoldF`), no
    `VarRegistry` needed (see the module header). Prime `p` only; identity otherwise. Systems at
    least `domainFoldIndexThreshold` large use the indexed loop; smaller ones use the direct loop —
    both compute the identical fold, mirroring the spec's own size-gated dispatch exactly. -/
def denseDomainFoldFV (pw : PrimeWitness p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let targets := denseTargetsV d
    if domainFoldIndexThreshold ≤ d.algebraicConstraints.length then
      denseFoldLoopV targets d (DenseFoldIdx.mk' d)
    else denseFoldLoopDirectV targets d
  else d

end ApcOptimizer.Dense
