import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchRuntime

set_option autoImplicit false

/-! # Dense `domainFold`, with compiled value-only evaluation

The hot evaluators (`denseGroupSurvivorsEV`, `denseConstOnSurvsV`) compile the group's covered
constraints once (via `DomainBatch.lean`'s `IExpr`) and evaluate every enumerated point by index,
value-only (`List (ZMod p)` points, no `VarId` per point). Systems at least
`domainFoldIndexThreshold` large use the index-preserving indexed loop; smaller ones the direct
loop. Runtime only — correctness is in `Proofs/DomainFold.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Value-only eager enumeration of a group's domain -/

/-- Cartesian product of the group's per-variable domain values, value-only (each point a
    `List (ZMod p)` in the input domain-list order). -/
def denseAssignmentsV : List (List (ZMod p)) → List (List (ZMod p))
  | [] => [[]]
  | d :: rest => (denseAssignmentsV rest).flatMap (fun a => d.map (fun v => v :: a))

/-! ## The group's survivor filter, compiled once per target -/

/-- Whether every compiled covered constraint `ces` zeroes at point `pt`. -/
def denseSurvZeroCWV (ops : DenseZModOps p) (isZero : ZMod p → Bool) (ces : List (IExpr p))
    (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWithV ops pt ie))

/-- The surviving group values, value-only: covered constraints `es` compiled once over key list
    `xs`, every enumerated point checked by index. Falls back to the uncompiled filter only if
    compilation fails (dead for a covered set, kept for totality). -/
def denseGroupSurvivorsEV (es : List (DenseExpr p)) (xs : List VarId)
    (domVals : List (List (ZMod p))) : List (List (ZMod p)) :=
  match denseCompileEs xs es with
  | some ces =>
    let ops : DenseZModOps p := denseZModOps
    let dec : DecidableEq (ZMod p) := inferInstance
    let isZero : ZMod p → Bool := fun v => @decide (v = ops.zero) (dec v ops.zero)
    let surv : DenseSurvV p := ⟨fun pt => denseSurvZeroCWV ops isZero ces pt⟩
    (denseAssignmentsV domVals).filter surv.run
  | none =>
    (denseAssignmentsV domVals).filter
      (fun a => es.all (fun c => decide (c.eval (denseEnvOfKeysV xs a) = 0)))

/-! ## `constOnSurvs`, compiled per candidate node -/

/-- `some c` if `e` evaluates to the same constant `c` on every survivor, else `none`. `e` is
    compiled once over key list `xs` and every survivor checked by index (uncompiled fallback kept
    for totality). -/
def denseConstOnSurvsV (xs : List VarId) (survsV : List (List (ZMod p))) (e : DenseExpr p) :
    Option (ZMod p) :=
  match survsV with
  | [] => none
  | s₀ :: rest =>
    match denseCompileE xs e with
    | some ie =>
      let ops : DenseZModOps p := denseZModOps
      let v₀ := denseIExprEvalWithV ops s₀ ie
      if (s₀ :: rest).all (fun s => decide (denseIExprEvalWithV ops s ie = v₀))
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

/-- Does the fold change anything? The direct path's no-op efficiency gate; `csRest` is the
    caller's precomputed non-covered constraint list. -/
def denseSystemHasFoldableWV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) (csRest : List (DenseExpr p)) : Bool :=
  csRest.any (fun c => c.hasFoldableV xs survsV) ||
    d.busInteractions.any (fun bi =>
      bi.multiplicity.hasFoldableV xs survsV || bi.payload.any (fun e => e.hasFoldableV xs survsV))

/-- The indexed path's no-op gate: scans only the items sharing a variable with `xs` through the
    prebuilt inverted indexes. -/
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

For systems smaller than `domainFoldIndexThreshold`. -/

/-- One checked fold for a candidate group, given the covered set `es` and its complement `csRest`
    (the non-covered constraints, feeding the no-op gate). -/
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

/-- The direct fold loop: one `partition` per target splits the covered set `es` and complement
    `csRest`, no index. -/
def denseFoldLoopDirectV : List (List VarId) → DenseConstraintSystem p → DenseConstraintSystem p
  | [], d => d
  | xs :: rest, d =>
    match d.algebraicConstraints.partition (denseCoveredBy xs) with
    | (es, csRest) => denseFoldLoopDirectV rest (denseFoldStepWithV d xs es csRest)

/-! ## The index-preserving indexed-path rewrite

The indexed path uses an `anyVarIn`-only gate feeding an order- and length-preserving in-place fold,
so `DenseFoldIdx.refresh` keeps both inverted indexes without rebuilding across an accepted fold
(positions never move); `denseFoldOutIdxV` computes that fold sparsely, touching only bucketed
candidate positions. -/

/-- The indexed-path fold rewrite, gated by `anyVarIn` alone: an expression sharing no variable with
    the group is returned untouched, letting `denseFoldOutIdxV` skip it. -/
def denseFoldRewriteIdxV (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs then denseFoldRewriteGoV xs survsV e else e

/-- The in-place fold, order- and length-preserving: fold every non-covered constraint and bus
    interaction in place, keep the covered (domain-pinning) constraints verbatim in place. Positions
    never move and rewrites only shrink variable sets, so an accepted fold can refresh the index
    without rebuild. -/
def denseFoldOutInPlaceV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map
      (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c),
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
      payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }) }

/-- The deduplicated set of bucket positions for the variables of `xs` — the positions an accepted
    fold can possibly touch. -/
def denseTouchedSet (idx : DenseCovIndex) (xs : List VarId) : Std.HashSet Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])).foldl (·.insert ·) ∅

/-- `denseFoldOutInPlaceV` computed sparsely: only candidate positions (bucketed under a variable of
    `xs`) are rewritten; all others pass through unchanged by position. -/
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

For systems at least `domainFoldIndexThreshold` large; the covered set is served from the prebuilt
`DenseFoldIdx`, refreshed (no rebuild) only on an accepted fold. -/

/-- One checked fold served from the prebuilt covered-constraint index; an accepted fold is computed
    sparsely (`denseFoldOutIdxV`) and the index refreshed without rebuild (`fidx.refresh`). -/
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

/-- Process the candidate groups sequentially, threading and refreshing the index. -/
def denseFoldLoopV : List (List VarId) → DenseConstraintSystem p → DenseFoldIdx p →
    DenseConstraintSystem p
  | [], d, _ => d
  | xs :: rest, d, fidx =>
    let r := denseFoldStepV d fidx xs
    denseFoldLoopV rest r.1 r.2

/-! ## The array-native indexed fold loop (runtime twin)

`denseFoldLoopV` threads the *list* system `d` and re-materializes it per accepted fold:
`denseFoldOutIdxV` maps over `d.algebraicConstraints.zipIdx` / `d.busInteractions.zipIdx` (each an
O(system) `toArray` + rebuild) and `DenseFoldIdx.refresh` converts the folded lists back to arrays.
The twin below threads only the `DenseFoldIdx` (already array-backed) and applies an accepted fold
with `Array.modify` at the touched positions — O(touched) per accept — materializing lists once at
the pass exit. `denseDomainFoldFV_eq_fast` (`Proofs/DomainFold.lean`) proves it equal to
`denseDomainFoldFV` and installs it with `@[csimp]`. -/

/-- `denseFoldOutIdxV` + `refresh`, array-native: modify only the touched positions, in place. -/
def denseFoldOutArrV (fidx : DenseFoldIdx p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseFoldIdx p :=
  match fidx with
  | ⟨idx, arr, bisIdx, arrBis⟩ =>
    ⟨idx,
     (denseTouchedSet idx xs).toList.foldl
       (fun a i => a.modify i
         (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c)) arr,
     bisIdx,
     (denseTouchedSet bisIdx xs).toList.foldl
       (fun a i => a.modify i
         (fun bi => { bi with
           multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
           payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) })) arrBis⟩

/-- `denseFoldStepV`, array-native: the identical probe/gate served from the shared index, with an
    accepted fold applied sparsely by `denseFoldOutArrV`. -/
def denseFoldStepArrV (fidx : DenseFoldIdx p) (xs : List VarId) : DenseFoldIdx p :=
  let es := denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs
  match denseGroupDoms es xs with
  | none => fidx
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableIdxV fidx xs survsV then
        denseFoldOutArrV fidx xs survsV
      else fidx
    else fidx

/-- Process the candidate groups sequentially, array-native. -/
def denseFoldLoopArrV : List (List VarId) → DenseFoldIdx p → DenseFoldIdx p
  | [], fidx => fidx
  | xs :: rest, fidx => denseFoldLoopArrV rest (denseFoldStepArrV fidx xs)

/-! ## The candidate group list -/

/-- The candidate fold targets: every constraint's 2–8-distinct-variable group all of whose
    variables occur in some single-variable constraint (`denseSvSet`), sorted by `VarId.index` and
    deduplicated. -/
def denseTargetsV (d : DenseConstraintSystem p) : List (List VarId) :=
  let svSet := denseSvSet d
  dedupHash (d.algebraicConstraints.filterMap (fun c =>
    let vs := HashedDedup.hashedDedup (hash ·) c.vars
    if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
      some (vs.mergeSort (fun a b => compare a.index b.index != .gt))
    else none))

/-! ## The pass -/

/-- Domain-constant subexpression folding: for a group of variables pinned to finite domains by
    "covered" constraints, enumerates the surviving joint assignments and replaces every
    wholly-in-group subexpression that is constant across all survivors by that constant. E.g. if
    the covered constraints force `x + y = 1` on every survivor, each `x + y` subterm folds to `1`. -/
def denseDomainFoldFV (pw : PrimeWitness p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let targets := denseTargetsV d
    if domainFoldIndexThreshold ≤ d.algebraicConstraints.length then
      denseFoldLoopV targets d (DenseFoldIdx.mk' d)
    else denseFoldLoopDirectV targets d
  else d

/-- `denseDomainFoldFV` with the array-native loop on the indexed path. Proven equal and installed
    by `denseDomainFoldFV_eq_fast` (`Proofs/DomainFold.lean`). -/
def denseDomainFoldFVFast (pw : PrimeWitness p) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if pw.isPrime = true then
    let targets := denseTargetsV d
    if domainFoldIndexThreshold ≤ d.algebraicConstraints.length then
      let fidx := denseFoldLoopArrV targets (DenseFoldIdx.mk' d)
      { algebraicConstraints := fidx.arr.toList, busInteractions := fidx.arrBis.toList }
    else denseFoldLoopDirectV targets d
  else d

end ApcOptimizer.Dense
