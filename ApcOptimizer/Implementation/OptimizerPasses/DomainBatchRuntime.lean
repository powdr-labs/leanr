import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch

set_option autoImplicit false

/-! # Dense `domainBatch`, with value-only box points

Box enumeration, the compiled survivor predicate, and the scan use **value-only points**
(`List (ZMod p)`, positionally aligned with a `keys : List VarId` computed once per target): nothing
on the enumeration path reads a key from a point, so carrying one would only cost a per-point key
scan. The shrinking candidate set is a fixed-length mask `List (Option (ZMod p))` aligned with
`keys`; `denseForcedOverV` zips it back with `keys` once at the end. Everything off the per-point
path (domain table, inverted index, compiler, dedup key, substitution) is reused from
`DomainBatch.lean` and `Gauss.lean`. Runtime-only: no proof obligations here. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Value-only positional lookup and compiled evaluation -/

/-- Positional lookup in a value-only point (position alone determines the value). -/
def denseLookupIxV (zero : ZMod p) : List (ZMod p) → Nat → ZMod p
  | [], _ => zero
  | v :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIxV zero rest i

/-- `IExpr.evalWith`, over a value-only point (hoisted `add`/`mul`). -/
def denseIExprEvalWithV (ops : DenseZModOps p) (pt : List (ZMod p)) :
    IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIxV ops.zero pt i
  | .add a b => ops.add (denseIExprEvalWithV ops pt a) (denseIExprEvalWithV ops pt b)
  | .mul a b => ops.mul (denseIExprEvalWithV ops pt a) (denseIExprEvalWithV ops pt b)

/-- `CBi.evalWith`, over a value-only point. -/
def denseCBiEvalWithV (ops : DenseZModOps p) (cbi : CBi p) (pt : List (ZMod p)) :
    BusInteraction (ZMod p) :=
  { busId := cbi.busId,
    multiplicity := denseIExprEvalWithV ops pt cbi.mult,
    payload := cbi.payload.map (fun ie => denseIExprEvalWithV ops pt ie) }

/-- Check that every compiled constraint vanishes, stopping at the first failure. -/
def denseAllZeroCWV (ops : DenseZModOps p) (pt : List (ZMod p)) : List (IExpr p) → Bool
  | [] => true
  | ie :: rest =>
    if denseIExprEvalWithV ops pt ie = ops.zero then denseAllZeroCWV ops pt rest else false

/-- Check every compiled bus obligation, skipping payload evaluation when multiplicity is zero. -/
def denseAllBusCWV (ops : DenseZModOps p) (bs : BusSemantics p)
    (pt : List (ZMod p)) : List (CBi p) → Bool
  | [] => true
  | cbi :: rest =>
    let mult := denseIExprEvalWithV ops pt cbi.mult
    if mult = ops.zero then denseAllBusCWV ops bs pt rest
    else
      let v : BusInteraction (ZMod p) :=
        { busId := cbi.busId,
          multiplicity := mult,
          payload := cbi.payload.map (fun ie => denseIExprEvalWithV ops pt ie) }
      if bs.violatesConstraint v then false else denseAllBusCWV ops bs pt rest

/-- `survivesAllCW`, over a value-only point: compiled items' zero test plus interactions'
    obligation check. -/
def denseSurvivesAllCWV (ops : DenseZModOps p) (bs : BusSemantics p)
    (ces : List (IExpr p)) (cbis : List (CBi p))
    (pt : List (ZMod p)) : Bool :=
  denseAllZeroCWV ops pt ces && denseAllBusCWV ops bs pt cbis

/-! ### The uncompiled fallback

Reached only if compilation fails — never for the covered items this pass compiles, so dead code
kept for totality. -/

/-- Value-only environment lookup against an explicit key list (fallback only; see above). -/
def denseEnvOfKeysV (keys : List VarId) (pt : List (ZMod p)) (y : VarId) : ZMod p :=
  match keys, pt with
  | [], _ => 0
  | _, [] => 0
  | x :: ks, v :: vs => if y == x then v else denseEnvOfKeysV ks vs y

/-- Fallback survivor predicate (see the fallback note above). -/
def denseSurvivesAllMV (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (pt : List (ZMod p)) : Bool :=
  es.all (fun e => decide (e.eval (denseEnvOfKeysV keys pt) = 0)) &&
    bis.all (fun bi =>
      let v : BusInteraction (ZMod p) :=
        { busId := bi.busId,
          multiplicity := bi.multiplicity.eval (denseEnvOfKeysV keys pt),
          payload := bi.payload.map (fun e => e.eval (denseEnvOfKeysV keys pt)) }
      decide (v.multiplicity = 0) || !bs.violatesConstraint v)

/-- A per-target survivor predicate, boxed in a one-field structure so its setup (ring instances,
    compilation, `isZero` closure) runs once per target rather than being eta-expanded into the
    per-point call path. -/
structure DenseSurvV (p : ℕ) where
  /-- The per-point survivor test (see `DenseSurvV`). -/
  run : List (ZMod p) → Bool

/-- The per-point survivor predicate for a target over value-only points: compiles the covered
    items against `keys` once, hoisting ring ops and the zero test, with the uncompiled fallback if
    compilation fails. Boxed in `DenseSurvV` (see there). -/
def denseCompiledSurvV (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) :
    DenseSurvV p :=
  match denseCompileEs keys es, denseCompileBis keys bis with
  | some ces, some cbis =>
    let ops : DenseZModOps p := denseZModOps
    ⟨fun pt => denseSurvivesAllCWV ops bs ces cbis pt⟩
  | _, _ => ⟨denseSurvivesAllMV bs es bis keys⟩

/-! ## Value-only lazy box enumeration -/

/-- Stream the Cartesian product of the domains into `f` as value-only points (in `keys` order). -/
def denseBoxFoldV {β : Type} (f : β → List (ZMod p) → β) (stop : β → Bool) :
    List (FiniteDomain p) → β → β
  | [], acc => if stop acc then acc else f acc []
  | d :: rest, acc =>
    denseBoxFoldV (fun acc' a => d.foldElts (fun acc'' v => f acc'' (v :: a)) stop acc') stop rest acc

/-- `(assignments doms).all pred`, value-only (used by `denseConstraintRedundantV`). -/
def denseAllBoxV (pred : List (ZMod p) → Bool) (doms : List (FiniteDomain p)) : Bool :=
  denseBoxFoldV (fun acc pt => acc && pred pt) (fun acc => !acc) doms true

/-! ### The value-only box scan

The tracked candidate set is a fixed-length mask `List (Option (ZMod p))` aligned with `keys`:
`some c` while that position is still forced to `c` by every survivor so far, `none` once some
survivor disagreed. Ruling a candidate out is a positional `List.zipWith` turning its slot to
`none`; the scan aborts once every slot is `none`. -/

/-- The scan's tracked candidates: a fixed-length mask aligned with `keys`. -/
abbrev DenseCandsV (p : ℕ) := List (Option (ZMod p))

/-- One scan step: `none` while hunting the first survivor (initializes the mask from its point);
    `some cands` intersects the mask against a surviving point, unchanged otherwise. -/
def denseScanStepV (surv : List (ZMod p) → Bool) :
    Option (DenseCandsV p) → List (ZMod p) → Option (DenseCandsV p)
  | none, pt => if surv pt = true then some (pt.map some) else none
  | some cands, pt =>
    if surv pt = true then
      some (cands.zipWith
        (fun c v => match c with | some cv => if cv = v then some cv else none | none => none) pt)
    else some cands

/-- The dense scan aborts once every tracked candidate has been ruled out. -/
def denseScanStopV : Option (DenseCandsV p) → Bool
  | none => false
  | some cands => cands.all Option.isNone

/-- The value-only box scan, streamed lazily over the symbolic domains; the caller
    (`denseForcedOverV`) zips the final mask with `keys` once, after the scan finishes. -/
def denseScanBoxV (surv : List (ZMod p) → Bool) (doms : List (FiniteDomain p)) :
    Option (DenseCandsV p) :=
  denseBoxFoldV (denseScanStepV surv) denseScanStopV doms none

/-! ## Redundancy check, value-only -/

/-- Is this constraint redundant for enumeration — identically zero on the box of its own
    variables' domains? -/
def denseConstraintRedundantV (T : DenseDomainTable p) (c : DenseExpr p) : Bool :=
  match T.doms (HashedDedup.hashedDedup (hash ·) c.vars) with
  | none => false
  | some d =>
    (d.map (fun yd => yd.2.size)).prod ≤ maxEnumSize &&
      match denseCompileE (d.map Prod.fst) c with
      | some ic =>
        let ops : DenseZModOps p := denseZModOps
        let dec : DecidableEq (ZMod p) := inferInstance
        denseAllBoxV
          (fun a => @decide (denseIExprEvalWithV ops a ic = ops.zero) (dec _ ops.zero))
          (d.map Prod.snd)
      | none =>
        denseAllBoxV (fun a => decide (c.eval (denseEnvOfKeysV (d.map Prod.fst) a) = 0))
          (d.map Prod.snd)

/-! ## `forcedOver`, value-only -/

/-- All checked forced constants over the variable set `xs`. `keys` drives the compiler and the
    final zip; the unkeyed `doms` drives the value-only scan. -/
def denseForcedOverV (bs : BusSemantics p) (facts : BusFacts p bs) (T : DenseDomainTable p)
    (fidx : DenseForcedIdx p) (xs : List VarId) : List (VarId × ZMod p) :=
  match T.doms xs with
  | none => []
  | some fdoms =>
    let boxSize := (fdoms.map (fun yd => yd.2.size)).prod
    if boxSize ≤ maxEnumSize then
      let esFull := denseCoveredIdxUnord fidx.csIdx fidx.arrCs (fun c => c.varsInF xs) xs
      let bis := denseCoveredIdxUnord fidx.bisIdx fidx.arrBis
        (fun bi => denseBIVarsInF xs bi && !bs.isStateful bi.busId) xs
      let es := denseCoveredIdxUnord fidx.activeIdx fidx.arrActive (fun c => c.varsInF xs) xs
      let informative := !esFull.isEmpty || bis.any (denseBiInformative bs facts)
      if informative && boxSize * (esFull.length + bis.length) ≤ maxEnumWork then
        let keys := fdoms.map Prod.fst
        let doms := fdoms.map Prod.snd
        let survC := denseCompiledSurvV bs es bis keys
        match denseScanBoxV survC.run doms with
        | none =>
          -- no surviving point: the box has no solutions, so everything is vacuously forced
          keys.map (fun x => (x, (0 : ZMod p)))
        | some cands =>
          -- recover the forced `(x, c)` pairs by zipping the mask with `keys` once, at the end
          (keys.zip cands).filterMap (fun xc => xc.2.map (fun c => (xc.1, c)))
      else []
    else []

/-! ## `collectForced`, value-only

Targets are deduplicated (`denseVarSetKey`) then folded in order; the independent per-target
enumerations can be spawned in parallel on large systems. -/

/-- The `seen`-deduplicated target list, keyed by `denseVarSetKey`: keeps the first target with
    each distinct variable set and drops later repeats. -/
def denseDedupTargetsV :
    List (List VarId) → Std.HashSet (List VarId) → List (List VarId)
  | [], _ => []
  | xs :: rest, seen =>
    let key := denseVarSetKey xs
    if seen.contains key then denseDedupTargetsV rest seen
    else xs :: denseDedupTargetsV rest (seen.insert key)

-- `denseDedupTargetsV` keeps both variables with equal names but distinct `VarId`s (distinct keys).
private def ddRegA : VarRegistry × VarId :=
  VarRegistry.empty.register { name := "x", powdrId? := some 1 }
private def ddRegB : VarRegistry × VarId :=
  ddRegA.1.register { name := "x", powdrId? := some 2 }
#guard denseDedupTargetsV [[ddRegA.2], [ddRegB.2]] ∅ == [[ddRegA.2], [ddRegB.2]]

/-- Collect every checked forced constant: dedup the targets, then fold each target's forced
    constants into the solution map in target order. When `parallel`, the independent per-target
    enumerations are spawned as `Task`s and joined in the same order, so the output is unchanged. -/
def denseCollectForcedV (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p) (parallel : Bool)
    (targets : List (List VarId)) (seen : Std.HashSet (List VarId)) (dσ0 : DenseSolved p) :
    DenseSolved p :=
  let uniq := denseDedupTargetsV targets seen
  if parallel then
    let tasks := uniq.map (fun xs => Task.spawn fun _ => denseForcedOverV bs facts T fidx xs)
    tasks.foldl (init := dσ0) fun dσ t =>
      dσ.insertAll ((t.get).map (fun f => (f.1, DenseExpr.const f.2)))
  else
    uniq.foldl (init := dσ0) fun dσ xs =>
      dσ.insertAll ((denseForcedOverV bs facts T fidx xs).map (fun f => (f.1, DenseExpr.const f.2)))

/-! ## The pass transform, value-only -/

/-- Domain-batch: builds a finite domain per variable (from constraints like `x*(x-1)=0` giving
    `x ∈ {0,1}`, and from bus range checks), enumerates the small Cartesian product of those
    domains, and for each variable that takes the same value in every surviving assignment infers
    that forced constant. Returns the map of all such `var := const` substitutions. -/
def denseDomainBatchσV (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseSolved p :=
  let T : DenseDomainTable p :=
    denseAddBusDoms bs facts d.busInteractions
      (denseAddConstraintDoms d.algebraicConstraints DenseDomainTable.empty)
  let targets := d.algebraicConstraints.map (fun e => HashedDedup.hashedDedup (hash ·) e.vars) ++
    d.busInteractions.map (fun bi => HashedDedup.hashedDedup (hash ·) (denseBIVars bi))
  let activeCs := d.algebraicConstraints.filter (fun c => !denseConstraintRedundantV T c)
  let fidx : DenseForcedIdx p :=
    { csIdx := denseCovBuild DenseExpr.vars d.algebraicConstraints,
      arrCs := d.algebraicConstraints.toArray,
      bisIdx := denseCovBuild denseBIVars d.busInteractions,
      arrBis := d.busInteractions.toArray,
      activeIdx := denseCovBuild DenseExpr.vars activeCs,
      arrActive := activeCs.toArray }
  -- Fan out only at keccak/SHA scale; below it the sequential fold avoids spawn overhead.
  denseCollectForcedV bs facts T fidx (8192 ≤ d.algebraicConstraints.length) targets ∅
    DenseSolved.empty

/-- The value-only dense domain-batch transform. -/
def denseDomainBatchTransformV (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then applyσ (denseDomainBatchσV bs facts d) d else d

end ApcOptimizer.Dense
