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

/-- `survivesAllCW`, over a value-only point: compiled items' zero test plus interactions'
    obligation check. -/
def denseSurvivesAllCWV (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (bs : BusSemantics p) (ces : List (IExpr p)) (cbis : List (CBi p))
    (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWithV ops pt ie)) &&
    cbis.all (fun cbi =>
      let v := denseCBiEvalWithV ops cbi pt
      isZero v.multiplicity || !bs.violatesConstraint v)

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
    let dec : DecidableEq (ZMod p) := inferInstance
    let isZero : ZMod p → Bool := fun v => @decide (v = ops.zero) (dec v ops.zero)
    ⟨fun pt => denseSurvivesAllCWV ops isZero bs ces cbis pt⟩
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

/-- One scan step: `none` hunts the first survivor and initializes tracked positions from its point;
    `some cands` intersects the mask against a surviving point, unchanged otherwise. -/
def denseCandsOfPointV : List Bool → List (ZMod p) → DenseCandsV p
  | track :: tracks, v :: vs =>
      (if track then some v else none) :: denseCandsOfPointV tracks vs
  | _, _ => []

def denseScanStepV (track : List Bool) (surv : List (ZMod p) → Bool) :
    Option (DenseCandsV p) → List (ZMod p) → Option (DenseCandsV p)
  | none, pt => if surv pt = true then some (denseCandsOfPointV track pt) else none
  | some cands, pt =>
    if surv pt = true then
      some (cands.zipWith
        (fun c v => match c with | some cv => if cv = v then some cv else none | none => none) pt)
    else some cands

/-- The dense scan aborts once every tracked candidate has been ruled out. -/
def denseScanStopV : Option (DenseCandsV p) → Bool
  | none => false
  | some cands => cands.all Option.isNone

/-- The value-only box scan, streamed lazily over the symbolic domains; false `track` positions
    remain absent from the candidate mask. -/
def denseScanBoxV (track : List Bool) (surv : List (ZMod p) → Bool)
    (doms : List (FiniteDomain p)) :
    Option (DenseCandsV p) :=
  denseBoxFoldV (denseScanStepV track surv) denseScanStopV doms none

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

structure DenseConstraintGatherV (p : ℕ) where
  fullCount : Nat
  active : List (DenseExpr p)

def denseGatherConstraintsLoopV (arr : Array (DenseConstraintPlan p)) (xs : List VarId) :
    List Nat → DenseConstraintGatherV p → DenseConstraintGatherV p
  | [], acc => acc
  | i :: rest, acc =>
    if h : i < arr.size then
      let plan := arr[i]
      if denseVarsInListF xs plan.vars then
        denseGatherConstraintsLoopV arr xs rest
          { fullCount := acc.fullCount + 1,
            active := if plan.active then plan.expr :: acc.active else acc.active }
      else denseGatherConstraintsLoopV arr xs rest acc
    else denseGatherConstraintsLoopV arr xs rest acc

def denseGatherConstraintsV (fidx : DenseForcedIdx p) (xs : List VarId) :
    DenseConstraintGatherV p :=
  denseGatherConstraintsLoopV fidx.arrCs xs (denseCandidates fidx.csIdx xs) ⟨0, []⟩

structure DenseBusGatherV (p : ℕ) where
  count : Nat
  informative : Bool
  interactions : List (BusInteraction (DenseExpr p))

def denseGatherBusesLoopV (arr : Array (DenseBusPlan p)) (xs : List VarId) :
    List Nat → DenseBusGatherV p → DenseBusGatherV p
  | [], acc => acc
  | i :: rest, acc =>
    if h : i < arr.size then
      let plan := arr[i]
      if plan.usable && denseVarsInListF xs plan.vars then
        denseGatherBusesLoopV arr xs rest
          { count := acc.count + 1,
            informative := acc.informative || plan.informative,
            interactions := plan.interaction :: acc.interactions }
      else denseGatherBusesLoopV arr xs rest acc
    else denseGatherBusesLoopV arr xs rest acc

def denseGatherBusesV (fidx : DenseForcedIdx p) (xs : List VarId) : DenseBusGatherV p :=
  denseGatherBusesLoopV fidx.arrBis xs (denseCandidates fidx.bisIdx xs) ⟨0, false, []⟩

def denseRestrictDomainV (dσ : DenseSolved p) (xd : VarId × FiniteDomain p) :
    VarId × FiniteDomain p :=
  match dσ.map[xd.1]? with
  | some (.const c) => (xd.1, .explicit [c])
  | _ => xd

def denseRestrictDomsV (dσ : DenseSolved p) (doms : List (VarId × FiniteDomain p)) :
    List (VarId × FiniteDomain p) :=
  doms.map (denseRestrictDomainV dσ)

def denseTrackDomsV (dσ : DenseSolved p) (doms : List (VarId × FiniteDomain p)) : List Bool :=
  doms.map fun xd =>
    match dσ.map[xd.1]? with
    | some (.const _) => false
    | _ => true

/-- All checked forced constants over the variable set `xs`. `keys` drives the compiler and the
    final zip; the unkeyed `doms` drives the value-only scan. -/
def denseForcedOverV (bs : BusSemantics p) (_facts : BusFacts p bs) (T : DenseDomainTable p)
    (fidx : DenseForcedIdx p) (dσ : DenseSolved p) (xs : List VarId) : List (VarId × ZMod p) :=
  match T.doms xs with
  | none => []
  | some baseDoms =>
    let fdoms := denseRestrictDomsV dσ baseDoms
    let boxSize := (fdoms.map (fun yd => yd.2.size)).prod
    if boxSize ≤ maxEnumSize then
      let cs := denseGatherConstraintsV fidx xs
      let bis := denseGatherBusesV fidx xs
      let informative := cs.fullCount != 0 || bis.informative
      if informative && boxSize * (cs.fullCount + bis.count) ≤ maxEnumWork then
        let keys := fdoms.map Prod.fst
        let doms := fdoms.map Prod.snd
        let survC := denseCompiledSurvV bs cs.active bis.interactions keys
        match denseScanBoxV (denseTrackDomsV dσ baseDoms) survC.run doms with
        | none =>
          -- no surviving point: the box has no solutions, so everything is vacuously forced
          keys.map (fun x => (x, (0 : ZMod p)))
        | some cands =>
          -- recover the forced `(x, c)` pairs by zipping the mask with `keys` once, at the end
          (keys.zip cands).filterMap (fun xc => xc.2.map (fun c => (xc.1, c)))
      else []
    else []

/-! ## `collectForced`, value-only -/

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
    constants into the solution map in target order. -/
def denseCollectForcedV (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p) (targets : List (List VarId))
    (seen : Std.HashSet (List VarId)) (dσ0 : DenseSolved p) :
    DenseSolved p :=
  let uniq := denseDedupTargetsV targets seen
  uniq.foldl (init := dσ0) fun dσ xs =>
    dσ.insertAll
      ((denseForcedOverV bs facts T fidx dσ xs).map (fun f => (f.1, DenseExpr.const f.2)))

/-! ## The pass transform, value-only -/

def denseConstraintPlansV (T : DenseDomainTable p) (cs : List (DenseExpr p)) :
    List (DenseConstraintPlan p) :=
  cs.map fun c =>
    { expr := c,
      vars := HashedDedup.hashedDedup (hash ·) c.vars,
      active := !denseConstraintRedundantV T c }

def denseBusPlansV (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) : List (DenseBusPlan p) :=
  bis.map fun bi =>
    let usable := !bs.isStateful bi.busId
    { interaction := bi,
      vars := HashedDedup.hashedDedup (hash ·) (denseBIVars bi),
      usable,
      informative := usable && denseBiInformative bs facts bi }

def densePlanTargetsV (cs : List (DenseConstraintPlan p)) (bis : List (DenseBusPlan p)) :
    List (List VarId) :=
  cs.map (fun c => c.vars) ++ bis.map (fun bi => bi.vars)

def denseForcedIdxV (cs : List (DenseConstraintPlan p)) (bis : List (DenseBusPlan p)) :
    DenseForcedIdx p :=
  { csIdx := denseAnchorCovBuild (fun c => c.vars) cs,
    arrCs := cs.toArray,
    bisIdx := denseAnchorCovBuild (fun bi => bi.vars) bis,
    arrBis := bis.toArray }

/-- Domain-batch: builds a finite domain per variable (from constraints like `x*(x-1)=0` giving
    `x ∈ {0,1}`, and from bus range checks), enumerates the small Cartesian product of those
    domains, and for each variable that takes the same value in every surviving assignment infers
    that forced constant. Returns the map of all such `var := const` substitutions. -/
def denseDomainBatchσV (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseSolved p :=
  let T : DenseDomainTable p :=
    denseAddBusDoms bs facts d.busInteractions
      (denseAddConstraintDoms d.algebraicConstraints DenseDomainTable.empty)
  let csPlans := denseConstraintPlansV T d.algebraicConstraints
  let busPlans := denseBusPlansV bs facts d.busInteractions
  let targets := densePlanTargetsV csPlans busPlans
  let fidx := denseForcedIdxV csPlans busPlans
  denseCollectForcedV bs facts T fidx targets ∅ DenseSolved.empty

/-- The value-only dense domain-batch transform. -/
def denseDomainBatchTransformV (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then applyσ (denseDomainBatchσV bs facts d) d else d

end ApcOptimizer.Dense
