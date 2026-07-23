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

/-- Direct relation implemented by a compiled byte-bus predicate. -/
inductive DenseBytePredKind where
  | xor
  | pair
  | or
  | and

def DenseBytePredKind.Holds (kind : DenseBytePredKind) (a b r : ZMod p) : Prop :=
  match kind with
  | .xor => r.val = Nat.xor a.val b.val
  | .pair => r = 0
  | .or => r.val = Nat.lor a.val b.val
  | .and => r.val = Nat.land a.val b.val

def denseBytePredRelationV (isZero : ZMod p → Bool) (kind : DenseBytePredKind)
    (a b r : ZMod p) : Bool :=
  match kind with
  | .xor => decide (r.val = Nat.xor a.val b.val)
  | .pair => isZero r
  | .or => decide (r.val = Nat.lor a.val b.val)
  | .and => decide (r.val = Nat.land a.val b.val)

/-- A compiled bus obligation. Supported exact facts evaluate scalar slots directly; `fallback`
    retains the opaque semantics for every other bus. -/
inductive DenseCBiPred (p : ℕ) where
  | always
  | varRange (mult x width : IExpr p)
  | varRangeConst (mult x : IExpr p) (bound : Nat)
  | tupleRange (mult x y : IExpr p) (boundX boundY : Nat)
  | fixedRange (mult value : IExpr p) (bound : Nat)
  | byte (mult o1 o2 result : IExpr p) (bound : Nat) (kind : DenseBytePredKind)
  | fallback (cbi : CBi p)

def denseCompileRangeCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (compiledMult : IExpr p) : Option (DenseCBiPred p) :=
  match bi.multiplicity.constValue? with
  | some mult =>
    if mult = 1 then
      match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some value => (denseCompileE keys value).map (fun iv => .fixedRange compiledMult iv bound)
        | none => none
      | none => none
    else none
  | none => none

def denseCompileByteCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) : Option (DenseCBiPred p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | none => none
    | some (op, o1, o2, result) =>
      match op.constValue?, denseCompileE keys o1, denseCompileE keys o2,
          denseCompileE keys result with
      | some opValue, some io1, some io2, some iresult =>
        if opValue = spec.xorOp then some (.byte mult io1 io2 iresult spec.bound .xor)
        else if opValue = spec.pairOp then some (.byte mult io1 io2 iresult spec.bound .pair)
        else
          match spec.orOp, spec.andOp with
          | some orOp, _ =>
            if opValue = orOp then some (.byte mult io1 io2 iresult spec.bound .or)
            else match spec.andOp with
              | some andOp =>
                if opValue = andOp then some (.byte mult io1 io2 iresult spec.bound .and) else none
              | none => none
          | none, some andOp =>
            if opValue = andOp then some (.byte mult io1 io2 iresult spec.bound .and) else none
          | none, none => none
      | _, _, _, _ => none

def denseCompileOtherCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) : Option (DenseCBiPred p) :=
  match denseCompileRangeCBiPredV facts keys bi mult with
  | some pred => some pred
  | none =>
    match denseCompileByteCBiPredV facts keys bi mult with
    | some pred => some pred
    | none => (denseCompileEs keys bi.payload).map (fun payload =>
        .fallback ⟨bi.busId, mult, payload⟩)

def denseCompilePairCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) (x width : DenseExpr p) :
    Option (DenseCBiPred p) :=
  match denseCompileE keys x, denseCompileE keys width with
  | some ix, some iwidth =>
    if facts.varRangeBus bi.busId then
      match width.constValue? with
      | some widthValue =>
        if widthValue.val ≤ 17 then some (.varRangeConst mult ix (2 ^ widthValue.val))
        else some (.varRange mult ix iwidth)
      | none => some (.varRange mult ix iwidth)
    else
      match facts.tupleRangeBus bi.busId with
      | some (boundX, boundY) => some (.tupleRange mult ix iwidth boundX boundY)
      | none => denseCompileOtherCBiPredV facts keys bi mult
  | _, _ => denseCompileOtherCBiPredV facts keys bi mult

def denseCompilePayloadCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs)
    (keys : List VarId) (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) :
    List (DenseExpr p) → Option (DenseCBiPred p)
  | [x, width] => denseCompilePairCBiPredV facts keys bi mult x width
  | _ => denseCompileOtherCBiPredV facts keys bi mult

def denseCompileCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseCBiPred p) :=
  if facts.neverViolates bi.busId then some .always
  else
    match denseCompileE keys bi.multiplicity with
    | none => none
    | some mult => denseCompilePayloadCBiPredV facts keys bi mult bi.payload

def denseCompileCBiPredsV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId) :
    List (BusInteraction (DenseExpr p)) → Option (List (DenseCBiPred p))
  | [] => some []
  | bi :: rest =>
    match denseCompileCBiPredV facts keys bi, denseCompileCBiPredsV facts keys rest with
    | some pred, some preds => some (pred :: preds)
    | _, _ => none

def denseCBiPredEvalV (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (bs : BusSemantics p) (pt : List (ZMod p)) : DenseCBiPred p → Bool
  | .always => true
  | .varRange mult x width =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else
      let xValue := denseIExprEvalWithV ops pt x
      let widthValue := denseIExprEvalWithV ops pt width
      decide (widthValue.val ≤ 17 ∧ xValue.val < 2 ^ widthValue.val)
  | .varRangeConst mult x bound =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else decide ((denseIExprEvalWithV ops pt x).val < bound)
  | .tupleRange mult x y boundX boundY =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else decide ((denseIExprEvalWithV ops pt x).val < boundX ∧
      (denseIExprEvalWithV ops pt y).val < boundY)
  | .fixedRange mult value bound =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else decide ((denseIExprEvalWithV ops pt value).val < bound)
  | .byte mult o1 o2 result bound kind =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else
      let a := denseIExprEvalWithV ops pt o1
      let b := denseIExprEvalWithV ops pt o2
      let r := denseIExprEvalWithV ops pt result
      decide (a.val < bound ∧ b.val < bound) && denseBytePredRelationV isZero kind a b r
  | .fallback cbi =>
    let multValue := denseIExprEvalWithV ops pt cbi.mult
    if isZero multValue then true
    else
      !bs.violatesConstraint
        { busId := cbi.busId,
          multiplicity := multValue,
          payload := cbi.payload.map (fun ie => denseIExprEvalWithV ops pt ie) }

/-- `survivesAllCW`, over a value-only point: compiled items' zero test plus interactions'
    obligation check. -/
def denseSurvivesAllCWV (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    (bs : BusSemantics p) (ces : List (IExpr p)) (cbis : List (DenseCBiPred p))
    (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWithV ops pt ie)) &&
    cbis.all (denseCBiPredEvalV ops isZero bs pt)

/-! ### The uncompiled fallback

Reached only if compilation fails — never for the covered items this pass compiles, so dead code
kept for totality. -/

/-- Value-only environment lookup against an explicit key list (fallback only; see above). -/
def denseEnvOfKeysV (keys : List VarId) (pt : List (ZMod p)) (y : VarId) : ZMod p :=
  match keys, pt with
  | [], _ => 0
  | _, [] => 0
  | x :: ks, v :: vs => if y == x then v else denseEnvOfKeysV ks vs y

/-- One source interaction's obligation over a value-only point. -/
def denseBiObligationV (bs : BusSemantics p) (bi : BusInteraction (DenseExpr p))
    (keys : List VarId) (pt : List (ZMod p)) : Bool :=
  let mult := bi.multiplicity.eval (denseEnvOfKeysV keys pt)
  if decide (mult = 0) then true
  else
    !bs.violatesConstraint
      { busId := bi.busId,
        multiplicity := mult,
        payload := bi.payload.map (fun e => e.eval (denseEnvOfKeysV keys pt)) }

/-- Fallback survivor predicate (see the fallback note above). -/
def denseSurvivesAllMV (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (pt : List (ZMod p)) : Bool :=
  es.all (fun e => decide (e.eval (denseEnvOfKeysV keys pt) = 0)) &&
    bis.all (fun bi => denseBiObligationV bs bi keys pt)

/-- A per-target survivor predicate, boxed in a one-field structure so its setup (ring instances,
    compilation, `isZero` closure) runs once per target rather than being eta-expanded into the
    per-point call path. -/
structure DenseSurvV (p : ℕ) where
  /-- The per-point survivor test (see `DenseSurvV`). -/
  run : List (ZMod p) → Bool

/-- The per-point survivor predicate for a target over value-only points: compiles the covered
    items against `keys` once, hoisting ring ops and the zero test, with the uncompiled fallback if
    compilation fails. Boxed in `DenseSurvV` (see there). -/
def denseCompiledSurvV (bs : BusSemantics p) (facts : BusFacts p bs) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) :
    DenseSurvV p :=
  match denseCompileEs keys es, denseCompileCBiPredsV facts keys bis with
  | some ces, some cbis =>
    let ops : DenseZModOps p := denseZModOps
    let dec : DecidableEq (ZMod p) := inferInstance
    let isZero : ZMod p → Bool := fun v => @decide (v = ops.zero) (dec v ops.zero)
    ⟨fun pt => denseSurvivesAllCWV ops isZero bs ces cbis pt⟩
  | _, _ => ⟨denseSurvivesAllMV bs es bis keys⟩

/-! ## Value-only lazy box enumeration -/

/-- Stream the Cartesian product of the domains into `f` as value-only points (in `keys` order). -/
def denseBoxFoldV {β : Type} (ops : DenseZModOps p) (f : β → List (ZMod p) → β)
    (stop : β → Bool) :
    List (FiniteDomain p) → β → β
  | [], acc => if stop acc then acc else f acc []
  | d :: rest, acc =>
    denseBoxFoldV ops (fun acc' a =>
      d.foldElts ops.zero (fun v => ops.add v ops.one)
        (fun acc'' v => f acc'' (v :: a)) stop acc') stop rest acc

/-- `(assignments doms).all pred`, value-only (used by `denseConstraintRedundantV`). -/
def denseAllBoxV (pred : List (ZMod p) → Bool) (doms : List (FiniteDomain p)) : Bool :=
  let ops : DenseZModOps p := denseZModOps
  denseBoxFoldV ops (fun acc pt => acc && pred pt) (fun acc => !acc) doms true

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
  let ops : DenseZModOps p := denseZModOps
  denseBoxFoldV ops (denseScanStepV surv) denseScanStopV doms none

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

def denseDomainBelowV (d : FiniteDomain p) (bound : Nat) : Bool :=
  match d with
  | .explicit vs => vs.all (fun v => decide (v.val < bound))
  | .range size => decide (size ≤ bound)

def denseExprDomainBelowV (T : DenseDomainTable p) (e : DenseExpr p) (bound : Nat) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < bound)
  | none =>
    match e with
    | .var i => match T.map[i]? with | some d => denseDomainBelowV d bound | none => false
    | _ => false

def denseRangeCheckDomainRedundantV {bs : BusSemantics p} (facts : BusFacts p bs)
    (T : DenseDomainTable p)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match bi.multiplicity.constValue? with
  | some mult =>
    if mult = 0 then true
    else if mult = 1 then
      match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some e => denseExprDomainBelowV T e bound
        | none => false
      | none => false
    else false
  | none => false

def denseConstBiV? (bi : BusInteraction (DenseExpr p)) : Option (BusInteraction (ZMod p)) := do
  let mult ← bi.multiplicity.constValue?
  let payload ← bi.payload.mapM DenseExpr.constValue?
  pure { busId := bi.busId, multiplicity := mult, payload }

def denseBytePairDomainRedundantV {bs : BusSemantics p} (facts : BusFacts p bs)
    (T : DenseDomainTable p) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match facts.byteXorSpec bi.busId with
  | none => false
  | some spec =>
    match spec.decode bi.payload with
    | none => false
    | some (op, o1, o2, result) =>
      match op.constValue?, result.constValue? with
      | some opValue, some resultValue =>
        opValue = spec.pairOp && resultValue = 0 &&
          denseExprDomainBelowV T o1 spec.bound && denseExprDomainBelowV T o2 spec.bound
      | _, _ => false

def denseBiDomainRedundantV (bs : BusSemantics p) (facts : BusFacts p bs) (T : DenseDomainTable p)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseConstBiV? bi with
  | some value => value.multiplicity = 0 || !bs.violatesConstraint value
  | none =>
    if facts.neverViolates bi.busId then true
    else
      match bi.payload with
      | [x, b] =>
        if facts.varRangeBus bi.busId then
          match b.constValue? with
          | some width =>
            if width.val ≤ 17 then denseExprDomainBelowV T x (2 ^ width.val) else false
          | none => false
        else
          match facts.tupleRangeBus bi.busId with
          | some (boundX, boundB) =>
            denseExprDomainBelowV T x boundX && denseExprDomainBelowV T b boundB
          | none => denseRangeCheckDomainRedundantV facts T bi ||
              denseBytePairDomainRedundantV facts T bi
      | _ => denseRangeCheckDomainRedundantV facts T bi ||
          denseBytePairDomainRedundantV facts T bi

def denseDomainConstantValueV? (d : FiniteDomain p) : Option (ZMod p) :=
  match d with
  | .explicit [] => none
  | .explicit (v :: vs) => if vs.all (fun w => decide (w = v)) then some v else none
  | .range size => if size = 1 then some 0 else none

def denseConstantDomainsV (fdoms : List (VarId × FiniteDomain p)) : List (VarId × ZMod p) :=
  fdoms.filterMap fun xd => (denseDomainConstantValueV? xd.2).map (fun c => (xd.1, c))

/-! ## `forcedOver`, value-only -/

structure DenseConstraintGatherV (p : ℕ) where
  fullCount : Nat
  active : List (DenseExpr p)

def denseGatherConstraintAtV (arr : Array (DenseConstraintPlan p)) (xs : List VarId)
    (acc : DenseConstraintGatherV p) (i : Nat) : DenseConstraintGatherV p :=
  if h : i < arr.size then
    let plan := arr[i]
    if denseVarsInListF xs plan.vars then
      { fullCount := acc.fullCount + 1,
        active := if plan.active then plan.expr :: acc.active else acc.active }
    else acc
  else acc

def denseGatherConstraintArrayV (arr : Array (DenseConstraintPlan p)) (xs : List VarId)
    (positions : Array Nat) (acc : DenseConstraintGatherV p) : DenseConstraintGatherV p :=
  positions.foldl (denseGatherConstraintAtV arr xs) acc

def denseGatherConstraintsV (fidx : DenseForcedIdx p) (xs : List VarId) :
    DenseConstraintGatherV p :=
  let acc := xs.foldl (fun acc v =>
    denseGatherConstraintArrayV fidx.arrCs xs (fidx.csIdx.buckets.getD v #[]) acc)
    ⟨fidx.csIdx.inactiveVarlessCount, []⟩
  denseGatherConstraintArrayV fidx.arrCs xs fidx.csIdx.activeVarless acc

structure DenseBusGatherV (p : ℕ) where
  count : Nat
  informative : Bool
  allDomainRedundant : Bool
  interactions : List (BusInteraction (DenseExpr p))

def denseGatherBusAtV (arr : Array (DenseBusPlan p)) (xs : List VarId)
    (acc : DenseBusGatherV p) (i : Nat) : DenseBusGatherV p :=
  if h : i < arr.size then
    let plan := arr[i]
    if plan.usable && denseVarsInListF xs plan.vars then
      { count := acc.count + 1,
        informative := acc.informative || plan.informative,
        allDomainRedundant := acc.allDomainRedundant && plan.domainRedundant,
        interactions := plan.interaction :: acc.interactions }
    else acc
  else acc

def denseGatherBusArrayV (arr : Array (DenseBusPlan p)) (xs : List VarId)
    (positions : Array Nat) (acc : DenseBusGatherV p) : DenseBusGatherV p :=
  positions.foldl (denseGatherBusAtV arr xs) acc

def denseGatherBusesV (fidx : DenseForcedIdx p) (xs : List VarId) : DenseBusGatherV p :=
  let acc := xs.foldl (fun acc v =>
    denseGatherBusArrayV fidx.arrBis xs (fidx.bisIdx.buckets.getD v #[]) acc)
    ⟨0, false, true, []⟩
  denseGatherBusArrayV fidx.arrBis xs fidx.bisIdx.varless acc

/-- All checked forced constants over the variable set `xs`. `keys` drives the compiler and the
    final zip; the unkeyed `doms` drives the value-only scan. -/
def denseForcedOverV (bs : BusSemantics p) (_facts : BusFacts p bs) (T : DenseDomainTable p)
    (fidx : DenseForcedIdx p) (xs : List VarId) : List (VarId × ZMod p) :=
  match T.doms xs with
  | none => []
  | some fdoms =>
    let boxSize := (fdoms.map (fun yd => yd.2.size)).prod
    if boxSize ≤ maxEnumSize then
      let cs := denseGatherConstraintsV fidx xs
      let bis := denseGatherBusesV fidx xs
      let informative := cs.fullCount != 0 || bis.informative
      if informative && boxSize * (cs.fullCount + bis.count) ≤ maxEnumWork then
        let keys := fdoms.map Prod.fst
        let doms := fdoms.map Prod.snd
        if cs.active.isEmpty && bis.allDomainRedundant &&
            doms.all (fun d => d.size != 0) then
          denseConstantDomainsV fdoms
        else
          let survC := denseCompiledSurvV bs _facts cs.active bis.interactions keys
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

def denseConstraintPlansV (T : DenseDomainTable p) (cs : List (DenseExpr p)) :
    List (DenseConstraintPlan p) :=
  cs.map fun c =>
    { expr := c,
      vars := HashedDedup.hashedDedup (hash ·) c.vars,
      active := !denseConstraintRedundantV T c }

def denseBusPlansV (bs : BusSemantics p) (facts : BusFacts p bs) (T : DenseDomainTable p)
    (bis : List (BusInteraction (DenseExpr p))) : List (DenseBusPlan p) :=
  bis.map fun bi =>
    let usable := !bs.isStateful bi.busId
    { interaction := bi,
      vars := HashedDedup.hashedDedup (hash ·) (denseBIVars bi),
      usable,
      informative := usable && denseBiInformative bs facts bi,
      domainRedundant := usable && denseBiDomainRedundantV bs facts T bi }

def densePlanTargetsV (cs : List (DenseConstraintPlan p)) (bis : List (DenseBusPlan p)) :
    List (List VarId) :=
  cs.map (fun c => c.vars) ++ bis.map (fun bi => bi.vars)

def denseFreezeBuckets (buckets : Std.HashMap VarId (List Nat)) :
    Std.HashMap VarId (Array Nat) :=
  buckets.fold (fun out v positions => out.insert v positions.toArray) ∅

def denseFreezeCovIndex (idx : DenseCovIndex) : DenseArrayCovIndex :=
  { buckets := denseFreezeBuckets idx.buckets,
    varless := idx.varless.toArray }

def denseConstraintCovIndexV (cs : List (DenseConstraintPlan p)) : DenseConstraintCovIndex :=
  let arr := cs.toArray
  let idx := denseAnchorCovBuild (fun c => c.vars) cs
  let summary := idx.varless.foldl (init := (0, #[])) fun acc i =>
    if h : i < arr.size then
      if arr[i].active then (acc.1, acc.2.push i) else (acc.1 + 1, acc.2)
    else acc
  { buckets := denseFreezeBuckets idx.buckets,
    inactiveVarlessCount := summary.1,
    activeVarless := summary.2 }

def denseForcedIdxV (cs : List (DenseConstraintPlan p)) (bis : List (DenseBusPlan p)) :
    DenseForcedIdx p :=
  { csIdx := denseConstraintCovIndexV cs,
    arrCs := cs.toArray,
    bisIdx := denseFreezeCovIndex (denseAnchorCovBuild (fun bi => bi.vars) bis),
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
  let busPlans := denseBusPlansV bs facts T d.busInteractions
  let targets := densePlanTargetsV csPlans busPlans
  let fidx := denseForcedIdxV csPlans busPlans
  -- Fan out only at keccak/SHA scale; below it the sequential fold avoids spawn overhead.
  denseCollectForcedV bs facts T fidx (8192 ≤ d.algebraicConstraints.length) targets ∅
    DenseSolved.empty

/-- The value-only dense domain-batch transform. -/
def denseDomainBatchTransformV (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then applyσ (denseDomainBatchσV bs facts d) d else d

end ApcOptimizer.Dense
