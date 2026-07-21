import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch

set_option autoImplicit false

/-! # Dense `domainBatch`, rebuilt with value-only box points (Task 3 — perf fix)

A committed keyed-point dense port (since removed) was byte-identical to the spec pass but
**+35% slower** on `apc_037`, entirely inside its box-scan hot loop. The root cause: that port
carried a full `List (VarId × ZMod p)` at every enumerated
box point, even though **nothing on the enumeration path ever reads a key from a point** — the
compiled predicates (`IExpr`/`CBi`, `lookupIx`) are already positional, and the box is always built
and scanned in one fixed key order (`keys := fdoms.map Prod.fst`). Carrying `VarId` in the hot
per-point data was pure overhead: a wasted allocation slot per entry, and (worse) the scan's candidate
tracking (`scanStep`'s `cands.filter (fun xc => decide (envOfFast pt xc.1 = xc.2))`) paid a **linear
key scan per remaining candidate, per point** to reproject values by key, an `O(|cands| · |keys|)` cost
per point that a purely positional design does not need.

This file rebuilds exactly the hot slice of that port — box enumeration, the compiled survivor
predicate, and the scan — with **value-only points** (`List (ZMod p)`, positionally aligned with a
`keys : List VarId` computed once per target, outside the per-point loop):

* `denseBoxFoldV` streams the Cartesian product as `List (ZMod p)` (no key travels with a point).
* `denseCompiledSurvV` / `denseIExprEvalWithV` / `denseCBiEvalWithV` evaluate the *same* compiled
  `IExpr`/`CBi` trees (variable-free; reused unchanged from the spec/old port) against a value-only
  point via a purely positional `denseLookupIxV` — identical control flow and hoisting to
  `compiledSurv`/`survivesAllCW`, only the point/lookup type changes.
* `denseScanBoxV` mirrors `scanBox`/`scanStep`/`scanWith` **exactly** in control flow (search for the
  first survivor, then track and intersect candidates, abort the moment nothing remains), but the
  shrinking `List (VarId × ZMod p)` candidate set becomes a **fixed-length candidate mask**
  `List (Option (ZMod p))`, positionally aligned with `keys`: a candidate is "ruled out" by turning its
  slot to `none` instead of removing it from a list keyed by identity. This is the representational
  change the value-only design *forces* (a per-point predicate can no longer look a candidate up by its
  `VarId`, since points carry none), and it is what removes the `O(|cands| · |keys|)` reprojection: the
  per-point update is one positional `List.zipWith`, and the abort check is `cands.all Option.isNone`.
  The set of forced values, their order, and the exact point at which the scan aborts are unchanged —
  only the container shape differs. `denseForcedOverV` zips the final mask with `keys` once, at the
  very end, to recover `List (VarId × ZMod p)` (what `collectForced`/`Solved.insertAll` consume).
* `denseConstraintRedundantV` gets the same treatment for the (smaller, per-constraint) redundancy
  box-check `allBox`/`constraintRedundant`.

Everything **not** on the per-point path is reused unchanged from `Dense/DomainBatch.lean` (old,
untouched) and `Dense/Gauss.lean`, since it was already measured at parity and is out of this task's
scope (per `VarId.md`/`VarIdAddendum.md`, `varSetKey`'s exact-set repair is an isolated follow-up, not
bundled here):

* the domain-table layer (`DenseDomainTable`, `.insertEntry`, `.doms`, `denseAddConstraintDoms`,
  `denseAddBusDoms`, `denseRootsIn`, `denseInteractionDomainF`) — built once per pass invocation, no
  per-point cost;
* the inverted covered-item index (`DenseCovIndex`, `denseCovBuild`, `denseCoveredIdxUnord`,
  `DenseForcedIdx`) — built once, O(local) per target;
* the covered-set / informativeness predicates (`DenseExpr.varsInF`, `denseBIVarsInF`,
  `denseBiInformative`) — cheap, no per-point work;
* the `IExpr`/`CBi` compiler (`denseVarIx`, `denseCompileE(s)`, `denseCompileBi(s)`) — compiled once
  per target, not per point, and produces the identical compiled term regardless of point
  representation;
* the target-dedup key (`denseVarSetKey`) and the final substitution layer (`DenseSolved`,
  `.insertAll`, `applyσ`).

No pipeline wiring and no correctness theorems here (the prover's job, per the Task 3 native-proof
architecture): every definition below is runtime-only, so there is nothing to discharge and no
proof obligations are left open. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Value-only positional lookup and compiled evaluation

`IExpr`/`CBi` are already variable-free (their leaves are positions, `.ix i`), so the *same* compiled
terms `denseCompileE`/`denseCompileBi` produce (reused unchanged, see the module header) are evaluated
here against a value-only point through a purely positional lookup — no `VarId` is read at all. -/

/-- Positional lookup in a value-only assignment (mirrors `lookupIx`/`denseLookupIx`, but the point
    carries no keys whatsoever — a box point is always evaluated in the same fixed `keys` order it was
    built in, so position alone determines the value). -/
def denseLookupIxV : List (ZMod p) → Nat → ZMod p
  | [], _ => 0
  | v :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIxV rest i

/-- `IExpr.evalWith`, over a value-only point (mirrors `IExpr.evalWith`/`denseIExprEvalWith`; same
    hoisted `add`/`mul`, same recursion). -/
def denseIExprEvalWithV (add mul : ZMod p → ZMod p → ZMod p) (pt : List (ZMod p)) :
    IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIxV pt i
  | .add a b => add (denseIExprEvalWithV add mul pt a) (denseIExprEvalWithV add mul pt b)
  | .mul a b => mul (denseIExprEvalWithV add mul pt a) (denseIExprEvalWithV add mul pt b)

/-- `CBi.evalWith`, over a value-only point (mirrors `CBi.evalWith`/`denseCBiEvalWith`). -/
def denseCBiEvalWithV (add mul : ZMod p → ZMod p → ZMod p) (cbi : CBi p) (pt : List (ZMod p)) :
    BusInteraction (ZMod p) :=
  { busId := cbi.busId,
    multiplicity := denseIExprEvalWithV add mul pt cbi.mult,
    payload := cbi.payload.map (fun ie => denseIExprEvalWithV add mul pt ie) }

/-- `survivesAllCW`, over a value-only point (mirrors `survivesAllCW`/`denseSurvivesAllCW`): the
    compiled items' zero test plus the compiled interactions' obligation check, both against the
    hoisted `add`/`mul`/`isZero`. -/
def denseSurvivesAllCWV (add mul : ZMod p → ZMod p → ZMod p) (isZero : ZMod p → Bool)
    (bs : BusSemantics p) (ces : List (IExpr p)) (cbis : List (CBi p))
    (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWithV add mul pt ie)) &&
    cbis.all (fun cbi =>
      let v := denseCBiEvalWithV add mul cbi pt
      isZero v.multiplicity || !bs.violatesConstraint v)

/-! ### The uncompiled fallback

Reached only if compilation fails — never, for the covered items this pass ever compiles (every
variable leaf of a covered item lies in the target's own `keys`), so this is dead code kept for
totality, exactly as `compiledSurv` keeps an uncompiled fallback arm. Since a
value-only point carries no keys to compare against, the fallback lookup walks the (compile-time)
`keys` list and the point in lockstep instead of scanning a keyed point — the natural value-only
analogue of `envOfFast`'s role here, forced by the representation, not a behavior change (the fallback
is never exercised on the scan's actual hot path). -/

/-- Value-only environment lookup against an explicit key list (fallback only; see above). -/
def denseEnvOfKeysV (keys : List VarId) (pt : List (ZMod p)) (y : VarId) : ZMod p :=
  match keys, pt with
  | [], _ => 0
  | _, [] => 0
  | x :: ks, v :: vs => if y == x then v else denseEnvOfKeysV ks vs y

/-- Fallback survivor predicate over dense items and a value-only point, given its key list (mirrors
    `survivesAllM`; see the fallback note above). -/
def denseSurvivesAllMV (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (pt : List (ZMod p)) : Bool :=
  es.all (fun e => decide (e.eval (denseEnvOfKeysV keys pt) = 0)) &&
    bis.all (fun bi =>
      let v : BusInteraction (ZMod p) :=
        { busId := bi.busId,
          multiplicity := bi.multiplicity.eval (denseEnvOfKeysV keys pt),
          payload := bi.payload.map (fun e => e.eval (denseEnvOfKeysV keys pt)) }
      decide (v.multiplicity = 0) || !bs.violatesConstraint v)

/-- A per-target survivor predicate, boxed in a one-field structure. This mirrors the spec's
    `compiledSurv`, whose return type is a `Subtype` (a non-`Pi` type): boxing the closure caps the
    compiled arity of `denseCompiledSurvV` at its explicit arguments, so the ring-instance chain, the
    `denseCompileEs`/`denseCompileBis` compilation, and the `isZero`-closure allocation run **once
    per target** (when the box is built) rather than being eta-expanded into the per-point call path.
    Returning a bare `List (ZMod p) → Bool` instead would let the compiler pull the point argument
    into the arity and re-run that whole setup on every enumerated box point. -/
structure DenseSurvV (p : ℕ) where
  /-- The per-point survivor test (see `DenseSurvV`). -/
  run : List (ZMod p) → Bool

/-- The per-point survivor predicate for a target, over value-only points (mirrors
    `compiledSurv`, boxed in `DenseSurvV` — no carried property; the prover states
    its correspondence). Compiles the covered items against `keys` once, hoists the ring operations and
    the zero test out of the per-point evaluation exactly as the spec does, and falls back to the
    uncompiled predicate only if compilation fails (dead for covered items). The `DenseSurvV` box (a
    non-`Pi` return type, like the spec's `Subtype`) is what keeps this setup off the per-point path;
    see `DenseSurvV`. -/
def denseCompiledSurvV (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) :
    DenseSurvV p :=
  match denseCompileEs keys es, denseCompileBis keys bis with
  | some ces, some cbis =>
    let addI : Add (ZMod p) := inferInstance
    let mulI : Mul (ZMod p) := inferInstance
    let dec : DecidableEq (ZMod p) := inferInstance
    let add := addI.add
    let mul := mulI.mul
    let isZero : ZMod p → Bool := fun v => @decide (v = 0) (dec v 0)
    ⟨fun pt => denseSurvivesAllCWV add mul isZero bs ces cbis pt⟩
  | _, _ => ⟨denseSurvivesAllMV bs es bis keys⟩

/-! ## Value-only lazy box enumeration

`FiniteDomain`/`FiniteDomain.foldElts`/`foldlStop`/`rangeFoldFrom` are variable-free already (reused
unchanged from the spec, no port needed at all); only the box *point* built while streaming them
changes shape, from `List (VarId × FiniteDomain p)` producing `List (VarId × ZMod p)` points, to
`List (FiniteDomain p)` (unkeyed — the domains in `keys` order) producing `List (ZMod p)` points. -/

/-- Stream the Cartesian product of the domains into `f`, value-only (mirrors `boxFold`; the point
    never carries a key, only its position in the (compile-time) `keys` order determines what it
    means). -/
def denseBoxFoldV {β : Type} (f : β → List (ZMod p) → β) (stop : β → Bool) :
    List (FiniteDomain p) → β → β
  | [], acc => if stop acc then acc else f acc []
  | d :: rest, acc =>
    denseBoxFoldV (fun acc' a => d.foldElts (fun acc'' v => f acc'' (v :: a)) stop acc') stop rest acc

/-- `(assignments (matList doms)).all pred`, value-only (mirrors `allBox`), for
    `denseConstraintRedundantV`'s per-constraint redundancy box-check. -/
def denseAllBoxV (pred : List (ZMod p) → Bool) (doms : List (FiniteDomain p)) : Bool :=
  denseBoxFoldV (fun acc pt => acc && pred pt) (fun acc => !acc) doms true

/-! ### The value-only box scan

The candidate set `scanWith`/`scanStep` track is represented as a **fixed-length mask**
`List (Option (ZMod p))`, positionally aligned with the target's `keys`: `some c` while the key at that
position is still forced to `c` by every survivor seen so far, `none` once some survivor disagreed.
Ruling a candidate out is turning its slot to `none` (a positional `List.zipWith` against the current
point) rather than removing it from a list keyed by identity (which would need a per-candidate,
per-point `VarId` comparison — exactly the reprojection cost this rebuild removes). The abort condition
`scanStop`'s `cands.isEmpty` becomes `cands.all Option.isNone`: the same moment (every candidate ruled
out), checked over the same fixed-length mask. -/

/-- The scan's tracked candidates: a fixed-length mask, positionally aligned with the target's
    `keys`. -/
abbrev DenseCandsV (p : ℕ) := List (Option (ZMod p))

/-- One dense scan step, value-only (mirrors `scanStep`): `none` while hunting the
    first survivor (initializes the mask directly from that survivor's point — no reprojection,
    since a value-only point already *is* positionally what the mask needs); `some cands` intersects
    the mask against the current point when it survives, unchanged otherwise. -/
def denseScanStepV (surv : List (ZMod p) → Bool) :
    Option (DenseCandsV p) → List (ZMod p) → Option (DenseCandsV p)
  | none, pt => if surv pt = true then some (pt.map some) else none
  | some cands, pt =>
    if surv pt = true then
      some (cands.zipWith
        (fun c v => match c with | some cv => if cv = v then some cv else none | none => none) pt)
    else some cands

/-- The dense scan aborts once every tracked candidate has been ruled out (mirrors `scanStop`). -/
def denseScanStopV : Option (DenseCandsV p) → Bool
  | none => false
  | some cands => cands.all Option.isNone

/-- The value-only box scan, streamed lazily over the symbolic domains (mirrors `scanBox`). No
    `keys` are threaded through the fold itself — the candidate mask is built and
    intersected purely positionally; the caller (`denseForcedOverV`) zips the final mask with `keys`
    exactly once, after the scan finishes. -/
def denseScanBoxV (surv : List (ZMod p) → Bool) (doms : List (FiniteDomain p)) :
    Option (DenseCandsV p) :=
  denseBoxFoldV (denseScanStepV surv) denseScanStopV doms none

/-! ## Redundancy check, value-only (mirrors `constraintRedundant`/`denseConstraintRedundant`) -/

/-- Is this constraint redundant for enumeration — identically zero on the box of its own variables'
    domains? Value-only rebuild of `denseConstraintRedundant`: same table lookup, same compile step
    (`denseCompileE`, unchanged — compiling doesn't touch points), same hoisted evaluation, only the
    box-check itself (`denseAllBoxV`) is value-only. -/
def denseConstraintRedundantV (T : DenseDomainTable p) (c : DenseExpr p) : Bool :=
  match T.doms (HashedDedup.hashedDedup (hash ·) c.vars) with
  | none => false
  | some d =>
    (d.map (fun yd => yd.2.size)).prod ≤ maxEnumSize &&
      match denseCompileE (d.map Prod.fst) c with
      | some ic =>
        let addI : Add (ZMod p) := inferInstance
        let mulI : Mul (ZMod p) := inferInstance
        let dec : DecidableEq (ZMod p) := inferInstance
        let add := addI.add
        let mul := mulI.mul
        denseAllBoxV (fun a => @decide (denseIExprEvalWithV add mul a ic = 0) (dec _ 0))
          (d.map Prod.snd)
      | none =>
        denseAllBoxV (fun a => decide (c.eval (denseEnvOfKeysV (d.map Prod.fst) a) = 0))
          (d.map Prod.snd)

/-! ## `forcedOver`, value-only (mirrors `forcedOver`/`denseForcedOver`)

Same domain-table lookup, same covered-item gathering through the (unchanged, built-once)
`DenseForcedIdx`/`denseCoveredIdxUnord`, same informativeness/work-cap gates, same compiled survivor
predicate construction — only the scan itself, and the final extraction of forced pairs from its
result, are value-only. -/

/-- All checked forced constants over the variable set `xs` (mirrors `forcedOver`/`denseForcedOver`,
    plain data — no witnesses; the prover states the entailment correspondence). The `keys`/`doms`
    split happens once per target (not per point): `keys` is threaded to the compiler and to the final
    zip, `doms` (unkeyed) drives the value-only scan. -/
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
          -- no surviving point at all: everything is vacuously forced (the box has no solutions)
          keys.map (fun x => (x, (0 : ZMod p)))
        | some cands =>
          -- the mask is positionally aligned with `keys`; recover the forced `(x, c)` pairs by
          -- zipping once, at the very end (not per point)
          (keys.zip cands).filterMap (fun xc => xc.2.map (fun c => (xc.1, c)))
      else []
    else []

/-! ## `collectForced`, value-only (mirrors `collectForced`/`denseCollectForced`)

Unchanged target-dedup key (`denseVarSetKey`, reused — out of this task's scope, see the module
header) and unchanged solution-map data structure (`DenseSolved`/`.insertAll`, reused from
`Dense/Gauss.lean`); only the per-target forcing (`denseForcedOverV`) is new. Mirrors the spec's
#165 split into a target dedup (`dedupTargets`) followed by an order-preserving fold, so the
independent per-target enumerations can be spawned in parallel on large systems. -/

/-- The `seen`-deduplicated target list (value-only twin of the spec's `dedupTargets`, keyed by the
    same `denseVarSetKey reg` the previous interleaved recursion used), split out so the per-target
    enumerations can be spawned in parallel. Dedup behaviour is byte-for-byte the previous
    interleaved threading — the exact-set-key repair is a separate follow-up (see the module
    header). -/
def denseDedupTargetsV (reg : VarRegistry) :
    List (List VarId) → Std.HashSet String → List (List VarId)
  | [], _ => []
  | xs :: rest, seen =>
    let key := denseVarSetKey reg xs
    if seen.contains key then denseDedupTargetsV reg rest seen
    else xs :: denseDedupTargetsV reg rest (seen.insert key)

/-- Collect every checked forced constant, mirroring the spec's `collectForced`: dedup the targets
    once (`denseDedupTargetsV`), then combine each target's forced constants into the solution map
    in target order. The per-target enumerations (`denseForcedOverV`) are independent — each is
    evaluated against the same table/index — so on large systems each is spawned as a `Task` and the
    results are joined **in target order** (`tasks.foldl … (t.get)`): the fold receives exactly the
    insertions the sequential fold would perform, so the pass output is unchanged and only wall-clock
    differs. Small systems keep the plain sequential fold. `parallel` is decided by the caller from
    the system size, matching the spec pass's gate. -/
def denseCollectForcedV (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p) (parallel : Bool)
    (targets : List (List VarId)) (seen : Std.HashSet String) (dσ0 : DenseSolved p) : DenseSolved p :=
  let uniq := denseDedupTargetsV reg targets seen
  if parallel then
    let tasks := uniq.map (fun xs => Task.spawn fun _ => denseForcedOverV bs facts T fidx xs)
    tasks.foldl (init := dσ0) fun dσ t =>
      dσ.insertAll ((t.get).map (fun f => (f.1, DenseExpr.const f.2)))
  else
    uniq.foldl (init := dσ0) fun dσ xs =>
      dσ.insertAll ((denseForcedOverV bs facts T fidx xs).map (fun f => (f.1, DenseExpr.const f.2)))

/-! ## The pass transform, value-only (mirrors `domainBatchPass`/`denseDomainBatchF`)

Build the domain table once, collect every forced constant via the value-only enumeration, substitute
the whole solution map through the system in one traversal (`applyσ`, reused unchanged from
`Dense/DomainBatch.lean` — it does not touch points). Prime `p` only (the same `pw` gates both this
and the spec pass); identity otherwise. No `DensePassResult`/`DenseVerifiedPassW` wrapper and no
wiring here — the prover states the correctness proof and wires this transform in. -/

/-- The dense solution map (mirrors the spec pass's `σ` / `denseDomainBatchσ`), built with the
    value-only `denseCollectForcedV`. -/
def denseDomainBatchσV (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
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
  -- Fan out only at keccak/SHA scale (the same raw-count gate as the spec pass): below it the
  -- sequential fold is byte-for-byte the same computation without spawn overhead.
  denseCollectForcedV bs facts reg T fidx (8192 ≤ d.algebraicConstraints.length) targets ∅
    DenseSolved.empty

/-- The value-only dense domain-batch transform (mirrors `domainBatchPass`/`denseDomainBatchF`). -/
def denseDomainBatchTransformV (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then applyσ (denseDomainBatchσV reg bs facts d) d else d

end ApcOptimizer.Dense
