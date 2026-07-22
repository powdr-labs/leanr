import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold

set_option autoImplicit false

/-! # Witness re-encoding — dense expression operations

Dense `VarId` definitions for witness re-encoding: environment
extension, the fast hoisted evaluator, the booleanity constraint, the group substitution and bit
box, the degree-aware group rewrite (`indicatorExpr`/`interpOfV`/`candSelect`/`groupRewriteCand`/
`groupRewrite`), the re-encoded output, the group's survivor enumeration and the checked
re-encoding certificate, the fresh bits' derived-variable methods (`imgVal`/`matchCM`/`bitCM`), the
interpolation polynomial, and the `foldRewrite`-gate test `sharesVarIn`. This is **impl-only**:
no correctness theorem is stated here — nothing here states or proves anything beyond the runtime
computation.

## The build/step/loop/pass layer

This section adds the *proof-free construction* layer on top of the expression ops above:
`denseBuildReencode` (including its hopeless-target prefilter and its indexed-vs-direct
covered-set gathering — reusing `denseCoveredIdx` (`DomainFold.lean`) and
`denseCovBuild`/`denseBuildStep` (`DomainBatch.lean`)), `denseDegPreReject` (the degree pre-gate),
`denseReencodeStep`/`denseReencodeLoop` (the per-candidate step and the sequential driver, including
the registry-extending fresh-variable plumbing), and `denseReencodeF` (a plain transform matching
the `ofExtending` builder's shape — the prover wires it with `DenseVerifiedPassW.ofExtending
(denseReencodeF pw b) …`). The correctness proof and the `ofExtending` wiring live in
`ReencodeProof.lean`.

### Fresh bits: where they are minted, and the freshness prefilter mechanism

`denseBuildReencode` mints the fresh bit variables only on its single accepting path (box small
enough, not the single-var-only hopeless case, `2 ≤ survs.length`, `k < xs.length`):
`denseRegisterBits` constructs the `Variable` values `{ name := freshBase ++ "_" ++ toString j }`
for `j = 0, …, k-1`, in order, and registers each via `reg.register`, threading the registry through
only that branch; every rejecting branch returns the registry **unchanged**. `VarRegistry.register`
is append-only and idempotent on an already-registered `Variable` (returns the existing `VarId`), so
a `denseReencodeStep` invocation whose candidate is later rejected by
`denseDegPreReject`/`denseCheckReencode`/`withinDegreeB` still threads the registry *as extended by*
`denseBuildReencode` onward: this is harmless, since the orphaned bit `VarId`s never occur in any
expression and so cannot affect any downstream `VarId`-keyed decision.

The **freshness prefilter** in `denseReencodeStep` runs *before* `denseBuildReencode`, so no bit
exists yet to look up by `VarId`: it tests
`match reg.idOf? { name := freshBase ++ "_0" } with | some i => varSet.contains i | none => false`.
If the candidate name was never registered at all it cannot be a system member (everything a
`DenseConstraintSystem` mentions is registered, by the pipeline's own coverage invariant), so the
`none` case is a clean "no collision"; if it *was* registered, membership in the current `varSet`
decides it.

### `varSet` is a plain `Std.HashSet VarId`

`denseReencodeStep`/`denseReencodeLoop` carry **no proof at all** (this file is impl-only), so
`varSet` here is a plain `Std.HashSet VarId`: the `.contains` decision and the accept-time rebuild
(`Std.HashSet.ofList ro.occ`) track the current system's occurring variables. Any
membership-implies-coverage fact needed for a proof is for the prover to restate and discharge
against `DenseConstraintSystem.CoveredBy`, not re-derived here.

### Ordering of the candidate-group targets

`denseReencodeF`'s target list sorts each candidate group with a **resolve-based comparator**,
`compare (reg.resolve a) (reg.resolve b) != .gt`, rather than a `VarId.index`-native order. This
matters because the candidate order is directly the *iteration* order of `denseReencodeLoop`'s
greedy, order-sensitive accept/reject sequence: it accepts or rejects each candidate group in turn
and threads its state to the next, so the group order determines which groups end up accepted. The
comparator only runs once per fixpoint iteration on this pass's cold target-construction path (not
per box point), unlike the hot per-box-point paths in
`Dense/DomainFoldNative.lean`/`BoxRewrite.lean`. `dedupHash`'s dedup order is list-order-preserving
regardless of the key's hash, so it introduces no further reordering.

### `denseBuildPruned`: a local twin of `CoveredIndex.buildPruned`

No dense twin of `CoveredIndex.buildPruned` (`CoveredIndex.lean:59`) exists elsewhere yet, so
`denseBuildPruned` below is a local, `VarId`-keyed definition (reusing the already-dense
`denseBuildStep`/`DenseCovIndex` from `DomainBatch.lean`), used for the pass-level initial index and
the accept-time rebuilt index in `denseReencodeStep`.

## Import-graph note

This file imports the dense `DomainFold.lean` primitives (`denseFindDomainAlg`, `denseCoveredBy`,
`denseCoveredCsOf`, `denseGroupDoms`, `denseAssignments`, `DenseExpr.hasVar`) directly — no local
copies.

The group-survivor enumeration (`denseSurvZeroCW`/`denseGroupSurvivorsE` below) is defined directly
against the *keyed* compiled evaluator `denseCompileEs`/`denseIExprEvalWith` (`DomainBatch.lean`).
This is a different function from `denseGroupSurvivorsEV` (`DomainFold`-side machinery, a value-only
rebuild used for a `domainFold`-specific perf path) — do not conflate the two.

## Other reuse decisions

* `VarId` equality is already a direct `Nat` comparison, so there is no separate "fast" env-lookup
  twin needed: every lookup below routes through `denseEnvOfFast` (`DomainBatch.lean`). Likewise
  `DenseExpr.varsInF` (`DomainBatch.lean`) and `DenseExpr.mentions` (`SubstMap.lean`) are each the
  single dense name used below wherever a "fast"-vs-plain distinction would otherwise apply.
* `DenseExpr.evalWith`/`DenseExpr.evalFast` hoist the `Add`/`Mul (ZMod p)` instance derivation once
  per call rather than once per expression node — this fast-path structure is unrelated to the
  `Variable`→`VarId` representation and is preserved here verbatim.
* `indicatorExpr` is **not** the same function as `FxSubst.lean`'s `denseIndicatorProd`: the latter
  (`others : List VarId`, `pt : List (VarId × ZMod p)`) folds over a separate variable list and looks
  each one up in `pt` via `denseEnvOfFast` (a scan per element), while `indicatorExpr`/
  `denseIndicatorExpr` folds directly over the pattern list itself, reading each pair's own stored
  value with no lookup at all — a different (and cheaper) computation. Defined fresh below as
  `denseIndicatorExpr`, not reused.
* `dedupHash` is fully generic
  (`{α : Type} [BEq α] [Hashable α]`) and representation-independent; it is reused unqualified at
  `VarId`, as `DomainFoldRuntime.lean`'s `denseTargetsV` also does — no dense-specific version is
  defined here. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Environment extension by an association list -/

/-- Override `denv` on the keys of `pairs` (first match wins). -/
def denseEnvExt : List (VarId × ZMod p) → (VarId → ZMod p) → VarId → ZMod p
  | [], denv, y => denv y
  | (x, v) :: rest, denv, y => if y = x then v else denseEnvExt rest denv y

/-! ## Fast evaluation (hoisted ring operations)

`+`/`*` on `ZMod p` with a *runtime* `p` re-derive the whole `CommRing (ZMod p)` instance chain at
every expression node: `evalFast` extracts the two operations from the instances once per
evaluation call, so each node is a direct closure call. -/

/-- `DenseExpr.eval` with the ring operations passed in. -/
def DenseExpr.evalWith (add mul : ZMod p → ZMod p → ZMod p) (denv : VarId → ZMod p) :
    DenseExpr p → ZMod p
  | .const n => n
  | .var i => denv i
  | .add a b => add (a.evalWith add mul denv) (b.evalWith add mul denv)
  | .mul a b => mul (a.evalWith add mul denv) (b.evalWith add mul denv)

/-- `DenseExpr.eval`, deriving the field operations once per call instead of per node. -/
def DenseExpr.evalFast (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  let addI : Add (ZMod p) := inferInstance
  let mulI : Mul (ZMod p) := inferInstance
  e.evalWith addI.add mulI.mul denv

/-! ## Booleanity constraint for the fresh bits -/

/-- `b · (b − 1)`. -/
def denseBoolConstraint (b : VarId) : DenseExpr p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

/-! ## The group substitution and the fresh bits' domain box -/

/-- The group substitution: defined on the group only, backed by a hash map. Reuses
    `denseContainsFast` (`DomainBatch.lean`). -/
def denseGroupSubst (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    VarId → Option (DenseExpr p) :=
  fun y => if denseContainsFast xs y then hm[y]? else none

/-- The `{0,1}` domain box of the fresh bits. -/
def denseBitBox (bits : List VarId) : List (VarId × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-! ## Degree-aware group rewriting -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. **Not** the same computation
    as `FxSubst.lean`'s `denseIndicatorProd` (see the module header: different fold shape). -/
def denseIndicatorExpr (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

/-- The interpolation of a whole subexpression over the bit patterns, from its precomputed
    per-pattern values. -/
def denseInterpOfV (patts : List (List (VarId × ZMod p))) (vals : List (ZMod p)) : DenseExpr p :=
  match vals with
  | [] => .const 0
  | v₀ :: _ =>
    if vals.all (fun v => decide (v = v₀)) then .const v₀
    else (patts.zip vals).foldl (fun acc av =>
      .add acc (.mul (denseIndicatorExpr av.1) (.const av.2))) (.const 0)

/-- The interpolation acceptance check on precomputed pieces: take `cand` only if its variables lie
    in the bits and it agrees with the (precomputed) substitution values on every pattern, else fall
    back to the plain substitution `sub`. Reuses `DenseExpr.varsInF` and `denseEnvOfFast`. -/
def denseCandSelect (bits : List VarId) (patts : List (List (VarId × ZMod p)))
    (sub cand : DenseExpr p) (vals : List (ZMod p)) : DenseExpr p :=
  if cand.varsInF bits &&
      (patts.zip vals).all (fun av => decide (cand.evalFast (denseEnvOfFast av.1) = av.2))
  then cand
  else sub

/-- Interpolation candidate with the checked fallback to plain substitution. Reuses
    `DenseExpr.substF` (`SubstMap.lean`), `denseEnvOfFast`, and `DenseExpr.fold` (`ExprOps.lean`). -/
def denseGroupRewriteCand (bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  let sub := e.substF σfn
  let vals := patts.map (fun aβ => sub.evalFast (denseEnvOfFast aβ))
  denseCandSelect bits patts sub ((denseInterpOfV patts vals).fold) vals

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else. Reuses `denseContainsFast` and `DenseExpr.varsInF`. -/
def denseGroupRewrite (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var y =>
      if denseContainsFast xs y then denseGroupRewriteCand bits σfn patts (.var y) else .var y
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.add a b)
      else .add (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.mul a b)
      else .mul (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)

/-! ## The re-encoded system -/

/-- The re-encoded system: substitute the group everywhere, keep only uncovered constraints, add
    booleanity for the bits. Reuses the (locally re-derived) `denseCoveredBy` and `denseAssignments`
    above. No dense `BusInteraction.mapExpr` exists, so the bus-interaction rewrite is inlined
    field-by-field, matching the shape already established by `DomainFoldRuntime.lean`'s fold-out
    functions. The whole rewrite closure (`groupSubst`/`bitBox`/`assignments`) is recomputed for the
    constraints and again for the bus interactions (no extra `let`-hoist across the two). -/
def denseReencodeOut (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))))
        ++ bits.map denseBoolConstraint,
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity :=
        denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))
          bi.multiplicity,
      payload := bi.payload.map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))) }) }

/-! ## The group's surviving values

Defined directly against the *keyed* compiled evaluator `denseCompileEs`/`denseIExprEvalWith`
(`DomainBatch.lean`, safely importable — see the module header: no `DomainFold.lean` dependency
needed here at all). -/

/-- All covered constraints zero at a point, with the ring ops hoisted out of the per-point
    evaluation. -/
def denseSurvZeroCW (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (a : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWith add mul a ie = 0))

/-- The surviving group values from a **precomputed** covered set: enumerated over the group's
    domains, filtered by the covered constraints, compiled once per target to positional `IExpr`s. -/
def denseGroupSurvivorsE (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    List (List (VarId × ZMod p)) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces =>
    (denseAssignments doms).filter
      (denseSurvZeroCW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul ces)
  | none =>
    (denseAssignments doms).filter
      (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0)))

/-! ## The checked re-encoding certificate -/

/-- All checked side conditions for one re-encoding step. Reuses the (locally re-derived)
    `denseGroupDoms`/`denseCoveredCsOf` above, `denseAssignments`/`denseBitBox`,
    `denseGroupSurvivorsE` above, `denseEnvOfFast`, and `DenseExpr.mentions`. The conjunct order
    keeps the deliberately-last freshness conjunct (the only `O(bits × system)` one,
    short-circuited to run only for the few already-cheaply-accepted groups). -/
def denseCheckReencode (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  match denseGroupDoms (denseCoveredCsOf d xs) xs with
  | none => false
  | some doms =>
    let es := denseCoveredCsOf d xs
    let survs := denseGroupSurvivorsE es doms
    let patts := denseAssignments (denseBitBox bits)
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ survs.length) &&
    decide (bits.length < xs.length) &&
    decide (bits.Nodup) &&
    -- the substituted group variables only mention bits
    xs.all (fun x =>
      ((DenseExpr.var x).substF (denseGroupSubst xs hm)).vars.all (fun v => bits.contains v)) &&
    -- completeness: every surviving group value is hit by some bit pattern
    survs.all (fun s => patts.any (fun aβ =>
      xs.all (fun x =>
        decide (((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)
          = denseEnvOfFast s x)))) &&
    -- soundness: every bit pattern's image satisfies the covered constraints
    patts.all (fun aβ => es.all (fun c =>
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0))) &&
    -- freshness: no bit occurs anywhere in the system. Deliberately the **last** conjunct.
    bits.all (fun b =>
      d.algebraicConstraints.all (fun c => !c.mentions b) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b)))

/-! ## Derived-variable methods for the fresh bits

Each bit is recovered from the group by a decision tree over the bit patterns: at the first
pattern whose interpolation image equals the group's values, output that pattern's bit. -/

/-- The interpolation image of group variable `x` at pattern `aβ` (a field constant). -/
def denseImgVal (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (aβ : List (VarId × ZMod p)) (x : VarId) : ZMod p :=
  ((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`, as nested `ifEqZero`. -/
def denseMatchCM (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) : DenseComputationMethod p :=
  match xs with
  | [] => thenM
  | x :: rest =>
      .ifEqZero (.add (.var x) (.const (-(imgFn x)))) (denseMatchCM rest imgFn thenM elseM) elseM

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit. -/
def denseBitCM (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) : DenseComputationMethod p :=
  match patts with
  | [] => .const 0
  | aβ :: rest =>
      denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b)) (denseBitCM rest xs hm b)

/-! ## Building the interpolation (proof-free) -/

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs — consumed by
    `denseBuildReencode` below, which supplies `pz` from `denseGroupSurvivorsE`'s keyed output. -/
def denseInterpPoly (pz : List (List (VarId × ZMod p) × List (VarId × ZMod p))) (x : VarId) :
    DenseExpr p :=
  pz.foldl (fun acc az => .add acc (.mul (denseIndicatorExpr az.1) (.const (denseEnvOfFast az.2 x))))
    (.const 0)

/-! ## Sharing a variable with a group (the `foldRewrite`-gate test) -/

/-- Does the expression share a variable with `xs`? (No allocation.) Reuses `denseContainsFast`.
    The same computation as `DenseExpr.anyVarIn` (`DomainFold.lean`), defined again here as its own
    local copy to avoid a cross-file dependency. -/
def DenseExpr.sharesVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.sharesVarIn xs || b.sharesVarIn xs
  | .mul a b => a.sharesVarIn xs || b.sharesVarIn xs

/-! ## The build/step/loop/pass layer (see the module header) -/

/-! ### A local dense twin of `CoveredIndex.buildPruned` -/

/-- `VarId`-keyed twin of `CoveredIndex.buildPruned` (`CoveredIndex.lean:59`): build the inverted
    index, skipping items with more than `maxVars` distinct variables. Local to this file (see the
    module header: no dense twin exists elsewhere; `denseBuildStep`/`DenseCovIndex` are reused
    unchanged from `DomainBatch.lean`). -/
def denseBuildPruned {α : Type} (varsOf : α → List VarId) (maxVars : Nat) (items : List α) :
    DenseCovIndex :=
  items.zipIdx.foldr (fun ai idx =>
    if (HashedDedup.hashedEraseDups (hash ·) (varsOf ai.1)).length ≤ maxVars then
      denseBuildStep varsOf ai idx
    else idx) ⟨∅, []⟩

/-! ### Minting the fresh bits -/

/-- Register the `k` fresh bit variables `freshBase ++ "_0", …, freshBase ++ "_(k-1)"` into `reg`,
    in order — the exact point `buildReencode` constructs them (see the module header: bit `VarId`s
    do not exist before this call). -/
def denseRegisterBits (reg : VarRegistry) (freshBase : String) (k : Nat) :
    VarRegistry × List VarId :=
  (List.range k).foldl
    (fun (acc : VarRegistry × List VarId) (j : Nat) =>
      let (r, bs) := acc
      let (r', i) := r.register ({ name := freshBase ++ "_" ++ toString j } : Variable)
      (r', bs ++ [i]))
    (reg, [])

/-! ### Building the candidate group's bits and substitution map -/

/-- Construct the bits and the substitution map for a candidate group (proof-free — the checked
    certificate re-verifies everything). Threads the registry through, registering only on the
    single accepting path (see the module header). Reuses `denseCoveredIdx` (`DomainFold.lean:137`,
    order-restoring) for the indexed branch and a plain `Array.foldr` filter for the direct
    branch. -/
def denseBuildReencode (reg : VarRegistry) (useIdx : Bool) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (xs : List VarId) (freshBase : String) :
    VarRegistry × Option (List VarId × Std.HashMap VarId (DenseExpr p)) :=
  let es := if useIdx then denseCoveredIdx csIdx arrCs (denseCoveredBy xs) xs
    else arrCs.foldr (fun c acc => if denseCoveredBy xs c then c :: acc else acc) []
  match denseGroupDoms es xs with
  | none => (reg, none)
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ 256 then
      if es.length == xs.length && es.all (fun c => c.vars.eraseDups.length == 1)
          && xs.length ≤ Nat.clog 2 boxSize then
        -- single-var-only covered set (one per variable): survivors = box; unencodable
        (reg, none)
      else
      let survs := denseGroupSurvivorsE es doms
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let (reg1, bits) := denseRegisterBits reg freshBase k
          let patts := denseAssignments (denseBitBox bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          (reg1, some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (denseInterpPoly pz x).fold)))))
        else (reg, none)
      else (reg, none)
    else (reg, none)

/-! ### The degree pre-gate -/

/-- **Degree pre-gate** (untrusted, necessary-condition): walk the system once with an early-exit
    `any`, rewriting only the items sharing a variable with the group, and fire when a rewritten
    item already exceeds the bound. -/
def denseDegPreReject (b : DegreeBound) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  let σ := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  d.algebraicConstraints.any (fun c =>
    c.sharesVarIn xs && !denseCoveredBy xs c &&
      decide (b.identities < (denseGroupRewrite xs bits σ patts c).degree)) ||
  d.busInteractions.any (fun bi =>
    (bi.multiplicity.sharesVarIn xs &&
      decide (b.busInteractions < (denseGroupRewrite xs bits σ patts bi.multiplicity).degree)) ||
    bi.payload.any (fun e =>
      e.sharesVarIn xs &&
        decide (b.busInteractions < (denseGroupRewrite xs bits σ patts e).degree)))

/-! ### One checked re-encoding step -/

/-- One checked re-encoding step (identity if construction or certificate fails), in gate order:
    the input-column gate, the fresh-name collision prefilter (see the module header for the exact
    mechanism), `denseBuildReencode`, the degree pre-gate, the group-membership/bits-disjointness/
    no-powdr-ID gates, `denseCheckReencode`, then the final `withinDegreeB` gate. Returns a plain
    6-tuple `(reg', d', derivs, csIdx', arrCs', varSet')` — no proof is carried (`varSet` is a plain
    `Std.HashSet VarId`, see the module header). `bsem : BusSemantics p` has no runtime role in this
    step and is dropped here (it is kept, necessarily, at `denseReencodeF`, whose signature
    `ofExtending` fixes). -/
def denseReencodeStep (b : DegreeBound) (useIdx : Bool)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (varSet : Std.HashSet VarId) (xs : List VarId)
    (freshBase : String) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p × DenseCovIndex ×
      Array (DenseExpr p) × Std.HashSet VarId :=
  if xs.all (fun x => reg.isInput x) then
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => varSet.contains i
      | none => false) then
    -- fresh-name collision: `denseCheckReencode` would reject after the full freshness scan
    (reg, d, [], csIdx, arrCs, varSet)
  else
  match denseBuildReencode reg useIdx csIdx arrCs xs freshBase with
  | (reg1, none) => (reg1, d, [], csIdx, arrCs, varSet)
  | (reg1, some (bits, hm)) =>
    -- Degree pre-gate: reject (exactly the candidates the final `withinDegreeB` would reject)
    -- before the certificate's whole-system freshness scan and the output materialization.
    if denseDegPreReject b d xs bits hm then (reg1, d, [], csIdx, arrCs, varSet)
    else
    if xs.all (fun x => varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOut d xs bits hm
      if ro.withinDegreeB b then
        -- `d` changed: rebuild the index and the variable set for `ro` (accepts are rare, so this
        -- is cheap overall).
        (reg1, ro,
         bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)),
         (if useIdx then denseBuildPruned DenseExpr.vars 8 ro.algebraicConstraints else ⟨∅, []⟩),
         ro.algebraicConstraints.toArray,
         Std.HashSet.ofList ro.occ)
      else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
  else (reg, d, [], csIdx, arrCs, varSet)

/-! ### The sequential driver -/

/-- Process the candidate groups sequentially (derivations concatenate; the registry, the inverted
    index, and the variable set are threaded and rebuilt by `denseReencodeStep` whenever it rewrites
    `d`). -/
def denseReencodeLoop (b : DegreeBound) (useIdx : Bool) :
    List (List VarId) → Nat → VarRegistry → DenseConstraintSystem p → DenseCovIndex →
      Array (DenseExpr p) → Std.HashSet VarId →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p
  | [], _, reg, d, _, _, _ => (reg, d, [])
  | xs :: rest, idx, reg, d, csIdx, arrCs, varSet =>
    let (reg1, d1, derivs1, csIdx1, arrCs1, varSet1) :=
      denseReencodeStep b useIdx reg d csIdx arrCs varSet xs
        (s!"rnc{d.algebraicConstraints.length}_{d.busInteractions.length}_{idx}")
    let (reg2, d2, derivs2) :=
      denseReencodeLoop b useIdx rest (idx + 1) reg1 d1 csIdx1 arrCs1 varSet1
    (reg2, d2, derivs1 ++ derivs2)

/-! ### The pass, as a plain registry-extending transform -/

/-- The witness re-encoding transform, shaped exactly for `DenseVerifiedPassW.ofExtending`
    (the prover wires it with `DenseVerifiedPassW.ofExtending (denseReencodeF pw b) …`): construct
    the candidate target groups (see the module header for the ordering comparator and the
    shared-`csVs` hoist), then dispatch. `facts` is unused: reencode is fact-free (its signature
    takes only `bsem`); the parameter exists solely to match `ofExtending`'s uniform transform
    shape. -/
def denseReencodeF (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bsem : BusSemantics p) (_facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    -- Each constraint's deduped variable list is computed once and shared between the single-
    -- variable set and the target list.
    let csVs := d.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
    let svSet : Std.HashSet VarId := csVs.foldl (init := ∅) fun s vs =>
      match vs with
      | [x] => s.insert x
      | _ => s
    let targets := dedupHash (csVs.filterMap (fun vs =>
      if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
        -- Ordering (deliberate divergence exception, see the module header): sort by the
        -- resolved `Variable`'s order.
        some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
      else none))
    let useIdx := 8192 ≤ d.algebraicConstraints.length
    denseReencodeLoop b useIdx targets 0 reg d
      (if useIdx then denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints else ⟨∅, []⟩)
      d.algebraicConstraints.toArray
      (Std.HashSet.ofList d.occ)
  else (reg, d, [])

end ApcOptimizer.Dense
