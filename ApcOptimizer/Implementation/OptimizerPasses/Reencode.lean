import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold

set_option autoImplicit false

/-! # Witness re-encoding — dense expression operations (Task 3, reencode native port, chunk R1)

Dense, `VarId`-native transliteration of the *expression-level* runtime definitions of
the reference `Reencode` pass (`Variable`/`Expression`-based): environment
extension, the fast hoisted evaluator, the booleanity constraint, the group substitution and bit
box, the degree-aware group rewrite (`indicatorExpr`/`interpOfV`/`candSelect`/`groupRewriteCand`/
`groupRewrite`), the re-encoded output, the group's survivor enumeration and the checked
re-encoding certificate, the fresh bits' derived-variable methods (`imgVal`/`matchCM`/`bitCM`), the
interpolation polynomial, and the `foldRewrite`-gate test `sharesVarIn`. This is **impl-only**:
every theorem in the spec file (the transport core `reencode_correct`/`reencode_correct_D`, the
enumerated-assignment structure lemmas, the pointwise environment facts, the booleanity/derived-
method soundness lemmas, and the capstone `checkReencode_sound_D`) is proof-side and left for the
prover — nothing here states or proves anything beyond the runtime computation.

## Chunk R2: the build/step/loop/pass layer

This chunk adds the *proof-free construction* layer on top of R1's expression ops:
`denseBuildReencode` (↔ `buildReencode`, including its hopeless-target prefilter and its
indexed-vs-direct covered-set gathering — reusing `denseCoveredIdx`, `DomainFold.lean:137`, and
`denseCovBuild`/`denseBuildStep`, `DomainBatch.lean:1195/1200`), `denseDegPreReject` (↔
`degPreReject`, the #165 degree pre-gate), `denseReencodeStep`/`denseReencodeLoop` (↔
`reencodeStep`/`reencodeLoop`, the per-candidate step and the sequential driver, including the
registry-extending fresh-variable plumbing), and `denseReencodeF` (↔ `reencodePass`, as a plain
transform matching the `ofExtending` builder's shape — the prover wires it with
`DenseVerifiedPassW.ofExtending (denseReencodeF pw b) …`). The native correctness proof and
the `ofExtending` wiring live in `ReencodeProof.lean`.

### Fresh bits: where they are minted, and the freshness prefilter mechanism

The spec constructs the fresh bit `Variable`s **inside `buildReencode`**, not in `reencodeStep` — only on the single accepting path (box small enough,
not the single-var-only hopeless case, `2 ≤ survs.length`, `k < xs.length`). `denseBuildReencode`
mints them at the **identical point**: `denseRegisterBits` constructs the same full `Variable`
values (`{ name := freshBase ++ "_" ++ toString j }`, `j = 0, …, k-1`, in order) and registers each
via `reg.register`, threading the registry through only that one branch; every rejecting branch of
`denseBuildReencode` returns the registry **unchanged**. `VarRegistry.register` is append-only and
idempotent on an already-registered `Variable` (returns the existing `VarId`), which is exactly the
bijection a canonical registry must have — so a `denseReencodeStep` invocation whose candidate is
later rejected by `denseDegPreReject`/`denseCheckReencode`/`withinDegreeB` still threads the
registry *as extended by* `denseBuildReencode` onward (harmless: the orphaned bit `VarId`s never
occur in any expression, so they cannot affect any downstream `VarId`-keyed decision); this mirrors
the spec exactly, where the constructed `Variable` values are simply discarded on rejection (no
persistent effect either way, since `Variable` has no identity beyond structural equality).

`reencodeStep`'s **freshness prefilter** (`varSet.val.contains { name := freshBase ++ "_0" }`,
`:1574`) runs *before* `buildReencode`, so no bit exists yet to look up by `VarId` — the dense
mirror resolves the decision honestly instead: a `Variable` is a member of the current system iff
it was registered *and* its `VarId` is in the current dense `varSet`. Concretely,
`match reg.idOf? { name := freshBase ++ "_0" } with | some i => varSet.contains i | none => false`
— if the candidate name was never registered at all it cannot be a system member (everything a
`DenseConstraintSystem` mentions is registered, by the pipeline's own coverage invariant), so the
`none` case is a clean "no collision"; if it *was* registered, membership in the current `varSet`
is exactly the spec's `Std.HashSet Variable` membership test transported through the registry
bijection.

### `varSet` is a plain `Std.HashSet VarId`

The spec threads `varSet` as a `Subtype` (`{ s : Std.HashSet Variable // ∀ x, s.contains x = true
→ x ∈ cs.vars }`) because `reencodeStep` returns a `PassCorrect`-carrying `Σ'` and needs the
membership-implies-coverage fact for its proof. `denseReencodeStep`/`denseReencodeLoop` carry
**no proof at all** (this chunk is impl-only), so `varSet` here is the plain `Std.HashSet VarId` —
the `.contains` decision and the accept-time rebuild (`Std.HashSet.ofList ro.occ`, mirroring the
spec's `Std.HashSet.ofList ro.vars`) are behaviourally identical to the spec's carried set; only the
subtype's proof obligation is dropped (left for the prover to restate and discharge against
`DenseConstraintSystem.CoveredBy`, not to re-derive here).

### Ordering parity for the candidate-group targets (deliberate divergence exception)

`denseReencodeF`'s target list (mirroring the spec's `csVs`/`svSet`/`targets` construction,
byte-identical text to `domainFoldPass`'s own preamble)
sorts each candidate group with a **resolve-based comparator**,
`compare (reg.resolve a) (reg.resolve b) != .gt` — reproducing the spec's `Variable`-`compare`
order exactly, rather than the `VarId.index`-native order `Dense/DomainFoldNative.lean`'s sibling
`denseTargetsV` uses. This is a deliberate, isolated exception to the general `VarId`-order
convention (`VarIdAddendum.md`: ordering is not normally a requirement): this candidate order is
directly the *iteration* order of `denseReencodeLoop`'s greedy, order-sensitive accept/reject
sequence, byte-identity is part of this merge's bar, and the cost is paid only on this pass's cold
target-construction path (once per fixpoint iteration, not per box point) — the opposite trade made
by `Dense/DomainFoldNative.lean`/`BoxRewrite.lean` on their genuinely hot paths. No precedent exists
for this specific choice (this is the first pass to make it); `csVs`/`svSet` are reconstructed here
literally from the spec text (the shared `let csVs := …` hoist feeding both `svSet` and `targets`)
rather than reusing `DomainFoldRuntime.lean`'s `denseSvSet`/`denseTargetsV`, which already diverge
from *their own* spec's identical shared-hoist shape (an audited, approved choice for domainFold
specifically, not one this chunk re-derives without instruction) — preserving the spec's own
`let`-sharing here is the more literal, lower-risk transliteration. `dedupHash`'s dedup order is
list-order-preserving regardless of the key's hash (`VarId` vs `Variable`), so no divergence there.

### `denseBuildPruned`: a local twin of `CoveredIndex.buildPruned`

No dense twin of `CoveredIndex.buildPruned` (`CoveredIndex.lean:59`) exists yet, and this chunk may
not edit any file besides this one — `denseBuildPruned` below is a local, `VarId`-keyed
transliteration (reusing the already-dense `denseBuildStep`/`DenseCovIndex` from
`DomainBatch.lean`), used exactly where the spec calls `CoveredIndex.buildPruned Expression.vars 8
…` (the pass-level initial index and the accept-time rebuilt index in `denseReencodeStep`).

## Import-graph note

This file imports the dense `DomainFold.lean` primitives (`denseFindDomainAlg`, `denseCoveredBy`,
`denseCoveredCsOf`, `denseGroupDoms`, `denseAssignments`, `DenseExpr.hasVar`) directly — no local
copies. Later chunks may likewise import `DomainFoldRuntime.lean` (`denseSvSet`,
`denseCoveredIdx`, `DenseFoldIdx`) without obstruction.

The group-survivor enumeration (`denseSurvZeroCW`/`denseGroupSurvivorsE` below) needs **no**
workaround: spec `Reencode.lean` itself defines `survZeroCW`/`groupSurvivorsE` (not
`DomainFold.lean`) directly against the *keyed* compiled evaluator `compileEs`/`IExpr.evalWith`
(`DomainBatch.lean`), so this chunk ports them literally against the safely-importable
`DomainBatch.lean` (`denseCompileEs`/`denseIExprEvalWith`) — the value-only rebuild
`denseGroupSurvivorsEV` the reuse table pointed at is `DomainFold`-side machinery built later as a
`domainFold`-specific perf fix, not what `groupSurvivorsE` itself is defined against.

## Other reuse decisions

* `envOf` has no separate "fast" dense twin: `VarId` equality is already a direct `Nat` comparison,
  so the codebase's existing convention (established by `BoxRewrite.lean`, see its module header) is
  to route every spec `envOf`/`envOfFast` use through `denseEnvOfFast` (`DomainBatch.lean`) — there is
  nothing left to speed up separately. Same story for `Expression.varsIn`/`Expression.varsInF`: both
  collapse to the single existing `DenseExpr.varsInF` (`DomainBatch.lean`), and `Expression.mentions`/
  `Expression.mentionsF` both collapse to the single existing `DenseExpr.mentions` (`SubstMap.lean`) —
  wherever the spec text below uses the "F" fast-path name, the dense port below uses the plain
  (already-fast) dense name and is noted at the call site.
* `Expression.evalFast`/`Expression.evalWith` (the ring-operation-hoisting hot-path helper this pass'
  own docstring calls out) has no existing dense twin — hoisting the `Add`/`Mul (ZMod p)` instance
  derivation once per call, rather than once per expression node, is unrelated to the `Variable`→
  `VarId` representation change, so it is ported here verbatim as `DenseExpr.evalWith`/
  `DenseExpr.evalFast` (preserving the fast-path helper, per the porting rules).
* `indicatorExpr` is **not** the same function as `FxSubst.lean`'s `denseIndicatorProd`: the latter
  (`others : List VarId`, `pt : List (VarId × ZMod p)`) folds over a separate variable list and looks
  each one up in `pt` via `denseEnvOfFast` (a scan per element), while `indicatorExpr`/
  `denseIndicatorExpr` folds directly over the pattern list itself, reading each pair's own stored
  value with no lookup at all — a different (and cheaper) computation, mirroring a different spec
  function. Ported fresh below as `denseIndicatorExpr`, not reused.
* `dedupHash` (spec) is fully generic
  (`{α : Type} [BEq α] [Hashable α]`) and representation-independent; it is reused unqualified at
  `VarId`, exactly as `DomainFoldRuntime.lean`'s `denseTargetsV` already does — no dense-specific
  version is defined here (not needed by any definition in this chunk; the candidate-group builder
  that calls it is a later chunk's scope). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Environment extension by an association list -/

/-- Override `denv` on the keys of `pairs` (first match wins). Mirrors `envExt`. -/
def denseEnvExt : List (VarId × ZMod p) → (VarId → ZMod p) → VarId → ZMod p
  | [], denv, y => denv y
  | (x, v) :: rest, denv, y => if y = x then v else denseEnvExt rest denv y

/-! ## Fast evaluation (hoisted ring operations)

Mirrors the spec's own "Fast evaluation" section: `+`/`*` on `ZMod p` with a *runtime* `p`
re-derive the whole `CommRing (ZMod p)` instance chain at every expression node: `evalFast`
extracts the two operations from the instances once per evaluation call, so each node is a direct
closure call. This is unrelated to `Variable`→`VarId` — the hot-path helper is ported verbatim. -/

/-- `DenseExpr.eval` with the ring operations passed in. Mirrors `Expression.evalWith`. -/
def DenseExpr.evalWith (add mul : ZMod p → ZMod p → ZMod p) (denv : VarId → ZMod p) :
    DenseExpr p → ZMod p
  | .const n => n
  | .var i => denv i
  | .add a b => add (a.evalWith add mul denv) (b.evalWith add mul denv)
  | .mul a b => mul (a.evalWith add mul denv) (b.evalWith add mul denv)

/-- `DenseExpr.eval`, deriving the field operations once per call instead of per node. Mirrors
    `Expression.evalFast`. -/
def DenseExpr.evalFast (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  let addI : Add (ZMod p) := inferInstance
  let mulI : Mul (ZMod p) := inferInstance
  e.evalWith addI.add mulI.mul denv

/-! ## Booleanity constraint for the fresh bits -/

/-- `b · (b − 1)`. Mirrors `boolConstraint`. -/
def denseBoolConstraint (b : VarId) : DenseExpr p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

/-! ## The group substitution and the fresh bits' domain box -/

/-- The group substitution: defined on the group only, backed by a hash map. Mirrors `groupSubst`,
    reusing `denseContainsFast` (`DomainBatch.lean`). -/
def denseGroupSubst (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    VarId → Option (DenseExpr p) :=
  fun y => if denseContainsFast xs y then hm[y]? else none

/-- The `{0,1}` domain box of the fresh bits. Mirrors `bitBox`. -/
def denseBitBox (bits : List VarId) : List (VarId × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-! ## Degree-aware group rewriting -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. Mirrors `indicatorExpr` —
    **not** `FxSubst.lean`'s `denseIndicatorProd` (see the module header: different fold shape, a
    different spec function). -/
def denseIndicatorExpr (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

/-- The interpolation of a whole subexpression over the bit patterns, from its precomputed
    per-pattern values. Mirrors `interpOfV`. -/
def denseInterpOfV (patts : List (List (VarId × ZMod p))) (vals : List (ZMod p)) : DenseExpr p :=
  match vals with
  | [] => .const 0
  | v₀ :: _ =>
    if vals.all (fun v => decide (v = v₀)) then .const v₀
    else (patts.zip vals).foldl (fun acc av =>
      .add acc (.mul (denseIndicatorExpr av.1) (.const av.2))) (.const 0)

/-- The interpolation acceptance check on precomputed pieces: take `cand` only if its variables lie
    in the bits and it agrees with the (precomputed) substitution values on every pattern, else fall
    back to the plain substitution `sub`. Mirrors `candSelect`, reusing `DenseExpr.varsInF` in place
    of the spec's `varsIn` (see the module header) and `denseEnvOfFast` in place of `envOf`. -/
def denseCandSelect (bits : List VarId) (patts : List (List (VarId × ZMod p)))
    (sub cand : DenseExpr p) (vals : List (ZMod p)) : DenseExpr p :=
  if cand.varsInF bits &&
      (patts.zip vals).all (fun av => decide (cand.evalFast (denseEnvOfFast av.1) = av.2))
  then cand
  else sub

/-- Interpolation candidate with the checked fallback to plain substitution. Mirrors
    `groupRewriteCand`, reusing `DenseExpr.substF` (`SubstMap.lean`), `denseEnvOfFast`, and
    `DenseExpr.fold` (`ExprOps.lean`). -/
def denseGroupRewriteCand (bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  let sub := e.substF σfn
  let vals := patts.map (fun aβ => sub.evalFast (denseEnvOfFast aβ))
  denseCandSelect bits patts sub ((denseInterpOfV patts vals).fold) vals

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else. Mirrors `groupRewrite`, reusing `denseContainsFast` and
    `DenseExpr.varsInF` (both already the collapsed "fast" dense names, see the module header). -/
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
    booleanity for the bits. Mirrors `reencodeOut`, reusing the (locally re-derived) `denseCoveredBy`
    and `denseAssignments` above. No dense `BusInteraction.mapExpr` exists (the spec's own is defined
    only at `Expression p`, see `Rewrite.lean`), so the bus-interaction rewrite is inlined
    field-by-field, matching the shape already established by `DomainFoldRuntime.lean`'s fold-out
    functions. The whole rewrite closure (`groupSubst`/`bitBox`/`assignments`) is recomputed for the
    constraints and again for the bus interactions exactly as the spec text does (no extra
    `let`-hoist beyond what the spec itself has). -/
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

Mirrors spec `Reencode.lean`'s own `survZeroCW`/`groupSurvivorsE` (:790–820) directly against the
*keyed* compiled evaluator `denseCompileEs`/`denseIExprEvalWith` (`DomainBatch.lean`, safely
importable — see the module header: no `DomainFold.lean` dependency needed here at all). -/

/-- All covered constraints zero at a point, with the ring ops hoisted out of the per-point
    evaluation. Mirrors `survZeroCW`. -/
def denseSurvZeroCW (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (a : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWith add mul a ie = 0))

/-- The surviving group values from a **precomputed** covered set: enumerated over the group's
    domains, filtered by the covered constraints, compiled once per target to positional `IExpr`s.
    Mirrors `groupSurvivorsE`. -/
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

/-- All checked side conditions for one re-encoding step. Mirrors `checkReencode`, reusing the
    (locally re-derived) `denseGroupDoms`/`denseCoveredCsOf` above, `denseAssignments`/`denseBitBox`,
    `denseGroupSurvivorsE` above, `denseEnvOfFast`, and `DenseExpr.mentions` in place of the spec's
    `mentionsF` (both already the collapsed "fast" dense name, see the module header). The conjunct
    **order is preserved exactly**, including the deliberately-last freshness conjunct (the only
    `O(bits × system)` one, short-circuited to run only for the few already-cheaply-accepted
    groups). -/
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

/-- The interpolation image of group variable `x` at pattern `aβ` (a field constant). Mirrors
    `imgVal`. -/
def denseImgVal (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (aβ : List (VarId × ZMod p)) (x : VarId) : ZMod p :=
  ((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`, as nested `ifEqZero`. Mirrors
    `matchCM`. -/
def denseMatchCM (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) : DenseComputationMethod p :=
  match xs with
  | [] => thenM
  | x :: rest =>
      .ifEqZero (.add (.var x) (.const (-(imgFn x)))) (denseMatchCM rest imgFn thenM elseM) elseM

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit.
    Mirrors `bitCM`. -/
def denseBitCM (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) : DenseComputationMethod p :=
  match patts with
  | [] => .const 0
  | aβ :: rest =>
      denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b)) (denseBitCM rest xs hm b)

/-! ## Building the interpolation (proof-free) -/

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs. Mirrors
    `interpPoly` — consumed by `denseBuildReencode` below, which supplies `pz` from
    `denseGroupSurvivorsE`'s keyed output. -/
def denseInterpPoly (pz : List (List (VarId × ZMod p) × List (VarId × ZMod p))) (x : VarId) :
    DenseExpr p :=
  pz.foldl (fun acc az => .add acc (.mul (denseIndicatorExpr az.1) (.const (denseEnvOfFast az.2 x))))
    (.const 0)

/-! ## Sharing a variable with a group (the `foldRewrite`-gate test) -/

/-- Does the expression share a variable with `xs`? (No allocation.) Mirrors
    `Expression.sharesVarIn`, reusing `denseContainsFast`. Same shape as `DenseExpr.anyVarIn`
    (`DomainFold.lean`) — the spec keeps two independently-defined but identical copies of this
    predicate (`Expression.anyVarIn` in `DomainFold.lean`, `Expression.sharesVarIn` here) to avoid a
    cross-file dependency; ported the same way here, as its own definition local to this file, for
    a direct line-parallel diff against its own spec twin. -/
def DenseExpr.sharesVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.sharesVarIn xs || b.sharesVarIn xs
  | .mul a b => a.sharesVarIn xs || b.sharesVarIn xs

/-! ## Chunk R2: the build/step/loop/pass layer (see the module header) -/

/-! ### A local dense twin of `CoveredIndex.buildPruned` -/

/-- `VarId`-keyed twin of `CoveredIndex.buildPruned` (`CoveredIndex.lean:59`): build the inverted
    index, skipping items with more than `maxVars` distinct variables. Local to this file (see the
    module header: no dense twin exists elsewhere, and this chunk may not edit `DomainBatch.lean`,
    where `denseBuildStep`/`DenseCovIndex` — reused here unchanged — live). -/
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
    certificate re-verifies everything). Mirrors `buildReencode`, threading the registry through
    (registration happens only on the single accepting path, exactly where the spec constructs the
    bit `Variable`s — see the module header). Reuses `denseCoveredIdx` (`DomainFold.lean:137`,
    order-restoring, mirrors `CoveredIndex.coveredIdx`) for the indexed branch and a plain
    `Array.foldr` filter for the direct branch, exactly as the spec dispatches. -/
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

/-- **Degree pre-gate** (untrusted, necessary-condition). Mirrors `degPreReject`: walk the system
    once with an early-exit `any`, rewriting only the items sharing a variable with the group, and
    fire when a rewritten item already exceeds the bound. -/
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

/-- One checked re-encoding step (identity if construction or certificate fails). Mirrors
    `reencodeStep`, **preserving the exact gate order**: the input-column gate, the fresh-name
    collision prefilter (see the module header for the exact mechanism), `denseBuildReencode`, the
    degree pre-gate, the group-membership/bits-disjointness/no-powdr-ID gates, `denseCheckReencode`,
    then the final `withinDegreeB` gate. Returns a plain 6-tuple `(reg', d', derivs, csIdx', arrCs',
    varSet')` — no proof is carried (`varSet` is a plain `Std.HashSet VarId`, see the module
    header). The spec threads `bsem : BusSemantics p` only to build the discarded branches'
    `PassCorrect.refl cs bsem` proof witness; since this chunk carries no proof at all, `bsem` has
    no runtime role here and is dropped (kept, necessarily, at `denseReencodeF`, whose signature
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
    `d`). Mirrors `reencodeLoop`, including the exact `freshBase` format string (`bsem` dropped for
    the same reason as `denseReencodeStep`, see its docstring). -/
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
    (the prover wires it with `DenseVerifiedPassW.ofExtending (denseReencodeF pw b) …`).
    Mirrors `reencodePass`'s target-group construction (see the module header for the ordering-
    parity comparator and the shared-`csVs` hoist) and dispatch. `facts` is unused: reencode is
    fact-free, as the spec pass is (its signature takes only `bsem`); the parameter exists solely to
    match `ofExtending`'s uniform transform shape. -/
def denseReencodeF (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bsem : BusSemantics p) (_facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    -- Each constraint's deduped variable list is computed once and shared between the single-
    -- variable set and the target list, exactly as the spec's `csVs` hoist does.
    let csVs := d.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
    let svSet : Std.HashSet VarId := csVs.foldl (init := ∅) fun s vs =>
      match vs with
      | [x] => s.insert x
      | _ => s
    let targets := dedupHash (csVs.filterMap (fun vs =>
      if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
        -- Ordering parity (deliberate divergence exception, see the module header): sort by the
        -- resolved `Variable`'s order, reproducing the spec's canonicalisation exactly.
        some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
      else none))
    let useIdx := 8192 ≤ d.algebraicConstraints.length
    denseReencodeLoop b useIdx targets 0 reg d
      (if useIdx then denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints else ⟨∅, []⟩)
      d.algebraicConstraints.toArray
      (Std.HashSet.ofList d.occ)
  else (reg, d, [])

end ApcOptimizer.Dense
