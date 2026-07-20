import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch

set_option autoImplicit false

/-! # Witness re-encoding — dense expression operations (Task 3, reencode native port, chunk R1)

Dense, `VarId`-native transliteration of the *expression-level* runtime definitions of
`OptimizerPasses/OldVariableBased/Reencode.lean` (`Variable`/`Expression`-based): environment
extension, the fast hoisted evaluator, the booleanity constraint, the group substitution and bit
box, the degree-aware group rewrite (`indicatorExpr`/`interpOfV`/`candSelect`/`groupRewriteCand`/
`groupRewrite`), the re-encoded output, the group's survivor enumeration and the checked
re-encoding certificate, the fresh bits' derived-variable methods (`imgVal`/`matchCM`/`bitCM`), the
interpolation polynomial, and the `foldRewrite`-gate test `sharesVarIn`. This is **impl-only**:
every theorem in the spec file (the transport core `reencode_correct`/`reencode_correct_D`, the
enumerated-assignment structure lemmas, the pointwise environment facts, the booleanity/derived-
method soundness lemmas, and the capstone `checkReencode_sound_D`) is proof-side and left for the
prover — nothing here states or proves anything beyond the runtime computation.

Still **out of scope for this chunk** (later chunks, per the reencode port plan): `buildReencode`
(the proof-free construction of a candidate group's bits + interpolation map, including its
hopeless-target prefilter and its indexed-vs-direct covered-set gathering), `degPreReject` (the
degree pre-gate), `reencodeStep`/`reencodeLoop` (the per-candidate step and the sequential driver,
including the registry-extending fresh-variable plumbing that consumes the `ofNativeExtending`
builder already added to `Bridge.lean`), and `reencodePass` (the top-level pass assembling the
candidate-group list and dispatching indexed vs direct covered-set gathering). The
`OldVariableBased.Reencode` import is kept: the `ofSpec` selector branch still runs the spec pass
until a later chunk flips it, and the prover's native proof may cite the spec's own transport
lemmas while it is under construction.

## ⚠️ Forced deviation: a circular import blocks reuse of `DomainFold.lean`'s primitives

The reuse table for this chunk points at several primitives living in the dense
`OptimizerPasses/DomainFold.lean`/`DomainFoldRuntime.lean` (`denseFindDomainAlg`, `denseCoveredBy`,
`denseCoveredCsOf`, `denseGroupDoms`, `denseAssignments`, `DenseExpr.hasVar`, and the value-only
survivor engine `denseGroupSurvivorsEV`/`denseAssignmentsV`). **These cannot be imported from this
file**: `OldVariableBased/DomainFold.lean` (the spec pass, unrelated to the dense one) imports the
*canonical* `OptimizerPasses/Reencode.lean` — i.e. *this file* — for the spec's own `coveredBy`/
`groupDoms` (defined in spec `Reencode.lean`, not spec `DomainFold.lean`). Before this chunk, the
canonical `Reencode.lean` was an empty wrapper, so that import was harmless; now that it carries
real dense content needing `DomainFold.lean`'s primitives, importing dense `DomainFold.lean` (or
`DomainFoldRuntime.lean`, which imports it) would close the cycle
`Reencode(canonical) → DomainFold(dense) → DomainFold(spec) → Reencode(canonical)`, which Lean
rejects outright (`bad import`).

Neither available fix is in scope here: redirecting `OldVariableBased/DomainFold.lean`'s (and
`OldVariableBased/HintCollapse.lean`'s, which has the same import for the same reason) import
target to `OptimizerPasses.OldVariableBased.Reencode` directly would be a purely import-graph,
zero-semantic-change edit, but it edits a spec pass file, which this chunk's hard rules forbid
without explicit sign-off; relocating the shared primitives out of `DomainFold.lean` into a common
lower module both files could import is a wider refactor touching every already-landed, natively-
proven pass built on `DomainFold.lean` (the whole addr-diseq/busPairCancel cluster:
`RootPairUnify`/`FlagUnify`/`FlagFoldDrops`/`FxSubst`/`BoxRewrite`/`FlagFold`/`BusPairCancel*`/
`DomainFoldProof`), well beyond this chunk's assigned scope and risk budget.

**Flagged for the orchestrator/prover:** this file therefore carries `private` copies — body-
identical to their `DomainFold.lean` twins, cited by name below — of the handful of small,
self-contained primitives it needs (`DenseExpr.hasVar`, `denseCoveredBy`, `denseCoveredCsOf`,
`denseFindDomainAlg`, `denseGroupDoms`, `denseAssignments`). `private` mangles each declaration's
real name per defining module, so these cannot collide with the public originals when both files
are eventually loaded together (e.g. via `DenseUmbrella.lean`); this was verified by a clean
`lake build`. **R2/R3 will hit the identical blocker** for `denseSvSet`/`denseCoveredIdx`/
`DenseFoldIdx` (needed by `buildReencode`/`reencodePass`'s indexed covered-set gathering) — a
permanent fix should be decided before those chunks land, not re-patched ad hoc per chunk.

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
* `dedupHash` (spec, `OldVariableBased/Reencode.lean:1632`) is fully generic
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

/-! ## Locally re-derived `DomainFold.lean` primitives (circular-import workaround)

See the module header's forced-deviation note: these six are `private`, body-identical to their
public `DomainFold.lean` twins, needed here only because that file cannot be imported from this
one. -/

/-- Dense `Expression.hasVar`. Private local copy of `DomainFold.lean`'s `DenseExpr.hasVar`. -/
private def DenseExpr.hasVar : DenseExpr p → Bool
  | .const _ => false
  | .var _ => true
  | .add a b => a.hasVar || b.hasVar
  | .mul a b => a.hasVar || b.hasVar

/-- Constraints whose (nonempty) variable set lies inside the group. Private local copy of
    `DomainFold.lean`'s `denseCoveredBy`. -/
private def denseCoveredBy (xs : List VarId) (c : DenseExpr p) : Bool :=
  c.hasVar && c.varsInF xs

/-- The group's covered constraints. Private local copy of `DomainFold.lean`'s
    `denseCoveredCsOf`. -/
private def denseCoveredCsOf (d : DenseConstraintSystem p) (xs : List VarId) : List (DenseExpr p) :=
  d.algebraicConstraints.filter (denseCoveredBy xs)

/-- Domain (root set) of `i` from the first covered constraint that determines one. Private local
    copy of `DomainFold.lean`'s `denseFindDomainAlg`, reusing `denseRootsIn` (`DomainBatch.lean`,
    safely importable). -/
private def denseFindDomainAlg (all : List (DenseExpr p)) (i : VarId) : Option (List (ZMod p)) :=
  match all with
  | [] => none
  | c :: rest =>
    if c.mentions i then
      match denseRootsIn i c with
      | some d => some d
      | none => denseFindDomainAlg rest i
    else denseFindDomainAlg rest i

/-- Domains for the group's variables, from the covered constraints only. Private local copy of
    `DomainFold.lean`'s `denseGroupDoms`. -/
private def denseGroupDoms (es : List (DenseExpr p)) :
    List VarId → Option (List (VarId × List (ZMod p)))
  | [] => some []
  | i :: rest =>
    match denseFindDomainAlg es i, denseGroupDoms es rest with
    | some d, some ds => some ((i, d) :: ds)
    | _, _ => none

/-- The Cartesian product of the group's per-variable domains, keyed. Private local copy of
    `DomainFold.lean`'s `denseAssignments`. -/
private def denseAssignments : List (VarId × List (ZMod p)) → List (List (VarId × ZMod p))
  | [] => [[]]
  | (i, d) :: rest => (denseAssignments rest).flatMap (fun a => d.map (fun v => (i, v) :: a))

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
    `interpPoly` — consumed by `buildReencode` (later chunk), which supplies `pz` from
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

end ApcOptimizer.Dense
