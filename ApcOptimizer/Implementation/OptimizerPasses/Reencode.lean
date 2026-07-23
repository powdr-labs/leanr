import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold

set_option autoImplicit false

/-! # Witness re-encoding — dense expression ops and the build/step/loop/pass layer.

Impl-only: no theorem is stated here. Correctness and the `ofExtending` wiring live in
`Proofs/Reencode.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Override `denv` on the keys of `pairs` (first match wins). -/
def denseEnvExt : List (VarId × ZMod p) → (VarId → ZMod p) → VarId → ZMod p
  | [], denv, y => denv y
  | (x, v) :: rest, denv, y => if y = x then v else denseEnvExt rest denv y

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

/-- `b · (b − 1)`. -/
def denseBoolConstraint (b : VarId) : DenseExpr p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

/-- Substitution defined only on the group `xs`, backed by `hm`. -/
def denseGroupSubst (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    VarId → Option (DenseExpr p) :=
  fun y => if denseContainsFast xs y then hm[y]? else none

/-- The `{0,1}` domain box of the fresh bits. -/
def denseBitBox (bits : List VarId) : List (VarId × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-! ## Degree-aware group rewriting -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. -/
def denseIndicatorExpr (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

/-- Interpolate a subexpression over the bit patterns from its precomputed per-pattern values. -/
def denseInterpOfV (patts : List (List (VarId × ZMod p))) (vals : List (ZMod p)) : DenseExpr p :=
  match vals with
  | [] => .const 0
  | v₀ :: _ =>
    if vals.all (fun v => decide (v = v₀)) then .const v₀
    else (patts.zip vals).foldl (fun acc av =>
      .add acc (.mul (denseIndicatorExpr av.1) (.const av.2))) (.const 0)

/-- Take `cand` if its variables lie in the bits and it agrees with the substitution values on
    every pattern; otherwise fall back to the plain substitution `sub`. -/
def denseCandSelect (bits : List VarId) (patts : List (List (VarId × ZMod p)))
    (sub cand : DenseExpr p) (vals : List (ZMod p)) : DenseExpr p :=
  if cand.varsInF bits &&
      (patts.zip vals).all (fun av => decide (cand.evalFast (denseEnvOfFast av.1) = av.2))
  then cand
  else sub

/-- Interpolation candidate with the checked fallback to plain substitution. -/
def denseGroupRewriteCand (bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  let sub := e.substF σfn
  let vals := patts.map (fun aβ => sub.evalFast (denseEnvOfFast aβ))
  denseCandSelect bits patts sub ((denseInterpOfV patts vals).fold) vals

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else. -/
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

/-- `denseGroupRewrite` with a cheap top-level skip: an expression that shares no variable with the
    group and holds no variable-free node to fold is returned untouched (`denseGroupRewrite` would
    rebuild it identically — see `denseGroupRewriteFast_eq` in `Proofs/Reencode.lean`). This turns
    the whole-system rewrite in `denseReencodeOut` sparse: the thousands of constraints untouched by
    a small group skip the rebuild/interpolation entirely. -/
def denseGroupRewriteFast (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs || e.hasConstFoldableNode then denseGroupRewrite xs bits σfn patts e else e

/-! ## The re-encoded system -/

/-- The re-encoded system: substitute the group everywhere, drop the now-covered constraints, and
    add booleanity constraints for the bits. -/
def denseReencodeOut (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseGroupRewriteFast xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))))
        ++ bits.map denseBoolConstraint,
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity :=
        denseGroupRewriteFast xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))
          bi.multiplicity,
      payload := bi.payload.map
        (denseGroupRewriteFast xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))) }) }

/-! ## The group's surviving values -/

/-- All covered constraints zero at a point (ring ops hoisted out of the per-point eval). -/
def denseSurvZeroCW (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (a : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWith add mul a ie = 0))

/-- The surviving group values: enumerate the group's domains, keep those satisfying the covered
    constraints. -/
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

/-- All checked side conditions for one re-encoding step. The freshness conjunct is deliberately
    last: it is the only `O(bits × system)` one, so short-circuiting runs it only for groups that
    already passed the cheap checks. -/
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
    -- freshness: no bit occurs anywhere in the system
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

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs. -/
def denseInterpPoly (pz : List (List (VarId × ZMod p) × List (VarId × ZMod p))) (x : VarId) :
    DenseExpr p :=
  pz.foldl (fun acc az => .add acc (.mul (denseIndicatorExpr az.1) (.const (denseEnvOfFast az.2 x))))
    (.const 0)

/-- Does the expression share a variable with `xs`? -/
def DenseExpr.sharesVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.sharesVarIn xs || b.sharesVarIn xs
  | .mul a b => a.sharesVarIn xs || b.sharesVarIn xs

/-! ## The build/step/loop/pass layer -/

inductive DenseReencodeRootPlan (p : ℕ)
  | any (roots : List (ZMod p))
  | one (var : VarId) (roots : List (ZMod p))

def denseReencodeRootPlanMul :
    DenseReencodeRootPlan p → DenseReencodeRootPlan p → Option (DenseReencodeRootPlan p)
  | .any left, .any right => some (.any (left ++ right))
  | .any left, .one var right => some (.one var (left ++ right))
  | .one var left, .any right => some (.one var (left ++ right))
  | .one leftVar left, .one rightVar right =>
      if leftVar = rightVar then some (.one leftVar (left ++ right)) else none

def denseBuildReencodeRootPlan : DenseExpr p → Option (DenseReencodeRootPlan p)
  | .mul a b =>
      match denseBuildReencodeRootPlan a, denseBuildReencodeRootPlan b with
      | some left, some right => denseReencodeRootPlanMul left right
      | _, _ => none
  | e =>
      match denseLinearize e with
      | none => none
      | some l =>
          let l := l.norm
          match l.terms with
          | [] => if l.const = 0 then none else some (.any [])
          | [(i, _)] => (denseRootsOfTerms i l.const l.terms).map (.one i)
          | _ => none

def denseReencodeRootPlanLookup (i : VarId) :
    DenseReencodeRootPlan p → Option (List (ZMod p))
  | .any roots => some roots
  | .one var roots => if var = i then some roots else none

abbrev DenseReencodeRootCache (p : ℕ) :=
  Std.HashMap Nat (Option (DenseReencodeRootPlan p))

def denseReencodeRootAt (cache : DenseReencodeRootCache p) (pos : Nat) (c : DenseExpr p) :
    Option (DenseReencodeRootPlan p) × DenseReencodeRootCache p :=
  match cache[pos]? with
  | some plan => (plan, cache)
  | none =>
      let plan := denseBuildReencodeRootPlan c
      (plan, cache.insert pos plan)

def denseFindDomainCached (i : VarId) :
    List (Nat × DenseExpr p) → DenseReencodeRootCache p →
      Option (List (ZMod p)) × DenseReencodeRootCache p
  | [], cache => (none, cache)
  | c :: rest, cache =>
      if c.2.mentions i then
        let (plan, cache) := denseReencodeRootAt cache c.1 c.2
        match plan.bind (denseReencodeRootPlanLookup i) with
        | some roots => (some roots, cache)
        | none => denseFindDomainCached i rest cache
      else denseFindDomainCached i rest cache

def denseGroupDomsCached (es : List (Nat × DenseExpr p)) :
    List VarId → DenseReencodeRootCache p →
      Option (List (VarId × List (ZMod p))) × DenseReencodeRootCache p
  | [], cache => (some [], cache)
  | i :: rest, cache =>
      let (head, cache) := denseFindDomainCached i es cache
      let (tail, cache) := denseGroupDomsCached es rest cache
      match head, tail with
      | some d, some ds => (some ((i, d) :: ds), cache)
      | _, _ => (none, cache)

def denseCoveredIdxPos (idx : DenseCovIndex) (arr : Array (DenseExpr p))
    (xs : List VarId) : List (Nat × DenseExpr p) :=
  let uniq := ((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList
  (uniq.mergeSort (· ≤ ·)).filterMap (fun i =>
    if h : i < arr.size then
      if denseCoveredBy xs arr[i] then some (i, arr[i]) else none
    else none)

/-- Build the inverted index (`VarId`-keyed twin of `CoveredIndex.buildPruned`), skipping items
    with more than `maxVars` distinct variables. -/
def denseBuildPruned {α : Type} (varsOf : α → List VarId) (maxVars : Nat) (items : List α) :
    DenseCovIndex :=
  items.zipIdx.foldr (fun ai idx =>
    if (HashedDedup.hashedEraseDups (hash ·) (varsOf ai.1)).length ≤ maxVars then
      denseBuildStep varsOf ai idx
    else idx) ⟨∅, []⟩

/-- Register the `k` fresh bit variables `freshBase ++ "_0", …, freshBase ++ "_(k-1)"` into `reg`,
    in order. -/
def denseRegisterBits (reg : VarRegistry) (freshBase : String) (k : Nat) :
    VarRegistry × List VarId :=
  (List.range k).foldl
    (fun (acc : VarRegistry × List VarId) (j : Nat) =>
      let (r, bs) := acc
      let (r', i) := r.register ({ name := freshBase ++ "_" ++ toString j } : Variable)
      (r', bs ++ [i]))
    (reg, [])

/-- Construct the bits and the substitution map for a candidate group (proof-free — the checked
    certificate re-verifies everything). Registers fresh bits only on the single accepting path. -/
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

/-- Construct a candidate using the retained per-constraint root cache. -/
def denseBuildReencodeCached (reg : VarRegistry) (useIdx : Bool) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (cache : DenseReencodeRootCache p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × Option (List VarId × Std.HashMap VarId (DenseExpr p)) ×
      DenseReencodeRootCache p :=
  let planned := if useIdx then denseCoveredIdxPos csIdx arrCs xs
    else arrCs.toList.zipIdx.foldr
      (fun c acc => if denseCoveredBy xs c.1 then (c.2, c.1) :: acc else acc) []
  let es := planned.map Prod.snd
  let (doms?, cache) := denseGroupDomsCached planned xs cache
  match doms? with
  | none => (reg, none, cache)
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ 256 then
      if es.length == xs.length && es.all (fun c => c.vars.eraseDups.length == 1)
          && xs.length ≤ Nat.clog 2 boxSize then
        (reg, none, cache)
      else
      let survs := denseGroupSurvivorsE es doms
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let (reg1, bits) := denseRegisterBits reg freshBase k
          let patts := denseAssignments (denseBitBox bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          (reg1,
            some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (denseInterpPoly pz x).fold)))),
            cache)
        else (reg, none, cache)
      else (reg, none, cache)
    else (reg, none, cache)

/-- Degree pre-gate (untrusted): rewrite only the items sharing a variable with the group and fire
    when a rewritten item already exceeds the bound. -/
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

/-- One checked re-encoding step (identity if construction or the certificate fails). Applies the
    gates in order, minting fresh bits and rewriting `d` only on full acceptance. -/
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
    -- fresh-name collision: `denseCheckReencode` would reject after the full freshness scan anyway
    (reg, d, [], csIdx, arrCs, varSet)
  else
  match denseBuildReencode reg useIdx csIdx arrCs xs freshBase with
  | (reg1, none) => (reg1, d, [], csIdx, arrCs, varSet)
  | (reg1, some (bits, hm)) =>
    -- Degree pre-gate: reject early what the final `withinDegreeB` gate would reject anyway.
    if denseDegPreReject b d xs bits hm then (reg1, d, [], csIdx, arrCs, varSet)
    else
    if xs.all (fun x => varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOut d xs bits hm
      if ro.withinDegreeB b then
        -- `d` changed: rebuild the index and variable set for `ro`.
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

structure DenseReencodeCacheState (p : ℕ) where
  csIdx : DenseCovIndex
  arrCs : Array (DenseExpr p)
  rootCache : DenseReencodeRootCache p
  varSet : Std.HashSet VarId

def denseReencodeStepCached (b : DegreeBound) (useIdx : Bool)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (state : DenseReencodeCacheState p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p × DenseReencodeCacheState p :=
  if xs.all (fun x => reg.isInput x) then
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => state.varSet.contains i
      | none => false) then
    (reg, d, [], state)
  else
  match denseBuildReencodeCached reg useIdx state.csIdx state.arrCs state.rootCache xs freshBase with
  | (reg1, none, rootCache) => (reg1, d, [], { state with rootCache })
  | (reg1, some (bits, hm), rootCache) =>
    let state := { state with rootCache }
    if denseDegPreReject b d xs bits hm then (reg1, d, [], state)
    else
    if xs.all (fun x => state.varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOut d xs bits hm
      if ro.withinDegreeB b then
        (reg1, ro,
         bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)),
         ⟨(if useIdx then denseBuildPruned DenseExpr.vars 8 ro.algebraicConstraints else ⟨∅, []⟩),
          ro.algebraicConstraints.toArray, ∅, Std.HashSet.ofList ro.occ⟩)
      else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
  else (reg, d, [], state)

/-- Process the candidate groups sequentially, threading the registry, index, and variable set. -/
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

def denseReencodeLoopCached (b : DegreeBound) (useIdx : Bool) :
    List (List VarId) → Nat → VarRegistry → DenseConstraintSystem p →
      DenseReencodeCacheState p →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p
  | [], _, reg, d, _ => (reg, d, [])
  | xs :: rest, idx, reg, d, state =>
    let (reg1, d1, derivs1, state1) :=
      denseReencodeStepCached b useIdx reg d state xs
        (s!"rnc{d.algebraicConstraints.length}_{d.busInteractions.length}_{idx}")
    let (reg2, d2, derivs2) :=
      denseReencodeLoopCached b useIdx rest (idx + 1) reg1 d1 state1
    (reg2, d2, derivs1 ++ derivs2)

/-- Witness re-encoding. When a group of variables `xs` is so constrained that only a few value
    combinations survive, mint `Nat.clog 2 #survivors` fresh boolean bits, rewrite each group
    variable as an interpolation polynomial over the bits, drop the now-covered constraints, and add
    booleanity constraints — e.g. a group with 3 surviving combinations becomes 2 bits, cutting the
    variable count. The transform is shaped for `DenseVerifiedPassW.ofExtending`; `facts` is unused
    (reencode is fact-free). -/
def denseReencodeF (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bsem : BusSemantics p) (_facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    -- Each constraint's deduped variable list, shared between `svSet` and `targets`.
    let csVs := d.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
    let svSet : Std.HashSet VarId := csVs.foldl (init := ∅) fun s vs =>
      match vs with
      | [x] => s.insert x
      | _ => s
    let targets := dedupHash (csVs.filterMap (fun vs =>
      if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
        -- Sort by the resolved `Variable`'s order: `denseReencodeLoop` below is a greedy,
        -- order-sensitive accept/reject sequence, so the group order determines the outcome.
        some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
      else none))
    let targetSlots := (targets.map List.length).sum
    let targetVars := targets.foldl
      (fun vars xs => xs.foldl (fun vars x => vars.insert x) vars)
      (∅ : Std.HashSet VarId)
    let useRootCache := 64 ≤ targetSlots - targetVars.size
    let useIdx := 8192 ≤ d.algebraicConstraints.length
    if useIdx ∧ useRootCache then
      denseReencodeLoopCached b useIdx targets 0 reg d
        ⟨denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints,
         d.algebraicConstraints.toArray, ∅, Std.HashSet.ofList d.occ⟩
    else
      denseReencodeLoop b useIdx targets 0 reg d
        (if useIdx then denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints else ⟨∅, []⟩)
        d.algebraicConstraints.toArray
        (Std.HashSet.ofList d.occ)
  else (reg, d, [])

end ApcOptimizer.Dense
