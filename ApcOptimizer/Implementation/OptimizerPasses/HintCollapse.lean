import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.HintCollapse
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.ExprOps
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Collapsing a multi-limb reciprocal-witness group to one hint — dense `VarId` port (impl-only)

Dense, `VarId`-native transliteration of the *runtime* definitions of
`OptimizerPasses/OldVariableBased/HintCollapse.lean` (`Variable`/`Expression`-based): the
single-variable linear peel (`extractLinear`/`peel`), the witness sum (`sumExpr`), the
once-in-the-target occurrence test (`occursOnlyInTarget`), the byte-bound coefficient recognizers
for both collapse shapes (`coeffVar`/`coeffsByteOK`, `diffVarsOf`/`sqCoeffsOK`), the per-constraint
witness-set scan (`witnessesOf`), the two collapse attempts (`tryOne`/`tryOneSq`) and the scanning
driver (`tryList`), and the pass itself (`hintCollapsePass`). This is **impl-only**: `collapse_correct`
and every theorem in the spec file are proof-side and left for the prover — nothing here states or
proves anything beyond the runtime computation. The spec's `reassign`/`assocReassign` and the
`hagree`/`hEeq`/`hbyte`/… certificates are **not** ported: they are arguments to the (Prop-valued)
`collapse_correct` theorem application, never inspected by `tryOne`/`tryOneSq`'s *data* result
(`out`/`derivs`, which the spec's own `PassResult` bundles as the unification target of that
application's conclusion type) — they carry zero runtime content to transliterate.

## Shape: a registry-extending native transform

Like `Reencode`, this pass mints a fresh derived witness (the reciprocal-hint `inv`), so it is
shaped for the registry-extending builder — the prover wires it with
`DenseVerifiedPassW.ofNativeExtending (denseHintCollapseF pw) …`
(`transform : VarRegistry → (bs) → BusFacts p bs → DenseConstraintSystem p → VarRegistry ×
DenseConstraintSystem p × DenseDerivations p`, `Reencode.lean`'s own shape). Still out of scope:
the correctness theorems and the `ofNativeExtending` call itself.

## Where the fresh variable is minted, and the freshness-decision mechanism

The spec constructs `inv` (`OldVariableBased/HintCollapse.lean:788`/`876`) **unconditionally**, at
the very top of `tryOne`/`tryOneSq`, before any of the `by_cases hchk` gates — cheaply (a `headD`
field read and a string append), so its cost is paid regardless of whether the candidate is
eventually accepted. `denseTryOne`/`denseTryOneSq` mirror this positioning exactly: the candidate
`Variable` (`⟨"hcinv#" ++ …, none⟩` / `⟨"hcsq#" ++ …, none⟩`, `powdrId? := none` literally, matching
`hinv_id`) is constructed first, unconditionally, from `reg.resolve (D.headD default)` — the *same*
full `Variable` the spec constructs, since resolving the head witness's `VarId` recovers exactly the
`Variable` that was originally registered for it (the `D = []` fallback, never observed downstream
because `2 ≤ D.length` fails first — see below — makes any placeholder harmless, exactly as the
spec's own `⟨"_", none⟩` fallback is never observed).

The spec's own freshness gate is a **generic** `decide (inv ∉ cs.vars)` — `ConstraintSystem.vars` is
an *un-deduplicated, un-indexed* `List Variable` recomputed fresh by `flatMap` on every call (no
`Std.HashSet`/registry is threaded for this specific check anywhere in the spec file), tested by
list membership. `Reencode.lean`'s "freshness prefilter" is the established mechanism for a
name-collision test in the dense representation without resolving every occurrence back to a
`Variable`: `reg.idOf?` on the *candidate* `Variable` (an `O(1)` hash lookup — if the candidate name
was never registered, it certainly isn't a system member) composed with a membership test against
the *dense* analogue of `cs.vars`, which is exactly `DenseConstraintSystem.occ` (`Measure.lean`, the
same un-deduplicated `flatMap` list the spec's `ConstraintSystem.vars` decodes to). `denseIsFresh`
below reproduces this: `reg.idOf? invVar` then, on a hit, `d.occ.contains i` — a linear scan over the
same list, at the same call frequency, with `VarId` equality (cheap `Nat` compare) standing in for
`Variable` equality (name-string compare), which is exactly the sanctioned "Variable equality/hash →
VarId equality/hash" substitution — **not** a persistent `Std.HashSet` (that would be a genuine
algorithmic addition the spec's own `tryOne`/`tryOneSq` do not make: no such set is built or threaded
anywhere for this check in the reference).

The fresh `VarId` is **registered only on the accepting branch** (the innermost `then` of
`denseTryOne`/`denseTryOneSq`'s gate cascade, right before constructing `out`/`derivs`), not on every
`tryOne`/`tryOneSq` attempt. This mirrors `Reencode.lean`'s own precedent (bits are minted only on
`buildReencode`'s narrow accepting path, not by every `reencodeStep` call) rather than the spec
`HintCollapse`'s literal *construction* point (unconditional, every call): since `Variable` carries no
persistent identity in the spec's `Variable`-based runtime, constructing-and-discarding one on every
rejected candidate is free there, but registering-and-discarding one on every rejected candidate in
the dense registry is not (`Array.push`/`HashMap.insert` per attempt, and — more importantly — it
would inflate every subsequent `VarId`-indexed structure in this and later passes for the run's
remaining lifetime). Both choices produce *identical* observable output (an unreferenced registered
`VarId` decodes to nothing and is invisible to every downstream decision, exactly as an unreferenced
spec `Variable` is); registering lazily is the non-regressing, harmlessly-equivalent representation
the Addendum favours ("do not add … expensive machinery merely to reproduce the reference", read in
reverse: do not *add* reference-only overhead the dense representation doesn't need either).

## One deliberate micro-hoist, flagged

The spec's `tryOne`/`tryOneSq`, written as a `by_cases hchk : (<bool chain>) = true` followed by a
proof term, textually re-invokes `peel D E` **up to six times** on an accepting candidate: up to four
times inside `hchk`'s conjunct chain (`coeffsByteOK`/`sqCoeffsOK` touches `.1`; the witness-freeness
and powdr-ID conjuncts each touch `.2`; the final box-fit conjunct touches `.1.length` again — each a
fresh, unshared textual occurrence, since none of this is `let`-bound in the spec) and twice more at
the `collapse_correct` call site (`sumExpr (peel D E).1` and `(peel D E).2` passed as separate
explicit — non-`Prop` — arguments). `denseTryOne`/`denseTryOneSq` below hoist `densePeel D E` into a
single `let (coeffs, rest) := …`, computed **only after** confirming `2 ≤ D.length` (so the common
`D.length < 2` case — the spec's own docstring calls out that this is "the vast majority" — still
short-circuits with *zero* `peel` cost, exactly matching the spec's early exit) and reused for every
later gate and for the output/derivation construction. This changes no decision, no gate order, and
no early exit — it only removes redundant re-computation of a pure, already-linear-in-`|E|` helper
that the spec's proof-term style (not its algorithm) forces to repeat. Flagged per instructions as
the one place this port is not a bare textual mirror.

## Reuse

`denseBuild` (`DigitFold.lean`) is the dense fact-derived bounds map — the `Std.HashMap VarId Nat`
that corresponds value-for-value, under `resolve`, to `(BoundsMap.build facts).map`; it plays the
role of `Bm.map` (the spec threads the `BoundsMap` wrapper only for its bundled soundness proof,
which this chunk does not carry). `DenseExpr.fold` (`ExprOps.lean`) mirrors `Expression.fold`
(recognizing a coefficient's normal form) and `DenseExpr.mentions` (`SubstMap.lean`) mirrors
`Expression.mentions` (the allocation-free occurrence test `occursOnlyInTarget` needs). `busVars`/
`cnt` are *not* dense twins of anything reusable — the spec builds them inline, once per pass
invocation, from nested `List.foldl`s directly over `Expression.vars`/`.dedup`; `denseHintCollapseF`
below reproduces the identical inline folds over `DenseExpr.vars`. `busVars`/`cnt` are dropped from
`denseTryOne`/`denseTryOneSq`'s parameter lists: the spec's own `tryOne`/`tryOneSq` take them (and
`hE`/`hD`) only to *type* the proof hypothesis `hD : D = witnessesOf cs busVars cnt E` — they are
never read by the runtime body, so there is nothing to transliterate for them at that level; they
stay exactly where they're actually used, in `witnessesOf`/`tryList`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Splitting off the linear part in one variable -/

/-- Split `E` as `coeff · wv + rest` in the single variable `wv`. Mirrors `extractLinear`
    (`OldVariableBased/HintCollapse.lean:39`). -/
def denseExtractLinear (wv : VarId) : DenseExpr p → DenseExpr p × DenseExpr p
  | .const c => (.const 0, .const c)
  | .var x => if x = wv then (.const 1, .const 0) else (.const 0, .var x)
  | .add e1 e2 =>
      let (c1, r1) := denseExtractLinear wv e1
      let (c2, r2) := denseExtractLinear wv e2
      (.add c1 c2, .add r1 r2)
  | .mul e1 e2 =>
      if wv ∈ e1.vars then
        let (c1, r1) := denseExtractLinear wv e1
        (.mul c1 e2, .mul r1 e2)
      else
        let (c2, r2) := denseExtractLinear wv e2
        (.mul e1 c2, .mul e1 r2)

/-- Peel every variable of `ds` off `E` in turn, returning the list of coefficients (one per `ds`
    entry) and the final remainder. Mirrors `peel` (`:71`). -/
def densePeel : List VarId → DenseExpr p → List (DenseExpr p) × DenseExpr p
  | [], E => ([], E)
  | wv :: ds, E =>
      let (c, r) := denseExtractLinear wv E
      let (cs, rest) := densePeel ds r
      (c :: cs, rest)

/-! ## Sum of expressions -/

/-- The expression `Σ l`. Mirrors `sumExpr` (`:126`). -/
def denseSumExpr (l : List (DenseExpr p)) : DenseExpr p := l.foldr DenseExpr.add (DenseExpr.const 0)

/-! ## Detection: a witness variable occurring only in the target constraint -/

/-- A witness variable `v` occurs (in the whole system) only in the target constraint `E`. Mirrors
    `occursOnlyInTarget` (`:569`), reusing `DenseExpr.mentions` (`SubstMap.lean`) in place of
    `Expression.mentions`. -/
def denseOccursOnlyInTarget (d : DenseConstraintSystem p) (E : DenseExpr p) (v : VarId) : Bool :=
  (d.algebraicConstraints.all (fun c => decide (c = E) || !(c.mentions v))) &&
  (d.busInteractions.all (fun bi =>
    !(bi.multiplicity.mentions v) && bi.payload.all (fun e => !(e.mentions v))))

/-! ## Plain-sum coefficient recognizer -/

/-- The single variable a coefficient reduces to: a bare `var a`, or `a·1` / `1·a`. Mirrors
    `coeffVar` (`:595`). -/
def denseCoeffVar : DenseExpr p → Option VarId
  | .var a => some a
  | .mul (.var a) (.const c) => if c = 1 then some a else none
  | .mul (.const c) (.var a) => if c = 1 then some a else none
  | _ => none

/-- Each coefficient's `fold` reduces to a single `≤ 256`-bounded, `D`-free, input-column variable.
    Mirrors `coeffsByteOK` (`:617`), reusing `DenseExpr.fold` (`ExprOps.lean`) and `denseBuild`
    (`DigitFold.lean`, playing the role of the spec's `Bm.map`) and `reg.isInput` (`Bridge.lean`) in
    place of `x.powdrId?.isSome`. -/
def denseCoeffsByteOK (reg : VarRegistry) (B : Std.HashMap VarId Nat) (D : List VarId) :
    List (DenseExpr p) → Bool
  | [] => true
  | c :: cs =>
    (match denseCoeffVar c.fold with
     | some a => (match B[a]? with | some b => decide (b ≤ 256) | none => false)
     | none => false) &&
    D.all (fun wv => decide (wv ∉ c.vars)) &&
    c.vars.all (fun x => reg.isInput x) &&
    denseCoeffsByteOK reg B D cs

/-! ## Sum-of-squares (difference) coefficient recognizer -/

/-- Recognize a `fold`-normalized difference `a - b` of two variables. Mirrors `diffVarsOf`
    (`:659`). -/
def denseDiffVarsOf : DenseExpr p → Option (VarId × VarId)
  | .add (.var a) (.mul (.const c) (.var b)) => if c = -1 then some (a, b) else none
  | _ => none

/-- Each coefficient's `fold` is a difference of two `≤ 256`-bounded, `D`-free, input-column
    variables. Mirrors `sqCoeffsOK` (`:678`). -/
def denseSqCoeffsOK (reg : VarRegistry) (B : Std.HashMap VarId Nat) (D : List VarId) :
    List (DenseExpr p) → Bool
  | [] => true
  | c :: cs =>
    (match denseDiffVarsOf c.fold with
     | some (a, b) =>
         (match B[a]? with | some ba => decide (ba ≤ 256) | none => false) &&
         (match B[b]? with | some bb => decide (bb ≤ 256) | none => false)
     | none => false) &&
    D.all (fun wv => decide (wv ∉ c.vars)) &&
    c.vars.all (fun x => reg.isInput x) &&
    denseSqCoeffsOK reg B D cs

/-! ## The once-in-`E` witness set -/

/-- The witnesses of `E`: variables occurring (in the whole system) only in `E`, prefiltered by a
    once-per-invocation constraint-occurrence counter (`cnt`) and a bus-occurring-variable set
    (`busVars`) so the expensive full-system `denseOccursOnlyInTarget` scan runs only for the rare
    single-occurrence candidates. Mirrors `witnessesOf` (`:770`); `E.vars.dedup` mirrors the spec's
    plain (non-hashed) `.dedup` verbatim — `witnessesOf` itself does not use the hashed dedup
    machinery. -/
def denseWitnessesOf (d : DenseConstraintSystem p) (busVars : Std.HashSet VarId)
    (cnt : Std.HashMap VarId Nat) (E : DenseExpr p) : List VarId :=
  E.vars.dedup.filter (fun v => !busVars.contains v && cnt.getD v 0 == 1
    && denseOccursOnlyInTarget d E v)

/-! ## Freshness: no collision with the current system (the `Reencode` prefilter mechanism) -/

/-- Is `v` absent from the current system? Mirrors the spec's `decide (inv ∉ cs.vars)`, using the
    `Reencode.lean` freshness-prefilter mechanism: a candidate never registered at all cannot be a
    system member (`none` case); if it *was* registered, membership in `d.occ` (the dense analogue of
    `ConstraintSystem.vars`, `Measure.lean`) is exactly the spec's list-membership test, transported
    through the registry bijection (`VarId` equality standing in for `Variable` equality — see the
    module header; **not** a persistent `Std.HashSet`, which the spec's own check never builds). -/
def denseIsFresh (reg : VarRegistry) (d : DenseConstraintSystem p) (v : Variable) : Bool :=
  match reg.idOf? v with
  | some i => !d.occ.contains i
  | none => true

/-! ## The plain-sum collapse attempt (`is-zero`/`seqz`) -/

/-- Attempt the plain-sum collapse with target constraint `E` and its precomputed witness set `D`.
    Mirrors `tryOne` (`:782`); the fresh witness `inv` is minted (registered) only on the accepting
    branch (see the module header). `busVars`/`cnt`/`hE`/`hD` are dropped: the spec's own `tryOne`
    body never reads them (they only type the dropped proof hypothesis `hD`). -/
def denseTryOne (reg : VarRegistry) (d : DenseConstraintSystem p) (Bm : Std.HashMap VarId Nat)
    (E : DenseExpr p) (D : List VarId) :
    Option (VarRegistry × DenseConstraintSystem p × DenseDerivations p) :=
  let invVar : Variable := ⟨"hcinv#" ++ (reg.resolve (D.headD default)).name, none⟩
  if 2 ≤ D.length then
    let (coeffs, rest) := densePeel D E
    if denseCoeffsByteOK reg Bm D coeffs then
    if D.all (fun wv => decide (wv ∉ rest.vars)) then
    if rest.vars.all (fun x => reg.isInput x) then
    if denseIsFresh reg d invVar then
    if coeffs.length * 256 ≤ p then
      let (reg1, invId) := reg.register invVar
      let denom := denseSumExpr coeffs
      let E' : DenseExpr p := .add (.mul denom (.var invId)) rest
      some (reg1,
        { d with algebraicConstraints :=
            d.algebraicConstraints.map (fun c => if c = E then E' else c) },
        [(invId, DenseComputationMethod.quotientOrZero (.mul (.const (-1)) rest) denom)])
    else none
    else none
    else none
    else none
    else none
  else none

/-! ## The sum-of-squares collapse attempt (`is-equal`) -/

/-- Attempt the sum-of-squares collapse. Mirrors `tryOneSq` (`:870`), sharing the module header's
    notes on freshness and the fresh witness's mint point. -/
def denseTryOneSq (reg : VarRegistry) (d : DenseConstraintSystem p) (Bm : Std.HashMap VarId Nat)
    (E : DenseExpr p) (D : List VarId) :
    Option (VarRegistry × DenseConstraintSystem p × DenseDerivations p) :=
  let invVar : Variable := ⟨"hcsq#" ++ (reg.resolve (D.headD default)).name, none⟩
  if 2 ≤ D.length then
    let (coeffs, rest) := densePeel D E
    if denseSqCoeffsOK reg Bm D coeffs then
    if D.all (fun wv => decide (wv ∉ rest.vars)) then
    if rest.vars.all (fun x => reg.isInput x) then
    if denseIsFresh reg d invVar then
    if coeffs.length * 65536 ≤ p then
      let (reg1, invId) := reg.register invVar
      let denom := denseSumExpr (coeffs.map (fun c => DenseExpr.mul c c))
      let E' : DenseExpr p := .add (.mul denom (.var invId)) rest
      some (reg1,
        { d with algebraicConstraints :=
            d.algebraicConstraints.map (fun c => if c = E then E' else c) },
        [(invId, DenseComputationMethod.quotientOrZero (.mul (.const (-1)) rest) denom)])
    else none
    else none
    else none
    else none
    else none
  else none

/-! ## The scanning driver -/

/-- Scan a constraint sublist for the first collapsible target, trying both the plain-sum and the
    sum-of-squares shape on each constraint, sharing the once-per-constraint witness set `D`. Mirrors
    `tryList` (`:981`); `hE`/`hmem` are dropped (proof-only, see the module header). -/
def denseTryList (reg : VarRegistry) (d : DenseConstraintSystem p) (Bm : Std.HashMap VarId Nat)
    (busVars : Std.HashSet VarId) (cnt : Std.HashMap VarId Nat) :
    List (DenseExpr p) → Option (VarRegistry × DenseConstraintSystem p × DenseDerivations p)
  | [] => none
  | E :: rest =>
    let D := denseWitnessesOf d busVars cnt E
    match denseTryOne reg d Bm E D with
    | some r => some r
    | none =>
      match denseTryOneSq reg d Bm E D with
      | some r => some r
      | none => denseTryList reg d Bm busVars cnt rest

/-! ## The pass, as a registry-extending native transform -/

/-- The hint-collapse transform, shaped for `DenseVerifiedPassW.ofNativeExtending` (the prover wires
    it with `DenseVerifiedPassW.ofNativeExtending (denseHintCollapseF pw) …`). Mirrors
    `hintCollapsePass` (`:1003`): identity when `p` isn't (witnessed) prime, else builds the bounds
    map (`denseBuild`, once), the bus-occurring variable set and the constraint-occurrence counter
    (both inline folds over `DenseExpr.vars`, once, exactly as the spec builds them), and scans. -/
def denseHintCollapseF (pw : PrimeWitness p) (reg : VarRegistry) (bsem : BusSemantics p)
    (facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    let Bm : Std.HashMap VarId Nat := denseBuild bsem facts d.busInteractions
    let busVars : Std.HashSet VarId := d.busInteractions.foldl (init := ∅) fun s bi =>
      bi.payload.foldl (fun s e => e.vars.foldl (·.insert ·) s)
        (bi.multiplicity.vars.foldl (·.insert ·) s)
    let cnt : Std.HashMap VarId Nat := d.algebraicConstraints.foldl (init := ∅) fun m c =>
      c.vars.dedup.foldl (fun m v => m.insert v (m.getD v 0 + 1)) m
    (denseTryList reg d Bm busVars cnt d.algebraicConstraints).getD (reg, d, [])
  else (reg, d, [])

end ApcOptimizer.Dense
