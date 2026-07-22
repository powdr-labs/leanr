import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.ExprOps
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Collapsing a multi-limb reciprocal-witness group to one hint

This file defines the single-variable linear peel (`denseExtractLinear`/`densePeel`), the witness
sum (`denseSumExpr`), the once-in-the-target occurrence test (`denseOccursOnlyInTarget`), the
byte-bound coefficient recognizers for both collapse shapes (`denseCoeffVar`/`denseCoeffsByteOK`,
`denseDiffVarsOf`/`denseSqCoeffsOK`), the per-constraint witness-set scan (`denseWitnessesOf`), the
two collapse attempts (`denseTryOne`/`denseTryOneSq`) and the scanning driver (`denseTryList`), and
the pass itself (`denseHintCollapseF`). Correctness (`collapse_correct`) is proved in
`HintCollapseProof.lean`; nothing here states or proves anything beyond the runtime computation.

## Shape: a registry-extending transform

Like `Reencode`, this pass mints a fresh derived witness (the reciprocal-hint `inv`), so it is
shaped for the registry-extending builder — the prover wires it with
`DenseVerifiedPassW.ofExtending (denseHintCollapseF pw) …`
(`transform : VarRegistry → (bs) → BusFacts p bs → DenseConstraintSystem p → VarRegistry ×
DenseConstraintSystem p × DenseDerivations p`, `Reencode.lean`'s own shape). Still out of scope:
the correctness theorems and the `ofExtending` call itself.

## Where the fresh variable is minted, and the freshness-decision mechanism

`denseTryOne`/`denseTryOneSq` construct the candidate `Variable` (`⟨"hcinv#" ++ …, none⟩` /
`⟨"hcsq#" ++ …, none⟩`, `powdrId? := none`) **unconditionally**, at the very top, before any of the
gates — cheaply (a `headD` field read and a string append), so its cost is paid regardless of
whether the candidate is eventually accepted. It is built from `reg.resolve (D.headD default)`; the
`D = []` fallback is never observed downstream, since `2 ≤ D.length` fails first (see below), so any
placeholder there is harmless.

`denseIsFresh` tests whether the candidate collides with the current system without resolving every
occurrence back to a `Variable`: `reg.idOf?` on the candidate (an `O(1)` hash lookup — if the name
was never registered, it certainly isn't a system member) composed, on a hit, with a membership test
against `DenseConstraintSystem.occ` (`Measure.lean`) — a linear scan with `VarId` equality (cheap
`Nat` compare) in place of `Variable` equality (name-string compare).

The fresh `VarId` is **registered only on the accepting branch** (the innermost `then` of
`denseTryOne`/`denseTryOneSq`'s gate cascade, right before constructing `out`/`derivs`), not on
every attempt — the same precedent as `Reencode.lean` (bits are minted only on `buildReencode`'s
narrow accepting path). Registering-and-discarding a `VarId` on every rejected candidate would cost
an `Array.push`/`HashMap.insert` per attempt and — more importantly — inflate every subsequent
`VarId`-indexed structure in this and later passes for the run's remaining lifetime. An unreferenced
registered `VarId` decodes to nothing and is invisible to every downstream decision, so registering
lazily changes no observable output.

## Peel is hoisted once

`denseTryOne`/`denseTryOneSq` hoist `densePeel D E` into a single `let (coeffs, rest) := …`,
computed **only after** confirming `2 ≤ D.length` (so the common `D.length < 2` case short-circuits
with *zero* `peel` cost) and reused for every later gate and for the output/derivation construction.

## Reuse

`denseBuild` (`DigitFold.lean`) is the dense fact-derived bounds map (`Std.HashMap VarId Nat`).
`DenseExpr.fold` (`ExprOps.lean`) recognizes a coefficient's normal form, and `DenseExpr.mentions`
(`SubstMap.lean`) is the allocation-free occurrence test `denseOccursOnlyInTarget` needs. `busVars`/
`cnt` are built inline, once per pass invocation, as nested `List.foldl`s directly over
`DenseExpr.vars`/`.dedup`. `busVars`/`cnt` are dropped from `denseTryOne`/`denseTryOneSq`'s parameter
lists, since the runtime body never reads them; they stay exactly where they're actually used, in
`denseWitnessesOf`/`denseTryList`. -/

/-! ## Representation-independent field-sum lemmas

`sum_val_eq` / `sum_zero_all_zero` / `sq_diff_val_lt` are `Nat`/`ZMod`-only wrap-free-sum lemmas,
kept here so the dense proof (`HintCollapseProof.lean`) can consume them. -/

section RehomedHintCollapse
variable {p : ℕ}

/-- If a list of field elements each has `.val < p` and their `.val`s sum to `< p`, the field sum's
    `.val` equals the natural-number sum (no wraparound). -/
theorem sum_val_eq (hp : 0 < p) :
    ∀ (L : List (ZMod p)), (L.map (fun x => x.val)).sum < p →
      L.sum.val = (L.map (fun x => x.val)).sum
  | [], _ => by simp
  | x :: rest, hfit => by
      haveI : NeZero p := ⟨hp.ne'⟩
      simp only [List.map_cons, List.sum_cons] at hfit ⊢
      have hrest : (rest.map (fun x => x.val)).sum < p := by omega
      have ih := sum_val_eq hp rest hrest
      have hadd : (x + rest.sum).val = x.val + rest.sum.val :=
        ZMod.val_add_of_lt (by rw [ih]; omega)
      rw [hadd, ih]

/-- Byte-bounded field elements summing (in the field) to `0`, with the value-sum below `p`, are all
    `0`. Used for the `Σ aᵢ = 0` completeness branch. -/
theorem sum_zero_all_zero (hp : 0 < p) (L : List (ZMod p))
    (hfit : (L.map (fun x => x.val)).sum < p) (h0 : L.sum = 0) :
    ∀ x ∈ L, x = 0 := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hval : (L.map (fun x => x.val)).sum = 0 := by
    have := sum_val_eq hp L hfit
    rw [h0] at this; simpa using this.symm
  intro x hx
  have hxval : x.val = 0 := by
    have : x.val ≤ (L.map (fun y => y.val)).sum :=
      List.single_le_sum (by intro _ _; exact Nat.zero_le _) _ (List.mem_map.2 ⟨x, hx, rfl⟩)
    omega
  exact (ZMod.val_eq_zero x).1 hxval

/-- The value of a squared difference of two byte-bounded field elements is `< 256²`. -/
theorem sq_diff_val_lt [NeZero p] (hp : 65536 ≤ p) (x y : ZMod p)
    (hx : x.val < 256) (hy : y.val < 256) : ((x - y) * (x - y)).val < 65536 := by
  rcases Nat.lt_or_ge x.val y.val with hlt | hge
  · -- x < y: x - y = -↑(y.val - x.val), squares to the same value
    have hd : x - y = -((y.val - x.val : ℕ) : ZMod p) := by
      have hcast : ((y.val - x.val : ℕ) : ZMod p) = y - x := by
        rw [Nat.cast_sub (le_of_lt hlt), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [hcast]; ring
    have hb : y.val - x.val ≤ 255 := by omega
    have hsq : (y.val - x.val) * (y.val - x.val) ≤ 255 * 255 := Nat.mul_le_mul hb hb
    rw [hd, neg_mul_neg, ← Nat.cast_mul, ZMod.val_natCast_of_lt (by omega)]; omega
  · -- x ≥ y: x - y = ↑(x.val - y.val)
    have hd : x - y = ((x.val - y.val : ℕ) : ZMod p) := by
      rw [Nat.cast_sub hge, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hb : x.val - y.val ≤ 255 := by omega
    have hsq : (x.val - y.val) * (x.val - y.val) ≤ 255 * 255 := Nat.mul_le_mul hb hb
    rw [hd, ← Nat.cast_mul, ZMod.val_natCast_of_lt (by omega)]; omega

end RehomedHintCollapse

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Splitting off the linear part in one variable -/

/-- Split `E` as `coeff · wv + rest` in the single variable `wv`. -/
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
    entry) and the final remainder. -/
def densePeel : List VarId → DenseExpr p → List (DenseExpr p) × DenseExpr p
  | [], E => ([], E)
  | wv :: ds, E =>
      let (c, r) := denseExtractLinear wv E
      let (cs, rest) := densePeel ds r
      (c :: cs, rest)

/-! ## Sum of expressions -/

/-- The expression `Σ l`. -/
def denseSumExpr (l : List (DenseExpr p)) : DenseExpr p := l.foldr DenseExpr.add (DenseExpr.const 0)

/-! ## Detection: a witness variable occurring only in the target constraint -/

/-- A witness variable `v` occurs (in the whole system) only in the target constraint `E`, using
    `DenseExpr.mentions` (`SubstMap.lean`). -/
def denseOccursOnlyInTarget (d : DenseConstraintSystem p) (E : DenseExpr p) (v : VarId) : Bool :=
  (d.algebraicConstraints.all (fun c => decide (c = E) || !(c.mentions v))) &&
  (d.busInteractions.all (fun bi =>
    !(bi.multiplicity.mentions v) && bi.payload.all (fun e => !(e.mentions v))))

/-! ## Plain-sum coefficient recognizer -/

/-- The single variable a coefficient reduces to: a bare `var a`, or `a·1` / `1·a`. -/
def denseCoeffVar : DenseExpr p → Option VarId
  | .var a => some a
  | .mul (.var a) (.const c) => if c = 1 then some a else none
  | .mul (.const c) (.var a) => if c = 1 then some a else none
  | _ => none

/-- Each coefficient's `fold` reduces to a single `≤ 256`-bounded, `D`-free, input-column variable,
    using `DenseExpr.fold` (`ExprOps.lean`), `denseBuild` (`DigitFold.lean`) for the bounds, and
    `reg.isInput` (`Bridge.lean`). -/
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

/-- Recognize a `fold`-normalized difference `a - b` of two variables. -/
def denseDiffVarsOf : DenseExpr p → Option (VarId × VarId)
  | .add (.var a) (.mul (.const c) (.var b)) => if c = -1 then some (a, b) else none
  | _ => none

/-- Each coefficient's `fold` is a difference of two `≤ 256`-bounded, `D`-free, input-column
    variables. -/
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
    single-occurrence candidates. `E.vars.dedup` is the plain (non-hashed) `.dedup` — this scan does
    not use the hashed dedup machinery. -/
def denseWitnessesOf (d : DenseConstraintSystem p) (busVars : Std.HashSet VarId)
    (cnt : Std.HashMap VarId Nat) (E : DenseExpr p) : List VarId :=
  E.vars.dedup.filter (fun v => !busVars.contains v && cnt.getD v 0 == 1
    && denseOccursOnlyInTarget d E v)

/-! ## Freshness: no collision with the current system (the `Reencode` prefilter mechanism) -/

/-- Is `v` absent from the current system? Uses the `Reencode.lean` freshness-prefilter mechanism: a
    candidate never registered at all cannot be a system member (`none` case); if it *was*
    registered, membership in `d.occ` (`Measure.lean`) is checked directly, with `VarId` equality in
    place of `Variable` equality (see the module header). -/
def denseIsFresh (reg : VarRegistry) (d : DenseConstraintSystem p) (v : Variable) : Bool :=
  match reg.idOf? v with
  | some i => !d.occ.contains i
  | none => true

/-! ## The plain-sum collapse attempt (`is-zero`/`seqz`) -/

/-- Attempt the plain-sum collapse with target constraint `E` and its precomputed witness set `D`.
    The fresh witness `inv` is minted (registered) only on the accepting branch (see the module
    header). -/
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

/-- Attempt the sum-of-squares collapse. See the module header for the notes on freshness and the
    fresh witness's mint point (shared with `denseTryOne`). -/
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
    sum-of-squares shape on each constraint, sharing the once-per-constraint witness set `D`. -/
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

/-! ## The pass, as a registry-extending transform -/

/-- The hint-collapse transform, shaped for `DenseVerifiedPassW.ofExtending` (wired with
    `DenseVerifiedPassW.ofExtending (denseHintCollapseF pw) …`): identity when `p` isn't (witnessed)
    prime, else builds the bounds map (`denseBuild`, once), the bus-occurring variable set and the
    constraint-occurrence counter (both inline folds over `DenseExpr.vars`, once), and scans. -/
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
