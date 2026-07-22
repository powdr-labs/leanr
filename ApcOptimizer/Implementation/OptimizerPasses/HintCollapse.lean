import ApcOptimizer.Implementation.OptimizerPasses.FactBounds
import ApcOptimizer.Implementation.OptimizerPasses.ExprOps
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Collapsing a multi-limb reciprocal-witness group to one hint

Runtime computation only; correctness (`collapse_correct`) lives in `Proofs/HintCollapse.lean`. Shaped
for `DenseVerifiedPassW.ofExtending`, since it mints a fresh reciprocal-hint witness (like
`Reencode.lean`). The fresh `VarId` is registered only on the accepting branch. -/

/-! ## Representation-independent field-sum lemmas (consumed by `Proofs/HintCollapse.lean`) -/

section RehomedHintCollapse
variable {p : ℕ}

/-- Wrap-free: with the value-sum below `p`, the field sum's `.val` is the natural-number sum. -/
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

/-- Byte-bounded field elements summing to `0` with the value-sum below `p` are all `0`. -/
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
  · have hd : x - y = -((y.val - x.val : ℕ) : ZMod p) := by
      have hcast : ((y.val - x.val : ℕ) : ZMod p) = y - x := by
        rw [Nat.cast_sub (le_of_lt hlt), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [hcast]; ring
    have hb : y.val - x.val ≤ 255 := by omega
    have hsq : (y.val - x.val) * (y.val - x.val) ≤ 255 * 255 := Nat.mul_le_mul hb hb
    rw [hd, neg_mul_neg, ← Nat.cast_mul, ZMod.val_natCast_of_lt (by omega)]; omega
  · have hd : x - y = ((x.val - y.val : ℕ) : ZMod p) := by
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

/-- Each coefficient's `fold` reduces to one `≤ 256`-bounded, `D`-free, input-column variable. -/
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

/-- The witnesses of `E`: variables occurring (in the whole system) only in `E`. The `cnt` /
    `busVars` prefilters keep the expensive full-system `denseOccursOnlyInTarget` scan to the rare
    single-occurrence candidates. -/
def denseWitnessesOf (d : DenseConstraintSystem p) (busVars : Std.HashSet VarId)
    (cnt : Std.HashMap VarId Nat) (E : DenseExpr p) : List VarId :=
  E.vars.dedup.filter (fun v => !busVars.contains v && cnt.getD v 0 == 1
    && denseOccursOnlyInTarget d E v)

/-! ## Freshness: no collision with the current system -/

/-- Is `v` absent from the current system? An unregistered candidate cannot be a member (`none`);
    otherwise membership in `d.occ` (`Measure.lean`) is checked by `VarId`. -/
def denseIsFresh (reg : VarRegistry) (d : DenseConstraintSystem p) (v : Variable) : Bool :=
  match reg.idOf? v with
  | some i => !d.occ.contains i
  | none => true

/-! ## The plain-sum collapse attempt (`is-zero`/`seqz`) -/

/-- Attempt the plain-sum collapse for target `E` with witness set `D`. The fresh witness `inv` is
    registered only on the accepting branch. -/
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

/-- Attempt the sum-of-squares collapse (the `is-equal` shape); shares `denseTryOne`'s mint
    discipline. -/
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

/-- Collapses a group of witnesses that each occur in a single constraint into one reciprocal hint:
    `Σ aᵢ·wᵢ + rest = 0` (byte-bounded `wᵢ`, each occurring only here) becomes `denom·inv + rest`
    with `denom = Σ aᵢ` and one fresh `inv := QuotientOrZero(−rest, denom)` (the `seqz`/`is-zero`
    idiom; a sum-of-squares variant handles `is-equal`). Identity unless `p` is witnessed prime. -/
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
