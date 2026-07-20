import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.CarryBranch

set_option autoImplicit false

/-! # Dense carry-branch resolution (Task 3)

Dense, `VarId`-native port of `carryBranchPass`. Gated on `p` prime, the pass rewrites every
algebraic constraint through `resolveExpr`, collapsing a product `f·g` to the factor that survives
whenever the other factor is *certified never-zero* by the fact-derived value bounds
(`BoundsMap.build facts`).

It is **fact-consuming**, so it is built with the DigitFold direct-`DensePassResult` construction
(threading the unchanged `BusFacts`). The fact-derived bounds map is the dense `Std.HashMap VarId Nat`
from `Dense/DigitFold.lean` (`denseBuild`), which corresponds value-for-value, under `resolve`, to
`(BoundsMap.build facts).map`. The interval certificate (`splitSumMax`/`intervalCert`/`neverZeroB`)
is coefficient-only, so its dense mirrors decode value-for-value; the recursive product collapse
(`resolveExpr`) decodes by structural induction. Only the algebraic constraints are rewritten (bus
interactions untouched), so the output commutation uses a per-constraint map lemma. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Decoding a per-constraint expression map -/

/-- Decoding distributes over a per-constraint expression rewrite that decodes pointwise (on the
    constraints, which are covered), leaving bus interactions untouched. -/
theorem VarRegistry.decodeCS_mapConstraints (reg : VarRegistry) (g : DenseExpr p → DenseExpr p)
    (g' : Expression p → Expression p) (d : DenseConstraintSystem p)
    (hg : ∀ e ∈ d.algebraicConstraints, reg.decodeExpr (g e) = g' (reg.decodeExpr e)) :
    reg.decodeCS { d with algebraicConstraints := d.algebraicConstraints.map g }
      = { reg.decodeCS d with
            algebraicConstraints := (reg.decodeCS d).algebraicConstraints.map g' } := by
  simp only [VarRegistry.decodeCS]
  congr 1
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun e he => hg e he)

/-! ## Dense two-sided interval certificate (coefficient-only, `VarId`-agnostic) -/

/-- Dense `splitSumMax` (see `splitSumMax`). -/
def denseSplitSumMax (B : Std.HashMap VarId Nat) :
    List (VarId × ZMod p) → Option (Nat × Nat)
  | [] => some (0, 0)
  | (v, a) :: rest =>
    match B[v]?, denseSplitSumMax B rest with
    | some bound, some acc =>
      if 1 ≤ bound then
        if a.val * (bound - 1) ≤ (-a).val * (bound - 1) then
          some (a.val * (bound - 1) + acc.1, acc.2)
        else
          some (acc.1, (-a).val * (bound - 1) + acc.2)
      else none
    | _, _ => none

/-- **`splitSumMax` commutes with decode** (given a value-correspondence `hbm` for the bounds maps,
    and all term ids valid). -/
theorem denseSplitSumMax_decode (reg : VarRegistry) {B : Std.HashMap VarId Nat}
    {specBM : Std.HashMap Variable Nat}
    (hbm : ∀ i, reg.Valid i → B[i]? = specBM[reg.resolve i]?) :
    ∀ (terms : List (VarId × ZMod p)), (∀ i ∈ terms.map Prod.fst, reg.Valid i) →
      splitSumMax specBM (terms.map (fun t => (reg.resolve t.1, t.2))) = denseSplitSumMax B terms := by
  intro terms
  induction terms with
  | nil => intro _; rfl
  | cons t rest ih =>
      intro hv
      obtain ⟨v, a⟩ := t
      have hvv : reg.Valid v := hv v (by simp)
      have hrestv : ∀ i ∈ rest.map Prod.fst, reg.Valid i := fun i hi => hv i (by simp [hi])
      simp only [List.map_cons, splitSumMax, denseSplitSumMax]
      rw [← hbm v hvv, ih hrestv]
      cases B[v]? <;> cases denseSplitSumMax B rest <;> rfl

/-- Dense `intervalCert` (see `intervalCert`). -/
def denseIntervalCert (B : Std.HashMap VarId Nat) (l : DenseLinExpr p) : Bool :=
  match denseSplitSumMax B l.terms with
  | none => false
  | some acc =>
    decide (acc.2 < l.const.val) && decide (l.const.val + acc.1 < p)

/-- **`intervalCert` commutes with decode.** -/
theorem denseIntervalCert_decode (reg : VarRegistry) {B : Std.HashMap VarId Nat}
    {specBM : Std.HashMap Variable Nat}
    (hbm : ∀ i, reg.Valid i → B[i]? = specBM[reg.resolve i]?)
    (l : DenseLinExpr p) (hl : ∀ i ∈ l.terms.map Prod.fst, reg.Valid i) :
    intervalCert specBM (reg.decodeLin l) = denseIntervalCert B l := by
  unfold intervalCert denseIntervalCert
  rw [show (reg.decodeLin l).terms = l.terms.map (fun t => (reg.resolve t.1, t.2)) from rfl,
    denseSplitSumMax_decode reg hbm l.terms hl]
  cases denseSplitSumMax B l.terms with
  | none => rfl
  | some acc => rfl

/-! ## Dense never-zero certificate -/

/-- Dense `neverZeroB` (see `neverZeroB`). -/
def denseNeverZeroB (B : Std.HashMap VarId Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | none => false
  | some l =>
    let n := l.norm
    (1 :: n.const⁻¹ :: n.terms.map (fun t => t.2⁻¹)).any (fun k =>
      denseIntervalCert B ((n.scale k).norm))

/-- **`neverZeroB` commutes with decode** for covered expressions. -/
theorem denseNeverZeroB_decode (reg : VarRegistry) {B : Std.HashMap VarId Nat}
    {specBM : Std.HashMap Variable Nat}
    (hbm : ∀ i, reg.Valid i → B[i]? = specBM[reg.resolve i]?)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    neverZeroB specBM (reg.decodeExpr e) = denseNeverZeroB B e := by
  unfold neverZeroB denseNeverZeroB
  rw [← reg.denseLinearize_decode e]
  cases hl : denseLinearize e with
  | none => rfl
  | some l =>
      have hlv := reg.denseLinearize_covered_terms hc hl
      have hnormv : ∀ i ∈ l.norm.terms.map Prod.fst, reg.Valid i :=
        fun i hi => hlv i (DenseLinExpr.norm_terms_fst l i hi)
      simp only [Option.map_some]
      rw [← reg.decodeLin_norm l hlv]
      have hlisteq :
          (1 :: (reg.decodeLin l.norm).const⁻¹ :: (reg.decodeLin l.norm).terms.map (fun t => t.2⁻¹))
            = (1 :: l.norm.const⁻¹ :: l.norm.terms.map (fun t => t.2⁻¹)) := by
        simp only [VarRegistry.decodeLin, List.map_map, Function.comp_def]
      rw [hlisteq]
      refine list_any_congr (fun k _ => ?_)
      have hsv : ∀ i ∈ (l.norm.scale k).terms.map Prod.fst, reg.Valid i := by
        intro i hi
        rw [DenseLinExpr.scale_terms_fst] at hi
        exact hnormv i hi
      have hsnv : ∀ i ∈ (l.norm.scale k).norm.terms.map Prod.fst, reg.Valid i :=
        fun i hi => hsv i (DenseLinExpr.norm_terms_fst _ i hi)
      rw [← reg.decodeLin_scale k l.norm, ← reg.decodeLin_norm (l.norm.scale k) hsv]
      exact denseIntervalCert_decode reg hbm (l.norm.scale k).norm hsnv

/-! ## Dense product-constraint resolution -/

/-- Dense `resolveExpr` (see `resolveExpr`). -/
def denseResolveExpr (B : Std.HashMap VarId Nat) : DenseExpr p → DenseExpr p
  | .mul f g =>
      if denseNeverZeroB B g then denseResolveExpr B f
      else if denseNeverZeroB B f then denseResolveExpr B g
      else .mul f g
  | e => e

/-- `resolveExpr` introduces no new variable (mirrors `resolveExpr_vars`). -/
theorem denseResolveExpr_vars (B : Std.HashMap VarId Nat) (e : DenseExpr p) :
    ∀ x ∈ (denseResolveExpr B e).vars, x ∈ e.vars := by
  induction e with
  | mul f g ihf ihg =>
      intro x hx
      simp only [denseResolveExpr] at hx
      simp only [DenseExpr.vars, List.mem_append]
      split_ifs at hx with h1 h2
      · exact Or.inl (ihf x hx)
      · exact Or.inr (ihg x hx)
      · simpa only [DenseExpr.vars, List.mem_append] using hx
  | const n => intro x hx; simpa only [denseResolveExpr] using hx
  | var y => intro x hx; simpa only [denseResolveExpr] using hx
  | add a b iha ihb => intro x hx; simpa only [denseResolveExpr] using hx

/-- **`resolveExpr` commutes with decode** for covered expressions. -/
theorem denseResolveExpr_decode (reg : VarRegistry) {B : Std.HashMap VarId Nat}
    {specBM : Std.HashMap Variable Nat}
    (hbm : ∀ i, reg.Valid i → B[i]? = specBM[reg.resolve i]?)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    reg.decodeExpr (denseResolveExpr B e) = resolveExpr specBM (reg.decodeExpr e) := by
  induction e with
  | mul f g ihf ihg =>
      obtain ⟨hcf, hcg⟩ := DenseExpr.coveredBy_mul.mp hc
      simp only [denseResolveExpr, VarRegistry.decodeExpr, resolveExpr,
        denseNeverZeroB_decode reg hbm g hcg, denseNeverZeroB_decode reg hbm f hcf]
      split_ifs with h1 h2
      · exact ihf hcf
      · exact ihg hcg
      · rfl
  | const n => rfl
  | var y => rfl
  | add a b iha ihb => rfl

/-! ## The dense transform and pass -/

/-- The dense carry-branch-resolution transform (gated on `p` prime). -/
def denseCarryBranchF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    { d with algebraicConstraints :=
        d.algebraicConstraints.map (denseResolveExpr (denseBuild bs facts d.busInteractions)) }
  else d

/-- The spec pass output, exposing the primality gate. -/
theorem carryBranchPass_out (pw : PrimeWitness p) (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    (carryBranchPass pw cs bs facts).out
      = if pw.isPrime = true then
          { cs with algebraicConstraints :=
              cs.algebraicConstraints.map (resolveExpr (BoundsMap.build (cs := cs) facts).map) }
        else cs := by
  unfold carryBranchPass
  by_cases h : pw.isPrime = true
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

theorem denseCarryBranchF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseCarryBranchF pw bs facts d).CoveredBy reg := by
  unfold denseCarryBranchF
  by_cases h : pw.isPrime = true
  · rw [if_pos h]
    refine ⟨fun e he => ?_, fun bi hbi => hcov.2 bi hbi⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact fun i hi =>
      hcov.1 e0 he0 i (denseResolveExpr_vars _ e0 i hi)
  · rw [if_neg h]; exact hcov

/-- The dense carry-branch-resolution pass. Fact-consuming; inherits `carryBranchPass`'s
    `PassCorrect` through the decode-commutation of its transform. -/
def denseCarryBranchPass (pw : PrimeWitness p) : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := denseCarryBranchF pw bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := denseCarryBranchF_covered pw reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := by
      show PassCorrect (reg.decodeCS d) (reg.decodeCS (denseCarryBranchF pw bs facts d))
        (reg.decodeDerivs ([] : DenseDerivations p)) bs
      have hbm : ∀ i, reg.Valid i → (denseBuild bs facts d.busInteractions)[i]?
          = (BoundsMap.build facts (cs := reg.decodeCS d) (bs := bs)).map[reg.resolve i]? := by
        intro i hi
        unfold denseBuild BoundsMap.build
        exact denseAddAll_decode facts reg d.busInteractions BoundsMap.empty ∅ hcov.2
          (fun _ h => h) (fun kk _ => by simp [BoundsMap.empty]) i hi
      have hout : reg.decodeCS (denseCarryBranchF pw bs facts d)
          = (carryBranchPass pw (reg.decodeCS d) bs facts).out := by
        rw [carryBranchPass_out]
        unfold denseCarryBranchF
        by_cases h : pw.isPrime = true
        · rw [if_pos h, if_pos h]
          exact reg.decodeCS_mapConstraints _ _ d
            (fun e he => denseResolveExpr_decode reg hbm e (hcov.1 e he))
        · rw [if_neg h, if_neg h]
      rw [show reg.decodeDerivs ([] : DenseDerivations p) = [] from rfl, hout]
      have hderiv : (carryBranchPass pw (reg.decodeCS d) bs facts).derivs = [] := by
        unfold carryBranchPass
        by_cases h : pw.isPrime = true
        · rw [dif_pos h]
        · rw [dif_neg h]
      have hc := (carryBranchPass pw (reg.decodeCS d) bs facts).correct
      rw [hderiv] at hc
      exact hc }

end ApcOptimizer.Dense
