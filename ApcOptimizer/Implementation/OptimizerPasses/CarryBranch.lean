import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense carry-branch resolution (runtime). Pass and `DensePassCorrect` proof in
`Proofs/CarryBranch.lean`; bounds map via `denseBuild` (`DigitFold.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense two-sided interval certificate (coefficient-only, `VarId`-agnostic) -/

/-- Max magnitudes `(pos, neg)` of the positive- and negative-coefficient term sums of `l`, under
    per-variable bounds `B` (each variable ranges over `[0, B[v])`); `none` if any is unbounded. -/
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

/-- Certifies `l`'s value stays strictly within an interval of length `< p` that never wraps
    around `0` (hence nonzero). -/
def denseIntervalCert (B : Std.HashMap VarId Nat) (l : DenseLinExpr p) : Bool :=
  match denseSplitSumMax B l.terms with
  | none => false
  | some acc =>
    decide (acc.2 < l.const.val) && decide (l.const.val + acc.1 < p)

/-! ## Dense never-zero certificate -/

/-- Certifies `e` never-zero under bounds `B`: linearize, then try `denseIntervalCert` on each
    rescaling by an inverse coefficient (the constant term's, or each term's). -/
def denseNeverZeroB (B : Std.HashMap VarId Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | none => false
  | some l =>
    let n := l.norm
    (1 :: n.const⁻¹ :: n.terms.map (fun t => t.2⁻¹)).any (fun k =>
      denseIntervalCert B ((n.scale k).norm))

/-! ## Dense product-constraint resolution -/

/-- Collapse a product `f·g` in a constraint to the surviving factor when the other factor is
    certified never-zero by the value bounds `B`: e.g. `(x-5)·g = 0` with `g` provably nonzero
    becomes `x-5 = 0`. Recurses into the surviving factor. -/
def denseResolveExpr (B : Std.HashMap VarId Nat) : DenseExpr p → DenseExpr p
  | .mul f g =>
      if denseNeverZeroB B g then denseResolveExpr B f
      else if denseNeverZeroB B f then denseResolveExpr B g
      else .mul f g
  | e => e

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

/-! ## The dense transform -/

/-- The dense carry-branch-resolution transform (gated on `p` prime). -/
def denseCarryBranchF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    { d with algebraicConstraints :=
        d.algebraicConstraints.map (denseResolveExpr (denseBuild bs facts d.busInteractions)) }
  else d

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

end ApcOptimizer.Dense
