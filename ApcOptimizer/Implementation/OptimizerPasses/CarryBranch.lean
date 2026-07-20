import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense carry-branch resolution — runtime (Task 3)

Dense, `VarId`-native port of `carryBranchPass`'s runtime. Gated on `p` prime, the pass rewrites
every algebraic constraint through `denseResolveExpr`, collapsing a product `f·g` to the factor that
survives whenever the other factor is *certified never-zero* by the fact-derived value bounds
(`denseBuild`, `DigitFold.lean`).

It is **fact-consuming**: the dense bounds map is the `Std.HashMap VarId Nat` built by `denseBuild`,
whose native value-level soundness (`denseBuild_sound`, `DigitFoldProof.lean`) is all the correctness
proof consumes. The interval certificate (`denseSplitSumMax`/`denseIntervalCert`/`denseNeverZeroB`)
is coefficient-only, and the recursive product collapse (`denseResolveExpr`) is structural. Only the
algebraic constraints are rewritten (bus interactions untouched). The native `DensePassCorrect`
proof and the pass itself live in `CarryBranchProof.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

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

/-- Dense `intervalCert` (see `intervalCert`). -/
def denseIntervalCert (B : Std.HashMap VarId Nat) (l : DenseLinExpr p) : Bool :=
  match denseSplitSumMax B l.terms with
  | none => false
  | some acc =>
    decide (acc.2 < l.const.val) && decide (l.const.val + acc.1 < p)

/-! ## Dense never-zero certificate -/

/-- Dense `neverZeroB` (see `neverZeroB`). -/
def denseNeverZeroB (B : Std.HashMap VarId Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | none => false
  | some l =>
    let n := l.norm
    (1 :: n.const⁻¹ :: n.terms.map (fun t => t.2⁻¹)).any (fun k =>
      denseIntervalCert B ((n.scale k).norm))

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
