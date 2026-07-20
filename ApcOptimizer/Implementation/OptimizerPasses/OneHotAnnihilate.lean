import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.OneHotAnnihilate

set_option autoImplicit false

/-! # Dense one-hot annihilation (Task 3)

Dense, `VarId`-native port of `OneHotAnnihilate.oneHotAnnihilatePass`. The pass appends `x = 0` for
every one-hot-annihilated variable `x`, read off the closer constraints. It is **fact-free**, so it
is built with `ofTransform`, inheriting the spec pass's `PassCorrect`: the dense transform decodes to
exactly the spec pass's output.

The recognizer chain (`affineCloser`/`readCloser`/`hasProd`/`deadFromCloser`/`deadVars`) is mirrored
on `DenseExpr`/`VarId`; each dense recognizer decodes to its spec counterpart (the closer/marker
analysis is coefficient- and structure-based, so `resolve`-stable), and the whole-value `==`
comparisons in `hasProd` commute with decode via the covered-injectivity lemma `decodeExpr_inj`. -/

namespace ApcOptimizer.Dense

open OneHotAnnihilate

variable {p : ℕ}

/-! ## A `==` correspondence and a small `any` congruence -/

/-- **`==` on covered dense expressions commutes with decode.** `resolve` is injective on valid ids,
    so `decodeExpr` is injective on covered values; hence structural equality of the decodes matches
    structural equality of the dense values. -/
theorem VarRegistry.decodeExpr_beq (reg : VarRegistry) {a b : DenseExpr p}
    (ha : a.CoveredBy reg) (hb : b.CoveredBy reg) :
    (reg.decodeExpr a == reg.decodeExpr b) = (a == b) := by
  show decide (reg.decodeExpr a = reg.decodeExpr b) = decide (a = b)
  exact decide_eq_decide.mpr
    ⟨fun he => reg.decodeExpr_inj ha hb he, fun he => congrArg reg.decodeExpr he⟩

/-- `any` respects a pointwise-equal predicate on the list's members. -/
theorem list_any_congr {α : Type _} {l : List α} {f g : α → Bool}
    (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.any_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `all` respects a pointwise-equal predicate on the list's members. -/
theorem list_all_congr {α : Type _} {l : List α} {f g : α → Bool}
    (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.all_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Decoding distributes over appending derived dense constraints. -/
theorem VarRegistry.decodeCS_append_constraints (reg : VarRegistry) (d : DenseConstraintSystem p)
    (dnew : List (DenseExpr p)) :
    reg.decodeCS { d with algebraicConstraints := d.algebraicConstraints ++ dnew }
      = { reg.decodeCS d with algebraicConstraints :=
            (reg.decodeCS d).algebraicConstraints ++ dnew.map reg.decodeExpr } := by
  simp only [VarRegistry.decodeCS, List.map_append]

/-! ## Dense recognizers -/

/-- Dense affine-closer recognizer (see `OneHotAnnihilate.affineCloser`). -/
def denseAffineCloser (a : DenseExpr p) : Option (DenseLinExpr p) :=
  match denseLinearize a with
  | some la =>
      if ((la.const = -1 ∧ la.terms.all (fun t => t.2 == 1)) ∨
          (la.const = 1 ∧ la.terms.all (fun t => t.2 == -1))) ∧ la.terms ≠ [] then some la else none
  | none => none

theorem denseAffineCloser_decode (reg : VarRegistry) (a : DenseExpr p) :
    affineCloser (reg.decodeExpr a) = (denseAffineCloser a).map reg.decodeLin := by
  unfold affineCloser denseAffineCloser
  rw [← reg.denseLinearize_decode a]
  cases hla : denseLinearize a with
  | none => rfl
  | some dla =>
      simp only [Option.map_some]
      have hcond : (((reg.decodeLin dla).const = -1 ∧
            (reg.decodeLin dla).terms.all (fun t => t.2 == 1)) ∨
          ((reg.decodeLin dla).const = 1 ∧
            (reg.decodeLin dla).terms.all (fun t => t.2 == -1))) ∧ (reg.decodeLin dla).terms ≠ []
          ↔ ((dla.const = -1 ∧ dla.terms.all (fun t => t.2 == 1)) ∨
              (dla.const = 1 ∧ dla.terms.all (fun t => t.2 == -1))) ∧ dla.terms ≠ [] := by
        simp only [VarRegistry.decodeLin, List.all_map, Function.comp_def, ne_eq,
          List.map_eq_nil_iff]
      by_cases hc : ((dla.const = -1 ∧ dla.terms.all (fun t => t.2 == 1)) ∨
          (dla.const = 1 ∧ dla.terms.all (fun t => t.2 == -1))) ∧ dla.terms ≠ []
      · rw [if_pos (hcond.mpr hc), if_pos hc]; rfl
      · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]; rfl

/-- Dense closer recognizer (see `OneHotAnnihilate.readCloser`). -/
def denseReadCloser (c : DenseExpr p) : Option (VarId × DenseLinExpr p) :=
  match c with
  | .mul a (.var i) => (denseAffineCloser a).map (fun la => (i, la))
  | _ => none

theorem denseReadCloser_decode (reg : VarRegistry) (c : DenseExpr p) :
    readCloser (reg.decodeExpr c)
      = (denseReadCloser c).map (fun t => (reg.resolve t.1, reg.decodeLin t.2)) := by
  cases c with
  | const n => rfl
  | var i => rfl
  | add a b => rfl
  | mul a b =>
      cases b with
      | const n => rfl
      | var i =>
          show readCloser (.mul (reg.decodeExpr a) (.var (reg.resolve i)))
            = ((denseAffineCloser a).map (fun la => (i, la))).map
                (fun t => (reg.resolve t.1, reg.decodeLin t.2))
          simp only [readCloser, denseAffineCloser_decode reg a, Option.map_map, Function.comp_def]
      | add e1 e2 => rfl
      | mul e1 e2 => rfl

/-- If a covered expression is recognised as a closer, the annihilated variable and every marker
    variable are valid. -/
theorem denseReadCloser_valid (reg : VarRegistry) {c : DenseExpr p} (hc : c.CoveredBy reg)
    {i : VarId} {la : DenseLinExpr p} (h : denseReadCloser c = some (i, la)) :
    reg.Valid i ∧ ∀ t ∈ la.terms, reg.Valid t.1 := by
  cases c with
  | const n => simp [denseReadCloser] at h
  | var j => simp [denseReadCloser] at h
  | add a b => simp [denseReadCloser] at h
  | mul a b =>
      cases b with
      | const n => simp [denseReadCloser] at h
      | var j =>
          simp only [denseReadCloser, Option.map_eq_some_iff] at h
          obtain ⟨la', hla', heq⟩ := h
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨hca, hcb⟩ := DenseExpr.coveredBy_mul.mp hc
          refine ⟨hcb j (by simp [DenseExpr.vars]), fun t ht => ?_⟩
          -- `la'` came from `denseLinearize a`; its term vars are vars of `a`
          have hlin : denseLinearize a = some la' := by
            have h := hla'
            unfold denseAffineCloser at h
            revert h
            cases denseLinearize a with
            | none => intro h; exact absurd h (by simp)
            | some dl =>
                intro h
                dsimp only at h
                by_cases hcnd : ((dl.const = -1 ∧ (dl.terms.all fun t => t.2 == 1))
                    ∨ (dl.const = 1 ∧ (dl.terms.all fun t => t.2 == -1))) ∧ dl.terms ≠ []
                · rw [if_pos hcnd] at h; exact h
                · rw [if_neg hcnd] at h; exact absurd h (by simp)
          exact hca t.1 (denseLinearize_vars a la' hlin t.1 (List.mem_map.2 ⟨t, ht, rfl⟩))
      | add e1 e2 => simp [denseReadCloser] at h
      | mul e1 e2 => simp [denseReadCloser] at h

/-- Dense `hasProd` (see `OneHotAnnihilate.hasProd`). -/
def denseHasProd (d : DenseConstraintSystem p) (v x : VarId) : Bool :=
  d.algebraicConstraints.any
    (fun c => c == .mul (.var v) (.var x) || c == .mul (.var x) (.var v))

theorem denseHasProd_decode (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) {v x : VarId} (hv : reg.Valid v) (hx : reg.Valid x) :
    hasProd (reg.decodeCS d) (reg.resolve v) (reg.resolve x) = denseHasProd d v x := by
  unfold hasProd denseHasProd
  show (d.algebraicConstraints.map reg.decodeExpr).any _ = _
  rw [List.any_map]
  refine list_any_congr (fun c hc => ?_)
  have hcc : c.CoveredBy reg := hcov.1 c hc
  have hdm1 : (DenseExpr.mul (DenseExpr.var v) (DenseExpr.var x) : DenseExpr p).CoveredBy reg :=
    DenseExpr.coveredBy_mul.mpr ⟨DenseExpr.coveredBy_var hv, DenseExpr.coveredBy_var hx⟩
  have hdm2 : (DenseExpr.mul (DenseExpr.var x) (DenseExpr.var v) : DenseExpr p).CoveredBy reg :=
    DenseExpr.coveredBy_mul.mpr ⟨DenseExpr.coveredBy_var hx, DenseExpr.coveredBy_var hv⟩
  have e1 := reg.decodeExpr_beq hcc hdm1
  have e2 := reg.decodeExpr_beq hcc hdm2
  simp only [VarRegistry.decodeExpr] at e1 e2
  simp only [Function.comp_apply, e1, e2]

/-- Dense dead-variable-from-closer recognizer (see `OneHotAnnihilate.deadFromCloser`). -/
def denseDeadFromCloser (d : DenseConstraintSystem p) (c : DenseExpr p) : Option VarId :=
  match denseReadCloser c with
  | some (x, la) => if la.terms.all (fun t => denseHasProd d t.1 x) then some x else none
  | none => none

theorem denseDeadFromCloser_decode (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (c : DenseExpr p) (hc : c.CoveredBy reg) :
    deadFromCloser (reg.decodeCS d) (reg.decodeExpr c)
      = (denseDeadFromCloser d c).map reg.resolve := by
  unfold deadFromCloser denseDeadFromCloser
  rw [denseReadCloser_decode reg c]
  cases hrc : denseReadCloser c with
  | none => rfl
  | some xla =>
      obtain ⟨x, la⟩ := xla
      obtain ⟨hxv, hltv⟩ := denseReadCloser_valid reg hc hrc
      simp only [Option.map_some]
      have hall : (reg.decodeLin la).terms.all
            (fun t => hasProd (reg.decodeCS d) t.1 (reg.resolve x))
          = la.terms.all (fun t => denseHasProd d t.1 x) := by
        show (la.terms.map (fun t => (reg.resolve t.1, t.2))).all _ = _
        rw [List.all_map]
        refine list_all_congr (fun t ht => ?_)
        exact denseHasProd_decode reg d hcov (hltv t ht) hxv
      rw [hall]
      by_cases hb : la.terms.all (fun t => denseHasProd d t.1 x)
      · rw [if_pos hb, if_pos hb]; rfl
      · rw [if_neg hb, if_neg hb]; rfl

/-- Dense one-hot dead variables (see `OneHotAnnihilate.deadVars`). -/
def denseDeadVars (d : DenseConstraintSystem p) : List VarId :=
  d.algebraicConstraints.filterMap (denseDeadFromCloser d)

theorem denseDeadVars_decode (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    deadVars (reg.decodeCS d) = (denseDeadVars d).map reg.resolve := by
  unfold deadVars denseDeadVars
  show (d.algebraicConstraints.map reg.decodeExpr).filterMap _ = _
  rw [List.filterMap_map, List.map_filterMap]
  exact List.filterMap_congr
    (fun c hc => denseDeadFromCloser_decode reg d hcov c (hcov.1 c hc))

/-- Every dense dead variable is valid. -/
theorem denseDeadVars_valid (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) : ∀ i ∈ denseDeadVars d, reg.Valid i := by
  intro i hi
  unfold denseDeadVars at hi
  rw [List.mem_filterMap] at hi
  obtain ⟨c, hc, hdc⟩ := hi
  have hcc : c.CoveredBy reg := hcov.1 c hc
  unfold denseDeadFromCloser at hdc
  cases hrc : denseReadCloser c with
  | none => rw [hrc] at hdc; simp at hdc
  | some xla =>
      obtain ⟨x, la⟩ := xla
      rw [hrc] at hdc
      dsimp only at hdc
      by_cases hg : (la.terms.all fun t => denseHasProd d t.1 x)
      · rw [if_pos hg] at hdc
        obtain rfl := Option.some.inj hdc
        exact (denseReadCloser_valid reg hcc hrc).1
      · rw [if_neg hg] at hdc; exact absurd hdc (by simp)

/-! ## The dense transform and pass -/

/-- The dense transform: append `x = 0` for every one-hot-annihilated dense variable. -/
def denseOneHotAnnihilateF (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { d with algebraicConstraints :=
      d.algebraicConstraints ++ (denseDeadVars d).map (fun i => DenseExpr.var i) }

/-- The dense one-hot annihilation pass. Fact-free, built with `ofTransform`; inherits
    `OneHotAnnihilate.oneHotAnnihilatePass`'s `PassCorrect`. -/
def denseOneHotAnnihilatePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofTransform (p := p)
    (fun _ d => denseOneHotAnnihilateF d)
    OneHotAnnihilate.oneHotAnnihilatePass
    (fun reg _ d hc => by
      refine ⟨fun e he => ?_, fun bi hbi => hc.2 bi hbi⟩
      rcases List.mem_append.1 he with h | h
      · exact hc.1 e h
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
        exact DenseExpr.coveredBy_var (denseDeadVars_valid reg d hc i hi))
    (fun reg _ facts d hc => by
      show reg.decodeCS (denseOneHotAnnihilateF d)
        = (OneHotAnnihilate.oneHotAnnihilatePass (reg.decodeCS d) _ facts).out
      have hkey : ((denseDeadVars d).map (fun i => (DenseExpr.var i : DenseExpr p))).map
              reg.decodeExpr
          = (deadVars (reg.decodeCS d)).map (fun x => Expression.var x) := by
        rw [List.map_map, denseDeadVars_decode reg d hc, List.map_map]
        rfl
      have hR : (OneHotAnnihilate.oneHotAnnihilatePass (reg.decodeCS d) _ facts).out
          = { reg.decodeCS d with algebraicConstraints := (reg.decodeCS d).algebraicConstraints
              ++ (deadVars (reg.decodeCS d)).map (fun x => Expression.var x) } := rfl
      rw [hR,
        show denseOneHotAnnihilateF d
          = { d with algebraicConstraints := d.algebraicConstraints
              ++ (denseDeadVars d).map (fun i => (DenseExpr.var i : DenseExpr p)) } from rfl,
        reg.decodeCS_append_constraints d, hkey])
    (fun _ _ _ => rfl)

end ApcOptimizer.Dense
