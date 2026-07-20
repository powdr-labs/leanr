import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # One-hot annihilation (idea 5)

A shift chip with a runtime shift amount but a fixed direction keeps *both* `bit_multiplier_left`
and `bit_multiplier_right`; one of them is dead. It is forced to `0` by the existing constraints,
but only through a linear combination *across the one-hot marker family* — a relation Gauss cannot
see because the constraints are nonlinear (products `markerᵢ · x`). Concretely, for a marker set
`{m₁, …, mₖ}` the block keeps

* `mᵢ · x = 0`   for every `i`   (the direction `i` is not selected), and
* `(m₁ + … + mₖ − 1) · x = 0`   (the "shift-by-0 / other-direction" closer),

and these entail `x = 0`: writing `s = Σ mᵢ`, the products give `s · x = Σ (mᵢ · x) = 0`, while the
closer gives `(s − 1) · x = 0`, i.e. `s · x − x = 0`; subtracting, `x = 0`.

This pass adds the entailed constraint `x = 0` (`ConstraintSystem.addConstraints_correct`); the
existing constant-fold / Gaussian elimination then substitutes the dead variable away and cascades.
It is purely equational — no field/primality assumption, no bus facts — and the added constraint has
degree 1, well within the bound. Soundness does not depend on the recognizer being precise: the added
equality `x = 0` is discharged as a linear combination of constraints already present, so a spurious
match either fails to find its supporting products (and emits nothing) or would add an equality that
genuinely holds.

The recognizer keys on the algebraic structure (a product `affine · x` whose affine cofactor has
constant term `−1` and unit coefficients, with `markerᵢ · x = 0` present for each cofactor variable),
not on any variable name or VM gadget, so it fires wherever a one-hot family annihilates a variable.
The optimizer emits the multiplier as the right factor, so the recognizer matches `A · x`. -/

namespace OneHotAnnihilate

variable {p : ℕ}

/-! ## Recognizing the closer `(Σ mᵢ − 1) · x` and the products `mᵢ · x` -/

/-- View an affine expression as a one-hot *closer* cofactor `±(Σ mᵢ − 1)`: its linear form has all
    coefficients equal to a common unit `k ∈ {1, −1}` and constant term `−k`, with at least one
    term. Both signs occur (the optimizer flips the closer's sign across passes), and both entail the
    same annihilation. -/
def affineCloser (a : Expression p) : Option (LinExpr p) :=
  match linearize a with
  | some la =>
      if ((la.const = -1 ∧ la.terms.all (fun t => t.2 == 1)) ∨
          (la.const = 1 ∧ la.terms.all (fun t => t.2 == -1))) ∧ la.terms ≠ [] then some la else none
  | none => none

/-- The affine-closer recognizer's guarantee: the cofactor is `Σ mᵢ − 1` (`k = 1`) or `1 − Σ mᵢ`
    (`k = −1`); in both, `const = −k` and every coefficient is `k`. -/
theorem affineCloser_spec (a : Expression p) (la : LinExpr p) (h : affineCloser a = some la) :
    linearize a = some la ∧
      ((la.const = -1 ∧ ∀ t ∈ la.terms, t.2 = 1) ∨ (la.const = 1 ∧ ∀ t ∈ la.terms, t.2 = -1)) := by
  unfold affineCloser at h
  split at h
  · rename_i l hl
    split at h
    · rename_i hcond
      obtain ⟨hc, _⟩ := hcond
      obtain rfl : l = la := by simpa using h
      refine ⟨hl, ?_⟩
      rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · exact Or.inl ⟨hc1, fun t ht => eq_of_beq (List.all_eq_true.1 hc2 t ht)⟩
      · exact Or.inr ⟨hc1, fun t ht => eq_of_beq (List.all_eq_true.1 hc2 t ht)⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Recognize a closer constraint `A · x` where `A` is a one-hot closer cofactor, returning the
    annihilated variable `x` and the cofactor's linear form. -/
def readCloser (c : Expression p) : Option (Variable × LinExpr p) :=
  match c with
  | .mul a (.var x) => (affineCloser a).map (fun la => (x, la))
  | _ => none

/-- `readCloser` succeeds only on `A · x` with `A` linearizing to `la`, `la.const = −1`, and every
    coefficient `1`. -/
theorem readCloser_spec (c : Expression p) (x : Variable) (la : LinExpr p)
    (h : readCloser c = some (x, la)) :
    (∃ A, c = .mul A (.var x) ∧ linearize A = some la) ∧
      ((la.const = -1 ∧ ∀ t ∈ la.terms, t.2 = 1) ∨ (la.const = 1 ∧ ∀ t ∈ la.terms, t.2 = -1)) := by
  cases c with
  | const n => simp [readCloser] at h
  | var y => simp [readCloser] at h
  | add a b => simp [readCloser] at h
  | mul a b =>
    cases b with
    | const n => simp [readCloser] at h
    | var y =>
      simp only [readCloser, Option.map_eq_some_iff] at h
      obtain ⟨la', hla', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨hlin, hform⟩ := affineCloser_spec a la' hla'
      exact ⟨⟨a, rfl, hlin⟩, hform⟩
    | add e1 e2 => simp [readCloser] at h
    | mul e1 e2 => simp [readCloser] at h

/-- Does `cs` contain the product constraint `v · x` (in either factor order)? -/
def hasProd (cs : ConstraintSystem p) (v x : Variable) : Bool :=
  cs.algebraicConstraints.any
    (fun c => c == .mul (.var v) (.var x) || c == .mul (.var x) (.var v))

/-- The dead variable a closer `c` annihilates, if all of its marker products are present. -/
def deadFromCloser (cs : ConstraintSystem p) (c : Expression p) : Option Variable :=
  match readCloser c with
  | some (x, la) => if la.terms.all (fun t => hasProd cs t.1 x) then some x else none
  | none => none

/-- Every one-hot-annihilated variable, read off the closer constraints. -/
def deadVars (cs : ConstraintSystem p) : List Variable :=
  cs.algebraicConstraints.filterMap (deadFromCloser cs)

/-! ## The entailment -/

/-- `Σ (env mᵢ) · x = 0` from `env mᵢ · x = 0` for every marker. -/
theorem sum_mul_eq_zero (terms : List (Variable × ZMod p)) (env : Variable → ZMod p) (xe : ZMod p)
    (hv : ∀ t ∈ terms, env t.1 * xe = 0) : (terms.map (fun t => env t.1)).sum * xe = 0 := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
    rw [List.map_cons, List.sum_cons, add_mul, hv t (List.mem_cons_self ..),
      ih (fun t' ht' => hv t' (List.mem_cons_of_mem _ ht')), add_zero]

/-- `Σ (k · env mᵢ) = k · Σ (env mᵢ)`. -/
theorem sum_map_mul_left (l : List (Variable × ZMod p)) (k : ZMod p) (env : Variable → ZMod p) :
    (l.map (fun t => k * env t.1)).sum = k * (l.map (fun t => env t.1)).sum := by
  induction l with
  | nil => simp
  | cons t rest ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, mul_add]

/-- The one-hot annihilation identity: `mᵢ·x = 0` for all markers plus `±(Σmᵢ − 1)·x = 0` force
    `x = 0`. Writing `s = Σ mᵢ`: from the products, `s·x = 0`; the closer gives `(s−1)·x = 0` or
    `(1−s)·x = 0`, either of which combines with `s·x = 0` to give `x = 0`. -/
theorem annihilate {terms : List (Variable × ZMod p)} {env : Variable → ZMod p} {xe : ZMod p}
    (hv : ∀ t ∈ terms, env t.1 * xe = 0)
    (hq : ((terms.map (fun t => env t.1)).sum - 1) * xe = 0 ∨
          (1 - (terms.map (fun t => env t.1)).sum) * xe = 0) : xe = 0 := by
  have hsum := sum_mul_eq_zero terms env xe hv
  rcases hq with h | h
  · rw [sub_mul, one_mul, hsum, zero_sub, neg_eq_zero] at h; exact h
  · rw [sub_mul, one_mul, hsum, sub_zero] at h; exact h

/-- The affine cofactor of a closer with common coefficient `k` evaluates to
    `la.const + k · Σ (env marker)`. -/
theorem cofactor_eval {A : Expression p} {la : LinExpr p} (hlin : linearize A = some la)
    (k : ZMod p) (hcoeff : ∀ t ∈ la.terms, t.2 = k) (env : Variable → ZMod p) :
    A.eval env = la.const + k * (la.terms.map (fun t => env t.1)).sum := by
  rw [linearize_eval A la hlin]
  unfold LinExpr.eval
  rw [show (la.terms.map (fun t => t.2 * env t.1)) = (la.terms.map (fun t => k * env t.1)) from
    List.map_congr_left (fun t ht => by rw [hcoeff t ht])]
  rw [sum_map_mul_left]

/-- Every `x ∈ deadVars cs` is forced to `0` by the system's constraints. -/
theorem deadVars_entailed (cs : ConstraintSystem p) (bs : BusSemantics p)
    (env : Variable → ZMod p) (hsat : cs.satisfies bs env) (x : Variable) (hx : x ∈ deadVars cs) :
    (Expression.var x).eval env = 0 := by
  obtain ⟨cq, hcq_mem, hdead⟩ := List.mem_filterMap.1 hx
  have hconstr : ∀ c ∈ cs.algebraicConstraints, c.eval env = 0 := hsat.1
  cases hrc : readCloser cq with
  | none => simp only [deadFromCloser, hrc] at hdead; exact absurd hdead (by simp)
  | some xla =>
    obtain ⟨x', la⟩ := xla
    simp only [deadFromCloser, hrc] at hdead
    split_ifs at hdead with hgate
    have hxeq : x' = x := by simpa using hdead
    obtain ⟨⟨A, hcform, hlin⟩, hform⟩ := readCloser_spec cq x' la hrc
    show env x = 0
    rw [← hxeq]
    -- closer: `(s − 1)·env x' = 0` or `(1 − s)·env x' = 0`
    have hcq0 : A.eval env * env x' = 0 := by
      have := hconstr cq hcq_mem; rw [hcform] at this; simpa only [Expression.eval] using this
    have hqeval : ((la.terms.map (fun t => env t.1)).sum - 1) * env x' = 0 ∨
        (1 - (la.terms.map (fun t => env t.1)).sum) * env x' = 0 := by
      rcases hform with ⟨hconst, hcoeff⟩ | ⟨hconst, hcoeff⟩
      · left
        rw [cofactor_eval hlin 1 hcoeff env, hconst] at hcq0
        linear_combination hcq0
      · right
        rw [cofactor_eval hlin (-1) hcoeff env, hconst] at hcq0
        linear_combination hcq0
    -- each marker product: `env v * env x' = 0`
    have hveval : ∀ t ∈ la.terms, env t.1 * env x' = 0 := by
      intro t ht
      have hp : hasProd cs t.1 x' = true := (List.all_eq_true.1 hgate) t ht
      unfold hasProd at hp
      obtain ⟨cv, hcv_mem, hcv⟩ := List.any_eq_true.1 hp
      have hcv0 : cv.eval env = 0 := hconstr cv hcv_mem
      simp only [Bool.or_eq_true] at hcv
      rcases hcv with he | he
      · obtain rfl := eq_of_beq he
        simpa only [Expression.eval] using hcv0
      · obtain rfl := eq_of_beq he
        simp only [Expression.eval] at hcv0
        rw [mul_comm] at hcv0
        exact hcv0
    exact annihilate hveval hqeval

/-! ## The pass -/

/-- Add `x = 0` for every one-hot-annihilated variable. -/
def oneHotAnnihilatePass : VerifiedPassW p := fun cs bs _ =>
  let new := (deadVars cs).map (fun x => Expression.var x)
  ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
    cs.addConstraints_correct bs new
      (by
        intro env _ hsat c hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
        exact deadVars_entailed cs bs env hsat x hx)
      (by
        intro c hc z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
        have hzy : z = y := by simpa only [Expression.vars, List.mem_singleton] using hz
        rw [hzy]
        obtain ⟨cq, hcq_mem, hdead⟩ := List.mem_filterMap.1 hy
        cases hrc : readCloser cq with
        | none => simp only [deadFromCloser, hrc] at hdead; exact absurd hdead (by simp)
        | some xla =>
          obtain ⟨x', la⟩ := xla
          simp only [deadFromCloser, hrc] at hdead
          split_ifs at hdead with hgate
          have hxeq : x' = y := by simpa using hdead
          obtain ⟨⟨A, hcform, _⟩, _⟩ := readCloser_spec cq x' la hrc
          rw [← hxeq]
          refine ConstraintSystem.mem_vars_of_constraint hcq_mem ?_
          rw [hcform]
          exact List.mem_append_right _ (List.mem_singleton.2 rfl))⟩

end OneHotAnnihilate
