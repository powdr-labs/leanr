import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.BridgeSteps
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagUnify

set_option autoImplicit false

/-! # Correctness for the dense Gauss-elimination pass.
Substitution-shaped: correctness rides on `DenseConstraintSystem.substF_denseCorrect`
(`Proofs/DomainBatch.lean`), fed the final solution map's entailment and occurrence closure, both
established by `denseSparseMarkowitzLoop_sound`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

def denseLinEnv (σ : VarId → Option (DenseLinExpr p)) (denv : VarId → ZMod p) :
    VarId → ZMod p :=
  fun i => match σ i with | some row => row.eval denv | none => denv i

theorem denseLinSubstData_eval (terms : List (VarId × ZMod p))
    (σ : VarId → Option (DenseLinExpr p)) (denv : VarId → ZMod p) (k : ZMod p) :
    terms.foldl (fun out yc =>
        match σ yc.1 with
        | some t => out + yc.2 * t.const
        | none => out) k
      + ((terms.flatMap (fun yc =>
          match σ yc.1 with
          | some t => t.terms.map (fun zc => (zc.1, yc.2 * zc.2))
          | none => [yc])).map (fun zc => zc.2 * denv zc.1)).sum
    = k + (terms.map (fun yc => yc.2 * denseLinEnv σ denv yc.1)).sum := by
  induction terms generalizing k with
  | nil => simp
  | cons yc rest ih =>
      simp only [List.foldl_cons, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      cases hσ : σ yc.1 with
      | none =>
          simp only [List.map_singleton, List.sum_singleton]
          rw [show denseLinEnv σ denv yc.1 = denv yc.1 by simp [denseLinEnv, hσ]]
          have hrest := ih k
          linear_combination hrest
      | some row =>
          simp only [List.map_map]
          rw [show denseLinEnv σ denv yc.1 = row.eval denv by simp [denseLinEnv, hσ],
            DenseLinExpr.eval]
          have hrest := ih (k + yc.2 * row.const)
          have hscale :
              ((row.terms.map fun zc => (zc.1, yc.2 * zc.2)).map
                  fun zc => zc.2 * denv zc.1).sum
                = yc.2 * ((row.terms.map fun zc => zc.2 * denv zc.1).sum) := by
            induction row.terms with
            | nil => simp
            | cons zc zs ihz =>
                simp only [List.map_cons, List.sum_cons, ihz]
                ring
          rw [show
            (row.terms.map ((fun zc => zc.2 * denv zc.1) ∘
              fun zc => (zc.1, yc.2 * zc.2))).sum
              = yc.2 * ((row.terms.map fun zc => zc.2 * denv zc.1).sum) by
                simpa [Function.comp_def] using hscale]
          linear_combination hrest

theorem denseLinSubstF_eval (l : DenseLinExpr p)
    (σ : VarId → Option (DenseLinExpr p)) (denv : VarId → ZMod p) :
    (denseLinSubstF l σ).eval denv = l.eval (denseLinEnv σ denv) := by
  rw [denseLinSubstF, DenseLinExpr.norm_eval]
  simp only [DenseLinExpr.eval]
  exact denseLinSubstData_eval l.terms σ denv l.const

theorem denseLinSubstF_terms_closed (l : DenseLinExpr p)
    (σ : VarId → Option (DenseLinExpr p)) (S : VarId → Prop)
    (hl : ∀ z ∈ l.terms.map Prod.fst, S z)
    (hσ : ∀ i row, σ i = some row → ∀ z ∈ row.terms.map Prod.fst, S z) :
    ∀ z ∈ (denseLinSubstF l σ).terms.map Prod.fst, S z := by
  intro z hz
  let rawTerms := l.terms.flatMap (fun yc =>
    match σ yc.1 with
    | some t => t.terms.map (fun zc => (zc.1, yc.2 * zc.2))
    | none => [yc])
  have hzraw : z ∈ rawTerms.map Prod.fst := by
    exact DenseLinExpr.norm_terms_fst
      ⟨l.terms.foldl (fun out yc =>
        match σ yc.1 with
        | some t => out + yc.2 * t.const
        | none => out) l.const, rawTerms⟩ z hz
  simp only [rawTerms, List.mem_map, List.mem_flatMap] at hzraw
  obtain ⟨zc, ⟨yc, hyc, hyout⟩, hzc⟩ := hzraw
  cases hrow : σ yc.1 with
  | none =>
      simp only [hrow, List.mem_singleton] at hyout
      subst zc
      exact hzc ▸ hl yc.1 (List.mem_map.2 ⟨yc, hyc, rfl⟩)
  | some row =>
      simp only [hrow, List.mem_map] at hyout
      obtain ⟨rc, hrc, hrczc⟩ := hyout
      subst zc
      exact hzc ▸ hσ yc.1 row hrow rc.1 (List.mem_map.2 ⟨rc, hrc, rfl⟩)

theorem denseLinAdd_eval (a b : DenseLinExpr p) (denv : VarId → ZMod p) :
    (denseLinAdd a b).eval denv = a.eval denv + b.eval denv := by
  rw [denseLinAdd, DenseLinExpr.norm_eval, DenseLinExpr.add_eval]

theorem denseLinScale_eval (k : ZMod p) (l : DenseLinExpr p) (denv : VarId → ZMod p) :
    (denseLinScale k l).eval denv = k * l.eval denv := by
  rw [denseLinScale, DenseLinExpr.norm_eval, DenseLinExpr.scale_eval]

theorem denseLinAdd_toExpr_eval (a b : DenseLinExpr p) (denv : VarId → ZMod p) :
    (denseLinAdd a b).toExpr.eval denv = a.toExpr.eval denv + b.toExpr.eval denv := by
  simp only [DenseLinExpr.toExpr_eval, denseLinAdd_eval]

theorem denseLinScale_toExpr_eval (k : ZMod p) (l : DenseLinExpr p)
    (denv : VarId → ZMod p) :
    (denseLinScale k l).toExpr.eval denv = k * l.toExpr.eval denv := by
  simp only [DenseLinExpr.toExpr_eval, denseLinScale_eval]

theorem denseLinAdd_terms_closed (a b : DenseLinExpr p) (S : VarId → Prop)
    (ha : ∀ z ∈ a.terms.map Prod.fst, S z)
    (hb : ∀ z ∈ b.terms.map Prod.fst, S z) :
    ∀ z ∈ (denseLinAdd a b).terms.map Prod.fst, S z := by
  intro z hz
  have hz' := DenseLinExpr.norm_terms_fst (a.add b) z hz
  simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hz'
  exact hz'.elim (ha z) (hb z)

theorem denseLinScale_terms_closed (k : ZMod p) (l : DenseLinExpr p) (S : VarId → Prop)
    (hl : ∀ z ∈ l.terms.map Prod.fst, S z) :
    ∀ z ∈ (denseLinScale k l).terms.map Prod.fst, S z := by
  intro z hz
  have hz' := DenseLinExpr.norm_terms_fst (l.scale k) z hz
  rw [DenseLinExpr.scale_terms_fst] at hz'
  exact hl z hz'

theorem denseSparseMulReduced_eval (ra rb : DenseGaussReduced p) (denv : VarId → ZMod p) :
    (denseReducedMul ra rb).toExpr.eval denv
      = ra.toExpr.eval denv * rb.toExpr.eval denv := by
  cases ra with
  | nonlinear ea =>
      cases rb <;> simp [denseReducedMul, DenseGaussReduced.toExpr, DenseExpr.eval]
  | affine la =>
      cases rb with
      | nonlinear eb => simp [denseReducedMul, DenseGaussReduced.toExpr, DenseExpr.eval]
      | affine lb =>
          simp only [denseReducedMul, DenseGaussReduced.toExpr]
          by_cases ha : la.terms.isEmpty
          · rw [if_pos ha]
            simp only [denseLinScale_toExpr_eval]
            rw [DenseLinExpr.toExpr_eval la]
            simp [DenseLinExpr.eval, List.isEmpty_iff.1 ha]
          · rw [if_neg ha]
            by_cases hb : lb.terms.isEmpty
            · rw [if_pos hb]
              simp only [denseLinScale_toExpr_eval]
              rw [DenseLinExpr.toExpr_eval lb]
              simp [DenseLinExpr.eval, List.isEmpty_iff.1 hb, mul_comm]
            · rw [if_neg hb]
              rfl

theorem denseSparseSubstF_eval (σ : VarId → Option (DenseLinExpr p)) (e : DenseExpr p)
    (denv : VarId → ZMod p) (hσ : ∀ i row, σ i = some row → denv i = row.eval denv) :
    (denseSparseSubstF σ e).toExpr.eval denv = e.eval denv := by
  have henv : denseLinEnv σ denv = denv := by
    funext i
    cases hi : σ i with
    | none => simp [denseLinEnv, hi]
    | some row => simp [denseLinEnv, hi, hσ i row hi]
  induction e with
  | const n => rfl
  | var i =>
      simp only [denseSparseSubstF]
      cases hi : σ i with
      | none =>
          simp only [DenseGaussReduced.toExpr, DenseExpr.eval]
          rw [DenseLinExpr.toExpr_eval]
          simp [DenseLinExpr.eval]
      | some row =>
          simp only [DenseGaussReduced.toExpr, DenseExpr.eval]
          rw [DenseLinExpr.toExpr_eval, ← hσ i row hi]
  | add a b iha ihb =>
      simp only [denseSparseSubstF]
      cases hlin : denseLinearize (.add a b) with
      | some row =>
          simp only [DenseGaussReduced.toExpr]
          rw [DenseLinExpr.toExpr_eval, denseLinSubstF_eval, henv,
            ← denseLinearize_eval (.add a b) row hlin]
      | none =>
          cases ha : denseSparseSubstF σ a <;>
            cases hb : denseSparseSubstF σ b <;>
            simp_all [denseReducedAdd, DenseGaussReduced.toExpr, DenseExpr.eval,
              denseLinAdd_toExpr_eval]
  | mul a b iha ihb =>
      simp only [denseSparseSubstF]
      cases hlin : denseLinearize (.mul a b) with
      | some row =>
          simp only [DenseGaussReduced.toExpr]
          rw [DenseLinExpr.toExpr_eval, denseLinSubstF_eval, henv,
            ← denseLinearize_eval (.mul a b) row hlin]
      | none =>
          have hm := denseSparseMulReduced_eval
            (denseSparseSubstF σ a) (denseSparseSubstF σ b) denv
          rw [iha, ihb] at hm
          simpa only [DenseExpr.eval] using hm

theorem denseLinSubstSolved_eq (l : DenseLinExpr p) (dσ : DenseSparseSolved p) :
    denseLinSubstSolved l dσ = denseLinSubstF l dσ.fn := by
  rfl

theorem denseSparseSubstSolved_eq (dσ : DenseSparseSolved p) (e : DenseExpr p) :
    denseSparseSubstSolved dσ e = denseSparseSubstF dσ.fn e := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
      simp only [denseSparseSubstSolved, denseSparseSubstF]
      split
      · rw [denseLinSubstSolved_eq]
      · rw [iha, ihb]
  | mul a b iha ihb =>
      simp only [denseSparseSubstSolved, denseSparseSubstF]
      split
      · rw [denseLinSubstSolved_eq]
      · rw [iha, ihb]

def DenseGaussReduced.support : DenseGaussReduced p → List VarId
  | .affine row => row.terms.map Prod.fst
  | .nonlinear expr => expr.vars

def DenseGaussReduced.Closed (r : DenseGaussReduced p) (S : VarId → Prop) : Prop :=
  ∀ z ∈ r.support, S z

theorem denseSparseAddReduced_closed (ra rb : DenseGaussReduced p) (S : VarId → Prop)
    (ha : ra.Closed S) (hb : rb.Closed S) :
    (denseReducedAdd ra rb).Closed S := by
  revert ha hb
  cases ra with
  | affine la =>
      cases rb with
      | affine lb =>
          intro ha hb
          simp only [denseReducedAdd, DenseGaussReduced.Closed,
            DenseGaussReduced.support] at ha hb ⊢
          exact denseLinAdd_terms_closed la lb S ha hb
      | nonlinear eb =>
          intro ha hb
          simp only [denseReducedAdd, DenseGaussReduced.Closed, DenseGaussReduced.support,
            DenseGaussReduced.toExpr] at ha hb ⊢
          intro z hz
          simp only [DenseExpr.vars, List.mem_append] at hz
          rcases hz with hz | hz
          · exact DenseLinExpr.toExpr_vars la z hz |> ha z
          · exact hb z hz
  | nonlinear ea =>
      cases rb with
      | affine lb =>
          intro ha hb
          simp only [denseReducedAdd, DenseGaussReduced.Closed, DenseGaussReduced.support,
            DenseGaussReduced.toExpr] at ha hb ⊢
          intro z hz
          simp only [DenseExpr.vars, List.mem_append] at hz
          rcases hz with hz | hz
          · exact ha z hz
          · exact DenseLinExpr.toExpr_vars lb z hz |> hb z
      | nonlinear eb =>
          intro ha hb
          simp only [denseReducedAdd, DenseGaussReduced.Closed, DenseGaussReduced.support,
            DenseGaussReduced.toExpr] at ha hb ⊢
          intro z hz
          simp only [DenseExpr.vars, List.mem_append] at hz
          rcases hz with hz | hz
          · exact ha z hz
          · exact hb z hz

theorem denseSparseMulReduced_closed (ra rb : DenseGaussReduced p) (S : VarId → Prop)
    (ha : ra.Closed S) (hb : rb.Closed S) :
    (denseReducedMul ra rb).Closed S := by
  revert ha hb
  cases ra with
  | affine la =>
      cases rb with
      | affine lb =>
          intro ha hb
          simp only [denseReducedMul, DenseGaussReduced.Closed,
            DenseGaussReduced.support] at ha hb ⊢
          by_cases hla : la.terms.isEmpty
          · rw [if_pos hla]
            exact denseLinScale_terms_closed la.const lb S hb
          · rw [if_neg hla]
            by_cases hlb : lb.terms.isEmpty
            · rw [if_pos hlb]
              exact denseLinScale_terms_closed lb.const la S ha
            · rw [if_neg hlb]
              intro z hz
              simp only [DenseExpr.vars, List.mem_append] at hz
              rcases hz with hz | hz
              · exact DenseLinExpr.toExpr_vars la z hz |> ha z
              · exact DenseLinExpr.toExpr_vars lb z hz |> hb z
      | nonlinear eb =>
          intro ha hb
          simp only [denseReducedMul, DenseGaussReduced.Closed, DenseGaussReduced.support,
            DenseGaussReduced.toExpr] at ha hb ⊢
          intro z hz
          simp only [DenseExpr.vars, List.mem_append] at hz
          rcases hz with hz | hz
          · exact DenseLinExpr.toExpr_vars la z hz |> ha z
          · exact hb z hz
  | nonlinear ea =>
      cases rb with
      | affine lb =>
          intro ha hb
          simp only [denseReducedMul, DenseGaussReduced.Closed, DenseGaussReduced.support,
            DenseGaussReduced.toExpr] at ha hb ⊢
          intro z hz
          simp only [DenseExpr.vars, List.mem_append] at hz
          rcases hz with hz | hz
          · exact ha z hz
          · exact DenseLinExpr.toExpr_vars lb z hz |> hb z
      | nonlinear eb =>
          intro ha hb
          simp only [denseReducedMul, DenseGaussReduced.Closed, DenseGaussReduced.support,
            DenseGaussReduced.toExpr] at ha hb ⊢
          intro z hz
          simp only [DenseExpr.vars, List.mem_append] at hz
          rcases hz with hz | hz
          · exact ha z hz
          · exact hb z hz

theorem denseSparseSubstF_closed (σ : VarId → Option (DenseLinExpr p)) (e : DenseExpr p)
    (S : VarId → Prop) (he : ∀ z ∈ e.vars, S z)
    (hσ : ∀ i row, σ i = some row → ∀ z ∈ row.terms.map Prod.fst, S z) :
    (denseSparseSubstF σ e).Closed S := by
  induction e with
  | const n =>
      simp [denseSparseSubstF, DenseGaussReduced.Closed, DenseGaussReduced.support]
  | var i =>
      simp only [denseSparseSubstF]
      cases hi : σ i with
      | none =>
          simp only [DenseGaussReduced.Closed, DenseGaussReduced.support,
            List.map_singleton, List.mem_singleton]
          intro z hz
          subst z
          exact he i (by simp [DenseExpr.vars])
      | some row =>
          simp only [DenseGaussReduced.Closed, DenseGaussReduced.support]
          exact hσ i row hi
  | add a b iha ihb =>
      simp only [denseSparseSubstF]
      cases hlin : denseLinearize (.add a b) with
      | some row =>
          simp only [DenseGaussReduced.Closed, DenseGaussReduced.support]
          apply denseLinSubstF_terms_closed row σ S
          · intro z hz
            exact he z (denseLinearize_mem_vars (.add a b) row hlin z hz)
          · exact hσ
      | none =>
          have hea : ∀ z ∈ a.vars, S z :=
            fun z hz => he z (by simp [DenseExpr.vars, hz])
          have heb : ∀ z ∈ b.vars, S z :=
            fun z hz => he z (by simp [DenseExpr.vars, hz])
          have ha := iha hea
          have hb := ihb heb
          exact denseSparseAddReduced_closed
            (denseSparseSubstF σ a) (denseSparseSubstF σ b) S ha hb
  | mul a b iha ihb =>
      simp only [denseSparseSubstF]
      cases hlin : denseLinearize (.mul a b) with
      | some row =>
          simp only [DenseGaussReduced.Closed, DenseGaussReduced.support]
          apply denseLinSubstF_terms_closed row σ S
          · intro z hz
            exact he z (denseLinearize_mem_vars (.mul a b) row hlin z hz)
          · exact hσ
      | none =>
          have hea : ∀ z ∈ a.vars, S z :=
            fun z hz => he z (by simp [DenseExpr.vars, hz])
          have heb : ∀ z ∈ b.vars, S z :=
            fun z hz => he z (by simp [DenseExpr.vars, hz])
          have ha := iha hea
          have hb := ihb heb
          exact denseSparseMulReduced_closed
            (denseSparseSubstF σ a) (denseSparseSubstF σ b) S ha hb

theorem denseLinSubst_eq (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p) :
    denseLinSubst s x t = denseLinSubstF s (fun y => if y = x then some t else none) := by
  have hconst :
      (fun (out : ZMod p) (yc : VarId × ZMod p) =>
        if yc.1 = x then out + yc.2 * t.const else out) =
      (fun out yc =>
        match if yc.1 = x then some t else none with
        | some row => out + yc.2 * row.const
        | none => out) := by
    funext out yc
    split <;> rfl
  have hterms :
      (fun (yc : VarId × ZMod p) =>
        if yc.1 = x then t.terms.map (fun zc => (zc.1, yc.2 * zc.2)) else [yc]) =
      (fun yc =>
        match if yc.1 = x then some t else none with
        | some row => row.terms.map (fun zc => (zc.1, yc.2 * zc.2))
        | none => [yc]) := by
    funext yc
    split <;> rfl
  unfold denseLinSubst denseLinSubstF
  apply congrArg DenseLinExpr.norm
  exact congrArg₂ DenseLinExpr.mk
    (congrArg (fun f => s.terms.foldl f s.const) hconst)
    (congrArg (fun f => s.terms.flatMap f) hterms)

theorem denseLinSubst_eval (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p)
    (denv : VarId → ZMod p) (hx : denv x = t.eval denv) :
    (denseLinSubst s x t).eval denv = s.eval denv := by
  rw [denseLinSubst_eq]
  rw [denseLinSubstF_eval]
  congr 1
  funext y
  by_cases hy : y = x
  · subst y
    simp [denseLinEnv, hx]
  · simp [denseLinEnv, hy]

theorem denseLinSubst_terms_closed (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p)
    (S : VarId → Prop) (hs : ∀ z ∈ s.terms.map Prod.fst, S z)
    (ht : ∀ z ∈ t.terms.map Prod.fst, S z) :
    ∀ z ∈ (denseLinSubst s x t).terms.map Prod.fst, S z := by
  rw [denseLinSubst_eq]
  apply denseLinSubstF_terms_closed s _ S hs
  intro i row hi
  by_cases hix : i = x
  · subst i
    have hrow : t = row := by simpa using hi
    subst row
    exact ht
  · simp [hix] at hi

theorem denseSparseSolveAt_sound (l : DenseLinExpr p) (x y : VarId)
    (t : DenseLinExpr p) (h : denseSparseSolveAt l x = some (y, t))
    (denv : VarId → ZMod p) (hl : l.eval denv = 0) :
    denv y = t.eval denv := by
  unfold denseSparseSolveAt at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denseLinScale_eval]
    have hs := l.eval_split x denv
    rw [h1, one_mul] at hs
    rw [hs] at hl
    linear_combination hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs := l.eval_split x denv
    rw [h2] at hs
    rw [hs] at hl
    linear_combination -hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denseLinScale_eval]
    have hs := l.eval_split x denv
    have h0 : l.coeff x * denv x + (l.others x).eval denv = 0 := by
      rw [← hs]
      exact hl
    linear_combination (l.coeff x)⁻¹ * h0 - denv x * h3

theorem denseSparseSolveAt_terms (l : DenseLinExpr p) (x y : VarId)
    (t : DenseLinExpr p) (h : denseSparseSolveAt l x = some (y, t)) :
    ∀ z ∈ t.terms.map Prod.fst, z ∈ l.terms.map Prod.fst := by
  unfold denseSparseSolveAt at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro z hz
    have hz' := DenseLinExpr.norm_terms_fst ((l.others x).scale (-1)) z hz
    rw [DenseLinExpr.scale_terms_fst] at hz'
    exact l.others_terms_fst_mem x z hz'
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun z hz => l.others_terms_fst_mem x z hz
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro z hz
    have hz' := DenseLinExpr.norm_terms_fst
      ((l.others x).scale (-(l.coeff x)⁻¹)) z hz
    rw [DenseLinExpr.scale_terms_fst] at hz'
    exact l.others_terms_fst_mem x z hz'

theorem denseSparseBest_sound (l : DenseLinExpr p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) (y : VarId) (t : DenseLinExpr p)
    (h : denseSparseBest l occ prot = some (y, t))
    (denv : VarId → ZMod p) (hl : l.eval denv = 0) :
    denv y = t.eval denv := by
  unfold denseSparseBest at h
  cases hm : denseBestPivot l occ prot with
  | none => simp [hm] at h
  | some q =>
      simp only [hm] at h
      exact denseSparseSolveAt_sound l q.1 y t h denv hl

theorem denseSparseBest_terms (l : DenseLinExpr p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) (y : VarId) (t : DenseLinExpr p)
    (h : denseSparseBest l occ prot = some (y, t)) :
    ∀ z ∈ t.terms.map Prod.fst, z ∈ l.terms.map Prod.fst := by
  unfold denseSparseBest at h
  cases hm : denseBestPivot l occ prot with
  | none => simp [hm] at h
  | some q =>
      simp only [hm] at h
      exact denseSparseSolveAt_terms l q.1 y t h

theorem denseReducedBest_sound (r : DenseGaussReduced p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) (y : VarId) (t : DenseLinExpr p)
    (h : denseReducedBest r occ prot = some (y, t))
    (denv : VarId → ZMod p) (hr : r.toExpr.eval denv = 0) :
    denv y = t.eval denv := by
  cases r with
  | nonlinear e => simp [denseReducedBest] at h
  | affine l =>
      exact denseSparseBest_sound l occ prot y t h denv
        (by simpa [DenseGaussReduced.toExpr, DenseLinExpr.toExpr_eval] using hr)

theorem denseReducedBest_terms (r : DenseGaussReduced p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) (y : VarId) (t : DenseLinExpr p)
    (h : denseReducedBest r occ prot = some (y, t)) :
    ∀ z ∈ t.terms.map Prod.fst, z ∈ r.support := by
  cases r with
  | nonlinear e => simp [denseReducedBest] at h
  | affine l => exact denseSparseBest_terms l occ prot y t h

theorem denseMarkowitzPick_sound (r : DenseGaussReduced p) (hint y : VarId)
    (t : DenseLinExpr p) (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (h : denseMarkowitzPick r hint occ prot = some (y, t))
    (denv : VarId → ZMod p) (hr : r.toExpr.eval denv = 0) :
    denv y = t.eval denv := by
  unfold denseMarkowitzPick at h
  cases r with
  | nonlinear e =>
      simp only at h
      exact denseReducedBest_sound (.nonlinear e) occ prot y t h denv hr
  | affine l =>
      cases hs : denseSparseSolveAt l hint with
      | none =>
          simp only [hs] at h
          exact denseReducedBest_sound (.affine l) occ prot y t h denv hr
      | some q =>
          have hq : q = (y, t) := Option.some.inj (by simpa [hs] using h)
          rw [hq] at hs
          exact denseSparseSolveAt_sound l hint y t hs denv
            (by simpa [DenseGaussReduced.toExpr, DenseLinExpr.toExpr_eval] using hr)

theorem denseMarkowitzPick_terms (r : DenseGaussReduced p) (hint y : VarId)
    (t : DenseLinExpr p) (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (h : denseMarkowitzPick r hint occ prot = some (y, t)) :
    ∀ z ∈ t.terms.map Prod.fst, z ∈ r.support := by
  unfold denseMarkowitzPick at h
  cases r with
  | nonlinear e =>
      simp only at h
      exact denseReducedBest_terms (.nonlinear e) occ prot y t h
  | affine l =>
      cases hs : denseSparseSolveAt l hint with
      | none =>
          simp only [hs] at h
          exact denseReducedBest_terms (.affine l) occ prot y t h
      | some q =>
          have hq : q = (y, t) := Option.some.inj (by simpa [hs] using h)
          rw [hq] at hs
          exact denseSparseSolveAt_terms l hint y t hs

theorem DenseSparseSolved.clearDeps_lookup (dσ : DenseSparseSolved p) (x y : VarId) :
    (dσ.clearDeps x).lookup y = dσ.lookup y := by
  rfl

@[simp] theorem DenseSparseSolved.empty_lookup (capacity : Nat) (x : VarId) :
    (DenseSparseSolved.empty capacity : DenseSparseSolved p).lookup x = none := by
  simp only [DenseSparseSolved.lookup, DenseSparseSolved.empty]
  by_cases h : x.index < capacity
  · rw [Array.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [Array.getElem?_eq_none (by simpa using h)]
    rfl

theorem DenseSparseSolved.markOldDeps_rows (dσ : DenseSparseSolved p)
    (terms : List (VarId × ZMod p)) :
    (markOldDeps dσ terms).rows = dσ.rows := by
  induction terms generalizing dσ with
  | nil => rfl
  | cons yc rest ih =>
      simp only [markOldDeps]
      rw [ih]

theorem DenseSparseSolved.addNewDeps_rows (dσ : DenseSparseSolved p) (owner : VarId)
    (terms : List (VarId × ZMod p)) :
    (addNewDeps owner dσ terms).rows = dσ.rows := by
  induction terms generalizing dσ with
  | nil => rfl
  | cons yc rest ih =>
      simp only [addNewDeps]
      split
      · rw [ih]
      · rw [ih]

theorem DenseSparseSolved.removeOldDeps_rows (dσ : DenseSparseSolved p) (owner : VarId)
    (terms : List (VarId × ZMod p)) :
    (removeOldDeps owner dσ terms).rows = dσ.rows := by
  induction terms generalizing dσ with
  | nil => rfl
  | cons yc rest ih =>
      simp only [removeOldDeps]
      split
      · rw [ih]
      · rw [ih]

theorem DenseSparseSolved.clearNewDepMarks_rows (dσ : DenseSparseSolved p)
    (terms : List (VarId × ZMod p)) :
    (clearNewDepMarks dσ terms).rows = dσ.rows := by
  induction terms generalizing dσ with
  | nil => rfl
  | cons yc rest ih =>
      simp only [clearNewDepMarks]
      rw [ih]

theorem DenseSparseSolved.diffDeps_rows (dσ : DenseSparseSolved p) (owner : VarId)
    (oldTerms newTerms : List (VarId × ZMod p)) :
    (dσ.diffDeps owner oldTerms newTerms).rows = dσ.rows := by
  simp only [diffDeps, clearNewDepMarks_rows, removeOldDeps_rows, addNewDeps_rows,
    markOldDeps_rows]

theorem DenseSparseSolved.replace_rows (dσ : DenseSparseSolved p) (x : VarId)
    (t : DenseLinExpr p) :
    (dσ.replace x t).rows = dσ.rows.setIfInBounds x.index (some t) := by
  simp only [DenseSparseSolved.replace, DenseSparseSolved.diffDeps_rows]

theorem DenseSparseSolved.replace_preserves {Q : VarId → DenseLinExpr p → Prop}
    (dσ : DenseSparseSolved p) (x : VarId) (t : DenseLinExpr p)
    (hσ : ∀ i row, dσ.lookup i = some row → Q i row) (ht : Q x t) :
    ∀ i row, (dσ.replace x t).lookup i = some row → Q i row := by
  intro i row hi
  simp only [DenseSparseSolved.lookup, dσ.replace_rows x t,
    Array.getElem?_setIfInBounds] at hi
  split at hi
  · next hxi =>
    split at hi
    · simp only [Option.join_some, Option.some.injEq] at hi
      have hix : x = i := by
        cases x
        cases i
        simp_all
      subst i
      simpa only [hi] using ht
    · simp at hi
  · exact hσ i row hi

theorem denseSparseAdoptStep_preserves {Q : VarId → DenseLinExpr p → Prop}
    (trackChanged : Bool) (x : VarId) (t : DenseLinExpr p)
    (acc : DenseSparseAdoption p) (y : VarId)
    (hacc : ∀ i row, acc.solved.lookup i = some row → Q i row)
    (hsubst : ∀ i row, Q i row → Q i (denseLinSubst row x t)) :
    ∀ i row, (denseSparseAdoptStep trackChanged x t acc y).solved.lookup i = some row →
      Q i row := by
  intro i row hi
  cases hy : acc.solved.lookup y with
  | none =>
      simp only [denseSparseAdoptStep, hy] at hi
      exact hacc i row hi
  | some old =>
      simp only [denseSparseAdoptStep, hy] at hi
      exact DenseSparseSolved.replace_preserves acc.solved y (denseLinSubst old x t)
        hacc (hsubst y old (hacc y old hy)) i row hi

theorem denseSparseAdopt_preserves {Q : VarId → DenseLinExpr p → Prop}
    (trackChanged : Bool) (dσ : DenseSparseSolved p) (x : VarId) (t : DenseLinExpr p)
    (hσ : ∀ i row, dσ.lookup i = some row → Q i row) (ht : Q x t)
    (hsubst : ∀ i row, Q i row → Q i (denseLinSubst row x t)) :
    ∀ i row, (denseSparseAdopt trackChanged dσ x t).solved.lookup i = some row → Q i row := by
  let initial : DenseSparseAdoption p :=
    { solved := dσ.clearDeps x
      changed :=
        if trackChanged then
          t.terms.foldl (fun changed yc => changed.insert yc.1)
            (Std.HashSet.emptyWithCapacity t.terms.length)
        else ∅ }
  have hinitial : ∀ i row, initial.solved.lookup i = some row → Q i row := by
    intro i row hi
    exact hσ i row (by simpa [initial, DenseSparseSolved.clearDeps_lookup] using hi)
  have hfold :
      ∀ (ys : List VarId) (acc : DenseSparseAdoption p),
        (∀ i row, acc.solved.lookup i = some row → Q i row) →
        ∀ i row, (ys.foldl (denseSparseAdoptStep trackChanged x t) acc).solved.lookup i =
          some row →
          Q i row := by
    intro ys
    induction ys with
    | nil => intro acc hacc; exact hacc
    | cons y rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        exact ih _ (denseSparseAdoptStep_preserves trackChanged x t acc y hacc hsubst)
  intro i row hi
  have hout := hfold (dσ.deps x).toList initial hinitial
  exact DenseSparseSolved.replace_preserves _ x t (hout) ht i row
    (by simpa [denseSparseAdopt, initial, Std.HashSet.fold_eq_foldl_toList] using hi)

theorem denseSparseGaussLoop_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : DenseGaussOcc) (prot : DenseGaussProt) :
    ∀ (pending : List (DenseExpr p)) (dσ : DenseSparseSolved p),
      (∀ c ∈ pending, c ∈ d.algebraicConstraints) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
        dσ.fn i = some t → denv i = t.eval denv) →
      (∀ i t, dσ.fn i = some t → ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
          (denseSparseGaussLoop occ prot pending dσ).fn i = some t →
          denv i = t.eval denv) ∧
      (∀ i t, (denseSparseGaussLoop occ prot pending dσ).fn i = some t →
          ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) := by
  intro pending
  induction pending with
  | nil => intro dσ _ hσs hσv; exact ⟨hσs, hσv⟩
  | cons c rest ih =>
      intro dσ hpend hσs hσv
      have hcmem : c ∈ d.algebraicConstraints := hpend c (List.mem_cons_self ..)
      have hrest : ∀ c' ∈ rest, c' ∈ d.algebraicConstraints :=
        fun c' h' => hpend c' (List.mem_cons_of_mem _ h')
      let c' := denseSparseSubstSolved dσ c
      cases hpick : denseReducedBest (denseSparseSubstSolved dσ c) occ prot with
      | none =>
          simp only [denseSparseGaussLoop, hpick]
          exact ih dσ hrest hσs hσv
      | some xt =>
          obtain ⟨x, t⟩ := xt
          have hcclosed : c'.Closed (· ∈ d.occ) := by
            change (denseSparseSubstSolved dσ c).Closed (· ∈ d.occ)
            rw [denseSparseSubstSolved_eq]
            apply denseSparseSubstF_closed dσ.fn c
            · intro z hz
              exact DenseConstraintSystem.mem_occ_of_constraint hcmem hz
            · exact hσv
          have hx : ∀ denv, d.satisfies bs denv → denv x = t.eval denv := by
            intro denv hsat
            apply denseReducedBest_sound c' occ prot x t hpick denv
            change (denseSparseSubstSolved dσ c).toExpr.eval denv = 0
            rw [denseSparseSubstSolved_eq,
              denseSparseSubstF_eval dσ.fn c denv (hσs denv hsat)]
            exact hsat.1 c hcmem
          have htocc : ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ := by
            intro z hz
            exact hcclosed z (denseReducedBest_terms c' occ prot x t hpick z hz)
          simp only [denseSparseGaussLoop, hpick]
          refine ih _ hrest ?_ ?_
          · intro denv hsat
            exact denseSparseAdopt_preserves false dσ x t (hσs denv hsat)
              (hx denv hsat)
              (fun y s hy => hy.trans
                (denseLinSubst_eval s x t denv (hx denv hsat)).symm)
          · exact denseSparseAdopt_preserves false dσ x t hσv htocc
              (fun y s hs => denseLinSubst_terms_closed s x t (· ∈ d.occ) hs htocc)

theorem denseSparseMarkowitzLoop_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (sources : Array (DenseExpr p))
    (hsrc : ∀ (i : Nat) (c : DenseExpr p),
      sources[i]? = some c → c ∈ d.algebraicConstraints) :
    ∀ (fuel : Nat) (st : DenseMarkowitzState p) (dσ : DenseSparseSolved p),
      (∀ denv, d.satisfies bs denv → ∀ i t,
        dσ.fn i = some t → denv i = t.eval denv) →
      (∀ i t, dσ.fn i = some t → ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) →
      (∀ denv, d.satisfies bs denv → ∀ i t,
          (denseMarkowitzLoop occ prot sources fuel st dσ).fn i = some t →
          denv i = t.eval denv) ∧
      (∀ i t, (denseMarkowitzLoop occ prot sources fuel st dσ).fn i = some t →
          ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) := by
  intro fuel
  induction fuel with
  | zero => intro st dσ hσs hσv; exact ⟨hσs, hσv⟩
  | succ fuel ih =>
      intro st dσ hσs hσv
      cases hpop : denseMarkowitzPopValid (st.heap.size + 1) st with
      | none =>
          simp only [denseMarkowitzLoop, hpop]
          exact ⟨hσs, hσv⟩
      | some out =>
          obtain ⟨entry, st'⟩ := out
          cases hsource : sources[entry.rowId]? with
          | none =>
              simp only [denseMarkowitzLoop, hpop, hsource]
              exact ih _ _ hσs hσv
          | some c =>
              have hcmem : c ∈ d.algebraicConstraints := hsrc entry.rowId c hsource
              let c' := denseSparseSubstSolved dσ c
              cases hpick :
                  denseMarkowitzPick (denseSparseSubstSolved dσ c) entry.pivot occ prot with
              | none =>
                  simp only [denseMarkowitzLoop, hpop, hsource, hpick]
                  exact ih _ _ hσs hσv
              | some xt =>
                  obtain ⟨x, t⟩ := xt
                  have hcclosed : c'.Closed (· ∈ d.occ) := by
                    change (denseSparseSubstSolved dσ c).Closed (· ∈ d.occ)
                    rw [denseSparseSubstSolved_eq]
                    apply denseSparseSubstF_closed dσ.fn c
                    · intro z hz
                      exact DenseConstraintSystem.mem_occ_of_constraint hcmem hz
                    · exact hσv
                  have hx : ∀ denv, d.satisfies bs denv → denv x = t.eval denv := by
                    intro denv hsat
                    apply denseMarkowitzPick_sound c' entry.pivot x t occ prot hpick denv
                    change (denseSparseSubstSolved dσ c).toExpr.eval denv = 0
                    rw [denseSparseSubstSolved_eq,
                      denseSparseSubstF_eval dσ.fn c denv (hσs denv hsat)]
                    exact hsat.1 c hcmem
                  have htocc : ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ := by
                    intro z hz
                    exact hcclosed z
                      (denseMarkowitzPick_terms c' entry.pivot x t occ prot hpick z hz)
                  let adopted := denseSparseAdopt true dσ x t
                  let dσ' := adopted.solved
                  have hnexts : ∀ denv, d.satisfies bs denv → ∀ i u,
                      dσ'.fn i = some u → denv i = u.eval denv := by
                    intro denv hsat
                    exact denseSparseAdopt_preserves true dσ x t (hσs denv hsat)
                      (hx denv hsat)
                      (fun y s hy => hy.trans
                        (denseLinSubst_eval s x t denv (hx denv hsat)).symm)
                  have hnextv : ∀ i u, dσ'.fn i = some u →
                      ∀ z ∈ u.terms.map Prod.fst, z ∈ d.occ := by
                    exact denseSparseAdopt_preserves true dσ x t hσv htocc
                      (fun y s hs =>
                        denseLinSubst_terms_closed s x t (· ∈ d.occ) hs htocc)
                  simp only [denseMarkowitzLoop, hpop, hsource, hpick]
                  exact ih _ dσ' hnexts hnextv

theorem denseSparseMarkowitzSchedule_sound (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) (capacity : Nat) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseMarkowitzSchedule d.algebraicConstraints occ prot capacity).fn i = some t →
        denv i = t.eval denv) ∧
    (∀ i t, (denseMarkowitzSchedule d.algebraicConstraints occ prot capacity).fn i = some t →
        ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) := by
  apply denseSparseMarkowitzLoop_sound bs d occ prot d.algebraicConstraints.toArray
  · intro i c hc
    rw [List.getElem?_toArray] at hc
    exact List.mem_of_getElem? hc
  · intro _ _ _ _ h
    simp [DenseSparseSolved.fn] at h
  · intro _ _ h
    simp [DenseSparseSolved.fn] at h

theorem denseSparseSourceOrderSchedule_sound (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) (capacity : Nat) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseSourceOrderSchedule d.algebraicConstraints occ prot capacity).fn i = some t →
        denv i = t.eval denv) ∧
    (∀ i t, (denseSourceOrderSchedule d.algebraicConstraints occ prot capacity).fn i = some t →
        ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) := by
  have hfirst := denseSparseGaussLoop_sound bs d occ prot
    d.algebraicConstraints (DenseSparseSolved.empty capacity)
    (fun _c hc => hc)
    (fun _ _ _ _ hti => by simp [DenseSparseSolved.fn] at hti)
    (fun _ _ hti => by simp [DenseSparseSolved.fn] at hti)
  by_cases hempty :
      (denseSparseGaussLoop occ prot d.algebraicConstraints
        (DenseSparseSolved.empty capacity)).isEmpty
  · simpa [denseSourceOrderSchedule, hempty] using hfirst
  · have hsecond := denseSparseGaussLoop_sound bs d occ prot
      d.algebraicConstraints
      (denseSparseGaussLoop occ prot d.algebraicConstraints
        (DenseSparseSolved.empty capacity))
      (fun _c hc => hc) hfirst.1 hfirst.2
    simpa [denseSourceOrderSchedule, hempty] using hsecond

theorem denseGaussSparseSchedule_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : DenseGaussOcc) (prot : DenseGaussProt) (capacity : Nat) :
    (∀ denv, d.satisfies bs denv → ∀ i row,
        (denseGaussSparseSchedule d.algebraicConstraints occ prot capacity).lookup i =
          some row →
        denv i = row.eval denv) ∧
    (∀ i row,
        (denseGaussSparseSchedule d.algebraicConstraints occ prot capacity).lookup i =
          some row →
        ∀ z ∈ row.terms.map Prod.fst, z ∈ d.occ) := by
  unfold denseGaussSparseSchedule
  split
  · exact denseSparseSourceOrderSchedule_sound bs d occ prot capacity
  · exact denseSparseMarkowitzSchedule_sound bs d occ prot capacity

theorem DenseSparseSolved.fnExpr_lookup (dσ : DenseSparseSolved p)
    (i : VarId) (e : DenseExpr p) (h : dσ.fnExpr i = some e) :
    ∃ row, dσ.lookup i = some row ∧ e = row.toExpr := by
  unfold DenseSparseSolved.fnExpr at h
  cases hrow : dσ.lookup i with
  | none => simp [hrow] at h
  | some row =>
      simp only [hrow, Option.map_some, Option.some.injEq] at h
      exact ⟨row, rfl, h.symm⟩

theorem denseSparseExprSubst_eq (dσ : DenseSparseSolved p) (e : DenseExpr p) :
    denseSparseExprSubst dσ e = e.substF dσ.fnExpr := by
  induction e with
  | const n => rfl
  | var x =>
      simp only [denseSparseExprSubst, DenseExpr.substF, DenseSparseSolved.fnExpr]
      cases hrow : dσ.lookup x <;> rfl
  | add a b iha ihb => simp only [denseSparseExprSubst, DenseExpr.substF, iha, ihb]
  | mul a b iha ihb => simp only [denseSparseExprSubst, DenseExpr.substF, iha, ihb]

theorem denseSparseBISubst_eq (dσ : DenseSparseSolved p)
    (bi : BusInteraction (DenseExpr p)) :
    denseSparseBISubst dσ bi = denseBIsubstF bi dσ.fnExpr := by
  have hfn : denseSparseExprSubst dσ = fun e => e.substF dσ.fnExpr :=
    funext (denseSparseExprSubst_eq dσ)
  cases bi
  simp only [denseSparseBISubst, denseBIsubstF, hfn]

theorem DenseConstraintSystem.substSparse_eq
    (d : DenseConstraintSystem p) (dσ : DenseSparseSolved p) :
    d.substSparse dσ = d.substF dσ.fnExpr := by
  have hfn : denseSparseExprSubst dσ = fun e => e.substF dσ.fnExpr :=
    funext (denseSparseExprSubst_eq dσ)
  have hbi : denseSparseBISubst dσ = fun bi => denseBIsubstF bi dσ.fnExpr :=
    funext (denseSparseBISubst_eq dσ)
  cases d
  simp only [DenseConstraintSystem.substSparse, DenseConstraintSystem.substF,
    hfn, hbi]

/-! ## The pass's correctness -/

/-- The scheduled sparse rows are entailed and occurrence-closed. -/
theorem denseGaussElimSized_loop_invariant (capacity : Nat)
    (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ i e,
        (denseGaussSparseSchedule d.algebraicConstraints
          (denseOccurrenceMap capacity d) (denseProtectedVars capacity d bs) capacity).fnExpr i =
            some e →
          denv i = e.eval denv) ∧
    (∀ i e, (denseGaussSparseSchedule d.algebraicConstraints
        (denseOccurrenceMap capacity d) (denseProtectedVars capacity d bs) capacity).fnExpr i =
          some e →
        ∀ z ∈ e.vars, z ∈ d.occ) := by
  have hs := denseGaussSparseSchedule_sound bs d (denseOccurrenceMap capacity d)
    (denseProtectedVars capacity d bs) capacity
  constructor
  · intro denv hsat i e he
    obtain ⟨row, hrow, rfl⟩ :=
      DenseSparseSolved.fnExpr_lookup _ i e he
    rw [DenseLinExpr.toExpr_eval]
    exact hs.1 denv hsat i row hrow
  · intro i e he z hz
    obtain ⟨row, hrow, rfl⟩ :=
      DenseSparseSolved.fnExpr_lookup _ i e he
    exact hs.2 i row hrow z (DenseLinExpr.toExpr_vars row z hz)

theorem denseGaussElimSized_covered (capacity : Nat) (reg : VarRegistry)
    (bs : BusSemantics p) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseGaussElimSized capacity bs d).CoveredBy reg := by
  simp only [denseGaussElimSized]
  split
  · exact hcov
  · rw [DenseConstraintSystem.substSparse_eq]
    refine DenseConstraintSystem.substF_covered hcov ?_
    intro i _ e he z hz
    exact DenseConstraintSystem.occ_valid hcov z
      ((denseGaussElimSized_loop_invariant capacity bs d).2 i e he z hz)

theorem denseGaussElimSized_correct (capacity : Nat) (reg : VarRegistry)
    (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseGaussElimSized capacity bs d) [] bs := by
  have hinv := denseGaussElimSized_loop_invariant capacity bs d
  simp only [denseGaussElimSized]
  split
  · exact DensePassCorrect.refl reg.isInput d bs
  · rw [DenseConstraintSystem.substSparse_eq]
    exact DenseConstraintSystem.substF_denseCorrect d _ bs reg.isInput
      (fun denv hsat i e he => hinv.1 denv hsat i e he)
      (fun i e he z hz => hinv.2 i e he z hz)

/-- The wired dense Gauss-elimination pass. -/
def denseGaussElimPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofDenseStep (fun reg bs _ d hcov =>
    DenseNativeStep.ofSame bs
      (denseGaussElimSized_covered reg.byId.size reg bs d hcov)
      (denseGaussElimSized_correct reg.byId.size reg bs d))

end ApcOptimizer.Dense
