import ApcOptimizer.Implementation.OptimizerPasses.Gauss
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

theorem denseLinSubst_eval (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p)
    (denv : VarId → ZMod p) (hx : denv x = t.eval denv) :
    (denseLinSubst s x t).eval denv = s.eval denv := by
  rw [denseLinSubst, denseLinSubstF_eval]
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

theorem denseSparseBest_sound (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) (y : VarId) (t : DenseLinExpr p)
    (h : denseSparseBest l occ prot = some (y, t))
    (denv : VarId → ZMod p) (hl : l.eval denv = 0) :
    denv y = t.eval denv := by
  unfold denseSparseBest at h
  cases hm : (densePivotDescs l occ prot).argmin Prod.snd with
  | none => simp [hm] at h
  | some q =>
      simp only [hm] at h
      exact denseSparseSolveAt_sound l q.1 y t h denv hl

theorem denseSparseBest_terms (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) (y : VarId) (t : DenseLinExpr p)
    (h : denseSparseBest l occ prot = some (y, t)) :
    ∀ z ∈ t.terms.map Prod.fst, z ∈ l.terms.map Prod.fst := by
  unfold denseSparseBest at h
  cases hm : (densePivotDescs l occ prot).argmin Prod.snd with
  | none => simp [hm] at h
  | some q =>
      simp only [hm] at h
      exact denseSparseSolveAt_terms l q.1 y t h

theorem denseReducedBest_sound (r : DenseGaussReduced p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) (y : VarId) (t : DenseLinExpr p)
    (h : denseReducedBest r occ prot = some (y, t))
    (denv : VarId → ZMod p) (hr : r.toExpr.eval denv = 0) :
    denv y = t.eval denv := by
  cases r with
  | nonlinear e => simp [denseReducedBest] at h
  | affine l =>
      exact denseSparseBest_sound l occ prot y t h denv
        (by simpa [DenseGaussReduced.toExpr, DenseLinExpr.toExpr_eval] using hr)

theorem denseReducedBest_terms (r : DenseGaussReduced p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) (y : VarId) (t : DenseLinExpr p)
    (h : denseReducedBest r occ prot = some (y, t)) :
    ∀ z ∈ t.terms.map Prod.fst, z ∈ r.support := by
  cases r with
  | nonlinear e => simp [denseReducedBest] at h
  | affine l => exact denseSparseBest_terms l occ prot y t h

theorem denseMarkowitzPick_sound (r : DenseGaussReduced p) (hint y : VarId)
    (t : DenseLinExpr p) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
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
    (t : DenseLinExpr p) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
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

theorem DenseSparseSolved.insertAll_map :
    ∀ (pairs : List (VarId × DenseLinExpr p)) (dσ : DenseSparseSolved p),
      (dσ.insertAll pairs).map =
        pairs.foldl (fun m pr => m.insert pr.1 pr.2) dσ.map := by
  intro pairs
  induction pairs with
  | nil => intro dσ; rfl
  | cons hd tl ih =>
      intro dσ
      obtain ⟨x, t⟩ := hd
      simp only [DenseSparseSolved.insertAll, List.foldl_cons]
      rw [ih]

theorem sparseFoldlInsert_preserves {Q : VarId → DenseLinExpr p → Prop} :
    ∀ (pairs : List (VarId × DenseLinExpr p))
      (m : Std.HashMap VarId (DenseLinExpr p)),
      (∀ i t, m[i]? = some t → Q i t) → (∀ pr ∈ pairs, Q pr.1 pr.2) →
      ∀ i t, (pairs.foldl (fun out pr => out.insert pr.1 pr.2) m)[i]? = some t →
        Q i t := by
  intro pairs
  induction pairs with
  | nil => intro m hm _ i t ht; exact hm i t ht
  | cons hd rest ih =>
      intro m hm hpairs i t ht
      obtain ⟨x, t0⟩ := hd
      simp only [List.foldl_cons] at ht
      refine ih (m.insert x t0) ?_
        (fun pr hpr => hpairs pr (List.mem_cons_of_mem _ hpr)) i t ht
      intro j s hjs
      rw [Std.HashMap.getElem?_insert] at hjs
      split_ifs at hjs with hjx
      · simp only [Option.some.injEq] at hjs
        have hj : x = j := by simpa using hjx
        rw [← hjs, ← hj]
        exact hpairs (x, t0) (List.mem_cons_self ..)
      · exact hm j s hjs

theorem DenseSparseSolved.insertAll_preserves {Q : VarId → DenseLinExpr p → Prop}
    (pairs : List (VarId × DenseLinExpr p)) (dσ : DenseSparseSolved p)
    (hσ : ∀ i t, dσ.fn i = some t → Q i t)
    (hpairs : ∀ pr ∈ pairs, Q pr.1 pr.2) :
    ∀ i t, (dσ.insertAll pairs).fn i = some t → Q i t := by
  intro i t ht
  simp only [DenseSparseSolved.fn, DenseSparseSolved.insertAll_map] at ht
  exact sparseFoldlInsert_preserves pairs dσ.map hσ hpairs i t ht

theorem denseSparseGaussLoop_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
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
      let c' := denseSparseSubstF dσ.fn c
      cases hpick : denseReducedBest (denseSparseSubstF dσ.fn c) occ prot with
      | none =>
          simp only [denseSparseGaussLoop, hpick]
          exact ih dσ hrest hσs hσv
      | some xt =>
          obtain ⟨x, t⟩ := xt
          have hcclosed : c'.Closed (· ∈ d.occ) := by
            apply denseSparseSubstF_closed dσ.fn c
            · intro z hz
              exact DenseConstraintSystem.mem_occ_of_constraint hcmem hz
            · exact hσv
          have hx : ∀ denv, d.satisfies bs denv → denv x = t.eval denv := by
            intro denv hsat
            apply denseReducedBest_sound c' occ prot x t hpick denv
            rw [denseSparseSubstF_eval dσ.fn c denv (hσs denv hsat)]
            exact hsat.1 c hcmem
          have htocc : ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ := by
            intro z hz
            exact hcclosed z (denseReducedBest_terms c' occ prot x t hpick z hz)
          have htouched : ∀ y s, (y, s) ∈
                ((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
                  (dσ.map[y]?).bind
                    (fun s => if s.mentions x then some (y, s) else none)) →
              dσ.fn y = some s := by
            intro y s hys
            obtain ⟨_, _, hy'⟩ := List.mem_filterMap.1 hys
            obtain ⟨s', hs', hif⟩ := Option.bind_eq_some_iff.1 hy'
            by_cases hm : s'.mentions x
            · rw [if_pos hm] at hif
              simp only [Option.some.injEq, Prod.mk.injEq] at hif
              obtain ⟨rfl, rfl⟩ := hif
              exact hs'
            · rw [if_neg hm] at hif
              exact absurd hif (by simp)
          simp only [denseSparseGaussLoop, hpick]
          refine ih _ hrest ?_ ?_
          · intro denv hsat
            refine DenseSparseSolved.insertAll_preserves _ dσ (hσs denv hsat) ?_
            intro pr hpr
            rcases List.mem_append.1 hpr with hin | hin
            · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
              have hmemys : dσ.fn y = some s := htouched y s hys
              have hy : denv y = s.eval denv := hσs denv hsat y s hmemys
              exact hy.trans (denseLinSubst_eval s x t denv (hx denv hsat)).symm
            · rw [List.mem_singleton] at hin
              subst hin
              exact hx denv hsat
          · refine DenseSparseSolved.insertAll_preserves _ dσ hσv ?_
            intro pr hpr
            rcases List.mem_append.1 hpr with hin | hin
            · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
              have hmemys : dσ.fn y = some s := htouched y s hys
              exact denseLinSubst_terms_closed s x t (· ∈ d.occ)
                (hσv y s hmemys) htocc
            · rw [List.mem_singleton] at hin
              subst hin
              exact htocc

theorem denseSparseMarkowitzLoop_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
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
              let c' := denseSparseSubstF dσ.fn c
              cases hpick :
                  denseMarkowitzPick (denseSparseSubstF dσ.fn c) entry.pivot occ prot with
              | none =>
                  simp only [denseMarkowitzLoop, hpop, hsource, hpick]
                  exact ih _ _ hσs hσv
              | some xt =>
                  obtain ⟨x, t⟩ := xt
                  have hcclosed : c'.Closed (· ∈ d.occ) := by
                    apply denseSparseSubstF_closed dσ.fn c
                    · intro z hz
                      exact DenseConstraintSystem.mem_occ_of_constraint hcmem hz
                    · exact hσv
                  have hx : ∀ denv, d.satisfies bs denv → denv x = t.eval denv := by
                    intro denv hsat
                    apply denseMarkowitzPick_sound c' entry.pivot x t occ prot hpick denv
                    rw [denseSparseSubstF_eval dσ.fn c denv (hσs denv hsat)]
                    exact hsat.1 c hcmem
                  have htocc : ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ := by
                    intro z hz
                    exact hcclosed z
                      (denseMarkowitzPick_terms c' entry.pivot x t occ prot hpick z hz)
                  have htouched : ∀ y s, (y, s) ∈
                        ((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
                          (dσ.map[y]?).bind
                            (fun s => if s.mentions x then some (y, s) else none)) →
                      dσ.fn y = some s := by
                    intro y s hys
                    obtain ⟨_, _, hy'⟩ := List.mem_filterMap.1 hys
                    obtain ⟨s', hs', hif⟩ := Option.bind_eq_some_iff.1 hy'
                    by_cases hm : s'.mentions x
                    · rw [if_pos hm] at hif
                      simp only [Option.some.injEq, Prod.mk.injEq] at hif
                      obtain ⟨rfl, rfl⟩ := hif
                      exact hs'
                    · rw [if_neg hm] at hif
                      exact absurd hif (by simp)
                  let pairs := denseMarkowitzAdoptPairs dσ x t
                  let dσ' := dσ.insertAll pairs
                  have hnexts : ∀ denv, d.satisfies bs denv → ∀ i u,
                      dσ'.fn i = some u → denv i = u.eval denv := by
                    intro denv hsat
                    refine DenseSparseSolved.insertAll_preserves pairs dσ
                      (hσs denv hsat) ?_
                    intro pr hpr
                    unfold denseMarkowitzAdoptPairs at hpr
                    rcases List.mem_append.1 hpr with hin | hin
                    · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
                      have hmemys : dσ.fn y = some s := htouched y s hys
                      have hy : denv y = s.eval denv := hσs denv hsat y s hmemys
                      exact hy.trans
                        (denseLinSubst_eval s x t denv (hx denv hsat)).symm
                    · rw [List.mem_singleton] at hin
                      subst hin
                      exact hx denv hsat
                  have hnextv : ∀ i u, dσ'.fn i = some u →
                      ∀ z ∈ u.terms.map Prod.fst, z ∈ d.occ := by
                    refine DenseSparseSolved.insertAll_preserves pairs dσ hσv ?_
                    intro pr hpr
                    unfold denseMarkowitzAdoptPairs at hpr
                    rcases List.mem_append.1 hpr with hin | hin
                    · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 hin
                      have hmemys : dσ.fn y = some s := htouched y s hys
                      exact denseLinSubst_terms_closed s x t (· ∈ d.occ)
                        (hσv y s hmemys) htocc
                    · rw [List.mem_singleton] at hin
                      subst hin
                      exact htocc
                  simp only [denseMarkowitzLoop, hpop, hsource, hpick]
                  exact ih _ dσ' hnexts hnextv

theorem denseSparseMarkowitzSchedule_sound (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseMarkowitzSchedule d.algebraicConstraints occ prot).fn i = some t →
        denv i = t.eval denv) ∧
    (∀ i t, (denseMarkowitzSchedule d.algebraicConstraints occ prot).fn i = some t →
        ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) := by
  apply denseSparseMarkowitzLoop_sound bs d occ prot d.algebraicConstraints.toArray
  · intro i c hc
    rw [List.getElem?_toArray] at hc
    exact List.mem_of_getElem? hc
  · intro _ _ _ _ h
    exact absurd h (by simp [DenseSparseSolved.fn, DenseSparseSolved.empty])
  · intro _ _ h
    exact absurd h (by simp [DenseSparseSolved.fn, DenseSparseSolved.empty])

theorem denseSparseSourceOrderSchedule_sound (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseSourceOrderSchedule d.algebraicConstraints occ prot).fn i = some t →
        denv i = t.eval denv) ∧
    (∀ i t, (denseSourceOrderSchedule d.algebraicConstraints occ prot).fn i = some t →
        ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) := by
  have hfirst := denseSparseGaussLoop_sound bs d occ prot
    d.algebraicConstraints DenseSparseSolved.empty
    (fun _c hc => hc)
    (fun _ _ _ _ hti =>
      absurd hti (by simp [DenseSparseSolved.fn, DenseSparseSolved.empty]))
    (fun _ _ hti =>
      absurd hti (by simp [DenseSparseSolved.fn, DenseSparseSolved.empty]))
  by_cases hempty :
      (denseSparseGaussLoop occ prot d.algebraicConstraints
        DenseSparseSolved.empty).map.isEmpty
  · simpa [denseSourceOrderSchedule, hempty] using hfirst
  · have hsecond := denseSparseGaussLoop_sound bs d occ prot
      d.algebraicConstraints
      (denseSparseGaussLoop occ prot d.algebraicConstraints DenseSparseSolved.empty)
      (fun _c hc => hc) hfirst.1 hfirst.2
    simpa [denseSourceOrderSchedule, hempty] using hsecond

theorem DenseSparseSolved.materialize_lookup (dσ : DenseSparseSolved p)
    (i : VarId) (e : DenseExpr p) (h : dσ.materialize.fn i = some e) :
    ∃ row, dσ.fn i = some row ∧ e = row.toExpr := by
  simp only [DenseSparseSolved.materialize, DenseSolved.fn] at h
  let pairs := dσ.map.toList.map (fun xt => (xt.1, xt.2.toExpr))
  have hpairs :
      pairs.foldl (fun out xt => out.insert xt.1 xt.2)
          (∅ : Std.HashMap VarId (DenseExpr p)) =
        dσ.map.toList.foldl (fun out xt => out.insert xt.1 xt.2.toExpr) ∅ := by
    exact List.foldl_map
  rw [← hpairs] at h
  apply foldl_insert_getElem pairs
    (∅ : Std.HashMap VarId (DenseExpr p))
    (Q := fun j out => ∃ row, dσ.fn j = some row ∧ out = row.toExpr)
  · intro j out hj
    exact absurd hj (by simp)
  · intro pr hpr
    obtain ⟨xt, hxt, rfl⟩ := List.mem_map.1 hpr
    refine ⟨xt.2, ?_, rfl⟩
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.1 hxt
  · exact h

theorem DenseSparseSolved.materialize_sound (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (dσ : DenseSparseSolved p)
    (hs : ∀ denv, d.satisfies bs denv → ∀ i t,
      dσ.fn i = some t → denv i = t.eval denv)
    (hv : ∀ i t, dσ.fn i = some t →
      ∀ z ∈ t.terms.map Prod.fst, z ∈ d.occ) :
    (∀ denv, d.satisfies bs denv → ∀ i e,
        dσ.materialize.fn i = some e → denv i = e.eval denv) ∧
    (∀ i e, dσ.materialize.fn i = some e → ∀ z ∈ e.vars, z ∈ d.occ) := by
  constructor
  · intro denv hsat i e he
    obtain ⟨row, hrow, rfl⟩ := dσ.materialize_lookup i e he
    rw [DenseLinExpr.toExpr_eval]
    exact hs denv hsat i row hrow
  · intro i e he z hz
    obtain ⟨row, hrow, rfl⟩ := dσ.materialize_lookup i e he
    exact hv i row hrow z (DenseLinExpr.toExpr_vars row z hz)

theorem denseGaussSchedule_sound (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseGaussSchedule d.algebraicConstraints occ prot).fn i = some t →
        denv i = t.eval denv) ∧
    (∀ i t, (denseGaussSchedule d.algebraicConstraints occ prot).fn i = some t →
        ∀ z ∈ t.vars, z ∈ d.occ) := by
  unfold denseGaussSchedule
  split
  · exact DenseSparseSolved.materialize_sound bs d _
      (denseSparseSourceOrderSchedule_sound bs d occ prot).1
      (denseSparseSourceOrderSchedule_sound bs d occ prot).2
  · exact DenseSparseSolved.materialize_sound bs d _
      (denseSparseMarkowitzSchedule_sound bs d occ prot).1
      (denseSparseMarkowitzSchedule_sound bs d occ prot).2


/-! ## The pass's correctness -/

/-- The scheduled solution map is entailed and occurrence-closed. -/
theorem denseGaussElim_loop_invariant (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ i t,
        (denseGaussSchedule d.algebraicConstraints
          (denseOccurrenceMap d) (denseProtectedVars d bs)).fn i = some t →
          denv i = t.eval denv) ∧
    (∀ i t, (denseGaussSchedule d.algebraicConstraints
        (denseOccurrenceMap d) (denseProtectedVars d bs)).fn i = some t →
        ∀ z ∈ t.vars, z ∈ d.occ) := by
  exact denseGaussSchedule_sound bs d (denseOccurrenceMap d) (denseProtectedVars d bs)

/-- `denseGaussElim` preserves coverage: on the non-trivial branch it substitutes an
    occurrence-closed solution map, whose solutions are covered because their variables occur in a
    covered system. -/
theorem denseGaussElim_covered (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseGaussElim bs d).CoveredBy reg := by
  rw [denseGaussElim_eq]
  split_ifs with hempty
  · exact hcov
  · refine DenseConstraintSystem.substF_covered hcov ?_
    intro i _ t hti z hz
    exact DenseConstraintSystem.occ_valid hcov z
      ((denseGaussElim_loop_invariant bs d).2 i t hti z hz)

/-- **Correctness of `denseGaussElim`.** The empty-map branch is the identity (`refl`); the
    substitution branch is `substF_denseCorrect`, fed the entailment and occurrence-closure of the
    final solution map. -/
theorem denseGaussElim_correct (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseGaussElim bs d) [] bs := by
  have hinv := denseGaussElim_loop_invariant bs d
  rw [denseGaussElim_eq]
  split_ifs with hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DenseConstraintSystem.substF_denseCorrect d _ bs reg.isInput
      (fun denv hsat i t hti => hinv.1 denv hsat i t hti)
      (fun i t hti z hz => hinv.2 i t hti z hz)

/-- The wired dense Gauss-elimination pass (transform `denseGaussElim`, `Gauss.lean`). -/
def denseGaussElimPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs _ d => denseGaussElim bs d)
    (fun _ _ _ => [])
    (fun reg bs _ d hcov => denseGaussElim_covered reg bs d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseGaussElim_correct reg bs d)

end ApcOptimizer.Dense
