import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchProof
import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnifyProof

set_option autoImplicit false

/-! # Witness re-encoding — dense structure lemmas (Task 3, reencode native port, chunk P1)

Native, `VarId`-side transliterations of the *structure lemmas below the transport core* of
`OptimizerPasses/OldVariableBased/Reencode.lean` — every proof-side fact the reencode transport core
(`reencode_correct`/`_D`, chunk P2) and the capstone certificate soundness (`checkReencode_sound_D`,
chunk P3) consume that is **not** itself the transport core. Each lemma is stated and proved
**natively** over dense environments `VarId → ZMod p`, decode-free, mirroring the spec proof
line-by-line over `DenseExpr`/`DenseComputationMethod` and the dense primitives of `Reencode.lean`
(chunk R1/R2), `DomainBatch.lean`, `DomainFold.lean`, and `Bridge.lean`.

Explicitly **out of scope** (P2/P3, not proved here): the transport core `reencCorrect`/
`reencode_correct`/`reencode_correct_D`, the certificate soundness `checkReencode_sound_D`, and
anything about `denseReencodeStep`/`denseReencodeLoop`/`denseReencodeF`.

## Lemma inventory (dense twin ↔ spec original in `OldVariableBased/Reencode.lean`)

* Environment extension (`:40`/`:57`): `denseEnvExt_eq_envOfFast_of_mem`, `denseEnvExt_eq_env_of_notmem`.
* `mentions`/vars + fast eval (`:69`/`:108`/`:123`): `denseMentions_false_not_mem_vars`,
  `DenseExpr.evalWith_eq`, `DenseExpr.evalFast_eq`.
* Booleanity (`:466`/`:471`): `denseBoolConstraint_eval_of_bool`, `dense_bool_of_boolConstraint_eval`.
* Enumerated assignments (`:387`/`:403`/`:423`): `denseAssignments_keys`,
  `denseEnvOf_mem_of_assignments`, `denseEnvOf_zipimg`.
* Substitution-map pointwise facts (`:440`/`:447`): `denseEnvF_eq_varSubst`, `denseSubstF_eval_agree`.
* Substitution vars + group rewrite (`:1003`/`:629`/`:679`/`:751`/`:1029`/`:1045`):
  `DenseExpr.substF_varsIn_bits`, `denseGroupRewriteCand_agree`, `denseGroupRewrite_agree`,
  `denseGroupRewrite_bi_agree`, `denseGroupRewriteCand_vars`, `denseGroupRewrite_vars`.
* Derived-variable methods (`:891`/`:928`/`:947`/`:971`/`:988`): `DenseComputationMethod.eval_congr`,
  `denseMatchCM_eval`, `denseMatchCM_vars`, `denseBitCM_eval`, `denseBitCM_vars`.
* Re-encoded output vars (`:1094`): `denseReencodeOut_vars_subset`.
* Survivor enumeration (`:550`/`:586`/`:656`/`:794`/`:825`): `denseVarIx_lookup`,
  `denseCompileE_eval`, `denseCompileEs_all`, `denseGroupSurvivorsE_eq`.
* Derivation map (`:1137`): `DenseDerivations.methodFor_map` (`methodFor_append` reused from
  `Bridge.lean`).

Reused unchanged from existing dense proof modules (not re-proved here): `DenseExpr.eval_congr`,
`denseVarsInF_sound`, `denseContainsFast_sound` (`DomainFold`/`DomainBatch`), `denseGroupDoms_fst`
(`DomainFold`), `DenseExpr.eval_substF`/`denseEnvF` (`DomainBatchProof`),
`DenseDerivations.methodFor_append` (`Bridge`), and `zip_map_self_mem` (generic,
`OldVariableBased/Reencode`).

The interpolation building blocks (`denseIndicatorExpr`/`denseInterpOfV`/`denseCandSelect`/
`denseInterpPoly`) have **no standalone eval lemma in the spec**: their acceptance/agreement content
is proved *inside* `groupRewriteCand_agree`/`groupRewriteCand_vars` (the `candSelect` self-check),
which the dense `denseGroupRewriteCand_agree`/`denseGroupRewriteCand_vars` port directly — so this
layer is covered without extra top-level lemmas. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Environment extension by an association list (↔ `envExt_eq_envOf_of_mem`/`envExt_eq_env_of_notmem`) -/

/-- On the keys, `denseEnvExt` agrees with `denseEnvOfFast`. Mirrors `envExt_eq_envOf_of_mem`. -/
theorem denseEnvExt_eq_envOfFast_of_mem (pairs : List (VarId × ZMod p)) (denv : VarId → ZMod p)
    (y : VarId) (h : y ∈ pairs.map Prod.fst) : denseEnvExt pairs denv y = denseEnvOfFast pairs y := by
  induction pairs with
  | nil => simp at h
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [denseEnvExt, denseEnvOfFast]
    by_cases hyx : y = x
    · rw [if_pos hyx, if_pos (by simp [hyx])]
    · rw [if_neg hyx, if_neg (by simpa using hyx)]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hyx
      · exact h

/-- Off the keys, `denseEnvExt` is `denv`. Mirrors `envExt_eq_env_of_notmem`. -/
theorem denseEnvExt_eq_env_of_notmem (pairs : List (VarId × ZMod p)) (denv : VarId → ZMod p)
    (y : VarId) (h : y ∉ pairs.map Prod.fst) : denseEnvExt pairs denv y = denv y := by
  induction pairs with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [denseEnvExt, if_neg h.1]
    exact ih h.2

/-! ## `mentions` and variable membership (↔ `mentions_false_not_mem_vars`) -/

theorem denseMentions_false_not_mem_vars (i : VarId) (e : DenseExpr p)
    (h : e.mentions i = false) : i ∉ e.vars := by
  induction e with
  | const n => simp [DenseExpr.vars]
  | var j =>
      simp only [DenseExpr.mentions] at h
      simp only [DenseExpr.vars, List.mem_singleton]
      intro hij
      subst hij
      simp at h
  | add a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx
  | mul a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx

/-! ## Fast evaluation (hoisted ring operations) (↔ `Expression.evalWith_eq`/`evalFast_eq`) -/

theorem DenseExpr.evalWith_eq (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (denv : VarId → ZMod p) (e : DenseExpr p) : e.evalWith add mul denv = e.eval denv := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp only [DenseExpr.evalWith, DenseExpr.eval, hadd, iha, ihb]
  | mul a b iha ihb => simp only [DenseExpr.evalWith, DenseExpr.eval, hmul, iha, ihb]

theorem DenseExpr.evalFast_eq (e : DenseExpr p) (denv : VarId → ZMod p) :
    e.evalFast denv = e.eval denv :=
  DenseExpr.evalWith_eq _ _ (fun _ _ => rfl) (fun _ _ => rfl) denv e

/-! ## Booleanity constraints for the fresh bits (↔ `boolConstraint_eval_of_bool`/`bool_of_boolConstraint_eval`) -/

theorem denseBoolConstraint_eval_of_bool (b : VarId) (denv : VarId → ZMod p)
    (h : denv b = 0 ∨ denv b = 1) : (denseBoolConstraint b).eval denv = 0 := by
  show denv b * (denv b + (-1)) = 0
  rcases h with h | h <;> rw [h] <;> ring

theorem dense_bool_of_boolConstraint_eval [Fact p.Prime] (b : VarId) (denv : VarId → ZMod p)
    (h : (denseBoolConstraint b).eval denv = 0) : denv b = 0 ∨ denv b = 1 := by
  have h' : denv b * (denv b + (-1)) = 0 := h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right
    linear_combination h1

/-! ## Structure of enumerated assignments (↔ `assignments_keys`/`envOf_mem_of_assignments`/`envOf_zipimg`) -/

/-- Every enumerated assignment has the domains' keys, in order. Mirrors `assignments_keys`. -/
theorem denseAssignments_keys (doms : List (VarId × List (ZMod p)))
    (a : List (VarId × ZMod p)) (h : a ∈ denseAssignments doms) :
    a.map Prod.fst = doms.map Prod.fst := by
  induction doms generalizing a with
  | nil =>
      simp only [denseAssignments, List.mem_singleton] at h
      subst h
      rfl
  | cons xd rest ih =>
    obtain ⟨x, d⟩ := xd
    simp only [denseAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp [ih a' ha']

/-- Every enumerated assignment's value at a (distinct-keyed) domain entry lies in that domain.
    Mirrors `envOf_mem_of_assignments`. -/
theorem denseEnvOf_mem_of_assignments (doms : List (VarId × List (ZMod p)))
    (hnd : (doms.map Prod.fst).Nodup) (a : List (VarId × ZMod p))
    (h : a ∈ denseAssignments doms) : ∀ xd ∈ doms, denseEnvOfFast a xd.1 ∈ xd.2 := by
  induction doms generalizing a with
  | nil => simp
  | cons xd0 rest ih =>
    obtain ⟨x, d⟩ := xd0
    simp only [denseAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp only [List.map_cons, List.nodup_cons] at hnd
    intro yd hyd
    rcases List.mem_cons.1 hyd with rfl | hyd
    · rw [denseEnvOfFast, if_pos (show (x == x) = true by simp)]
      exact hv
    · have hne : yd.1 ≠ x := by
        intro heq
        exact hnd.1 (heq ▸ List.mem_map.2 ⟨yd, hyd, rfl⟩)
      have hbf : (yd.1 == x) = false := beq_eq_false_iff_ne.mpr hne
      rw [denseEnvOfFast, if_neg (by simp [hbf])]
      exact ih hnd.2 a' ha' yd hyd

/-- `denseEnvOfFast` of a zipped image list reads off the image function. Mirrors `envOf_zipimg`. -/
theorem denseEnvOf_zipimg (xs : List VarId) (g : VarId → ZMod p) (y : VarId) (hy : y ∈ xs) :
    denseEnvOfFast (xs.map (fun x => (x, g x))) y = g y := by
  induction xs with
  | nil => simp at hy
  | cons x rest ih =>
    simp only [List.map_cons, denseEnvOfFast]
    by_cases hyx : y = x
    · rw [if_pos (by simp [hyx]), hyx]
    · rw [if_neg (by simp [hyx])]
      exact ih (by
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h hyx
        · exact h)

/-! ## Pointwise environment facts for the substitution map (↔ `envF_eq_varSubst`/`substF_eval_agree`) -/

/-- `denseEnvF` at any variable is the evaluation of the substituted variable expression. Mirrors
    `envF_eq_varSubst`. -/
theorem denseEnvF_eq_varSubst (σ : VarId → Option (DenseExpr p)) (denv : VarId → ZMod p)
    (y : VarId) : denseEnvF σ denv y = ((DenseExpr.var y).substF σ).eval denv := by
  show (match σ y with | some t => t.eval denv | none => denv y)
    = ((match σ y with | some t => t | none => .var y) : DenseExpr p).eval denv
  cases σ y <;> rfl

/-- Expression-level agreement from pointwise environment agreement. Mirrors `substF_eval_agree`. -/
theorem denseSubstF_eval_agree (σ : VarId → Option (DenseExpr p)) (denv₀ denv₁ : VarId → ZMod p)
    (e : DenseExpr p) (h : ∀ y ∈ e.vars, denseEnvF σ denv₀ y = denv₁ y) :
    (e.substF σ).eval denv₀ = e.eval denv₁ := by
  rw [DenseExpr.eval_substF]
  exact DenseExpr.eval_congr e _ _ h

/-! ## Membership completeness for `denseContainsFast` (helper for `denseGroupRewrite_agree`) -/

theorem denseContainsFast_of_mem (xs : List VarId) (y : VarId) (h : y ∈ xs) :
    denseContainsFast xs y = true := by
  induction xs with
  | nil => simp at h
  | cons x rest ih =>
    simp only [denseContainsFast, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (by simp)
    · exact Or.inr (ih h)

/-! ## Degree-aware group rewriting (↔ `substF_varsIn_bits`/`groupRewriteCand_agree`/`groupRewrite_agree`/`groupRewrite_bi_agree`) -/

/-- Substituting a wholly-in-group expression (whose group variables `σfn` maps into the bits)
    yields an expression over the bits only. Mirrors `Expression.substF_varsIn_bits`. -/
theorem DenseExpr.substF_varsIn_bits (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) (hin : e.varsInF xs = true) :
    ∀ v ∈ (e.substF σfn).vars, v ∈ bits := by
  induction e with
  | const n => intro v hv; simp [DenseExpr.substF, DenseExpr.vars] at hv
  | var y =>
      intro v hv
      exact hσ y (denseContainsFast_sound xs y (by simpa [DenseExpr.varsInF] using hin)) v hv
  | add a b iha ihb =>
      rw [DenseExpr.varsInF, Bool.and_eq_true] at hin
      intro v hv
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv
  | mul a b iha ihb =>
      rw [DenseExpr.varsInF, Bool.and_eq_true] at hin
      intro v hv
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv

/-- Interpolation candidate agreement: on a bit pattern that agrees with `denv₀` and off which the
    substitution map matches `denv₁`, the checked interpolation candidate evaluates as the original.
    Mirrors `groupRewriteCand_agree` (the `candSelect` self-check content). -/
theorem denseGroupRewriteCand_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (e : DenseExpr p) (hin : e.varsInF xs = true)
    (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (denseGroupRewriteCand bits σfn patts e).eval denv₀ = e.eval denv₁ := by
  have hnotbits : ∀ y ∈ e.vars, y ∉ bits := by
    intro y hy hyb
    exact absurd hy (denseMentions_false_not_mem_vars y e (hfresh y hyb))
  have hsubstF : (e.substF σfn).eval denv₀ = e.eval denv₁ := by
    rw [DenseExpr.eval_substF]
    apply DenseExpr.eval_congr
    intro y hy
    exact hpoint y (hnotbits y hy)
  simp only [denseGroupRewriteCand]
  unfold denseCandSelect
  split
  · next hchk =>
    rw [Bool.and_eq_true] at hchk
    have hβ := of_decide_eq_true (List.all_eq_true.mp hchk.2 _
      (zip_map_self_mem (fun aβ => (e.substF σfn).evalFast (denseEnvOfFast aβ)) patts aβ haβ))
    have hchk1 := hchk.1
    simp only [DenseExpr.evalFast_eq] at hβ hchk1 ⊢
    have hcvars : ∀ v ∈ ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).vars, v ∈ bits :=
      denseVarsInF_sound bits _ hchk1
    have h₀β : ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).eval denv₀
        = ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).eval (denseEnvOfFast aβ) := by
      apply DenseExpr.eval_congr
      intro v hv
      exact hbitsagree v (hcvars v hv)
    rw [h₀β, hβ, DenseExpr.eval_substF]
    apply DenseExpr.eval_congr
    intro y hy
    have hyx : y ∈ xs := denseVarsInF_sound xs e hin y hy
    rw [denseEnvF_eq_varSubst]
    have hstep : ((DenseExpr.var y).substF σfn).eval (denseEnvOfFast aβ)
        = ((DenseExpr.var y).substF σfn).eval denv₀ := by
      apply DenseExpr.eval_congr
      intro v hv
      exact (hbitsagree v (hpolyvars y hyx v hv)).symm
    rw [hstep, ← denseEnvF_eq_varSubst]
    exact hpoint y (hnotbits y hy)
  · exact hsubstF

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else, agreeing pointwise with the original. Mirrors `groupRewrite_agree`. -/
theorem denseGroupRewrite_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (e : DenseExpr p) (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (denseGroupRewrite xs bits σfn patts e).eval denv₀ = e.eval denv₁ := by
  induction e with
  | const n => rfl
  | var y =>
      simp only [denseGroupRewrite]
      by_cases hyx : denseContainsFast xs y = true
      · rw [if_pos hyx]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.var y)
          (show (DenseExpr.var y).varsInF xs = true from hyx) hfresh
      · rw [if_neg hyx]
        have hyxs : y ∉ xs := fun h => hyx (denseContainsFast_of_mem xs y h)
        have hynb : y ∉ bits := by
          intro hyb
          have := hfresh y hyb
          simp [DenseExpr.mentions] at this
        have := hpoint y hynb
        unfold denseEnvF at this
        rw [hσnone y hyxs] at this
        show (DenseExpr.var y).eval denv₀ = (DenseExpr.var y).eval denv₁
        exact this
  | add a b iha ihb =>
      simp only [denseGroupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.add a b) hin hfresh
      · rw [if_neg hin]
        show ((denseGroupRewrite xs bits σfn patts a).eval denv₀)
          + ((denseGroupRewrite xs bits σfn patts b).eval denv₀) = a.eval denv₁ + b.eval denv₁
        rw [iha hfa, ihb hfb]
  | mul a b iha ihb =>
      simp only [denseGroupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.mul a b) hin hfresh
      · rw [if_neg hin]
        show ((denseGroupRewrite xs bits σfn patts a).eval denv₀)
          * ((denseGroupRewrite xs bits σfn patts b).eval denv₀) = a.eval denv₁ * b.eval denv₁
        rw [iha hfa, ihb hfb]

/-- Bus-interaction-level agreement for the group rewrite, over the field-by-field inlined rewrite
    that `denseReencodeOut` produces (there is no dense `BusInteraction.mapExpr`). Mirrors
    `groupRewrite_bi_agree`. -/
theorem denseGroupRewrite_bi_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (bi : BusInteraction (DenseExpr p))
    (hfreshM : ∀ b ∈ bits, bi.multiplicity.mentions b = false)
    (hfreshP : ∀ e ∈ bi.payload, ∀ b ∈ bits, e.mentions b = false) :
    denseBIEval { bi with
        multiplicity := denseGroupRewrite xs bits σfn patts bi.multiplicity,
        payload := bi.payload.map (denseGroupRewrite xs bits σfn patts) } denv₀
      = denseBIEval bi denv₁ := by
  unfold denseBIEval
  congr 1
  · exact denseGroupRewrite_agree xs bits σfn patts hσnone denv₀ denv₁ aβ haβ hbitsagree
      hpolyvars hpoint bi.multiplicity hfreshM
  · rw [List.map_map]
    refine List.map_congr_left (fun e he => ?_)
    simp only [Function.comp_apply]
    exact denseGroupRewrite_agree xs bits σfn patts hσnone denv₀ denv₁ aβ haβ hbitsagree
      hpolyvars hpoint e (hfreshP e he)

/-- A rewritten wholly-in-group expression is over the bits only. Mirrors `groupRewriteCand_vars`. -/
theorem denseGroupRewriteCand_vars (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) (hin : e.varsInF xs = true) :
    ∀ v ∈ (denseGroupRewriteCand bits σfn patts e).vars, v ∈ bits := by
  intro v hv
  simp only [denseGroupRewriteCand] at hv
  unfold denseCandSelect at hv
  split at hv
  · next hchk =>
      rw [Bool.and_eq_true] at hchk
      exact denseVarsInF_sound bits _ hchk.1 v hv
  · exact DenseExpr.substF_varsIn_bits xs bits σfn hσ e hin v hv

/-- Every variable of a group-rewritten expression is either an original variable of `e` or a fresh
    bit. Mirrors `groupRewrite_vars`. -/
theorem denseGroupRewrite_vars (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) :
    ∀ v ∈ (denseGroupRewrite xs bits σfn patts e).vars, v ∈ e.vars ∨ v ∈ bits := by
  induction e with
  | const n => simp [denseGroupRewrite, DenseExpr.vars]
  | var y =>
      simp only [denseGroupRewrite]
      by_cases hyx : denseContainsFast xs y = true
      · rw [if_pos hyx]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.var y)
          (show (DenseExpr.var y).varsInF xs = true from hyx) v hv)
      · rw [if_neg hyx]; intro v hv; exact Or.inl hv
  | add a b iha ihb =>
      simp only [denseGroupRewrite]
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.add a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [DenseExpr.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
  | mul a b iha ihb =>
      simp only [denseGroupRewrite]
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.mul a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [DenseExpr.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h

/-! ## The re-encoded system's variables (↔ `reencodeOut_vars_subset`) -/

/-- Every variable of the re-encoded system is either an original variable of `d` or a fresh bit —
    proven by construction from the certified substitution, so the pass needs no scan. Mirrors
    `reencodeOut_vars_subset` (stated natively over `occ`). -/
theorem denseReencodeOut_vars_subset (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars, v ∈ bits) :
    ∀ v ∈ (denseReencodeOut d xs bits hm).occ, v ∈ d.occ ∨ v ∈ bits := by
  intro v hv
  have gr := denseGroupRewrite_vars xs bits (denseGroupSubst xs hm)
    (denseAssignments (denseBitBox bits)) hσ
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hv
  rcases hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · simp only [denseReencodeOut, List.mem_append] at hc
    rcases hc with hc | hc
    · rcases List.mem_map.1 hc with ⟨c0, hc0, rfl⟩
      rcases gr c0 v hcv with h | h
      · exact Or.inl (DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc0) h)
      · exact Or.inr h
    · rcases List.mem_map.1 hc with ⟨b, hb, rfl⟩
      right
      have hvb : v = b := by simpa [denseBoolConstraint, DenseExpr.vars] using hcv
      exact hvb ▸ hb
  · simp only [denseReencodeOut, List.mem_map] at hbi
    rcases hbi with ⟨bi0, hbi0, rfl⟩
    simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hbiv
    rcases hbiv with hmv | ⟨e, he, hev⟩
    · rcases gr bi0.multiplicity v hmv with h | h
      · refine Or.inl (DenseConstraintSystem.mem_occ_of_bi hbi0 ?_)
        simp only [denseBIVars, List.mem_append]; exact Or.inl h
      · exact Or.inr h
    · rcases List.mem_map.1 he with ⟨e0, he0, rfl⟩
      rcases gr e0 v hev with h | h
      · refine Or.inl (DenseConstraintSystem.mem_occ_of_bi hbi0 ?_)
        simp only [denseBIVars, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨e0, he0, h⟩
      · exact Or.inr h

/-! ## Derived-variable methods for the fresh bits (↔ `ComputationMethod.eval_congr`/`matchCM`/`bitCM`) -/

/-- A dense computation method reads only its variables. Mirrors `ComputationMethod.eval_congr`. -/
theorem DenseComputationMethod.eval_congr (cm : DenseComputationMethod p) (e1 e2 : VarId → ZMod p) :
    (∀ v ∈ cm.vars, e1 v = e2 v) → cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => intro _; rfl
  | quotientOrZero num den =>
      intro h
      have hn : num.eval e1 = num.eval e2 :=
        DenseExpr.eval_congr num _ _ (fun v hv => h v (List.mem_append_left _ hv))
      have hd : den.eval e1 = den.eval e2 :=
        DenseExpr.eval_congr den _ _ (fun v hv => h v (List.mem_append_right _ hv))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      intro h
      have hc : cond.eval e1 = cond.eval e2 :=
        DenseExpr.eval_congr cond _ _ (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hv)))
      have ht := iht (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hv)))
      have he := ihe (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inr hv))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, ht, he]

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`. Mirrors `matchCM_eval`. -/
theorem denseMatchCM_eval (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) (denv : VarId → ZMod p) :
    (denseMatchCM xs imgFn thenM elseM).eval denv
    = if xs.all (fun x => decide (imgFn x = denv x)) then thenM.eval denv else elseM.eval denv := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      show (DenseComputationMethod.ifEqZero _ (denseMatchCM rest imgFn thenM elseM) elseM).eval denv = _
      rw [DenseComputationMethod.eval]
      by_cases hx : imgFn x = denv x
      · rw [if_pos (show (DenseExpr.add (.var x) (.const (-(imgFn x)))).eval denv = 0 by
              show denv x + -(imgFn x) = 0; rw [hx]; ring), ih, List.all_cons]
        simp [hx]
      · rw [if_neg (show (DenseExpr.add (.var x) (.const (-(imgFn x)))).eval denv ≠ 0 by
              show denv x + -(imgFn x) ≠ 0; intro h; exact hx (by linear_combination -h)),
            List.all_cons]
        simp [hx]

/-- Variables of `denseMatchCM` lie in `xs` together with those of the branches. Mirrors
    `matchCM_vars`. -/
theorem denseMatchCM_vars (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) :
    ∀ v ∈ (denseMatchCM xs imgFn thenM elseM).vars, v ∈ xs ∨ v ∈ thenM.vars ∨ v ∈ elseM.vars := by
  induction xs with
  | nil => intro v hv; exact Or.inr (Or.inl hv)
  | cons x rest ih =>
      intro v hv
      simp only [denseMatchCM, DenseComputationMethod.vars, DenseExpr.vars, List.nil_append,
        List.append_assoc, List.mem_append, List.mem_singleton] at hv
      rcases hv with rfl | hv | hv
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih v hv with h | h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inr hv)

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit.
    Mirrors `bitCM_eval`. -/
theorem denseBitCM_eval (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) (denv : VarId → ZMod p) :
    (denseBitCM patts xs hm b).eval denv
    = match patts.find? (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) with
      | some aβ => denseEnvOfFast aβ b
      | none => 0 := by
  induction patts with
  | nil => rfl
  | cons aβ rest ih =>
      show (denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b))
        (denseBitCM rest xs hm b)).eval denv = _
      rw [denseMatchCM_eval, List.find?_cons]
      by_cases hmatch : xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x)) = true
      · rw [if_pos hmatch, hmatch]; rfl
      · rw [if_neg hmatch]
        simp only [hmatch, ih]

/-- The derivation of bit `b` reads only group variables. Mirrors `bitCM_vars`. -/
theorem denseBitCM_vars (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) :
    ∀ v ∈ (denseBitCM patts xs hm b).vars, v ∈ xs := by
  induction patts with
  | nil => intro v hv; simp [denseBitCM, DenseComputationMethod.vars] at hv
  | cons aβ rest ih =>
      intro v hv
      rcases denseMatchCM_vars xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b))
        (denseBitCM rest xs hm b) v hv with h | h | h
      · exact h
      · simp [DenseComputationMethod.vars] at h
      · exact ih v h

/-! ## Survivor enumeration (↔ `varIx_lookup`/`compileE_eval`/`compileEs_all`/`groupSurvivorsE_eq`)

The keyed compiled-evaluation correspondence for the group-survivor enumeration. R1 ports
`denseGroupSurvivorsE`/`denseSurvZeroCW` against the **keyed** compiled evaluator
(`denseCompileEs`/`denseIExprEvalWith`, `DomainBatch.lean`); these are the keyed native mirrors of
the spec's `varIx_lookup`/`compileE_eval`/`compileEs_all` (the value-only siblings
`denseVarIx_lookupV_env`/`denseCompileE_evalV`/`denseCompileEs_allV` in `DomainBatchProof.lean` serve
the `domainFold`/`domainBatch` value path). -/

/-- Positional lookup at `y`'s first key position is exactly the `denseEnvOfFast` scan, on any
    assignment with the given keys. Mirrors `varIx_lookup`. -/
theorem denseVarIx_lookup (keys : List VarId) (y : VarId) (i : Nat)
    (h : denseVarIx keys y = some i) (pt : List (VarId × ZMod p))
    (hpt : pt.map Prod.fst = keys) : denseLookupIx pt i = denseEnvOfFast pt y := by
  induction keys generalizing i pt with
  | nil => exact absurd h (by simp [denseVarIx])
  | cons x rest ih =>
    cases pt with
    | nil => exact absurd hpt (by simp)
    | cons xv pt' =>
      obtain ⟨x', v⟩ := xv
      simp only [List.map_cons, List.cons.injEq] at hpt
      obtain ⟨rfl, hpt'⟩ := hpt
      rw [denseVarIx] at h
      split_ifs at h with hfast
      · simp only [Option.some.injEq] at h
        subst h
        rw [denseLookupIx, denseEnvOfFast, if_pos hfast]
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        rw [denseLookupIx, denseEnvOfFast, if_neg hfast]
        exact ih j hj pt' hpt'

/-- Compiled keyed evaluation agrees with the source's keyed-environment evaluation. Mirrors
    `compileE_eval`. -/
theorem denseCompileE_eval (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (keys : List VarId) (e : DenseExpr p) (ie : IExpr p) (h : denseCompileE keys e = some ie)
    (pt : List (VarId × ZMod p)) (hpt : pt.map Prod.fst = keys) :
    denseIExprEvalWith add mul pt ie = e.eval (denseEnvOfFast pt) := by
  induction e generalizing ie with
  | const n => simp only [denseCompileE, Option.some.injEq] at h; subst h; rfl
  | var y =>
      rw [denseCompileE, Option.map_eq_some_iff] at h
      obtain ⟨i, hi, rfl⟩ := h
      show denseIExprEvalWith add mul pt (.ix i) = denseEnvOfFast pt y
      rw [denseIExprEvalWith]
      exact denseVarIx_lookup keys y i hi pt hpt
  | add a b iha ihb =>
      rw [denseCompileE] at h
      cases ha : denseCompileE keys a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [ha, hb] at h; exact absurd h (by simp)
        | some ib =>
          rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          show add (denseIExprEvalWith add mul pt ia) (denseIExprEvalWith add mul pt ib)
            = a.eval (denseEnvOfFast pt) + b.eval (denseEnvOfFast pt)
          rw [hadd, iha ia ha, ihb ib hb]
  | mul a b iha ihb =>
      rw [denseCompileE] at h
      cases ha : denseCompileE keys a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [ha, hb] at h; exact absurd h (by simp)
        | some ib =>
          rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          show mul (denseIExprEvalWith add mul pt ia) (denseIExprEvalWith add mul pt ib)
            = a.eval (denseEnvOfFast pt) * b.eval (denseEnvOfFast pt)
          rw [hmul, iha ia ha, ihb ib hb]

/-- Compiled-list zero-check agrees with the source list's, keyed. Mirrors `compileEs_all`. -/
theorem denseCompileEs_all (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b) (keys : List VarId)
    (es : List (DenseExpr p)) (ces : List (IExpr p)) (h : denseCompileEs keys es = some ces)
    (pt : List (VarId × ZMod p)) (hpt : pt.map Prod.fst = keys) :
    ces.all (fun ie => decide (denseIExprEvalWith add mul pt ie = 0))
      = es.all (fun c => decide (c.eval (denseEnvOfFast pt) = 0)) := by
  induction es generalizing ces with
  | nil => simp only [denseCompileEs, Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    rw [denseCompileEs] at h
    cases he : denseCompileE keys e with
    | none => rw [he] at h; exact absurd h (by simp)
    | some ie =>
      cases hr : denseCompileEs keys rest with
      | none => rw [he, hr] at h; exact absurd h (by simp)
      | some irest =>
        rw [he, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [List.all_cons, List.all_cons, ih irest hr,
          denseCompileE_eval add mul hadd hmul keys e ie he pt hpt]

/-- `denseGroupSurvivorsE` computes the identical list to the direct `evalFast`/`denseEnvOfFast`
    filter — the index-compiled path is a pure speedup. Mirrors `groupSurvivorsE_eq`. -/
theorem denseGroupSurvivorsE_eq (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    denseGroupSurvivorsE es doms
      = (denseAssignments doms).filter
          (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0))) := by
  unfold denseGroupSurvivorsE
  split
  · rename_i ces hce
    refine List.filter_congr (fun a ha => ?_)
    have hkeys : a.map Prod.fst = doms.map Prod.fst := denseAssignments_keys doms a ha
    have hval : (fun c : DenseExpr p => decide (c.evalFast (denseEnvOfFast a) = 0))
        = (fun c : DenseExpr p => decide (c.eval (denseEnvOfFast a) = 0)) := by
      funext c; rw [DenseExpr.evalFast_eq]
    rw [hval]
    unfold denseSurvZeroCW
    exact denseCompileEs_all (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul
      (fun _ _ => rfl) (fun _ _ => rfl) (doms.map Prod.fst) es ces hce a hkeys
  · rfl

/-! ## The generic dense transport core (↔ `reencode_correct`/`reencode_correct_D`)

The keyed assignment membership/readout facts the capstone consumes (`mem_denseAssignments` for the
keyed `denseAssignments doms`, and `denseEnvOfFast_map`, the keyed sibling of the value-only
`mem_assignmentsV`) are reused unchanged from `RootPairUnifyProof.lean` — they are generic
`VarId`-keyed enumeration facts, not reencode-specific, so no local copy is added.

The native `VarId`-side analogue of the spec's `ConstraintSystem.reencode_correct_D`: a witness
transport principle producing `DensePassCorrect` directly. `out` replaces every expression `e` by
`grw e` (field-inlined for bus interactions — there is no dense `BusInteraction.mapExpr`), keeps only
the constraints selected by `keep`, and appends `newCs`; the fresh columns carry the dense
derivations `dd`. Given forward transport (with the input-column frame and the native
`DenseOutReconstructs` obligation) and backward transport under which every original expression
evaluates identically, the step is `DensePassCorrect`. Nothing here mentions bits or groups — a
generic principle, decode-free. -/

theorem DenseConstraintSystem.reencode_correct_D (d out : DenseConstraintSystem p)
    (bs : BusSemantics p) (isInput : VarId → Bool)
    (grw : DenseExpr p → DenseExpr p) (keep : DenseExpr p → Bool)
    (newCs : List (DenseExpr p)) (dd : DenseDerivations p)
    (hout : out =
      { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
        busInteractions := d.busInteractions.map (fun bi =>
          { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) })
    (hfwd : ∀ denv, d.satisfies bs denv → ∃ denv',
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ newCs, c.eval denv' = 0) ∧
      (∀ i, isInput i = true → denv' i = denv i) ∧
      (∀ inputVarIds, (∀ i ∈ d.occ, isInput i = true → i ∈ inputVarIds) →
        DenseOutReconstructs isInput inputVarIds d out dd denv denv'))
    (hbwd : ∀ denv', out.satisfies bs denv' → ∃ denv,
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ d.algebraicConstraints, keep c = false → c.eval denv = 0))
    (hVars : ∀ i ∈ out.occ, isInput i = true → i ∈ d.occ) :
    DensePassCorrect isInput d out dd bs := by
  subst hout
  -- side-effect equality under bus-interaction agreement
  have hside : ∀ (denv denv' : VarId → ZMod p),
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      DenseConstraintSystem.sideEffects
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' = d.sideEffects bs denv := by
    intro denv denv' hB
    show ((d.busInteractions.map (fun bi =>
        { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })).filter
        (fun bi => bs.isStateful bi.busId)).map _ = _
    rw [filter_map_busId_comm d.busInteractions
        (fun bi => { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })
        bs (fun _ => rfl), List.map_map]
    exact List.map_congr_left (fun bi hbi => by
      simp only [Function.comp_apply, hB bi (List.mem_of_mem_filter hbi)])
  -- admissible transfer under bus-interaction agreement
  have hdisc : ∀ (denv denv' : VarId → ZMod p),
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      (DenseConstraintSystem.admissible
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' ↔ d.admissible bs denv) := by
    intro denv denv' hB
    unfold DenseConstraintSystem.admissible
    have hmap : ((d.busInteractions.map (fun bi =>
          { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })).map
          (fun bi => denseBIEval bi denv'))
        = d.busInteractions.map (fun bi => denseBIEval bi denv) := by
      rw [List.map_map]
      exact List.map_congr_left (fun bi hbi => hB bi hbi)
    rw [hmap]
  -- recover `d.satisfies denv` from a satisfying output and the backward agreement
  have hsatd : ∀ (denv denv' : VarId → ZMod p),
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) →
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      (∀ c ∈ d.algebraicConstraints, keep c = false → c.eval denv = 0) →
      DenseConstraintSystem.satisfies
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' → d.satisfies bs denv := by
    intro denv denv' hA hB hdrop hsat'
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · by_cases hk : keep c = true
      · have hmem : grw c ∈ ((d.algebraicConstraints.filter keep).map grw) ++ newCs :=
          List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hk⟩, rfl⟩)
        have h1 := hsat'.1 _ hmem
        rw [hA c hc] at h1; exact h1
      · exact hdrop c hc (by simpa using hk)
    · show (denseBIEval bi denv).multiplicity ≠ 0 → bs.violatesConstraint (denseBIEval bi denv) = false
      have hmem : { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }
          ∈ (d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })) :=
        List.mem_map.2 ⟨bi, hbi, rfl⟩
      have h2 := hsat'.2 _ hmem
      rw [hB bi hbi] at h2
      exact h2
  refine ⟨?_, ?_, hVars, ?_⟩
  · -- Soundness: `out.implies d`.
    intro denv' hsat'
    obtain ⟨denv, hA, hB, hdrop⟩ := hbwd denv' hsat'
    refine ⟨denv, hsatd denv denv' hA hB hdrop hsat', ?_⟩
    rw [hside denv denv' hB]; exact BusState.equiv_refl _
  · -- Invariant preservation.
    intro hinv denv' hsat' bi' hbi'
    obtain ⟨denv, hA, hB, hdrop⟩ := hbwd denv' hsat'
    have hd := hsatd denv denv' hA hB hdrop hsat'
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    show (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv').multiplicity ≠ 0 →
      bs.breaksInvariant (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv') = false
    rw [hB bi0 hbi0]
    exact hinv denv hd bi0 hbi0
  · -- Completeness with derivations.
    intro denv hadm hsat
    obtain ⟨denv', hA, hB, hnew, hframe, hrec⟩ := hfwd denv hsat
    refine ⟨denv', ⟨fun c hc => ?_, fun bi hbi => ?_⟩, (hdisc denv denv' hB).2 hadm, ?_, hframe, hrec⟩
    · rcases List.mem_append.1 hc with h | h
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
        rw [hA c0 (List.mem_of_mem_filter hc0)]
        exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hnew c h
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      show (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv').multiplicity ≠ 0 →
        bs.violatesConstraint (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv') = false
      rw [hB bi0 hbi0]
      exact hsat.2 bi0 hbi0
    · rw [hside denv denv' hB]; exact BusState.equiv_refl _

/-! ## Derivation-list map lookup (↔ `Derivations.methodFor_map`) -/

/-- The method list built for the fresh bits supplies `g w` for a bit `w`, nothing otherwise.
    Mirrors `Derivations.methodFor_map` (`methodFor_append` reused from `Bridge.lean`). -/
theorem DenseDerivations.methodFor_map (bits : List VarId) (g : VarId → DenseComputationMethod p)
    (w : VarId) :
    DenseDerivations.methodFor (bits.map (fun b => (b, g b))) w
      = if w ∈ bits then some (g w) else none := by
  induction bits with
  | nil => simp [DenseDerivations.methodFor]
  | cons b rest ih =>
      simp only [List.map_cons, DenseDerivations.methodFor, ih, List.mem_cons]
      by_cases hw : w ∈ rest
      · simp [hw]
      · by_cases hbw : b = w
        · subst hbw; simp [hw]
        · have hwb : w ≠ b := fun h => hbw h.symm
          simp [hw, hbw, hwb, Option.orElse]

/-! ## The capstone: certificate soundness (↔ `checkReencode_sound_D`)

The native `VarId`-side analogue of `checkReencode_sound_D`. It supplies the forward transport (with
the input-column frame and the native `DenseOutReconstructs` obligation for the minted bits) and the
backward transport to `DenseConstraintSystem.reencode_correct_D`, producing `DensePassCorrect` for
the re-encoded output and the fresh bits' derivations, over the **extended** registry's `isInput`.

Freshness / `isInput` of the minted bits (spec's `hbn : b.powdrId? = none`) enters as the abstract
hypothesis `hbnInput : ∀ b ∈ bits, isInput b = false` — the extended registry's `reg1.isInput b =
(reg1.resolve b).powdrId?.isSome`, which is `false` for a bit registered with
`{ name := freshBase ++ … }` (no `powdrId?`), discharged by the wiring step (P3). The group columns'
`isInput = true` and their `d.occ` membership (spec's `hxs`/`hxsCs`) likewise enter abstractly
(`hxsInput`/`hxsOcc`); P3 supplies them from the runtime `xs.all (fun x => reg.isInput x)` gate and
the registry extension (`reg1.isInput x = reg.isInput x` for a valid `x`). -/

theorem denseCheckReencode_sound [Fact p.Prime] (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (isInput : VarId → Bool) (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (hxsInput : ∀ x ∈ xs, isInput x = true) (hxsOcc : ∀ x ∈ xs, x ∈ d.occ)
    (hxsB : ∀ x ∈ xs, x ∉ bits) (hbnInput : ∀ b ∈ bits, isInput b = false)
    (hchk : denseCheckReencode d xs bits hm = true) :
    DensePassCorrect isInput d (denseReencodeOut d xs bits hm)
      (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b))) bs := by
  unfold denseCheckReencode at hchk
  split at hchk
  · exact absurd hchk (by simp)
  rename_i doms hdoms
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨_hbox, _hm2⟩, _hprofit⟩, hnodup⟩, hvarsB⟩, hC5⟩, hC6⟩, hfreshB⟩ := hchk
  have hnodup' : bits.Nodup := of_decide_eq_true hnodup
  have hkeys : doms.map Prod.fst = xs := denseGroupDoms_fst (denseCoveredCsOf d xs) xs doms hdoms
  have hbitKeys : (denseBitBox (p := p) bits).map Prod.fst = bits := by
    unfold denseBitBox; rw [List.map_map]; simp [Function.comp_def]
  have hpolyVars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars,
      v ∈ bits := by
    intro y hy v hv
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp (List.all_eq_true.mp hvarsB y hy) v hv)
  have hσnone : ∀ y, y ∉ xs → denseGroupSubst xs hm y = none := by
    intro y hy
    show (if denseContainsFast xs y = true then hm[y]? else none) = none
    rw [if_neg (fun h => hy (denseContainsFast_sound xs y h))]
  have hfreshCm : ∀ c ∈ d.algebraicConstraints, ∀ b ∈ bits, c.mentions b = false := by
    intro c hc b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    simpa using List.all_eq_true.mp h1.1 c hc
  have hfreshMm : ∀ bi ∈ d.busInteractions, ∀ b ∈ bits, bi.multiplicity.mentions b = false := by
    intro bi hbi b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using h2.1
  have hfreshPm : ∀ bi ∈ d.busInteractions, ∀ e ∈ bi.payload, ∀ b ∈ bits,
      e.mentions b = false := by
    intro bi hbi e he b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using List.all_eq_true.mp h2.2 e he
  -- FORWARD (with the input frame and the native `DenseOutReconstructs` obligation)
  have hfwd_D : ∀ denv, d.satisfies bs denv → ∃ denv',
      (∀ c ∈ d.algebraicConstraints,
        ((denseGroupRewrite xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits))) c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with
            multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits)) bi.multiplicity,
            payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits))) } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ bits.map denseBoolConstraint, c.eval denv' = 0) ∧
      (∀ i, isInput i = true → denv' i = denv i) ∧
      (∀ inputVarIds, (∀ i ∈ d.occ, isInput i = true → i ∈ inputVarIds) →
        DenseOutReconstructs isInput inputVarIds d (denseReencodeOut d xs bits hm)
          (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)))
          denv denv') := by
    intro denv hsat
    have hallES : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 := fun c hc =>
      hsat.1 c (List.mem_of_mem_filter hc)
    have hdsound := denseGroupDoms_sound denv (denseCoveredCsOf d xs) hallES xs doms hdoms
    have hamem : (doms.map (fun yd => (yd.1, denv yd.1))) ∈ denseAssignments doms :=
      mem_denseAssignments doms denv hdsound
    have hasurv : (doms.map (fun yd => (yd.1, denv yd.1)))
        ∈ denseGroupSurvivorsE (denseCoveredCsOf d xs) doms := by
      rw [denseGroupSurvivorsE_eq]
      refine List.mem_filter.2 ⟨hamem, ?_⟩
      rw [List.all_eq_true]
      intro c hc
      rw [decide_eq_true_iff, DenseExpr.evalFast_eq]
      have hcov := List.of_mem_filter hc
      rw [denseCoveredBy, Bool.and_eq_true] at hcov
      have hcvars : ∀ v ∈ c.vars, v ∈ doms.map Prod.fst := by
        rw [hkeys]; exact denseVarsInF_sound xs c hcov.2
      have heq : c.eval (denseEnvOfFast (doms.map (fun yd => (yd.1, denv yd.1)))) = c.eval denv :=
        DenseExpr.eval_congr c _ _ (fun v hv => denseEnvOfFast_map doms denv v (hcvars v hv))
      rw [heq]; exact hallES c hc
    have hC5' : (denseAssignments (denseBitBox bits)).any
        (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) = true := by
      rw [List.any_eq_true]
      obtain ⟨aβ, ha, hp⟩ := List.any_eq_true.1 (List.all_eq_true.mp hC5 _ hasurv)
      refine ⟨aβ, ha, ?_⟩
      rw [List.all_eq_true] at hp ⊢
      intro x hx
      have hsx : denseEnvOfFast (doms.map (fun yd => (yd.1, denv yd.1))) x = denv x :=
        denseEnvOfFast_map doms denv x (by rw [hkeys]; exact hx)
      have hpp := hp x hx
      rw [hsx] at hpp
      exact hpp
    cases hfindEnv : (denseAssignments (denseBitBox bits)).find?
        (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) with
    | none =>
        exfalso
        rw [List.find?_eq_none] at hfindEnv
        obtain ⟨aβ0, ha0, hp0⟩ := List.any_eq_true.1 hC5'
        exact absurd hp0 (by simpa using hfindEnv aβ0 ha0)
    | some aβ =>
      have haβ : aβ ∈ denseAssignments (denseBitBox bits) := List.mem_of_find?_eq_some hfindEnv
      have hβpred : xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x)) = true := by
        simpa using List.find?_some hfindEnv
      have hkeysβ : aβ.map Prod.fst = bits := by
        rw [denseAssignments_keys (denseBitBox bits) aβ haβ, hbitKeys]
      have henvxs : ∀ x ∈ xs, denseEnvExt aβ denv x = denv x := fun x hx =>
        denseEnvExt_eq_env_of_notmem aβ denv x (by rw [hkeysβ]; exact hxsB x hx)
      have hpoint : ∀ y, y ∉ bits →
          denseEnvF (denseGroupSubst xs hm) (denseEnvExt aβ denv) y = denv y := by
        intro y hyb
        by_cases hyx : y ∈ xs
        · rw [denseEnvF_eq_varSubst]
          have hagree : ((DenseExpr.var y).substF (denseGroupSubst xs hm)).eval (denseEnvExt aβ denv)
              = ((DenseExpr.var y).substF (denseGroupSubst xs hm)).eval (denseEnvOfFast aβ) := by
            apply DenseExpr.eval_congr
            intro v hv
            exact denseEnvExt_eq_envOfFast_of_mem aβ denv v (by rw [hkeysβ]; exact hpolyVars y hyx v hv)
          rw [hagree, ← DenseExpr.evalFast_eq]
          exact of_decide_eq_true (List.all_eq_true.mp hβpred y hyx)
        · unfold denseEnvF
          rw [hσnone y hyx]
          exact denseEnvExt_eq_env_of_notmem aβ denv y (by rw [hkeysβ]; exact hyb)
      have hbitsagree : ∀ b ∈ bits, denseEnvExt aβ denv b = denseEnvOfFast aβ b := fun b hb =>
        denseEnvExt_eq_envOfFast_of_mem aβ denv b (by rw [hkeysβ]; exact hb)
      refine ⟨denseEnvExt aβ denv, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        exact denseGroupRewrite_agree xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) hσnone (denseEnvExt aβ denv) denv aβ haβ
          hbitsagree hpolyVars hpoint c (hfreshCm c hc)
      · intro bi hbi
        exact denseGroupRewrite_bi_agree xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) hσnone (denseEnvExt aβ denv) denv aβ haβ
          hbitsagree hpolyVars hpoint bi (hfreshMm bi hbi) (hfreshPm bi hbi)
      · intro c hc
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
        apply denseBoolConstraint_eval_of_bool
        have hbk : b ∈ aβ.map Prod.fst := hkeysβ ▸ hb
        rw [denseEnvExt_eq_envOfFast_of_mem aβ denv b hbk]
        have hmem := denseEnvOf_mem_of_assignments (denseBitBox bits)
          (by rw [hbitKeys]; exact hnodup') aβ haβ
          (b, ([0, 1] : List (ZMod p))) (List.mem_map.2 ⟨b, hb, rfl⟩)
        simpa using hmem
      · intro i hii
        refine denseEnvExt_eq_env_of_notmem aβ denv i ?_
        rw [hkeysβ]
        intro hib
        rw [hbnInput i hib] at hii
        simp at hii
      · intro inputVarIds hcov1 i hiout hisF
        rw [DenseDerivations.methodFor_map bits
          (fun b => denseBitCM (denseAssignments (denseBitBox bits)) xs hm b) i]
        by_cases hib : i ∈ bits
        · rw [if_pos hib]
          refine ⟨fun j hj => hxsInput j (denseBitCM_vars _ xs hm i j hj), fun j hj => ?_, ?_⟩
          · exact hcov1 j (hxsOcc j (denseBitCM_vars _ xs hm i j hj))
              (hxsInput j (denseBitCM_vars _ xs hm i j hj))
          · have hval : (denseBitCM (denseAssignments (denseBitBox bits)) xs hm i).eval
                (denseEnvExt aβ denv) = denseEnvOfFast aβ i := by
              rw [DenseComputationMethod.eval_congr
                  (denseBitCM (denseAssignments (denseBitBox bits)) xs hm i)
                  (denseEnvExt aβ denv) denv
                  (fun v hv => henvxs v (denseBitCM_vars _ xs hm i v hv)),
                denseBitCM_eval, hfindEnv]
            rw [hval]
            exact (hbitsagree i hib).symm
        · rw [if_neg hib]
          refine ⟨?_, denseEnvExt_eq_env_of_notmem aβ denv i (by rw [hkeysβ]; exact hib)⟩
          rcases denseReencodeOut_vars_subset d xs bits hm hpolyVars i hiout with h | h
          · exact h
          · exact absurd h hib
  -- BACKWARD
  have hbwd : ∀ denv', (denseReencodeOut d xs bits hm).satisfies bs denv' → ∃ denv,
      (∀ c ∈ d.algebraicConstraints,
        ((denseGroupRewrite xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits))) c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with
            multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits)) bi.multiplicity,
            payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits))) } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ d.algebraicConstraints, (fun c => !denseCoveredBy xs c) c = false → c.eval denv = 0) := by
    intro denv' hsat'
    have hbool : ∀ b ∈ bits, denv' b = 0 ∨ denv' b = 1 := by
      intro b hb
      apply dense_bool_of_boolConstraint_eval
      exact hsat'.1 _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩))
    have haβmem : ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1)))
        ∈ denseAssignments (denseBitBox bits) := by
      apply mem_denseAssignments
      intro yd hyd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hyd
      simpa using hbool b hb
    have hβenv : ∀ b ∈ bits,
        denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) b = denv' b := by
      intro b hb
      exact denseEnvOfFast_map (denseBitBox bits) denv' b (by rw [hbitKeys]; exact hb)
    have hkeysP : (xs.map (fun x =>
        (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))).map Prod.fst = xs := by
      rw [List.map_map]; simp [Function.comp_def]
    have hpoint : ∀ y, denseEnvF (denseGroupSubst xs hm) denv' y
        = denseEnvExt (xs.map (fun x =>
            (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv' y := by
      intro y
      by_cases hyx : y ∈ xs
      · rw [denseEnvF_eq_varSubst,
          denseEnvExt_eq_envOfFast_of_mem _ denv' y (by rw [hkeysP]; exact hyx),
          denseEnvOf_zipimg xs _ y hyx]
      · unfold denseEnvF
        rw [hσnone y hyx]
        exact (denseEnvExt_eq_env_of_notmem _ denv' y (by rw [hkeysP]; exact hyx)).symm
    have hexpr : ∀ e : DenseExpr p, (e.substF (denseGroupSubst xs hm)).eval denv'
        = e.eval (denseEnvExt (xs.map (fun x =>
            (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv') :=
      fun e => denseSubstF_eval_agree (denseGroupSubst xs hm) denv' _ e (fun y _ => hpoint y)
    have hbitsagree' : ∀ b ∈ bits,
        denv' b = denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) b :=
      fun b hb => (hβenv b hb).symm
    refine ⟨denseEnvExt (xs.map (fun x =>
        (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv', ?_, ?_, ?_⟩
    · intro c hc
      exact denseGroupRewrite_agree xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) hσnone denv' _
        ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) haβmem hbitsagree' hpolyVars
        (fun y _ => hpoint y) c (hfreshCm c hc)
    · intro bi hbi
      exact denseGroupRewrite_bi_agree xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) hσnone denv' _
        ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) haβmem hbitsagree' hpolyVars
        (fun y _ => hpoint y) bi (hfreshMm bi hbi) (hfreshPm bi hbi)
    · intro c hc hkc
      have hcov : denseCoveredBy xs c = true := by simpa using hkc
      have hcmem : c ∈ denseCoveredCsOf d xs := List.mem_filter.2 ⟨hc, hcov⟩
      have h6 := List.all_eq_true.mp (List.all_eq_true.mp hC6 _ haβmem) c hcmem
      rw [decide_eq_true_iff, DenseExpr.evalFast_eq] at h6
      have hcvars : ∀ v ∈ c.vars, v ∈ xs := by
        rw [denseCoveredBy, Bool.and_eq_true] at hcov
        exact denseVarsInF_sound xs c hcov.2
      have hagree : (c.substF (denseGroupSubst xs hm)).eval
            (denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))))
          = (c.substF (denseGroupSubst xs hm)).eval denv' := by
        rw [DenseExpr.eval_substF, DenseExpr.eval_substF]
        apply DenseExpr.eval_congr
        intro y hy
        rw [denseEnvF_eq_varSubst, denseEnvF_eq_varSubst]
        apply DenseExpr.eval_congr
        intro v hv
        exact hβenv v (hpolyVars y (hcvars y hy) v hv)
      rw [← hexpr c, ← hagree]
      exact h6
  -- no new powdr-ID column: every output variable is a `d`-column or a (non-input) bit
  have hVars : ∀ i ∈ (denseReencodeOut d xs bits hm).occ, isInput i = true → i ∈ d.occ := by
    intro i hi hii
    rcases denseReencodeOut_vars_subset d xs bits hm hpolyVars i hi with h | h
    · exact h
    · rw [hbnInput i h] at hii; simp at hii
  exact DenseConstraintSystem.reencode_correct_D d (denseReencodeOut d xs bits hm) bs isInput
    (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits)))
    (fun c => !denseCoveredBy xs c)
    (bits.map denseBoolConstraint)
    (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)))
    rfl hfwd_D hbwd hVars

end ApcOptimizer.Dense
