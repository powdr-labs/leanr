import Leanr.Implementation.OptimizerPasses.DomainBatch

set_option autoImplicit false

/-! # Witness re-encoding (fewer variables for enumerable witness sets)

A new *kind* of optimization: all passes so far eliminate variables whose values are
**entailed**. This pass eliminates *witness freedom* that is merely **inefficiently encoded**:
if the constraints over a variable group `xs` (all constraints whose variables lie inside the
group) restrict it to `m` joint values, then `⌈log₂ m⌉` fresh boolean variables suffice to
select among them — e.g. OpenVM's load/store `flags` (4 variables, 4 valid combinations
selecting the runtime shift) become 2 booleans, and a runtime one-hot selector of width `w`
becomes `⌈log₂ w⌉` bits. The original group is *substituted away* by interpolation
polynomials in the fresh bits, the group-only constraints are dropped (every bit pattern maps
into the valid set), and booleanity constraints for the bits are added.

Correctness is different from substitution: neither system's witnesses extend the other's.
The transport core (`reencode_correct`) takes two *witness transformations* — forward
(satisfying `env` ↦ bit assignment matching the group's current value) and backward (boolean
bits ↦ the selected group value) — under which every original expression **evaluates
identically**, so constraints, bus obligations, side effects, and the memory discipline all
transfer by pointwise equality of the evaluated messages.

Everything the proofs consume is decidable and index-free: the valid set is enumerated over
constraint-derived domains (`findDomainAlg` roots), the bit patterns over `{0,1}` boxes
(`assignments`), and the two coverage checks are `∀ pattern, image satisfies dropped` and
`∀ survivor, ∃ pattern with that image`. Requires prime `p` (booleanity needs an integral
domain); gated at runtime like the domain passes. -/

variable {p : ℕ}

/-! ## Environment extension by an association list -/

/-- Override `env` on the keys of `pairs` (first match wins, mirroring `envOf`). -/
def envExt : List (Variable × ZMod p) → (Variable → ZMod p) → Variable → ZMod p
  | [], env, y => env y
  | (x, v) :: rest, env, y => if y = x then v else envExt rest env y

/-- On the keys, `envExt` agrees with `envOf`. -/
theorem envExt_eq_envOf_of_mem (pairs : List (Variable × ZMod p)) (env : Variable → ZMod p)
    (y : Variable) (h : y ∈ pairs.map Prod.fst) : envExt pairs env y = envOf pairs y := by
  induction pairs with
  | nil => simp at h
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [envExt, envOf]
    by_cases hyx : y = x
    · rw [if_pos hyx, if_pos hyx]
    · rw [if_neg hyx, if_neg hyx]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hyx
      · exact h

/-- Off the keys, `envExt` is `env`. -/
theorem envExt_eq_env_of_notmem (pairs : List (Variable × ZMod p)) (env : Variable → ZMod p)
    (y : Variable) (h : y ∉ pairs.map Prod.fst) : envExt pairs env y = env y := by
  induction pairs with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [envExt, if_neg h.1]
    exact ih h.2

/-! ## `mentions` and variable membership -/

theorem mentions_false_not_mem_vars (x : Variable) (e : Expression p)
    (h : e.mentions x = false) : x ∉ e.vars := by
  induction e with
  | const n => simp [Expression.vars]
  | var y =>
      simp only [Expression.mentions] at h
      simp only [Expression.vars, List.mem_singleton]
      intro hxy
      subst hxy
      simp at h
  | add a b iha ihb =>
      simp only [Expression.mentions, Bool.or_eq_false_iff] at h
      simp only [Expression.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx
  | mul a b iha ihb =>
      simp only [Expression.mentions, Bool.or_eq_false_iff] at h
      simp only [Expression.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx

/-! ## The transport core -/

/-- The soundness + completeness + invariant obligations of the re-encoder, *without* the
    derived-variable reconstruction (and input-column frame) that the threaded `PassCorrect`
    additionally requires. This is the pre-derivations refinement, spelled out (`implies` + a plain
    admissible-completeness witness + invariant preservation) rather than via the audited
    `refines`, which now also carries the derivations. The transport proofs below establish this;
    wiring the fresh bits' `ComputationMethod`s into a full `PassCorrect` (so the re-encoder can
    rejoin the pipeline) is the remaining work — see the note on `reencodePass`. -/
def ConstraintSystem.reencCorrect (cs out : ConstraintSystem p) (bs : BusSemantics p) : Prop :=
  (out.implies cs bs ∧
    (∀ env, cs.admissible bs env → cs.satisfies bs env →
      ∃ env', out.satisfies bs env' ∧ out.admissible bs env' ∧
        cs.sideEffects bs env ≈ out.sideEffects bs env')) ∧
  (cs.guaranteesInvariants bs → out.guaranteesInvariants bs)

/-- **Re-encoding correctness.** `out` replaces every expression `e` by `e.substF σ`, keeps
    only the constraints selected by `keep`, and appends `newCs`. If satisfying assignments
    transport in both directions such that every original expression *evaluates identically*
    (forward additionally establishing `newCs`, backward additionally the dropped
    constraints), the step is `reencCorrect`. Nothing here mentions bits or groups — it is a
    generic witness-transport principle. -/
theorem ConstraintSystem.reencode_correct (cs : ConstraintSystem p) (bsem : BusSemantics p)
    (rw : Expression p → Expression p) (keep : Expression p → Bool)
    (newCs : List (Expression p))
    (hfwd : ∀ env, cs.satisfies bsem env → ∃ env',
      (∀ c ∈ cs.algebraicConstraints, (rw c).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) ∧
      (∀ c ∈ newCs, c.eval env' = 0))
    (hbwd : ∀ env',
      (ConstraintSystem.satisfies
        { algebraicConstraints :=
            ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
          busInteractions := cs.busInteractions.map (·.mapExpr rw) } bsem env') → ∃ env,
      (∀ c ∈ cs.algebraicConstraints, (rw c).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) ∧
      (∀ c ∈ cs.algebraicConstraints, keep c = false → c.eval env = 0)) :
    ConstraintSystem.reencCorrect cs
      { algebraicConstraints :=
          ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
        busInteractions := cs.busInteractions.map (·.mapExpr rw) } bsem := by
  unfold ConstraintSystem.reencCorrect
  set out : ConstraintSystem p :=
    { algebraicConstraints :=
        ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
      busInteractions := cs.busInteractions.map (·.mapExpr rw) } with hout
  -- message-list equality under expression-wise agreement
  have hmsgs : ∀ (env env' : Variable → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) →
      ∀ busId, (out.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => bi.eval env')
        = (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => bi.eval env) := by
    intro env env' hB busId
    show ((cs.busInteractions.map (·.mapExpr rw)).filter (fun bi => bi.busId = busId)).map
        (fun bi => bi.eval env') = _
    rw [List.filter_map]
    rw [List.filter_congr (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => decide (b.busId = busId)) ∘
        (fun b => b.mapExpr rw)) bi = decide (bi.busId = busId)))]
    rw [List.map_map]
    exact List.map_congr_left (fun bi hbi =>
      hB bi (List.mem_of_mem_filter hbi))
  -- side-effect equality under expression-wise agreement
  have hside : ∀ (env env' : Variable → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) →
      out.sideEffects bsem env' = cs.sideEffects bsem env := by
    intro env env' hB
    show ((cs.busInteractions.map (·.mapExpr rw)).filter
        (fun bi => bsem.isStateful bi.busId)).map _ = _
    rw [List.filter_map]
    rw [List.filter_congr (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => bsem.isStateful b.busId) ∘
        (fun b => b.mapExpr rw)) bi = bsem.isStateful bi.busId))]
    rw [List.map_map]
    exact List.map_congr_left (fun bi hbi => by
      simp only [Function.comp_apply, hB bi (List.mem_of_mem_filter hbi)])
  -- admissible transfer under expression-wise agreement (the evaluated messages coincide)
  have hdisc : ∀ (env env' : Variable → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) →
      (out.admissible bsem env' ↔ cs.admissible bsem env) := by
    intro env env' hB
    unfold ConstraintSystem.admissible
    have hmap : (out.busInteractions.map (fun bi => bi.eval env'))
        = cs.busInteractions.map (fun bi => bi.eval env) := by
      show ((cs.busInteractions.map (·.mapExpr rw)).map (fun bi => bi.eval env')) = _
      rw [List.map_map]
      exact List.map_congr_left (fun bi hbi => hB bi hbi)
    rw [hmap]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- soundness: out implies cs
    intro env' hsat'
    obtain ⟨env, hA, hB, hdrop⟩ := hbwd env' hsat'
    refine ⟨env, ⟨?_, ?_⟩, ?_⟩
    · intro c hc
      by_cases hk : keep c = true
      · have hmem : rw c ∈ out.algebraicConstraints :=
          List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hk⟩, rfl⟩)
        have := hsat'.1 _ hmem
        rw [hA c hc] at this
        exact this
      · exact hdrop c hc (by simpa using hk)
    · intro bi hbi
      have hmem : bi.mapExpr rw ∈ out.busInteractions := List.mem_map.2 ⟨bi, hbi, rfl⟩
      have := hsat'.2 _ hmem
      rw [hB bi hbi] at this
      exact this
    · rw [hside env env' hB]
      exact BusState.equiv_refl _
  · -- completeness: cs intended-implies out
    intro env hint hsat
    obtain ⟨env', hA, hB, hnew⟩ := hfwd env hsat
    refine ⟨env', ⟨?_, ?_⟩, (hdisc env env' hB).2 hint, ?_⟩
    · intro c hc
      rcases List.mem_append.1 hc with h | h
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
        rw [hA c0 (List.mem_of_mem_filter hc0)]
        exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hnew c h
    · intro bi hbi
      obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      rw [hB bi0 hbi0]
      exact hsat.2 bi0 hbi0
    · rw [hside env env' hB]
      exact BusState.equiv_refl _
  · -- invariant preservation
    intro hinv env' hsat' bi' hbi'
    obtain ⟨env, hA, hB, hdrop⟩ := hbwd env' hsat'
    have hsatcs : cs.satisfies bsem env := by
      refine ⟨?_, ?_⟩
      · intro c hc
        by_cases hk : keep c = true
        · have hmem : rw c ∈ out.algebraicConstraints :=
            List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hk⟩, rfl⟩)
          have := hsat'.1 _ hmem
          rw [hA c hc] at this
          exact this
        · exact hdrop c hc (by simpa using hk)
      · intro bi hbi
        have hmem : bi.mapExpr rw ∈ out.busInteractions := List.mem_map.2 ⟨bi, hbi, rfl⟩
        have := hsat'.2 _ hmem
        rw [hB bi hbi] at this
        exact this
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    rw [hB bi0 hbi0]
    exact hinv env hsatcs bi0 hbi0

/-- The threaded (derived-variable) version of `reencode_correct`: the same transport, but the forward
    additionally keeps every input column's value (`hpow`) and reconstructs the output's derived
    columns from the input columns via `deriv` (`hrecon`), and no new powdr-ID column is introduced
    (`hS`). Produces the full `PassCorrect` the pipeline consumes. -/
theorem ConstraintSystem.reencode_correct_D (cs : ConstraintSystem p) (bsem : BusSemantics p)
    (rw : Expression p → Expression p) (keep : Expression p → Bool)
    (newCs : List (Expression p)) (deriv : Derivations p)
    (hfwd : ∀ env, cs.satisfies bsem env → ∃ env',
      (∀ c ∈ cs.algebraicConstraints, (rw c).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) ∧
      (∀ c ∈ newCs, c.eval env' = 0) ∧
      (∀ v : Variable, v.powdrId?.isSome → env' v = env v) ∧
      (∀ dsIn : Derivations p, cs.reconstructs dsIn env →
        ({ algebraicConstraints := ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
           busInteractions := cs.busInteractions.map (·.mapExpr rw) } :
             ConstraintSystem p).reconstructs (dsIn ++ deriv) env'))
    (hbwd : ∀ env',
      (ConstraintSystem.satisfies
        { algebraicConstraints :=
            ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
          busInteractions := cs.busInteractions.map (·.mapExpr rw) } bsem env') → ∃ env,
      (∀ c ∈ cs.algebraicConstraints, (rw c).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) ∧
      (∀ c ∈ cs.algebraicConstraints, keep c = false → c.eval env = 0))
    (hS : ∀ v ∈ ({ algebraicConstraints := ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
                    busInteractions := cs.busInteractions.map (·.mapExpr rw) } :
                    ConstraintSystem p).vars, v.powdrId?.isSome → v ∈ cs.vars) :
    PassCorrect cs
      { algebraicConstraints :=
          ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
        busInteractions := cs.busInteractions.map (·.mapExpr rw) } deriv bsem := by
  set out : ConstraintSystem p :=
    { algebraicConstraints :=
        ((cs.algebraicConstraints.filter keep).map rw) ++ newCs,
      busInteractions := cs.busInteractions.map (·.mapExpr rw) } with hout
  have hside : ∀ (env env' : Variable → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) →
      out.sideEffects bsem env' = cs.sideEffects bsem env := by
    intro env env' hB
    show ((cs.busInteractions.map (·.mapExpr rw)).filter
        (fun bi => bsem.isStateful bi.busId)).map _ = _
    rw [List.filter_map]
    rw [List.filter_congr (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => bsem.isStateful b.busId) ∘
        (fun b => b.mapExpr rw)) bi = bsem.isStateful bi.busId))]
    rw [List.map_map]
    exact List.map_congr_left (fun bi hbi => by
      simp only [Function.comp_apply, hB bi (List.mem_of_mem_filter hbi)])
  have hdisc : ∀ (env env' : Variable → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.mapExpr rw).eval env' = bi.eval env) →
      (out.admissible bsem env' ↔ cs.admissible bsem env) := by
    intro env env' hB
    unfold ConstraintSystem.admissible
    have hmap : (out.busInteractions.map (fun bi => bi.eval env'))
        = cs.busInteractions.map (fun bi => bi.eval env) := by
      show ((cs.busInteractions.map (·.mapExpr rw)).map (fun bi => bi.eval env')) = _
      rw [List.map_map]
      exact List.map_congr_left (fun bi hbi => hB bi hbi)
    rw [hmap]
  -- soundness and invariant come from the plain transport
  have hplain := cs.reencode_correct bsem rw keep newCs
    (fun env hsat => let ⟨env', hA, hB, hnew, _, _⟩ := hfwd env hsat; ⟨env', hA, hB, hnew⟩) hbwd
  rw [ConstraintSystem.reencCorrect] at hplain
  refine ⟨hplain.1.1, hplain.2, hS, ?_⟩
  intro env hadm hsat
  obtain ⟨env', hA, hB, hnew, hpow, hrecon⟩ := hfwd env hsat
  refine ⟨env', ⟨?_, ?_⟩, (hdisc env env' hB).2 hadm, ?_, hpow, hrecon⟩
  · intro c hc
    rcases List.mem_append.1 hc with h | h
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
      rw [hA c0 (List.mem_of_mem_filter hc0)]
      exact hsat.1 c0 (List.mem_of_mem_filter hc0)
    · exact hnew c h
  · intro bi hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
    rw [hB bi0 hbi0]
    exact hsat.2 bi0 hbi0
  · rw [hside env env' hB]; exact BusState.equiv_refl _

/-! ## Structure of enumerated assignments -/

/-- Every enumerated assignment has the domains' keys, in order. -/
theorem assignments_keys (doms : List (Variable × List (ZMod p)))
    (a : List (Variable × ZMod p)) (h : a ∈ assignments doms) :
    a.map Prod.fst = doms.map Prod.fst := by
  induction doms generalizing a with
  | nil =>
      simp only [assignments, List.mem_singleton] at h
      subst h
      rfl
  | cons xd rest ih =>
    obtain ⟨x, d⟩ := xd
    simp only [assignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp [ih a' ha']

/-- Every enumerated assignment's value at a (distinct-keyed) domain entry lies in that
    domain. -/
theorem envOf_mem_of_assignments (doms : List (Variable × List (ZMod p)))
    (hnd : (doms.map Prod.fst).Nodup) (a : List (Variable × ZMod p))
    (h : a ∈ assignments doms) : ∀ xd ∈ doms, envOf a xd.1 ∈ xd.2 := by
  induction doms generalizing a with
  | nil => simp
  | cons xd0 rest ih =>
    obtain ⟨x, d⟩ := xd0
    simp only [assignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp only [List.map_cons, List.nodup_cons] at hnd
    intro yd hyd
    rcases List.mem_cons.1 hyd with rfl | hyd
    · simp [envOf, hv]
    · have hne : yd.1 ≠ x := by
        intro heq
        exact hnd.1 (heq ▸ List.mem_map.2 ⟨yd, hyd, rfl⟩)
      simp only [envOf, if_neg hne]
      exact ih hnd.2 a' ha' yd hyd

/-- `envOf` of a zipped image list reads off the image function. -/
theorem envOf_zipimg (xs : List Variable) (g : Variable → ZMod p) (y : Variable) (hy : y ∈ xs) :
    envOf (xs.map (fun x => (x, g x))) y = g y := by
  induction xs with
  | nil => simp at hy
  | cons x rest ih =>
    simp only [List.map_cons, envOf]
    by_cases hyx : y = x
    · rw [if_pos hyx, hyx]
    · rw [if_neg hyx]
      exact ih (by
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h hyx
        · exact h)

/-! ## Pointwise environment facts for the substitution map -/

/-- `envF` at any variable is the evaluation of the substituted variable expression. -/
theorem envF_eq_varSubst (σ : Variable → Option (Expression p)) (env : Variable → ZMod p)
    (y : Variable) : envF σ env y = ((Expression.var y).substF σ).eval env := by
  show (match σ y with | some t => t.eval env | none => env y)
    = ((match σ y with | some t => t | none => .var y) : Expression p).eval env
  cases σ y <;> rfl

/-- Expression-level agreement from pointwise environment agreement. -/
theorem substF_eval_agree (σ : Variable → Option (Expression p)) (env₀ env₁ : Variable → ZMod p)
    (e : Expression p) (h : ∀ y ∈ e.vars, envF σ env₀ y = env₁ y) :
    (e.substF σ).eval env₀ = e.eval env₁ := by
  rw [Expression.eval_substF]
  exact Expression.eval_congr e _ _ h

/-- Bus-interaction-level agreement from pointwise environment agreement over its vars. -/
theorem substF_bi_agree (σ : Variable → Option (Expression p)) (env₀ env₁ : Variable → ZMod p)
    (bi : BusInteraction (Expression p)) (h : ∀ y ∈ bi.vars, envF σ env₀ y = env₁ y) :
    (bi.substF σ).eval env₀ = bi.eval env₁ := by
  rw [BusInteraction.eval_substF]
  exact BusInteraction.eval_congr bi _ _ h

/-! ## Booleanity constraints for the fresh bits -/

/-- `b · (b − 1)`. -/
def boolConstraint (b : Variable) : Expression p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

theorem boolConstraint_eval_of_bool (b : Variable) (env : Variable → ZMod p)
    (h : env b = 0 ∨ env b = 1) : (boolConstraint b).eval env = 0 := by
  show env b * (env b + (-1)) = 0
  rcases h with h | h <;> rw [h] <;> ring

theorem bool_of_boolConstraint_eval [Fact p.Prime] (b : Variable) (env : Variable → ZMod p)
    (h : (boolConstraint b).eval env = 0) : env b = 0 ∨ env b = 1 := by
  have h' : env b * (env b + (-1)) = 0 := h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right
    linear_combination h1

/-! ## The checked re-encoding step -/

/-- Does the expression contain any variable? (No allocation.) -/
def Expression.hasVar : Expression p → Bool
  | .const _ => false
  | .var _ => true
  | .add a b => a.hasVar || b.hasVar
  | .mul a b => a.hasVar || b.hasVar

/-- Constraints whose (nonempty) variable set lies inside the group. -/
def coveredBy (xs : List Variable) (c : Expression p) : Bool :=
  c.hasVar && c.varsIn xs

/-- Domains for the group's variables, from the covered constraints only. -/
def groupDoms (es : List (Expression p)) : List Variable → Option (List (Variable × List (ZMod p)))
  | [] => some []
  | x :: rest =>
    match findDomainAlg es x, groupDoms es rest with
    | some d, some ds => some ((x, d) :: ds)
    | _, _ => none

theorem groupDoms_fst (es : List (Expression p)) (xs : List Variable)
    (doms : List (Variable × List (ZMod p))) (h : groupDoms es xs = some doms) :
    doms.map Prod.fst = xs := by
  induction xs generalizing doms with
  | nil => simp only [groupDoms, Option.some.injEq] at h; subst h; rfl
  | cons x rest ih =>
    rw [groupDoms] at h
    cases hd : findDomainAlg es x with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : groupDoms es rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some ds =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [ih ds hr]

theorem groupDoms_sound [Fact p.Prime] (es : List (Expression p)) (xs : List Variable)
    (doms : List (Variable × List (ZMod p))) (h : groupDoms es xs = some doms)
    (env : Variable → ZMod p) (hall : ∀ c ∈ es, c.eval env = 0) :
    ∀ yd ∈ doms, env yd.1 ∈ yd.2 := by
  induction xs generalizing doms with
  | nil => simp only [groupDoms, Option.some.injEq] at h; subst h; simp
  | cons x rest ih =>
    rw [groupDoms] at h
    cases hd : findDomainAlg es x with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : groupDoms es rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some ds =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        intro yd hyd
        rcases List.mem_cons.1 hyd with rfl | hyd
        · exact findDomainAlg_sound es x d hd env hall
        · exact ih ds hr yd hyd

/-- The group substitution: defined on the group only, backed by a hash map. -/
def groupSubst (xs : List Variable) (hm : Std.HashMap Variable (Expression p)) :
    Variable → Option (Expression p) :=
  fun y => if xs.contains y then hm[y]? else none

/-- The `{0,1}` domain box of the fresh bits. -/
def bitBox (bits : List Variable) : List (Variable × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-! ## Degree-aware group rewriting

Substituting the interpolation polynomials variable-by-variable composes their degree with
the surrounding expression and overshoots the zkVM's degree bound (`DegreeBound`). Instead,
every *maximal wholly-in-group subexpression* is replaced by its own interpolation over the
bit patterns — any function of `k` bits is multilinear of degree ≤ `k`. The rewrite is
self-checking: the folded interpolation candidate is accepted only if its variables lie in
the bits and it agrees with the plain substitution on every pattern (a decidable, exhaustive
check), otherwise the rewrite falls back to the plain substitution (and the step-level
degree guard decides). -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. -/
def indicatorExpr (aβ : List (Variable × ZMod p)) : Expression p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

/-- The interpolation of a whole subexpression over the bit patterns. When the subexpression
    takes the **same value on every pattern** (e.g. a register index that is `52` regardless of
    the opcode flags being re-encoded), we emit that bare constant instead of the one-hot
    polynomial `Σ indicator·c`. That keeps such an address literally constant — so downstream
    memory unification's `addrConstsEq` still recognizes it and the register access keeps
    chaining — and lowers the degree. Only the `varsIn`/agreement check in `groupRewriteCand`
    consumes `interpOf`, and a constant passes both (no vars; equals the shared value on every
    pattern), so this is transparent to the correctness proof. -/
def interpOf (σfn : Variable → Option (Expression p))
    (patts : List (List (Variable × ZMod p))) (e : Expression p) : Expression p :=
  match patts with
  | [] => .const 0
  | aβ₀ :: _ =>
    let v₀ := (e.substF σfn).eval (envOf aβ₀)
    if patts.all (fun aβ => decide ((e.substF σfn).eval (envOf aβ) = v₀)) then .const v₀
    else patts.foldl (fun acc aβ =>
      .add acc (.mul (indicatorExpr aβ) (.const ((e.substF σfn).eval (envOf aβ))))) (.const 0)

/-- Interpolation candidate with the checked fallback to plain substitution. -/
def groupRewriteCand (bits : List Variable) (σfn : Variable → Option (Expression p))
    (patts : List (List (Variable × ZMod p))) (e : Expression p) : Expression p :=
  if ((interpOf σfn patts e).fold).varsIn bits &&
      patts.all (fun aβ => decide (((interpOf σfn patts e).fold).eval (envOf aβ)
        = (e.substF σfn).eval (envOf aβ)))
  then (interpOf σfn patts e).fold
  else e.substF σfn

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else. -/
def groupRewrite (xs bits : List Variable) (σfn : Variable → Option (Expression p))
    (patts : List (List (Variable × ZMod p))) : Expression p → Expression p
  | .const n => .const n
  | .var y =>
      if xs.contains y then groupRewriteCand bits σfn patts (.var y) else .var y
  | .add a b =>
      if (Expression.add a b).varsIn xs then groupRewriteCand bits σfn patts (.add a b)
      else .add (groupRewrite xs bits σfn patts a) (groupRewrite xs bits σfn patts b)
  | .mul a b =>
      if (Expression.mul a b).varsIn xs then groupRewriteCand bits σfn patts (.mul a b)
      else .mul (groupRewrite xs bits σfn patts a) (groupRewrite xs bits σfn patts b)

theorem groupRewriteCand_agree (xs bits : List Variable)
    (σfn : Variable → Option (Expression p)) (patts : List (List (Variable × ZMod p)))
    (env₀ env₁ : Variable → ZMod p) (aβ : List (Variable × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, env₀ b = envOf aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → envF σfn env₀ y = env₁ y)
    (e : Expression p) (hin : e.varsIn xs = true)
    (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (groupRewriteCand bits σfn patts e).eval env₀ = e.eval env₁ := by
  have hnotbits : ∀ y ∈ e.vars, y ∉ bits := by
    intro y hy hyb
    exact absurd hy (mentions_false_not_mem_vars y e (hfresh y hyb))
  have hsubstF : (e.substF σfn).eval env₀ = e.eval env₁ := by
    rw [Expression.eval_substF]
    apply Expression.eval_congr
    intro y hy
    exact hpoint y (hnotbits y hy)
  unfold groupRewriteCand
  split
  · next hchk =>
    rw [Bool.and_eq_true] at hchk
    have hcvars : ∀ v ∈ ((interpOf σfn patts e).fold).vars, v ∈ bits :=
      Expression.varsIn_sound bits _ hchk.1
    have h₀β : ((interpOf σfn patts e).fold).eval env₀
        = ((interpOf σfn patts e).fold).eval (envOf aβ) := by
      apply Expression.eval_congr
      intro v hv
      exact hbitsagree v (hcvars v hv)
    have hβ := of_decide_eq_true (List.all_eq_true.mp hchk.2 aβ haβ)
    rw [h₀β, hβ, Expression.eval_substF]
    apply Expression.eval_congr
    intro y hy
    have hyx : y ∈ xs := Expression.varsIn_sound xs e hin y hy
    rw [envF_eq_varSubst]
    have hstep : ((Expression.var y).substF σfn).eval (envOf aβ)
        = ((Expression.var y).substF σfn).eval env₀ := by
      apply Expression.eval_congr
      intro v hv
      exact (hbitsagree v (hpolyvars y hyx v hv)).symm
    rw [hstep, ← envF_eq_varSubst]
    exact hpoint y (hnotbits y hy)
  · exact hsubstF

theorem groupRewrite_agree (xs bits : List Variable)
    (σfn : Variable → Option (Expression p)) (patts : List (List (Variable × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (env₀ env₁ : Variable → ZMod p) (aβ : List (Variable × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, env₀ b = envOf aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → envF σfn env₀ y = env₁ y)
    (e : Expression p) (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (groupRewrite xs bits σfn patts e).eval env₀ = e.eval env₁ := by
  induction e with
  | const n => rfl
  | var y =>
      simp only [groupRewrite]
      by_cases hyx : xs.contains y
      · rw [if_pos hyx]
        exact groupRewriteCand_agree xs bits σfn patts env₀ env₁ aβ haβ hbitsagree
          hpolyvars hpoint (.var y) (by simpa [Expression.varsIn] using hyx) hfresh
      · rw [if_neg hyx]
        have hyxs : y ∉ xs := fun h => hyx (List.contains_iff_mem.mpr h)
        have hynb : y ∉ bits := by
          intro hyb
          have := hfresh y hyb
          simp [Expression.mentions] at this
        have := hpoint y hynb
        unfold envF at this
        rw [hσnone y hyxs] at this
        exact this
  | add a b iha ihb =>
      simp only [groupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [Expression.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [Expression.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (Expression.add a b).varsIn xs = true
      · rw [if_pos hin]
        exact groupRewriteCand_agree xs bits σfn patts env₀ env₁ aβ haβ hbitsagree
          hpolyvars hpoint (.add a b) hin hfresh
      · rw [if_neg hin]
        show ((groupRewrite xs bits σfn patts a).eval env₀)
          + ((groupRewrite xs bits σfn patts b).eval env₀) = a.eval env₁ + b.eval env₁
        rw [iha hfa, ihb hfb]
  | mul a b iha ihb =>
      simp only [groupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [Expression.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [Expression.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (Expression.mul a b).varsIn xs = true
      · rw [if_pos hin]
        exact groupRewriteCand_agree xs bits σfn patts env₀ env₁ aβ haβ hbitsagree
          hpolyvars hpoint (.mul a b) hin hfresh
      · rw [if_neg hin]
        show ((groupRewrite xs bits σfn patts a).eval env₀)
          * ((groupRewrite xs bits σfn patts b).eval env₀) = a.eval env₁ * b.eval env₁
        rw [iha hfa, ihb hfb]

/-- Bus-interaction-level agreement for the group rewrite. -/
theorem groupRewrite_bi_agree (xs bits : List Variable)
    (σfn : Variable → Option (Expression p)) (patts : List (List (Variable × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (env₀ env₁ : Variable → ZMod p) (aβ : List (Variable × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, env₀ b = envOf aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → envF σfn env₀ y = env₁ y)
    (bi : BusInteraction (Expression p))
    (hfreshM : ∀ b ∈ bits, bi.multiplicity.mentions b = false)
    (hfreshP : ∀ e ∈ bi.payload, ∀ b ∈ bits, e.mentions b = false) :
    (bi.mapExpr (groupRewrite xs bits σfn patts)).eval env₀ = bi.eval env₁ := by
  unfold BusInteraction.mapExpr BusInteraction.eval
  simp only [List.map_map]
  congr 1
  · exact groupRewrite_agree xs bits σfn patts hσnone env₀ env₁ aβ haβ hbitsagree
      hpolyvars hpoint bi.multiplicity hfreshM
  · apply List.map_congr_left
    intro e he
    exact groupRewrite_agree xs bits σfn patts hσnone env₀ env₁ aβ haβ hbitsagree
      hpolyvars hpoint e (hfreshP e he)

/-- The re-encoded system: substitute the group everywhere, keep only uncovered constraints,
    add booleanity for the bits. -/
def reencodeOut (cs : ConstraintSystem p) (xs bits : List Variable)
    (hm : Std.HashMap Variable (Expression p)) : ConstraintSystem p :=
  { algebraicConstraints :=
      ((cs.algebraicConstraints.filter (fun c => !coveredBy xs c)).map
        (groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits)))) ++ bits.map boolConstraint,
    busInteractions := cs.busInteractions.map (·.mapExpr (groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits)))) }

/-- The group's covered constraints. -/
def coveredCsOf (cs : ConstraintSystem p) (xs : List Variable) : List (Expression p) :=
  cs.algebraicConstraints.filter (coveredBy xs)

/-- The surviving group values: enumerated over the group's domains, filtered by the covered
    constraints. The covered set is bound outside the filter so it is computed **once**, not once
    per enumerated assignment (the `let` zeta-reduces away in proofs, so this is transparent). -/
def groupSurvivors (cs : ConstraintSystem p) (xs : List Variable)
    (doms : List (Variable × List (ZMod p))) : List (List (Variable × ZMod p)) :=
  let es := coveredCsOf cs xs
  (assignments doms).filter
    (fun a => es.all (fun c => decide (c.eval (envOf a) = 0)))

/-- All checked side conditions for one re-encoding step. -/
def checkReencode (cs : ConstraintSystem p) (xs bits : List Variable)
    (hm : Std.HashMap Variable (Expression p)) : Bool :=
  match groupDoms (coveredCsOf cs xs) xs with
  | none => false
  | some doms =>
    -- Bind these once rather than recomputing them inside the checks below: `groupSurvivors` and
    -- `assignments (bitBox …)` each appear twice, and `coveredCsOf` was rebuilt once per bit
    -- pattern. The `let`s zeta-reduce away in `checkReencode_sound_D`, so this is transparent.
    let survs := groupSurvivors cs xs doms
    let patts := assignments (bitBox bits)
    let es := coveredCsOf cs xs
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ survs.length) &&
    decide (bits.length < xs.length) &&
    decide (bits.Nodup) &&
    -- freshness: no bit occurs anywhere in the system
    bits.all (fun b =>
      cs.algebraicConstraints.all (fun c => !c.mentions b) &&
      cs.busInteractions.all (fun bi =>
        !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b))) &&
    -- the substituted group variables only mention bits
    xs.all (fun x =>
      ((Expression.var x).substF (groupSubst xs hm)).vars.all (fun v => bits.contains v)) &&
    -- completeness: every surviving group value is hit by some bit pattern
    survs.all (fun s => patts.any (fun aβ =>
      xs.all (fun x =>
        decide (((Expression.var x).substF (groupSubst xs hm)).eval (envOf aβ) = envOf s x)))) &&
    -- soundness: every bit pattern's image satisfies the covered constraints
    patts.all (fun aβ => es.all (fun c =>
      decide ((c.substF (groupSubst xs hm)).eval (envOf aβ) = 0)))

/-! ## Derived-variable methods for the fresh bits

Each bit is recovered from the group by a decision tree over the bit patterns: at the first pattern
whose interpolation image equals the group's values, output that pattern's bit. This inverts
`group = poly(bits)` for witness generation, and — crucially — the pattern the forward direction
selects (`find?` below) is exactly this first match, so the method computes the witness's bit. -/

/-- A computation method reads only its variables. -/
theorem ComputationMethod.eval_congr (cm : ComputationMethod p) (e1 e2 : Variable → ZMod p) :
    (∀ v ∈ cm.vars, e1 v = e2 v) → cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => intro _; rfl
  | quotientOrZero num den =>
      intro h
      have hn : num.eval e1 = num.eval e2 :=
        Expression.eval_congr num _ _ (fun v hv => h v (List.mem_append_left _ hv))
      have hd : den.eval e1 = den.eval e2 :=
        Expression.eval_congr den _ _ (fun v hv => h v (List.mem_append_right _ hv))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      intro h
      have hc : cond.eval e1 = cond.eval e2 :=
        Expression.eval_congr cond _ _ (fun v hv =>
          h v (List.mem_append_left _ (List.mem_append_left _ hv)))
      have ht := iht (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv)))
      have he := ihe (fun v hv => h v (List.mem_append_right _ hv))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, ht, he]

/-- The interpolation image of group variable `x` at pattern `aβ` (a field constant). -/
def imgVal (xs : List Variable) (hm : Std.HashMap Variable (Expression p))
    (aβ : List (Variable × ZMod p)) (x : Variable) : ZMod p :=
  ((Expression.var x).substF (groupSubst xs hm)).eval (envOf aβ)

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`, as nested `ifEqZero`. -/
def matchCM (xs : List Variable) (imgFn : Variable → ZMod p)
    (thenM elseM : ComputationMethod p) : ComputationMethod p :=
  match xs with
  | [] => thenM
  | x :: rest =>
      .ifEqZero (.add (.var x) (.const (-(imgFn x)))) (matchCM rest imgFn thenM elseM) elseM

theorem matchCM_eval (xs : List Variable) (imgFn : Variable → ZMod p)
    (thenM elseM : ComputationMethod p) (env : Variable → ZMod p) :
    (matchCM xs imgFn thenM elseM).eval env
    = if xs.all (fun x => decide (imgFn x = env x)) then thenM.eval env else elseM.eval env := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      show (ComputationMethod.ifEqZero _ (matchCM rest imgFn thenM elseM) elseM).eval env = _
      rw [ComputationMethod.eval]
      by_cases hx : imgFn x = env x
      · rw [if_pos (show (Expression.add (.var x) (.const (-(imgFn x)))).eval env = 0 by
              show env x + -(imgFn x) = 0; rw [hx]; ring), ih, List.all_cons]
        simp [hx]
      · rw [if_neg (show (Expression.add (.var x) (.const (-(imgFn x)))).eval env ≠ 0 by
              show env x + -(imgFn x) ≠ 0; intro h; exact hx (by linear_combination -h)),
            List.all_cons]
        simp [hx]

/-- Variables of `matchCM` lie in `xs` together with those of the branches. -/
theorem matchCM_vars (xs : List Variable) (imgFn : Variable → ZMod p)
    (thenM elseM : ComputationMethod p) :
    ∀ v ∈ (matchCM xs imgFn thenM elseM).vars, v ∈ xs ∨ v ∈ thenM.vars ∨ v ∈ elseM.vars := by
  induction xs with
  | nil => intro v hv; exact Or.inr (Or.inl hv)
  | cons x rest ih =>
      intro v hv
      simp only [matchCM, ComputationMethod.vars, Expression.vars, List.nil_append,
        List.append_assoc, List.mem_append, List.mem_singleton] at hv
      rcases hv with rfl | hv | hv
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih v hv with h | h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inr hv)

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit. -/
def bitCM (patts : List (List (Variable × ZMod p))) (xs : List Variable)
    (hm : Std.HashMap Variable (Expression p)) (b : Variable) : ComputationMethod p :=
  match patts with
  | [] => .const 0
  | aβ :: rest => matchCM xs (imgVal xs hm aβ) (.const (envOf aβ b)) (bitCM rest xs hm b)

theorem bitCM_eval (patts : List (List (Variable × ZMod p))) (xs : List Variable)
    (hm : Std.HashMap Variable (Expression p)) (b : Variable) (env : Variable → ZMod p) :
    (bitCM patts xs hm b).eval env
    = match patts.find? (fun aβ => xs.all (fun x => decide (imgVal xs hm aβ x = env x))) with
      | some aβ => envOf aβ b
      | none => 0 := by
  induction patts with
  | nil => rfl
  | cons aβ rest ih =>
      show (matchCM xs (imgVal xs hm aβ) (.const (envOf aβ b)) (bitCM rest xs hm b)).eval env = _
      rw [matchCM_eval, List.find?_cons]
      by_cases hmatch : xs.all (fun x => decide (imgVal xs hm aβ x = env x)) = true
      · rw [if_pos hmatch, hmatch]; rfl
      · rw [if_neg hmatch]
        simp only [hmatch, ih]

/-- The derivation of bit `b` reads only group variables. -/
theorem bitCM_vars (patts : List (List (Variable × ZMod p))) (xs : List Variable)
    (hm : Std.HashMap Variable (Expression p)) (b : Variable) :
    ∀ v ∈ (bitCM patts xs hm b).vars, v ∈ xs := by
  induction patts with
  | nil => intro v hv; simp [bitCM, ComputationMethod.vars] at hv
  | cons aβ rest ih =>
      intro v hv
      rcases matchCM_vars xs (imgVal xs hm aβ) (.const (envOf aβ b)) (bitCM rest xs hm b) v hv
        with h | h | h
      · exact h
      · simp [ComputationMethod.vars] at h
      · exact ih v h

/-- Substituting a wholly-in-group expression (whose group variables `σfn` maps into the bits)
    yields an expression over the bits only. -/
theorem Expression.substF_varsIn_bits (xs bits : List Variable)
    (σfn : Variable → Option (Expression p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF σfn).vars, v ∈ bits)
    (e : Expression p) (hin : e.varsIn xs = true) :
    ∀ v ∈ (e.substF σfn).vars, v ∈ bits := by
  induction e with
  | const n => intro v hv; simp [Expression.substF, Expression.vars] at hv
  | var y =>
      intro v hv
      exact hσ y (List.contains_iff_mem.mp (by simpa [Expression.varsIn] using hin)) v hv
  | add a b iha ihb =>
      rw [Expression.varsIn, Bool.and_eq_true] at hin
      intro v hv
      simp only [Expression.substF, Expression.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv
  | mul a b iha ihb =>
      rw [Expression.varsIn, Bool.and_eq_true] at hin
      intro v hv
      simp only [Expression.substF, Expression.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv

/-- A rewritten wholly-in-group expression is over the bits only. -/
theorem groupRewriteCand_vars (xs bits : List Variable)
    (σfn : Variable → Option (Expression p)) (patts : List (List (Variable × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF σfn).vars, v ∈ bits)
    (e : Expression p) (hin : e.varsIn xs = true) :
    ∀ v ∈ (groupRewriteCand bits σfn patts e).vars, v ∈ bits := by
  intro v hv
  unfold groupRewriteCand at hv
  split at hv
  · next hchk =>
      rw [Bool.and_eq_true] at hchk
      exact Expression.varsIn_sound bits _ hchk.1 v hv
  · exact Expression.substF_varsIn_bits xs bits σfn hσ e hin v hv

/-- Every variable of a group-rewritten expression is either an original variable of `e` or a
    fresh bit. -/
theorem groupRewrite_vars (xs bits : List Variable)
    (σfn : Variable → Option (Expression p)) (patts : List (List (Variable × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF σfn).vars, v ∈ bits)
    (e : Expression p) :
    ∀ v ∈ (groupRewrite xs bits σfn patts e).vars, v ∈ e.vars ∨ v ∈ bits := by
  induction e with
  | const n => simp [groupRewrite, Expression.vars]
  | var y =>
      simp only [groupRewrite]
      by_cases hyx : xs.contains y
      · rw [if_pos hyx]; intro v hv
        exact Or.inr (groupRewriteCand_vars xs bits σfn patts hσ (.var y)
          (by simpa [Expression.varsIn] using hyx) v hv)
      · rw [if_neg hyx]; intro v hv; exact Or.inl hv
  | add a b iha ihb =>
      simp only [groupRewrite]
      by_cases hin : (Expression.add a b).varsIn xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (groupRewriteCand_vars xs bits σfn patts hσ (.add a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [Expression.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
  | mul a b iha ihb =>
      simp only [groupRewrite]
      by_cases hin : (Expression.mul a b).varsIn xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (groupRewriteCand_vars xs bits σfn patts hσ (.mul a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [Expression.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h

/-- Every variable of the re-encoded system is either an original variable of `cs` or a fresh
    bit — proven by construction from the certified substitution, so the pass needs no scan. -/
theorem reencodeOut_vars_subset (cs : ConstraintSystem p) (xs bits : List Variable)
    (hm : Std.HashMap Variable (Expression p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF (groupSubst xs hm)).vars, v ∈ bits) :
    ∀ v ∈ (reencodeOut cs xs bits hm).vars, v ∈ cs.vars ∨ v ∈ bits := by
  intro v hv
  have gr := groupRewrite_vars xs bits (groupSubst xs hm) (assignments (bitBox bits)) hσ
  rcases ConstraintSystem.mem_vars.1 hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · simp only [reencodeOut, List.mem_append] at hc
    rcases hc with hc | hc
    · rcases List.mem_map.1 hc with ⟨c0, hc0, rfl⟩
      rcases gr c0 v hcv with h | h
      · exact Or.inl (ConstraintSystem.mem_vars_of_constraint (List.mem_of_mem_filter hc0) h)
      · exact Or.inr h
    · rcases List.mem_map.1 hc with ⟨b, hb, rfl⟩
      right
      have hvb : v = b := by simpa [boolConstraint, Expression.vars] using hcv
      exact hvb ▸ hb
  · simp only [reencodeOut, List.mem_map] at hbi
    rcases hbi with ⟨bi0, hbi0, rfl⟩
    rcases hbiv with hmv | ⟨e, he, hev⟩
    · simp only [BusInteraction.mapExpr] at hmv
      rcases gr bi0.multiplicity v hmv with h | h
      · exact Or.inl (ConstraintSystem.mem_vars_of_mult hbi0 h)
      · exact Or.inr h
    · simp only [BusInteraction.mapExpr] at he
      rcases List.mem_map.1 he with ⟨e0, he0, rfl⟩
      rcases gr e0 v hev with h | h
      · exact Or.inl (ConstraintSystem.mem_vars_of_payload hbi0 he0 h)
      · exact Or.inr h

/-- Appending derivations: the later list `B` takes precedence, so a fresh variable's method there
    overrides any earlier entry for it (this is what makes the reconstruction robust to duplicates). -/
theorem Derivations.methodFor_append (A B : Derivations p) (v : Variable) :
    Derivations.methodFor (A ++ B) v
      = (Derivations.methodFor B v).orElse (fun _ => Derivations.methodFor A v) := by
  induction A with
  | nil => simp [Derivations.methodFor]
  | cons pcm rest ih =>
      obtain ⟨u, cm⟩ := pcm
      simp only [List.cons_append, Derivations.methodFor, ih]
      cases Derivations.methodFor B v <;> simp [Option.orElse]

/-- The method list built for the fresh bits supplies `g w` for a bit `w`, nothing otherwise. -/
theorem Derivations.methodFor_map (bits : List Variable) (g : Variable → ComputationMethod p)
    (w : Variable) :
    Derivations.methodFor (bits.map (fun b => (b, g b))) w
      = if w ∈ bits then some (g w) else none := by
  induction bits with
  | nil => simp [Derivations.methodFor]
  | cons b rest ih =>
      simp only [List.map_cons, Derivations.methodFor, ih, List.mem_cons]
      by_cases hw : w ∈ rest
      · simp [hw]
      · by_cases hbw : b = w
        · subst hbw; simp [hw]
        · have hwb : w ≠ b := fun h => hbw h.symm
          simp [hw, hbw, hwb, Option.orElse]

theorem checkReencode_sound_D [Fact p.Prime] (cs : ConstraintSystem p) (bsem : BusSemantics p)
    (xs bits : List Variable) (hm : Std.HashMap Variable (Expression p))
    (hxs : ∀ x ∈ xs, x.powdrId?.isSome) (hxsB : ∀ x ∈ xs, x ∉ bits)
    (hbn : ∀ b ∈ bits, b.powdrId? = none)
    (hchk : checkReencode cs xs bits hm = true) :
    PassCorrect cs (reencodeOut cs xs bits hm)
      (bits.map (fun b => (b, bitCM (assignments (bitBox bits)) xs hm b))) bsem := by
  unfold checkReencode at hchk
  split at hchk
  · exact absurd hchk (by simp)
  rename_i doms hdoms
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hbox, hm2⟩, hprofit⟩, hnodup⟩, hfreshB⟩, hvarsB⟩, hC5⟩, hC6⟩ := hchk
  have hnodup' : bits.Nodup := of_decide_eq_true hnodup
  have hkeys := groupDoms_fst (coveredCsOf cs xs) xs doms hdoms
  have hbitKeys : (bitBox (p := p) bits).map Prod.fst = bits := by
    unfold bitBox
    rw [List.map_map]
    simp [Function.comp_def]
  -- per-expression freshness, unpacked
  have hfreshC : ∀ b ∈ bits, ∀ c ∈ cs.algebraicConstraints, b ∉ c.vars := by
    intro b hb c hc
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have := List.all_eq_true.mp h1.1 c hc
    exact mentions_false_not_mem_vars b c (by simpa using this)
  have hfreshBi : ∀ b ∈ bits, ∀ bi ∈ cs.busInteractions, b ∉ bi.vars := by
    intro b hb bi hbi
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    intro hmem
    unfold BusInteraction.vars at hmem
    rcases List.mem_append.1 hmem with hmem | hmem
    · exact mentions_false_not_mem_vars b bi.multiplicity (by simpa using h2.1) hmem
    · obtain ⟨e, he, hbe⟩ := List.mem_flatMap.1 hmem
      exact mentions_false_not_mem_vars b e
        (by simpa using List.all_eq_true.mp h2.2 e he) hbe
  -- the substituted group variables' expressions live over the bits
  have hpolyVars : ∀ y ∈ xs, ∀ v ∈ ((Expression.var y).substF (groupSubst xs hm)).vars,
      v ∈ bits := by
    intro y hy v hv
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp (List.all_eq_true.mp hvarsB y hy) v hv)
  -- output variables are original `cs` variables or fresh bits (by construction, no scan)
  have hvars : ∀ v ∈ (reencodeOut cs xs bits hm).vars, v ∈ cs.vars ∨ v ∈ bits :=
    reencodeOut_vars_subset cs xs bits hm hpolyVars
  have hσnone : ∀ y, y ∉ xs → groupSubst xs hm y = none := by
    intro y hy
    simp [groupSubst, hy]
  have hfreshCm : ∀ c ∈ cs.algebraicConstraints, ∀ b ∈ bits, c.mentions b = false := by
    intro c hc b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    simpa using List.all_eq_true.mp h1.1 c hc
  have hfreshMm : ∀ bi ∈ cs.busInteractions, ∀ b ∈ bits,
      bi.multiplicity.mentions b = false := by
    intro bi hbi b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using h2.1
  have hfreshPm : ∀ bi ∈ cs.busInteractions, ∀ e ∈ bi.payload, ∀ b ∈ bits,
      e.mentions b = false := by
    intro bi hbi e he b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using List.all_eq_true.mp h2.2 e he
  -- bits are fresh: none of them occurs in `cs`
  have hbitsCs : ∀ b ∈ bits, b ∉ cs.vars := by
    intro b hb hmem
    rw [ConstraintSystem.mem_vars] at hmem
    rcases hmem with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
    · exact hfreshC b hb c hc hcv
    · refine hfreshBi b hb bi hbi ?_
      unfold BusInteraction.vars
      rcases hbiv with h | ⟨e, he, hev⟩
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, hev⟩)
  -- FORWARD (with the frame and derived-variable reconstruction)
  have hfwd_D : ∀ env, cs.satisfies bsem env → ∃ env',
      (∀ c ∈ cs.algebraicConstraints,
        ((groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits))) c).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions,
        (bi.mapExpr (groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits)))).eval env' = bi.eval env) ∧
      (∀ c ∈ bits.map boolConstraint, c.eval env' = 0) ∧
      (∀ v : Variable, v.powdrId?.isSome → env' v = env v) ∧
      (∀ dsIn : Derivations p, cs.reconstructs dsIn env →
        (reencodeOut cs xs bits hm).reconstructs
          (dsIn ++ bits.map (fun b => (b, bitCM (assignments (bitBox bits)) xs hm b))) env') := by
    intro env hsat
    have hallES : ∀ c ∈ coveredCsOf cs xs, c.eval env = 0 := fun c hc =>
      hsat.1 c (List.mem_of_mem_filter hc)
    have hdsound := groupDoms_sound (coveredCsOf cs xs) xs doms hdoms env hallES
    have hamem : (doms.map (fun yd => (yd.1, env yd.1))) ∈ assignments doms :=
      mem_assignments doms env hdsound
    have hasurv : (doms.map (fun yd => (yd.1, env yd.1))) ∈ groupSurvivors cs xs doms := by
      refine List.mem_filter.2 ⟨hamem, ?_⟩
      rw [List.all_eq_true]
      intro c hc
      rw [decide_eq_true_iff]
      have hcov := List.of_mem_filter hc
      rw [coveredBy, Bool.and_eq_true] at hcov
      have hcvars : ∀ v ∈ c.vars, v ∈ doms.map Prod.fst := by
        rw [hkeys]
        exact Expression.varsIn_sound _ c hcov.2
      have heq : c.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = c.eval env :=
        Expression.eval_congr c _ _ (fun v hv => envOf_map doms env v (hcvars v hv))
      rw [heq]
      exact hallES c hc
    -- select the first pattern whose interpolation image matches the group (deterministic, so it
    -- coincides with what `bitCM` computes); it exists by the `hC5` completeness check
    have hC5' : (assignments (bitBox bits)).any
        (fun aβ => xs.all (fun x => decide (imgVal xs hm aβ x = env x))) = true := by
      rw [List.any_eq_true]
      obtain ⟨aβ, ha, hp⟩ := List.any_eq_true.1 (List.all_eq_true.mp hC5 _ hasurv)
      refine ⟨aβ, ha, ?_⟩
      rw [List.all_eq_true] at hp ⊢
      intro x hx
      have hsx : envOf (doms.map (fun yd => (yd.1, env yd.1))) x = env x :=
        envOf_map doms env x (hkeys ▸ hx)
      have := hp x hx
      rwa [hsx] at this
    cases hfindEnv : (assignments (bitBox bits)).find?
        (fun aβ => xs.all (fun x => decide (imgVal xs hm aβ x = env x))) with
    | none =>
        exfalso
        rw [List.find?_eq_none] at hfindEnv
        obtain ⟨aβ0, ha0, hp0⟩ := List.any_eq_true.1 hC5'
        exact absurd hp0 (by simpa using hfindEnv aβ0 ha0)
    | some aβ =>
      have haβ : aβ ∈ assignments (bitBox bits) := List.mem_of_find?_eq_some hfindEnv
      have hβpred : xs.all (fun x => decide (imgVal xs hm aβ x = env x)) = true := by
        simpa using List.find?_some hfindEnv
      have hkeysβ : aβ.map Prod.fst = bits := by
        rw [assignments_keys (bitBox bits) aβ haβ, hbitKeys]
      have hxbits : ∀ x ∈ xs, x ∉ bits := hxsB
      have henvxs : ∀ x ∈ xs, envExt aβ env x = env x := fun x hx =>
        envExt_eq_env_of_notmem aβ env x (by rw [hkeysβ]; exact hxbits x hx)
      -- pointwise agreement off the bits
      have hpoint : ∀ y, y ∉ bits → envF (groupSubst xs hm) (envExt aβ env) y = env y := by
        intro y hyb
        by_cases hyx : y ∈ xs
        · rw [envF_eq_varSubst]
          have hagree : ((Expression.var y).substF (groupSubst xs hm)).eval (envExt aβ env)
              = ((Expression.var y).substF (groupSubst xs hm)).eval (envOf aβ) := by
            apply Expression.eval_congr
            intro v hv
            exact envExt_eq_envOf_of_mem aβ env v (hkeysβ ▸ hpolyVars y hyx v hv)
          rw [hagree]
          exact of_decide_eq_true (List.all_eq_true.mp hβpred y hyx)
        · have hnone : groupSubst xs hm y = none := by
            simp [groupSubst, hyx]
          unfold envF
          rw [hnone]
          exact envExt_eq_env_of_notmem aβ env y (hkeysβ ▸ hyb)
      have hbitsagree : ∀ b ∈ bits, envExt aβ env b = envOf aβ b := fun b hb =>
        envExt_eq_envOf_of_mem aβ env b (hkeysβ ▸ hb)
      refine ⟨envExt aβ env, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        exact groupRewrite_agree xs bits (groupSubst xs hm) (assignments (bitBox bits))
          hσnone (envExt aβ env) env aβ haβ hbitsagree hpolyVars hpoint c (hfreshCm c hc)
      · intro bi hbi
        exact groupRewrite_bi_agree xs bits (groupSubst xs hm) (assignments (bitBox bits))
          hσnone (envExt aβ env) env aβ haβ hbitsagree hpolyVars hpoint bi
          (hfreshMm bi hbi) (hfreshPm bi hbi)
      · intro c hc
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
        apply boolConstraint_eval_of_bool
        have hbk : b ∈ aβ.map Prod.fst := hkeysβ ▸ hb
        rw [envExt_eq_envOf_of_mem aβ env b hbk]
        have hmem := envOf_mem_of_assignments (bitBox bits)
          (by rw [hbitKeys]; exact hnodup') aβ haβ
          (b, ([0, 1] : List (ZMod p))) (List.mem_map.2 ⟨b, hb, rfl⟩)
        simpa using hmem
      · -- frame: input columns keep their value (only fresh bits change)
        intro v hvpow
        refine envExt_eq_env_of_notmem aβ env v ?_
        rw [hkeysβ]
        intro hvb
        rw [hbn v hvb] at hvpow
        simp at hvpow
      · -- reconstruction (later derivations win, so a fresh bit's method overrides any dsIn entry)
        intro dsIn hdsIn w hwout hwnone
        rcases hvars w hwout with hwcs | hwb
        · -- a surviving input column of `cs`: not a fresh bit, so `dsIn`'s method is the one used
          have hwnb : w ∉ bits := fun h => hbitsCs w h hwcs
          obtain ⟨cm, hcm, hcmv, hcmeval⟩ := hdsIn w hwcs hwnone
          refine ⟨cm, ?_, hcmv, ?_⟩
          · simp [Derivations.methodFor_append, Derivations.methodFor_map, hwnb, hcm]
          · rw [ComputationMethod.eval_congr cm (envExt aβ env) env (fun v hv => by
              refine envExt_eq_env_of_notmem aβ env v ?_
              rw [hkeysβ]
              intro hvb
              have hp := hcmv v hv
              rw [hbn v hvb] at hp
              simp at hp), hcmeval]
            exact (envExt_eq_env_of_notmem aβ env w (by
              rw [hkeysβ]; intro hwb; exact hbitsCs w hwb hwcs)).symm
        · -- a fresh bit: its `bitCM` method (the last listed for `w`) computes it
          refine ⟨bitCM (assignments (bitBox bits)) xs hm w, ?_,
            fun v hv => hxs v (bitCM_vars _ xs hm w v hv), ?_⟩
          · simp [Derivations.methodFor_append, Derivations.methodFor_map, hwb]
          · rw [ComputationMethod.eval_congr (bitCM (assignments (bitBox bits)) xs hm w)
              (envExt aβ env) env (fun v hv => henvxs v (bitCM_vars _ xs hm w v hv)),
              bitCM_eval, hfindEnv, envExt_eq_envOf_of_mem aβ env w (hkeysβ ▸ hwb)]
  -- BACKWARD
  have hbwd : ∀ env',
      (ConstraintSystem.satisfies
        { algebraicConstraints :=
            ((cs.algebraicConstraints.filter (fun c => !coveredBy xs c)).map
              (groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits)))) ++ bits.map boolConstraint,
          busInteractions := cs.busInteractions.map (·.mapExpr (groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits)))) }
        bsem env') → ∃ env,
      (∀ c ∈ cs.algebraicConstraints,
        ((groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits))) c).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions,
        (bi.mapExpr (groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits)))).eval env' = bi.eval env) ∧
      (∀ c ∈ cs.algebraicConstraints, (!coveredBy xs c) = false → c.eval env = 0) := by
    intro env' hsat'
    have hbool : ∀ b ∈ bits, env' b = 0 ∨ env' b = 1 := by
      intro b hb
      apply bool_of_boolConstraint_eval
      exact hsat'.1 _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩))
    have haβmem : ((bitBox (p := p) bits).map (fun yd => (yd.1, env' yd.1)))
        ∈ assignments (bitBox bits) := by
      apply mem_assignments
      intro yd hyd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hyd
      simpa using hbool b hb
    have hβenv : ∀ b ∈ bits, envOf ((bitBox (p := p) bits).map (fun yd => (yd.1, env' yd.1))) b
        = env' b := by
      intro b hb
      exact envOf_map (bitBox bits) env' b (by rw [hbitKeys]; exact hb)
    -- the image environment
    set env := envExt
      (xs.map (fun x => (x, ((Expression.var x).substF (groupSubst xs hm)).eval env')))
      env' with henv
    have hkeysP : (xs.map (fun x =>
        (x, ((Expression.var x).substF (groupSubst xs hm)).eval env'))).map Prod.fst = xs := by
      rw [List.map_map]
      simp [Function.comp_def]
    have hpoint : ∀ y, envF (groupSubst xs hm) env' y = env y := by
      intro y
      by_cases hyx : y ∈ xs
      · rw [envF_eq_varSubst, henv]
        rw [envExt_eq_envOf_of_mem _ env' y (by rw [hkeysP]; exact hyx)]
        rw [envOf_zipimg xs _ y hyx]
      · have hnone : groupSubst xs hm y = none := by
          simp [groupSubst, hyx]
        unfold envF
        rw [hnone, henv]
        rw [envExt_eq_env_of_notmem _ env' y (by rw [hkeysP]; exact hyx)]
    have hexpr : ∀ e : Expression p,
        (e.substF (groupSubst xs hm)).eval env' = e.eval env :=
      fun e => substF_eval_agree _ _ _ e (fun y _ => hpoint y)
    have hkeysβ' : ((bitBox (p := p) bits).map (fun yd => (yd.1, env' yd.1))).map Prod.fst
        = bits := by
      unfold bitBox
      rw [List.map_map, List.map_map]
      simp [Function.comp_def]
    have hbitsagree' : ∀ b ∈ bits,
        env' b = envOf ((bitBox (p := p) bits).map (fun yd => (yd.1, env' yd.1))) b :=
      fun b hb => (hβenv b hb).symm
    refine ⟨env, ?_, ?_, ?_⟩
    · intro c hc
      exact groupRewrite_agree xs bits (groupSubst xs hm) (assignments (bitBox bits))
        hσnone env' env _ haβmem hbitsagree' hpolyVars (fun y _ => hpoint y) c
        (hfreshCm c hc)
    · intro bi hbi
      exact groupRewrite_bi_agree xs bits (groupSubst xs hm) (assignments (bitBox bits))
        hσnone env' env _ haβmem hbitsagree' hpolyVars (fun y _ => hpoint y) bi
        (hfreshMm bi hbi) (hfreshPm bi hbi)
    · intro c hc hkc
      have hcov : coveredBy xs c = true := by simpa using hkc
      have hcmem : c ∈ coveredCsOf cs xs := List.mem_filter.2 ⟨hc, hcov⟩
      have h6 := List.all_eq_true.mp (List.all_eq_true.mp hC6 _ haβmem) c hcmem
      rw [decide_eq_true_iff] at h6
      -- transport the pattern-image fact to env
      have hcvars : ∀ v ∈ c.vars, v ∈ xs := by
        rw [coveredBy, Bool.and_eq_true] at hcov
        exact Expression.varsIn_sound _ c hcov.2
      have hagree : (c.substF (groupSubst xs hm)).eval
            (envOf ((bitBox (p := p) bits).map (fun yd => (yd.1, env' yd.1))))
          = (c.substF (groupSubst xs hm)).eval env' := by
        rw [Expression.eval_substF, Expression.eval_substF]
        apply Expression.eval_congr
        intro y hy
        rw [envF_eq_varSubst, envF_eq_varSubst]
        apply Expression.eval_congr
        intro v hv
        exact hβenv v (hpolyVars y (hcvars y hy) v hv)
      rw [← hexpr c, ← hagree]
      exact h6
  -- no new powdr-ID column: every output variable is a `cs` variable or a (no-ID) bit
  have hS : ∀ v ∈ (reencodeOut cs xs bits hm).vars, v.powdrId?.isSome → v ∈ cs.vars := by
    intro v hv hvpow
    rcases hvars v hv with h | h
    · exact h
    · rw [hbn v h] at hvpow; simp at hvpow
  show PassCorrect cs (reencodeOut cs xs bits hm)
    (bits.map (fun b => (b, bitCM (assignments (bitBox bits)) xs hm b))) bsem
  unfold reencodeOut
  exact cs.reencode_correct_D bsem
    (groupRewrite xs bits (groupSubst xs hm) (assignments (bitBox bits))) (fun c => !coveredBy xs c)
    (bits.map boolConstraint) (bits.map (fun b => (b, bitCM (assignments (bitBox bits)) xs hm b)))
    hfwd_D hbwd hS

/-! ## Building the interpolation (proof-free) and the pass -/

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs. -/
def interpPoly (pz : List (List (Variable × ZMod p) × List (Variable × ZMod p))) (x : Variable) :
    Expression p :=
  pz.foldl (fun acc az => .add acc (.mul (indicatorExpr az.1) (.const (envOf az.2 x))))
    (.const 0)

/-- Construct the bits and the substitution map for a candidate group (proof-free — the
    checked certificate re-verifies everything). -/
def buildReencode (cs : ConstraintSystem p) (xs : List Variable) (freshBase : String) :
    Option (List Variable × Std.HashMap Variable (Expression p)) :=
  match groupDoms (coveredCsOf cs xs) xs with
  | none => none
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survs := groupSurvivors cs xs doms
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let bits := (List.range k).map (fun j => ({ name := freshBase ++ "_" ++ toString j } : Variable))
          let patts := assignments (bitBox (p := p) bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (interpPoly pz x).fold))))
        else none
      else none
    else none

/-- One checked re-encoding step (identity if construction or certificate fails). The expensive
    filter — `buildReencode` — runs first, so the remaining side conditions (all cheap: the group
    is all input columns and disjoint from the fresh bits, the bits carry no powdr ID) are only
    checked for the few groups that are actually re-encodable. The output-variable frame is proven
    by construction (`reencodeOut_vars_subset`), so no per-variable scan is needed. -/
def reencodeStep [Fact p.Prime] (bsem : BusSemantics p) (cs : ConstraintSystem p)
    (xs : List Variable) (freshBase : String) : PassResult cs bsem :=
  if hxs : xs.all (fun x => x.powdrId?.isSome) = true then
  match hb : buildReencode cs xs freshBase with
  | none => ⟨cs, [], PassCorrect.refl cs bsem⟩
  | some (bits, hm) =>
    if hxsB : xs.all (fun x => decide (x ∉ bits)) = true then
    if hbn : bits.all (fun b => decide (b.powdrId? = none)) = true then
    if hchk : checkReencode cs xs bits hm = true then
      let ro := reencodeOut cs xs bits hm
      if ro.withinDegreeB bsem.degreeBound then
        ⟨ro,
         bits.map (fun b => (b, bitCM (assignments (bitBox bits)) xs hm b)),
         checkReencode_sound_D cs bsem xs bits hm
           (fun x hx => by simpa using List.all_eq_true.mp hxs x hx)
           (fun x hx => of_decide_eq_true (List.all_eq_true.mp hxsB x hx))
           (fun b hbm => of_decide_eq_true (List.all_eq_true.mp hbn b hbm))
           hchk⟩
      else ⟨cs, [], PassCorrect.refl cs bsem⟩
    else ⟨cs, [], PassCorrect.refl cs bsem⟩
    else ⟨cs, [], PassCorrect.refl cs bsem⟩
    else ⟨cs, [], PassCorrect.refl cs bsem⟩
  else ⟨cs, [], PassCorrect.refl cs bsem⟩

/-- Process the candidate groups sequentially (correctness composes; derivations concatenate). -/
def reencodeLoop [Fact p.Prime] (bsem : BusSemantics p) :
    List (List Variable) → Nat → (cs : ConstraintSystem p) → PassResult cs bsem
  | [], _, cs => ⟨cs, [], PassCorrect.refl cs bsem⟩
  | xs :: rest, idx, cs =>
    let r1 := reencodeStep bsem cs xs
      (s!"rnc{cs.algebraicConstraints.length}_{cs.busInteractions.length}_{idx}")
    let r2 := reencodeLoop bsem rest (idx + 1) r1.out
    ⟨r2.out, r1.derivs ++ r2.derivs, r1.correct.andThen r2.correct⟩

/-- `List.dedup` computed in linear time via a hash set, with the **identical** result: an element
    is kept at its last-occurrence position (exactly `List.dedup`'s order), so swapping this in is a
    pure speedup — `reencodeLoop`'s correctness is independent of the target list, and its
    (order-sensitive, greedy) behaviour is unchanged because the list itself is unchanged. -/
def dedupHash {α : Type} [BEq α] [Hashable α] (l : List α) : List α :=
  (l.reverse.foldl (fun (st : List α × Std.HashSet α) t =>
    if st.2.contains t then st else (t :: st.1, st.2.insert t))
    (([], ∅) : List α × Std.HashSet α)).1

/-- The witness re-encoding pass: for every constraint's (small) all-input-column variable group
    whose covered constraints allow only a few joint values, re-encode the group with `⌈log₂ m⌉`
    fresh booleans and ship each bit's derived-variable method. Prime `p` only; identity otherwise. -/
def reencodePass : VerifiedPass p := fun cs bsem =>
  if hpr : p.Prime then
    haveI : Fact p.Prime := ⟨hpr⟩
    -- `dedupHash` replaces the quadratic `List.dedup` over the (up to thousands of) target
    -- variable-sets, producing the identical list in linear time.
    let targets := dedupHash (cs.algebraicConstraints.filterMap (fun c =>
      let vs := c.vars.dedup
      if 2 ≤ vs.length && vs.length ≤ 8 then some (vs.mergeSort (fun a b => compare a b != .gt)) else none))
    reencodeLoop bsem targets 0 cs
  else ⟨cs, [], PassCorrect.refl cs bsem⟩
