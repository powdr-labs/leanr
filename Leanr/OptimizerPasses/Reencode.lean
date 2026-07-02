import Leanr.OptimizerPasses.DomainBatch

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
def envExt : List (String × ZMod p) → (String → ZMod p) → String → ZMod p
  | [], env, y => env y
  | (x, v) :: rest, env, y => if y = x then v else envExt rest env y

/-- On the keys, `envExt` agrees with `envOf`. -/
theorem envExt_eq_envOf_of_mem (pairs : List (String × ZMod p)) (env : String → ZMod p)
    (y : String) (h : y ∈ pairs.map Prod.fst) : envExt pairs env y = envOf pairs y := by
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
theorem envExt_eq_env_of_notmem (pairs : List (String × ZMod p)) (env : String → ZMod p)
    (y : String) (h : y ∉ pairs.map Prod.fst) : envExt pairs env y = env y := by
  induction pairs with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [envExt, if_neg h.1]
    exact ih h.2

/-! ## `mentions` and variable membership -/

theorem mentions_false_not_mem_vars (x : String) (e : Expression p)
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

/-- **Re-encoding correctness.** `out` replaces every expression `e` by `e.substF σ`, keeps
    only the constraints selected by `keep`, and appends `newCs`. If satisfying assignments
    transport in both directions such that every original expression *evaluates identically*
    (forward additionally establishing `newCs`, backward additionally the dropped
    constraints), the step is `PassCorrect`. Nothing here mentions bits or groups — it is a
    generic witness-transport principle. -/
theorem ConstraintSystem.reencode_correct (cs : ConstraintSystem p) (bsem : BusSemantics p)
    (σ : String → Option (Expression p)) (keep : Expression p → Bool)
    (newCs : List (Expression p))
    (hfwd : ∀ env, cs.satisfies bsem env → ∃ env',
      (∀ c ∈ cs.algebraicConstraints, (c.substF σ).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions, (bi.substF σ).eval env' = bi.eval env) ∧
      (∀ c ∈ newCs, c.eval env' = 0))
    (hbwd : ∀ env',
      (ConstraintSystem.satisfies
        { algebraicConstraints :=
            ((cs.algebraicConstraints.filter keep).map (·.substF σ)) ++ newCs,
          busInteractions := cs.busInteractions.map (·.substF σ) } bsem env') → ∃ env,
      (∀ c ∈ cs.algebraicConstraints, (c.substF σ).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions, (bi.substF σ).eval env' = bi.eval env) ∧
      (∀ c ∈ cs.algebraicConstraints, keep c = false → c.eval env = 0)) :
    PassCorrect cs
      { algebraicConstraints :=
          ((cs.algebraicConstraints.filter keep).map (·.substF σ)) ++ newCs,
        busInteractions := cs.busInteractions.map (·.substF σ) } bsem := by
  set out : ConstraintSystem p :=
    { algebraicConstraints :=
        ((cs.algebraicConstraints.filter keep).map (·.substF σ)) ++ newCs,
      busInteractions := cs.busInteractions.map (·.substF σ) } with hout
  -- message-list equality under expression-wise agreement
  have hmsgs : ∀ (env env' : String → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.substF σ).eval env' = bi.eval env) →
      ∀ busId, (out.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => bi.eval env')
        = (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => bi.eval env) := by
    intro env env' hB busId
    show ((cs.busInteractions.map (·.substF σ)).filter (fun bi => bi.busId = busId)).map
        (fun bi => bi.eval env') = _
    rw [List.filter_map]
    rw [List.filter_congr (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => decide (b.busId = busId)) ∘
        (fun b => b.substF σ)) bi = decide (bi.busId = busId)))]
    rw [List.map_map]
    exact List.map_congr_left (fun bi hbi =>
      hB bi (List.mem_of_mem_filter hbi))
  -- side-effect equality under expression-wise agreement
  have hside : ∀ (env env' : String → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.substF σ).eval env' = bi.eval env) →
      out.sideEffects bsem env' = cs.sideEffects bsem env := by
    intro env env' hB
    show ((cs.busInteractions.map (·.substF σ)).filter
        (fun bi => bsem.isStateful bi.busId)).map _ = _
    rw [List.filter_map]
    rw [List.filter_congr (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => bsem.isStateful b.busId) ∘
        (fun b => b.substF σ)) bi = bsem.isStateful bi.busId))]
    rw [List.map_map]
    exact List.map_congr_left (fun bi hbi => by
      simp only [Function.comp_apply, hB bi (List.mem_of_mem_filter hbi)])
  -- discipline transfer under expression-wise agreement
  have hdisc : ∀ (env env' : String → ZMod p),
      (∀ bi ∈ cs.busInteractions, (bi.substF σ).eval env' = bi.eval env) →
      (out.memoryDiscipline bsem env' ↔ cs.memoryDiscipline bsem env) := by
    intro env env' hB
    unfold ConstraintSystem.memoryDiscipline
    constructor
    · intro h busId shape hdecl
      have := h busId shape hdecl
      rwa [hmsgs env env' hB busId] at this
    · intro h busId shape hdecl
      rw [hmsgs env env' hB busId]
      exact h busId shape hdecl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- out implies cs
    intro env' hsat'
    obtain ⟨env, hA, hB, hdrop⟩ := hbwd env' hsat'
    refine ⟨env, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro c hc
      by_cases hk : keep c = true
      · have hmem : c.substF σ ∈ out.algebraicConstraints :=
          List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hk⟩, rfl⟩)
        have := hsat'.1 _ hmem
        rw [hA c hc] at this
        exact this
      · exact hdrop c hc (by simpa using hk)
    · intro bi hbi
      have hmem : bi.substF σ ∈ out.busInteractions := List.mem_map.2 ⟨bi, hbi, rfl⟩
      have := hsat'.2.1 _ hmem
      rw [hB bi hbi] at this
      exact this
    · exact (hdisc env env' hB).1 hsat'.2.2
    · rw [hside env env' hB]
      exact BusState.equiv_refl _
  · -- cs implies out
    intro env hsat
    obtain ⟨env', hA, hB, hnew⟩ := hfwd env hsat
    refine ⟨env', ⟨?_, ?_, ?_⟩, ?_⟩
    · intro c hc
      rcases List.mem_append.1 hc with h | h
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
        rw [hA c0 (List.mem_of_mem_filter hc0)]
        exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hnew c h
    · intro bi hbi
      obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      rw [hB bi0 hbi0]
      exact hsat.2.1 bi0 hbi0
    · exact (hdisc env env' hB).2 hsat.2.2
    · rw [hside env env' hB]
      exact BusState.equiv_refl _
  · -- invariant preservation
    intro hinv env' hsat' bi' hbi'
    obtain ⟨env, hA, hB, hdrop⟩ := hbwd env' hsat'
    have hsatcs : cs.satisfies bsem env := by
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        by_cases hk : keep c = true
        · have hmem : c.substF σ ∈ out.algebraicConstraints :=
            List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hk⟩, rfl⟩)
          have := hsat'.1 _ hmem
          rw [hA c hc] at this
          exact this
        · exact hdrop c hc (by simpa using hk)
      · intro bi hbi
        have hmem : bi.substF σ ∈ out.busInteractions := List.mem_map.2 ⟨bi, hbi, rfl⟩
        have := hsat'.2.1 _ hmem
        rw [hB bi hbi] at this
        exact this
      · exact (hdisc env env' hB).1 hsat'.2.2
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    rw [hB bi0 hbi0]
    exact hinv env hsatcs bi0 hbi0

/-! ## Structure of enumerated assignments -/

/-- Every enumerated assignment has the domains' keys, in order. -/
theorem assignments_keys (doms : List (String × List (ZMod p)))
    (a : List (String × ZMod p)) (h : a ∈ assignments doms) :
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
theorem envOf_mem_of_assignments (doms : List (String × List (ZMod p)))
    (hnd : (doms.map Prod.fst).Nodup) (a : List (String × ZMod p))
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
theorem envOf_zipimg (xs : List String) (g : String → ZMod p) (y : String) (hy : y ∈ xs) :
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
theorem envF_eq_varSubst (σ : String → Option (Expression p)) (env : String → ZMod p)
    (y : String) : envF σ env y = ((Expression.var y).substF σ).eval env := by
  show (match σ y with | some t => t.eval env | none => env y)
    = ((match σ y with | some t => t | none => .var y) : Expression p).eval env
  cases σ y <;> rfl

/-- Expression-level agreement from pointwise environment agreement. -/
theorem substF_eval_agree (σ : String → Option (Expression p)) (env₀ env₁ : String → ZMod p)
    (e : Expression p) (h : ∀ y ∈ e.vars, envF σ env₀ y = env₁ y) :
    (e.substF σ).eval env₀ = e.eval env₁ := by
  rw [Expression.eval_substF]
  exact Expression.eval_congr e _ _ h

/-- Bus-interaction-level agreement from pointwise environment agreement over its vars. -/
theorem substF_bi_agree (σ : String → Option (Expression p)) (env₀ env₁ : String → ZMod p)
    (bi : BusInteraction (Expression p)) (h : ∀ y ∈ bi.vars, envF σ env₀ y = env₁ y) :
    (bi.substF σ).eval env₀ = bi.eval env₁ := by
  rw [BusInteraction.eval_substF]
  exact BusInteraction.eval_congr bi _ _ h

/-! ## Booleanity constraints for the fresh bits -/

/-- `b · (b − 1)`. -/
def boolConstraint (b : String) : Expression p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

theorem boolConstraint_eval_of_bool (b : String) (env : String → ZMod p)
    (h : env b = 0 ∨ env b = 1) : (boolConstraint b).eval env = 0 := by
  show env b * (env b + (-1)) = 0
  rcases h with h | h <;> rw [h] <;> ring

theorem bool_of_boolConstraint_eval [Fact p.Prime] (b : String) (env : String → ZMod p)
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

/-- Do all the expression's variables lie in `xs`? (No allocation.) -/
def Expression.varsIn (xs : List String) : Expression p → Bool
  | .const _ => true
  | .var y => xs.contains y
  | .add a b => a.varsIn xs && b.varsIn xs
  | .mul a b => a.varsIn xs && b.varsIn xs

theorem Expression.varsIn_sound (xs : List String) (e : Expression p)
    (h : e.varsIn xs = true) : ∀ v ∈ e.vars, v ∈ xs := by
  induction e with
  | const n => simp [Expression.vars]
  | var y =>
      intro v hv
      simp only [Expression.vars, List.mem_singleton] at hv
      subst hv
      exact List.contains_iff_mem.mp (by simpa [Expression.varsIn] using h)
  | add a b iha ihb =>
      rw [Expression.varsIn, Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv
  | mul a b iha ihb =>
      rw [Expression.varsIn, Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv

/-- Constraints whose (nonempty) variable set lies inside the group. -/
def coveredBy (xs : List String) (c : Expression p) : Bool :=
  c.hasVar && c.varsIn xs

/-- Domains for the group's variables, from the covered constraints only. -/
def groupDoms (es : List (Expression p)) : List String → Option (List (String × List (ZMod p)))
  | [] => some []
  | x :: rest =>
    match findDomainAlg es x, groupDoms es rest with
    | some d, some ds => some ((x, d) :: ds)
    | _, _ => none

theorem groupDoms_fst (es : List (Expression p)) (xs : List String)
    (doms : List (String × List (ZMod p))) (h : groupDoms es xs = some doms) :
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

theorem groupDoms_sound [Fact p.Prime] (es : List (Expression p)) (xs : List String)
    (doms : List (String × List (ZMod p))) (h : groupDoms es xs = some doms)
    (env : String → ZMod p) (hall : ∀ c ∈ es, c.eval env = 0) :
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
def groupSubst (xs : List String) (hm : Std.HashMap String (Expression p)) :
    String → Option (Expression p) :=
  fun y => if xs.contains y then hm[y]? else none

/-- The re-encoded system: substitute the group everywhere, keep only uncovered constraints,
    add booleanity for the bits. -/
def reencodeOut (cs : ConstraintSystem p) (xs bits : List String)
    (hm : Std.HashMap String (Expression p)) : ConstraintSystem p :=
  { algebraicConstraints :=
      ((cs.algebraicConstraints.filter (fun c => !coveredBy xs c)).map
        (·.substF (groupSubst xs hm))) ++ bits.map boolConstraint,
    busInteractions := cs.busInteractions.map (·.substF (groupSubst xs hm)) }

/-- The group's covered constraints. -/
def coveredCsOf (cs : ConstraintSystem p) (xs : List String) : List (Expression p) :=
  cs.algebraicConstraints.filter (coveredBy xs)

/-- The surviving group values: enumerated over the group's domains, filtered by the covered
    constraints. -/
def groupSurvivors (cs : ConstraintSystem p) (xs : List String)
    (doms : List (String × List (ZMod p))) : List (List (String × ZMod p)) :=
  (assignments doms).filter
    (fun a => (coveredCsOf cs xs).all (fun c => decide (c.eval (envOf a) = 0)))

/-- The `{0,1}` domain box of the fresh bits. -/
def bitBox (bits : List String) : List (String × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-- All checked side conditions for one re-encoding step. -/
def checkReencode (cs : ConstraintSystem p) (xs bits : List String)
    (hm : Std.HashMap String (Expression p)) : Bool :=
  match groupDoms (coveredCsOf cs xs) xs with
  | none => false
  | some doms =>
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ (groupSurvivors cs xs doms).length) &&
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
    (groupSurvivors cs xs doms).all (fun s => (assignments (bitBox bits)).any (fun aβ =>
      xs.all (fun x =>
        decide (((Expression.var x).substF (groupSubst xs hm)).eval (envOf aβ) = envOf s x)))) &&
    -- soundness: every bit pattern's image satisfies the covered constraints
    (assignments (bitBox bits)).all (fun aβ => (coveredCsOf cs xs).all (fun c =>
      decide ((c.substF (groupSubst xs hm)).eval (envOf aβ) = 0)))

theorem checkReencode_sound [Fact p.Prime] (cs : ConstraintSystem p) (bsem : BusSemantics p)
    (xs bits : List String) (hm : Std.HashMap String (Expression p))
    (hchk : checkReencode cs xs bits hm = true) :
    PassCorrect cs (reencodeOut cs xs bits hm) bsem := by
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
  -- FORWARD
  have hfwd : ∀ env, cs.satisfies bsem env → ∃ env',
      (∀ c ∈ cs.algebraicConstraints,
        (c.substF (groupSubst xs hm)).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions,
        (bi.substF (groupSubst xs hm)).eval env' = bi.eval env) ∧
      (∀ c ∈ bits.map boolConstraint, c.eval env' = 0) := by
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
    obtain ⟨aβ, haβ, hβval⟩ := List.any_eq_true.1 (List.all_eq_true.mp hC5 _ hasurv)
    have hkeysβ : aβ.map Prod.fst = bits := by
      rw [assignments_keys (bitBox bits) aβ haβ, hbitKeys]
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
        have hval := List.all_eq_true.mp hβval y hyx
        rw [decide_eq_true_iff] at hval
        rw [hval]
        exact envOf_map doms env y (hkeys ▸ hyx)
      · have hnone : groupSubst xs hm y = none := by
          simp [groupSubst, List.contains_iff_mem, hyx]
        unfold envF
        rw [hnone]
        exact envExt_eq_env_of_notmem aβ env y (hkeysβ ▸ hyb)
    refine ⟨envExt aβ env, ?_, ?_, ?_⟩
    · intro c hc
      apply substF_eval_agree
      intro y hy
      apply hpoint
      intro hyb
      exact hfreshC y hyb c hc hy
    · intro bi hbi
      apply substF_bi_agree
      intro y hy
      apply hpoint
      intro hyb
      exact hfreshBi y hyb bi hbi hy
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      apply boolConstraint_eval_of_bool
      have hbk : b ∈ aβ.map Prod.fst := hkeysβ ▸ hb
      rw [envExt_eq_envOf_of_mem aβ env b hbk]
      have hmem := envOf_mem_of_assignments (bitBox bits)
        (by rw [hbitKeys]; exact hnodup') aβ haβ
        (b, ([0, 1] : List (ZMod p))) (List.mem_map.2 ⟨b, hb, rfl⟩)
      simpa using hmem
  -- BACKWARD
  have hbwd : ∀ env',
      (ConstraintSystem.satisfies
        { algebraicConstraints :=
            ((cs.algebraicConstraints.filter (fun c => !coveredBy xs c)).map
              (·.substF (groupSubst xs hm))) ++ bits.map boolConstraint,
          busInteractions := cs.busInteractions.map (·.substF (groupSubst xs hm)) }
        bsem env') → ∃ env,
      (∀ c ∈ cs.algebraicConstraints,
        (c.substF (groupSubst xs hm)).eval env' = c.eval env) ∧
      (∀ bi ∈ cs.busInteractions,
        (bi.substF (groupSubst xs hm)).eval env' = bi.eval env) ∧
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
          simp [groupSubst, List.contains_iff_mem, hyx]
        unfold envF
        rw [hnone, henv]
        rw [envExt_eq_env_of_notmem _ env' y (by rw [hkeysP]; exact hyx)]
    have hexpr : ∀ e : Expression p,
        (e.substF (groupSubst xs hm)).eval env' = e.eval env :=
      fun e => substF_eval_agree _ _ _ e (fun y _ => hpoint y)
    refine ⟨env, fun c _ => hexpr c, ?_, ?_⟩
    · intro bi _
      exact substF_bi_agree _ _ _ bi (fun y _ => hpoint y)
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
  show PassCorrect cs (reencodeOut cs xs bits hm) bsem
  unfold reencodeOut
  exact cs.reencode_correct bsem (groupSubst xs hm) (fun c => !coveredBy xs c)
    (bits.map boolConstraint) hfwd hbwd

/-! ## Building the interpolation (proof-free) and the pass -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. -/
def indicatorExpr (aβ : List (String × ZMod p)) : Expression p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs. -/
def interpPoly (pz : List (List (String × ZMod p) × List (String × ZMod p))) (x : String) :
    Expression p :=
  pz.foldl (fun acc az => .add acc (.mul (indicatorExpr az.1) (.const (envOf az.2 x))))
    (.const 0)

/-- Construct the bits and the substitution map for a candidate group (proof-free — the
    checked certificate re-verifies everything). -/
def buildReencode (cs : ConstraintSystem p) (xs : List String) (freshBase : String) :
    Option (List String × Std.HashMap String (Expression p)) :=
  match groupDoms (coveredCsOf cs xs) xs with
  | none => none
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survs := groupSurvivors cs xs doms
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let bits := (List.range k).map (fun j => freshBase ++ "_" ++ toString j)
          let patts := assignments (bitBox (p := p) bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (interpPoly pz x).fold))))
        else none
      else none
    else none

/-- One checked re-encoding step (identity if construction or certificate fails). -/
def reencodeStep [Fact p.Prime] (bsem : BusSemantics p) (cs : ConstraintSystem p)
    (xs : List String) (freshBase : String) :
    { out : ConstraintSystem p // PassCorrect cs out bsem } :=
  match buildReencode cs xs freshBase with
  | none => ⟨cs, cs.equivalentTo_refl bsem, _root_.id⟩
  | some (bits, hm) =>
    if hchk : checkReencode cs xs bits hm = true then
      ⟨reencodeOut cs xs bits hm, checkReencode_sound cs bsem xs bits hm hchk⟩
    else ⟨cs, cs.equivalentTo_refl bsem, _root_.id⟩

/-- Process the candidate groups sequentially (correctness composes by transitivity). -/
def reencodeLoop [Fact p.Prime] (bsem : BusSemantics p) :
    List (List String) → Nat → (cs : ConstraintSystem p) →
    { out : ConstraintSystem p // PassCorrect cs out bsem }
  | [], _, cs => ⟨cs, cs.equivalentTo_refl bsem, _root_.id⟩
  | xs :: rest, idx, cs =>
    let r1 := reencodeStep bsem cs xs
      (s!"rnc{cs.algebraicConstraints.length}_{cs.busInteractions.length}_{idx}")
    let r2 := reencodeLoop bsem rest (idx + 1) r1.val
    ⟨r2.val,
     ConstraintSystem.equivalentTo_trans r2.property.1 r1.property.1,
     fun h => r2.property.2 (r1.property.2 h)⟩

/-- The witness re-encoding pass: for every constraint's (small) variable group whose covered
    constraints allow only a few joint values, re-encode the group with `⌈log₂ m⌉` fresh booleans.
    Prime `p` only (booleanity needs an integral domain); identity otherwise. -/
def reencodePass : VerifiedPass p := fun cs bsem =>
  if hpr : p.Prime then
    haveI : Fact p.Prime := ⟨hpr⟩
    let targets := (cs.algebraicConstraints.filterMap (fun c =>
      let vs := c.vars.dedup
      if 2 ≤ vs.length && vs.length ≤ 8 then some (vs.mergeSort (· ≤ ·)) else none)).dedup
    reencodeLoop bsem targets 0 cs
  else ⟨cs, cs.equivalentTo_refl bsem, _root_.id⟩
