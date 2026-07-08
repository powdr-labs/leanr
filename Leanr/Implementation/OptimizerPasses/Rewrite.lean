import Leanr.Implementation.OptimizerPasses.Basic

set_option autoImplicit false

/-! # Generic equivalence-preserving rewrites

Two reusable, proof-carrying building blocks that (unlike substitution) keep the environment
fixed:

* `ConstraintSystem.mapExpr` — apply an **eval-preserving** expression transform `g`
  (`∀ e env, (g e).eval env = e.eval env`) to every expression in the system. Any such `g` yields
  an equivalent system (`ConstraintSystem.mapExpr_correct`). This is the foundation for constant
  folding / algebraic simplification: those rewrites never change what an expression evaluates to,
  so they are automatically correct.

* `ConstraintSystem.filterConstraints` — drop algebraic constraints selected by a predicate,
  provided the dropped ones are *identically zero* (`ConstraintSystem.filterConstraints_correct`).
  This removes trivially-true constraints (e.g. `0 = 0`) left behind by simplification.

No field/primality assumptions are used. -/

variable {p : ℕ}

/-! ## Eval-preserving expression maps -/

/-- Apply `g` to every expression of a bus interaction. -/
def BusInteraction.mapExpr (bi : BusInteraction (Expression p)) (g : Expression p → Expression p) :
    BusInteraction (Expression p) :=
  { busId := bi.busId, multiplicity := g bi.multiplicity, payload := bi.payload.map g }

/-- Apply `g` to every expression of a constraint system (all algebraic constraints, and each bus
    interaction's multiplicity and payload). -/
def ConstraintSystem.mapExpr (cs : ConstraintSystem p) (g : Expression p → Expression p) :
    ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints.map g,
    busInteractions := cs.busInteractions.map (·.mapExpr g) }

/-- If `g` introduces no new variables per expression, the rewritten system introduces none. -/
theorem ConstraintSystem.mapExpr_vars_subset (cs : ConstraintSystem p)
    {g : Expression p → Expression p}
    (hgv : ∀ (e : Expression p) (x : Variable), x ∈ (g e).vars → x ∈ e.vars) :
    ∀ x ∈ (cs.mapExpr g).vars, x ∈ cs.vars := by
  intro x hx
  rw [ConstraintSystem.mem_vars] at hx
  rcases hx with ⟨c, hc, hxc⟩ | ⟨bi, hbi, hxbi⟩
  · simp only [ConstraintSystem.mapExpr, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    exact ConstraintSystem.mem_vars_of_constraint hc0 (hgv c0 x hxc)
  · simp only [ConstraintSystem.mapExpr, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    rcases hxbi with hm | ⟨e, he, hxe⟩
    · simp only [BusInteraction.mapExpr] at hm
      exact ConstraintSystem.mem_vars_of_mult hbi0 (hgv bi0.multiplicity x hm)
    · simp only [BusInteraction.mapExpr, List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      exact ConstraintSystem.mem_vars_of_payload hbi0 he0 (hgv e0 x hxe)

section EvalPreserving
variable {g : Expression p → Expression p} (hg : ∀ e (env : Variable → ZMod p), (g e).eval env = e.eval env)

include hg

theorem BusInteraction.eval_mapExpr (bi : BusInteraction (Expression p)) (env : Variable → ZMod p) :
    (bi.mapExpr g).eval env = bi.eval env := by
  simp only [BusInteraction.mapExpr, BusInteraction.eval, hg, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, hg]

/-- The evaluated interactions of a rewritten system, restricted to one bus, are unchanged
    (an eval-preserving map never changes a bus id or a value). -/
theorem ConstraintSystem.msgs_mapExpr (cs : ConstraintSystem p) (busId : Nat)
    (env : Variable → ZMod p) :
    ((cs.mapExpr g).busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => bi.eval env)
    = (cs.busInteractions.filter (fun bi => bi.busId = busId)).map (fun bi => bi.eval env) := by
  simp only [ConstraintSystem.mapExpr]
  rw [List.filter_map]
  rw [List.filter_congr
    (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => decide (b.busId = busId)) ∘
        (fun b => b.mapExpr g)) bi = decide (bi.busId = busId)))]
  rw [List.map_map]
  exact List.map_congr_left (fun bi _ => bi.eval_mapExpr hg env)

/-- `admissible` is untouched by eval-preserving rewrites — generically in the VM predicate. -/
theorem ConstraintSystem.admissible_mapExpr (cs : ConstraintSystem p)
    (bs : BusSemantics p) (env : Variable → ZMod p) :
    (cs.mapExpr g).admissible bs env ↔ cs.admissible bs env := by
  unfold ConstraintSystem.admissible
  have hmap : (cs.mapExpr g).busInteractions.map (fun bi => bi.eval env)
      = cs.busInteractions.map (fun bi => bi.eval env) := by
    simp only [ConstraintSystem.mapExpr, List.map_map]
    exact List.map_congr_left (fun bi _ => bi.eval_mapExpr hg env)
  rw [hmap]

theorem ConstraintSystem.satisfies_mapExpr (cs : ConstraintSystem p) (bs : BusSemantics p)
    (env : Variable → ZMod p) : (cs.mapExpr g).satisfies bs env ↔ cs.satisfies bs env := by
  simp only [ConstraintSystem.satisfies, ConstraintSystem.mapExpr] at *
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c0 hc0 => ?_, fun bi0 hbi0 => ?_⟩
    · have := hc _ (List.mem_map.2 ⟨c0, hc0, rfl⟩); rwa [hg] at this
    · have := hb _ (List.mem_map.2 ⟨bi0, hbi0, rfl⟩); rwa [bi0.eval_mapExpr hg] at this
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hc' => ?_, fun bi hbi' => ?_⟩
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'; rw [hg]; exact hc c0 hc0
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'; rw [bi0.eval_mapExpr hg]; exact hb bi0 hbi0

theorem ConstraintSystem.sideEffects_mapExpr (cs : ConstraintSystem p) (bs : BusSemantics p)
    (env : Variable → ZMod p) : (cs.mapExpr g).sideEffects bs env = cs.sideEffects bs env := by
  simp only [ConstraintSystem.sideEffects, ConstraintSystem.mapExpr]
  induction cs.busInteractions with
  | nil => rfl
  | cons bi rest ih =>
      simp only [List.map_cons, List.filter_cons]
      have hbus : bs.isStateful (bi.mapExpr g).busId = bs.isStateful bi.busId := rfl
      rw [hbus]
      by_cases hstate : bs.isStateful bi.busId = true
      · simp only [if_pos hstate, List.map_cons, ih, bi.eval_mapExpr hg]
      · simp only [if_neg hstate, ih]

/-- **Correctness of eval-preserving maps.** If `g` never changes what an expression evaluates to
    (`hg`) and introduces no new variables (`hgv`), then rewriting every expression with `g` yields
    an equivalent, invariant-preserving system. -/
theorem ConstraintSystem.mapExpr_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (hgv : ∀ (e : Expression p) (x : Variable), x ∈ (g e).vars → x ∈ e.vars) :
    PassCorrect cs (cs.mapExpr g) [] [] bs := by
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.mapExpr_vars_subset hgv) ?_
  · intro env hsat
    refine ⟨env, (cs.satisfies_mapExpr hg bs env).1 hsat, ?_⟩
    rw [cs.sideEffects_mapExpr hg]; exact BusState.equiv_refl _
  · intro hinv env hsat bi hbi
    have hsatcs : cs.satisfies bs env := (cs.satisfies_mapExpr hg bs env).1 hsat
    simp only [ConstraintSystem.mapExpr, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    simp only [bi0.eval_mapExpr hg]
    exact hinv env hsatcs bi0 hbi0
  · intro env hadm hsat
    refine ⟨(cs.satisfies_mapExpr hg bs env).2 hsat, (cs.admissible_mapExpr hg bs env).2 hadm, ?_⟩
    rw [cs.sideEffects_mapExpr hg]; exact BusState.equiv_refl _

end EvalPreserving

/-! ## Removing identically-zero constraints -/

/-- Keep only the algebraic constraints satisfying `keep`; bus interactions are untouched. -/
def ConstraintSystem.filterConstraints (cs : ConstraintSystem p) (keep : Expression p → Bool) :
    ConstraintSystem p :=
  { cs with algebraicConstraints := cs.algebraicConstraints.filter keep }

theorem ConstraintSystem.filterConstraints_vars_subset (cs : ConstraintSystem p)
    (keep : Expression p → Bool) : ∀ x ∈ (cs.filterConstraints keep).vars, x ∈ cs.vars := by
  intro x hx
  rw [ConstraintSystem.mem_vars] at hx ⊢
  rcases hx with ⟨c, hc, hxc⟩ | ⟨bi, hbi, hxbi⟩
  · exact Or.inl ⟨c, List.mem_of_mem_filter hc, hxc⟩
  · exact Or.inr ⟨bi, hbi, hxbi⟩

/-- **Correctness of trivial-constraint removal.** Dropping algebraic constraints is equivalence-
    preserving as long as every dropped constraint is identically zero (hence vacuously true). -/
theorem ConstraintSystem.filterConstraints_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (keep : Expression p → Bool)
    (h : ∀ c ∈ cs.algebraicConstraints, keep c = false → ∀ env, c.eval env = 0) :
    PassCorrect cs (cs.filterConstraints keep) [] [] bs := by
  have hiff : ∀ env, (cs.filterConstraints keep).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    simp only [ConstraintSystem.satisfies, ConstraintSystem.filterConstraints]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨fun c hcmem => ?_, hb⟩
      by_cases hk : keep c = true
      · exact hc c (List.mem_filter.2 ⟨hcmem, hk⟩)
      · exact h c hcmem (by simpa using hk) env
    · rintro ⟨hc, hb⟩
      exact ⟨fun c hcmem => hc c (List.mem_filter.1 hcmem).1, hb⟩
  have hside : ∀ env, (cs.filterConstraints keep).sideEffects bs env = cs.sideEffects bs env :=
    fun _ => rfl
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.filterConstraints_vars_subset keep) ?_
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    exact hinv env ((hiff env).1 hsat) bi hbi
  · intro env hadm hsat
    exact ⟨(hiff env).2 hsat, hadm, by rw [hside]; exact BusState.equiv_refl _⟩

/-! ## Removing zero-multiplicity bus interactions -/

/-- Keep only the bus interactions satisfying `keep`; algebraic constraints untouched. -/
def ConstraintSystem.filterBus (cs : ConstraintSystem p) (keep : BusInteraction (Expression p) → Bool) :
    ConstraintSystem p :=
  { cs with busInteractions := cs.busInteractions.filter keep }

theorem ConstraintSystem.filterBus_vars_subset (cs : ConstraintSystem p)
    (keep : BusInteraction (Expression p) → Bool) :
    ∀ x ∈ (cs.filterBus keep).vars, x ∈ cs.vars := by
  intro x hx
  rw [ConstraintSystem.mem_vars] at hx ⊢
  rcases hx with ⟨c, hc, hxc⟩ | ⟨bi, hbi, hxbi⟩
  · exact Or.inl ⟨c, hc, hxc⟩
  · exact Or.inr ⟨bi, List.mem_of_mem_filter hbi, hxbi⟩

/-- Dropping interactions that are (under `a`) either inactive (multiplicity `0`) or on a
    stateless bus preserves `admissible` — generically in the VM predicate. `ConstraintSystem.admissible`
    only looks at the active *stateful* evaluated messages, which such a drop leaves unchanged.
    Covers both zero-multiplicity removal (`ZeroMultBus`) and stateless-lookup removal (`TautoBus`). -/
theorem ConstraintSystem.admissible_filterBus (cs : ConstraintSystem p)
    (bs : BusSemantics p) (keep : BusInteraction (Expression p) → Bool) (a : Variable → ZMod p)
    (h : ∀ bi ∈ cs.busInteractions, keep bi = false →
        (bi.eval a).multiplicity = 0 ∨ bs.isStateful bi.busId = false) :
    (cs.filterBus keep).admissible bs a ↔ cs.admissible bs a := by
  unfold ConstraintSystem.admissible
  simp only [ConstraintSystem.filterBus]
  -- the active∧stateful evaluated message list is the same before and after the drop
  have key : ∀ (L : List (BusInteraction (Expression p))),
      (∀ bi ∈ L, keep bi = false →
        (bi.eval a).multiplicity = 0 ∨ bs.isStateful bi.busId = false) →
      ((L.filter keep).map (fun bi => bi.eval a)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
        = (L.map (fun bi => bi.eval a)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons bi rest ih =>
      intro hL
      have hrest := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
      by_cases hk : keep bi = true
      · rw [List.filter_cons_of_pos hk]
        simp only [List.map_cons, List.filter_cons, hrest]
      · have hbusId : (bi.eval a).busId = bi.busId := rfl
        have hPfalse : (decide ((bi.eval a).multiplicity ≠ 0) && bs.isStateful (bi.eval a).busId)
            = false := by
          rcases hL bi (List.mem_cons_self ..) (by simpa using hk) with hz | hst
          · simp [hz]
          · rw [hbusId, hst, Bool.and_false]
        rw [List.filter_cons_of_neg (by simpa using hk), List.map_cons]
        simp only [List.filter_cons, hPfalse, Bool.false_eq_true, if_false]
        exact hrest
  rw [key cs.busInteractions h]

/-- Net multiplicity is unchanged by dropping (via `keep = false`) bus interactions whose evaluated
    multiplicity is `0`: such an interaction contributes `0` to every message's net multiplicity, so
    the two bus states are `≈`-equal. -/
theorem multiplicitySum_filterBus (bs : BusSemantics p) (env : Variable → ZMod p)
    (keep : BusInteraction (Expression p) → Bool) (message : BusMessage p)
    (bis : List (BusInteraction (Expression p)))
    (h0 : ∀ bi ∈ bis, keep bi = false → (bi.eval env).multiplicity = 0) :
    multiplicitySum message
      ((bis.filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity)))
    = multiplicitySum message
      (((bis.filter keep).filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity))) := by
  induction bis with
  | nil => rfl
  | cons bi rest ih =>
      have hrest : ∀ b ∈ rest, keep b = false → (b.eval env).multiplicity = 0 :=
        fun b hb => h0 b (List.mem_cons_of_mem _ hb)
      by_cases hkeep : keep bi = true
      · by_cases hstate : bs.isStateful bi.busId = true
        · rw [List.filter_cons_of_pos (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_pos hkeep,
              List.filter_cons_of_pos (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate]
          simp only [List.map_cons, multiplicitySum, ih hrest]
        · rw [List.filter_cons_of_neg (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_pos hkeep,
              List.filter_cons_of_neg (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate]
          exact ih hrest
      · have hbi0 : (bi.eval env).multiplicity = 0 :=
          h0 bi (List.mem_cons_self ..) (by simpa using hkeep)
        by_cases hstate : bs.isStateful bi.busId = true
        · rw [List.filter_cons_of_pos (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_neg hkeep]
          simp only [List.map_cons, multiplicitySum, hbi0, ite_self, zero_add]
          exact ih hrest
        · rw [List.filter_cons_of_neg (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate,
              List.filter_cons_of_neg hkeep]
          exact ih hrest

/-- **Correctness of zero-multiplicity bus removal.** Dropping bus interactions whose multiplicity
    is identically `0` is equivalence- and invariant-preserving: their `violatesConstraint`
    obligation is vacuous (multiplicity `≠ 0` is false), and a `0`-multiplicity stateful entry adds
    `0` to every net multiplicity. Unlike cancelling opposite-sign pairs, this drops no real
    obligation, so it is sound for *arbitrary* bus semantics. -/
theorem ConstraintSystem.filterBus_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (keep : BusInteraction (Expression p) → Bool) (_hp1 : (1 : ZMod p) ≠ 0)
    (h : ∀ bi ∈ cs.busInteractions, keep bi = false → ∀ env, (bi.eval env).multiplicity = 0) :
    PassCorrect cs (cs.filterBus keep) [] [] bs := by
  have hiff : ∀ env, (cs.filterBus keep).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    simp only [ConstraintSystem.satisfies]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨hc, fun bi hbimem => ?_⟩
      by_cases hk : keep bi = true
      · exact hb bi (List.mem_filter.2 ⟨hbimem, hk⟩)
      · intro hne; exact absurd (h bi hbimem (by simpa using hk) env) hne
    · rintro ⟨hc, hb⟩
      exact ⟨hc, fun bi hbimem => hb bi (List.mem_filter.1 hbimem).1⟩
  have hside : ∀ env, cs.sideEffects bs env ≈ (cs.filterBus keep).sideEffects bs env := by
    intro env message
    simp only [ConstraintSystem.sideEffects, ConstraintSystem.filterBus]
    exact multiplicitySum_filterBus bs env keep message cs.busInteractions
      (fun bi hbi hkf => h bi hbi hkf env)
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.filterBus_vars_subset keep) ?_
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, BusState.equiv_symm (hside env)⟩
  · intro hinv env hsat bi hbi
    have hbimem : bi ∈ cs.busInteractions :=
      (List.mem_filter.1 (by simpa only [ConstraintSystem.filterBus] using hbi)).1
    exact hinv env ((hiff env).1 hsat) bi hbimem
  · intro env hadm hsat
    exact ⟨(hiff env).2 hsat,
      (cs.admissible_filterBus bs keep env (fun bi hbi hkf => Or.inl (h bi hbi hkf env))).2 hadm,
      hside env⟩
