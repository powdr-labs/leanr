import Leanr.OptimizerPasses.Basic

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

section EvalPreserving
variable {g : Expression p → Expression p} (hg : ∀ e (env : String → ZMod p), (g e).eval env = e.eval env)

include hg

theorem BusInteraction.eval_mapExpr (bi : BusInteraction (Expression p)) (env : String → ZMod p) :
    (bi.mapExpr g).eval env = bi.eval env := by
  simp only [BusInteraction.mapExpr, BusInteraction.eval, hg, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, hg]

theorem ConstraintSystem.satisfies_mapExpr (cs : ConstraintSystem p) (bs : BusSemantics p)
    (env : String → ZMod p) : (cs.mapExpr g).satisfies bs env ↔ cs.satisfies bs env := by
  simp only [ConstraintSystem.satisfies, ConstraintSystem.mapExpr]
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
    (env : String → ZMod p) : (cs.mapExpr g).sideEffects bs env = cs.sideEffects bs env := by
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

/-- **Correctness of eval-preserving maps.** If `g` never changes what an expression evaluates to,
    then rewriting every expression with `g` yields an equivalent, invariant-preserving system. -/
theorem ConstraintSystem.mapExpr_correct (cs : ConstraintSystem p) (bs : BusSemantics p) :
    PassCorrect cs (cs.mapExpr g) bs := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro env hsat
    refine ⟨env, (cs.satisfies_mapExpr hg bs env).1 hsat, ?_⟩
    rw [cs.sideEffects_mapExpr hg]; exact BusState.equiv_refl _
  · intro env hsat
    refine ⟨env, (cs.satisfies_mapExpr hg bs env).2 hsat, ?_⟩
    rw [cs.sideEffects_mapExpr hg]; exact BusState.equiv_refl _
  · intro hinv env hsat bi hbi
    have hsatcs : cs.satisfies bs env := (cs.satisfies_mapExpr hg bs env).1 hsat
    simp only [ConstraintSystem.mapExpr, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    simp only [bi0.eval_mapExpr hg]
    exact hinv env hsatcs bi0 hbi0

end EvalPreserving

/-! ## Removing identically-zero constraints -/

/-- Keep only the algebraic constraints satisfying `keep`; bus interactions are untouched. -/
def ConstraintSystem.filterConstraints (cs : ConstraintSystem p) (keep : Expression p → Bool) :
    ConstraintSystem p :=
  { cs with algebraicConstraints := cs.algebraicConstraints.filter keep }

/-- **Correctness of trivial-constraint removal.** Dropping algebraic constraints is equivalence-
    preserving as long as every dropped constraint is identically zero (hence vacuously true). -/
theorem ConstraintSystem.filterConstraints_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (keep : Expression p → Bool)
    (h : ∀ c ∈ cs.algebraicConstraints, keep c = false → ∀ env, c.eval env = 0) :
    PassCorrect cs (cs.filterConstraints keep) bs := by
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
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro env hsat
    exact ⟨env, (hiff env).2 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    exact hinv env ((hiff env).1 hsat) bi hbi

/-! ## Removing zero-multiplicity bus interactions -/

/-- Keep only the bus interactions satisfying `keep`; algebraic constraints untouched. -/
def ConstraintSystem.filterBus (cs : ConstraintSystem p) (keep : BusInteraction (Expression p) → Bool) :
    ConstraintSystem p :=
  { cs with busInteractions := cs.busInteractions.filter keep }

/-- Net multiplicity is unchanged by dropping (via `keep = false`) bus interactions whose evaluated
    multiplicity is `0`: such an interaction contributes `0` to every message's net multiplicity, so
    the two bus states are `≈`-equal. -/
theorem multiplicitySum_filterBus (bs : BusSemantics p) (env : String → ZMod p)
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
    (keep : BusInteraction (Expression p) → Bool)
    (h : ∀ bi ∈ cs.busInteractions, keep bi = false → ∀ env, (bi.eval env).multiplicity = 0) :
    PassCorrect cs (cs.filterBus keep) bs := by
  have hiff : ∀ env, (cs.filterBus keep).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    simp only [ConstraintSystem.satisfies, ConstraintSystem.filterBus]
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
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, BusState.equiv_symm (hside env)⟩
  · intro env hsat
    exact ⟨env, (hiff env).2 hsat, hside env⟩
  · intro hinv env hsat bi hbi
    have hbimem : bi ∈ cs.busInteractions :=
      (List.mem_filter.1 (by simpa only [ConstraintSystem.filterBus] using hbi)).1
    exact hinv env ((hiff env).1 hsat) bi hbimem
