import Leanr.OptimizerPasses.Basic

set_option autoImplicit false

/-! # Simultaneous substitution: the batch counterpart of `Subst.lean`

`Subst.lean` eliminates one variable per system rewrite; on parsed machines with hundreds of
solvable variables that costs one full-system traversal *per variable*. This file provides the
batch core: substitute a whole *map* of solved variables in a single traversal.

The map is any function `f : String → Option (Expression p)` (passes use a `Std.HashMap`
lookup); `x` with `f x = some t` is replaced by `t`. Semantics are stated against the rebound
environment `envF f env` (each mapped variable rebound to its solution's value), exactly like
`Function.update` in the single-variable case. The correctness theorem
`ConstraintSystem.substF_correct` needs every mapped pair to be entailed: satisfying
assignments must force `env x = t.eval env` for all `f x = some t`.

Unlike sequential single substitutions, one `substF` application does **not** re-substitute
inside inserted solutions — so passes must supply a *resolved* map (no mapped variable occurs
in any solution) for full elimination. Resolvedness is a quality concern only; correctness
holds for any entailed map. Purely equational — no field assumptions. -/

variable {p : ℕ}

/-! ## Substitution on expressions -/

/-- Substitute every variable `x` with `f x = some t` by `t` (one traversal; inserted
    solutions are not re-visited). -/
def Expression.substF (f : String → Option (Expression p)) : Expression p → Expression p
  | .const n => .const n
  | .var y => match f y with | some t => t | none => .var y
  | .add a b => .add (a.substF f) (b.substF f)
  | .mul a b => .mul (a.substF f) (b.substF f)

/-- The environment with every mapped variable rebound to its solution's value. -/
def envF (f : String → Option (Expression p)) (env : String → ZMod p) : String → ZMod p :=
  fun y => match f y with | some t => t.eval env | none => env y

theorem Expression.eval_substF (e : Expression p) (f : String → Option (Expression p))
    (env : String → ZMod p) : (e.substF f).eval env = e.eval (envF f env) := by
  induction e with
  | const n => rfl
  | var y =>
      show (match f y with | some t => t | none => .var y).eval env = envF f env y
      unfold envF
      cases f y <;> rfl
  | add a b iha ihb => simp only [Expression.substF, Expression.eval, iha, ihb]
  | mul a b iha ihb => simp only [Expression.substF, Expression.eval, iha, ihb]

/-- If every mapped pair is respected by `env`, rebinding changes nothing. -/
theorem envF_eq_self (f : String → Option (Expression p)) (env : String → ZMod p)
    (H : ∀ y t, f y = some t → env y = t.eval env) : envF f env = env := by
  funext y
  unfold envF
  cases hy : f y with
  | none => rfl
  | some t => exact (H y t hy).symm

/-! ## Substitution on bus interactions and systems -/

/-- Substitute the map in every expression of a bus interaction. -/
def BusInteraction.substF (bi : BusInteraction (Expression p))
    (f : String → Option (Expression p)) : BusInteraction (Expression p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.substF f,
    payload := bi.payload.map (·.substF f) }

theorem BusInteraction.eval_substF (bi : BusInteraction (Expression p))
    (f : String → Option (Expression p)) (env : String → ZMod p) :
    (bi.substF f).eval env = bi.eval (envF f env) := by
  simp only [BusInteraction.substF, BusInteraction.eval, Expression.eval_substF, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, Expression.eval_substF]

/-- Substitute the map everywhere in a constraint system. -/
def ConstraintSystem.substF (cs : ConstraintSystem p) (f : String → Option (Expression p)) :
    ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints.map (·.substF f),
    busInteractions := cs.busInteractions.map (·.substF f) }

/-- The evaluated interactions of a substituted system, restricted to one bus, are those of
    the original under the rebound environment (substitution never changes a bus id). -/
theorem ConstraintSystem.msgs_substF (cs : ConstraintSystem p)
    (f : String → Option (Expression p)) (busId : Nat) (a : String → ZMod p) :
    ((cs.substF f).busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => bi.eval a)
    = (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => bi.eval (envF f a)) := by
  simp only [ConstraintSystem.substF]
  rw [List.filter_map]
  rw [List.filter_congr
    (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => decide (b.busId = busId)) ∘
        (fun b => b.substF f)) bi = decide (bi.busId = busId)))]
  rw [List.map_map]
  exact List.map_congr_left (fun bi _ => bi.eval_substF f a)

/-- `admissible` transfers across simultaneous substitution — generically in the VM predicate. -/
theorem ConstraintSystem.admissible_substF (cs : ConstraintSystem p)
    (f : String → Option (Expression p)) (bs : BusSemantics p) (a : String → ZMod p) :
    (cs.substF f).admissible bs a ↔ cs.admissible bs (envF f a) := by
  unfold ConstraintSystem.admissible
  have hmap : (cs.substF f).busInteractions.map (fun bi => bi.eval a)
      = cs.busInteractions.map (fun bi => bi.eval (envF f a)) := by
    simp only [ConstraintSystem.substF, List.map_map]
    exact List.map_congr_left (fun bi _ => bi.eval_substF f a)
  rw [hmap]

/-- `satisfies` transfers across simultaneous substitution. -/
theorem ConstraintSystem.satisfies_substF (cs : ConstraintSystem p)
    (f : String → Option (Expression p)) (bs : BusSemantics p) (a : String → ZMod p) :
    (cs.substF f).satisfies bs a ↔ cs.satisfies bs (envF f a) := by
  simp only [ConstraintSystem.satisfies, ConstraintSystem.substF] at *
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c0 hc0 => ?_, fun bi0 hbi0 => ?_⟩
    · have := hc _ (List.mem_map.2 ⟨c0, hc0, rfl⟩)
      rwa [Expression.eval_substF] at this
    · have := hb _ (List.mem_map.2 ⟨bi0, hbi0, rfl⟩)
      rwa [BusInteraction.eval_substF] at this
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hc' => ?_, fun bi hbi' => ?_⟩
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
      rw [Expression.eval_substF]; exact hc c0 hc0
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
      rw [BusInteraction.eval_substF]; exact hb bi0 hbi0

/-- `sideEffects` transfers across simultaneous substitution. -/
theorem ConstraintSystem.sideEffects_substF (cs : ConstraintSystem p)
    (f : String → Option (Expression p)) (bs : BusSemantics p) (a : String → ZMod p) :
    (cs.substF f).sideEffects bs a = cs.sideEffects bs (envF f a) := by
  simp only [ConstraintSystem.sideEffects, ConstraintSystem.substF]
  induction cs.busInteractions with
  | nil => rfl
  | cons bi rest ih =>
      simp only [List.map_cons, List.filter_cons]
      have hbus : bs.isStateful (bi.substF f).busId = bs.isStateful bi.busId := rfl
      rw [hbus]
      by_cases hstate : bs.isStateful bi.busId = true
      · simp only [if_pos hstate, List.map_cons, ih, BusInteraction.eval_substF]
      · simp only [if_neg hstate, ih]

/-- **Simultaneous-substitution correctness.** If every satisfying assignment of `cs` forces
    `x = t` for every mapped pair `f x = some t`, then substituting the whole map at once is
    `PassCorrect`: equivalent to `cs` and invariant-preserving. The batch counterpart of
    `ConstraintSystem.subst_correct`. -/
theorem ConstraintSystem.substF_correct (cs : ConstraintSystem p)
    (f : String → Option (Expression p)) (bs : BusSemantics p)
    (H : ∀ env, cs.satisfies bs env → ∀ y t, f y = some t → env y = t.eval env) :
    PassCorrect cs (cs.substF f) bs := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- soundness: (cs.substF f) implies cs
    intro env hsat
    refine ⟨envF f env, (cs.satisfies_substF f bs env).1 hsat, ?_⟩
    rw [cs.sideEffects_substF]
    exact BusState.equiv_refl _
  · -- completeness: cs intended-implies (cs.substF f)
    intro env hint hsat
    have henv : envF f env = env := envF_eq_self f env (H env hsat)
    refine ⟨env, ?_, ?_, ?_⟩
    · rw [cs.satisfies_substF, henv]; exact hsat
    · rw [cs.admissible_substF, henv]; exact hint
    · rw [cs.sideEffects_substF, henv]; exact BusState.equiv_refl _
  · -- invariant preservation
    intro hinv env hsat bi hbi
    have hsatcs : cs.satisfies bs (envF f env) := (cs.satisfies_substF f bs env).1 hsat
    simp only [ConstraintSystem.substF, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    simp only [bi0.eval_substF f env]
    exact hinv (envF f env) hsatcs bi0 hbi0
