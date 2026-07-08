import Leanr.Implementation.OptimizerPasses.Basic

set_option autoImplicit false

/-! # Simultaneous substitution: the batch counterpart of `Subst.lean`

`Subst.lean` eliminates one variable per system rewrite; on parsed machines with hundreds of
solvable variables that costs one full-system traversal *per variable*. This file provides the
batch core: substitute a whole *map* of solved variables in a single traversal.

The map is any function `f : Variable → Option (Expression p)` (passes use a `Std.HashMap`
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
def Expression.substF (f : Variable → Option (Expression p)) : Expression p → Expression p
  | .const n => .const n
  | .var y => match f y with | some t => t | none => .var y
  | .add a b => .add (a.substF f) (b.substF f)
  | .mul a b => .mul (a.substF f) (b.substF f)

/-- The environment with every mapped variable rebound to its solution's value. -/
def envF (f : Variable → Option (Expression p)) (env : Variable → ZMod p) : Variable → ZMod p :=
  fun y => match f y with | some t => t.eval env | none => env y

theorem Expression.eval_substF (e : Expression p) (f : Variable → Option (Expression p))
    (env : Variable → ZMod p) : (e.substF f).eval env = e.eval (envF f env) := by
  induction e with
  | const n => rfl
  | var y =>
      show (match f y with | some t => t | none => .var y).eval env = envF f env y
      unfold envF
      cases f y <;> rfl
  | add a b iha ihb => simp only [Expression.substF, Expression.eval, iha, ihb]
  | mul a b iha ihb => simp only [Expression.substF, Expression.eval, iha, ihb]

/-- If every mapped pair is respected by `env`, rebinding changes nothing. -/
theorem envF_eq_self (f : Variable → Option (Expression p)) (env : Variable → ZMod p)
    (H : ∀ y t, f y = some t → env y = t.eval env) : envF f env = env := by
  funext y
  unfold envF
  cases hy : f y with
  | none => rfl
  | some t => exact (H y t hy).symm

/-! ## Substitution on bus interactions and systems -/

/-- Substitute the map in every expression of a bus interaction. -/
def BusInteraction.substF (bi : BusInteraction (Expression p))
    (f : Variable → Option (Expression p)) : BusInteraction (Expression p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.substF f,
    payload := bi.payload.map (·.substF f) }

theorem BusInteraction.eval_substF (bi : BusInteraction (Expression p))
    (f : Variable → Option (Expression p)) (env : Variable → ZMod p) :
    (bi.substF f).eval env = bi.eval (envF f env) := by
  simp only [BusInteraction.substF, BusInteraction.eval, Expression.eval_substF, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, Expression.eval_substF]

/-- Substitute the map everywhere in a constraint system. -/
def ConstraintSystem.substF (cs : ConstraintSystem p) (f : Variable → Option (Expression p)) :
    ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints.map (·.substF f),
    busInteractions := cs.busInteractions.map (·.substF f) }

/-- The evaluated interactions of a substituted system, restricted to one bus, are those of
    the original under the rebound environment (substitution never changes a bus id). -/
theorem ConstraintSystem.msgs_substF (cs : ConstraintSystem p)
    (f : Variable → Option (Expression p)) (busId : Nat) (a : Variable → ZMod p) :
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
    (f : Variable → Option (Expression p)) (bs : BusSemantics p) (a : Variable → ZMod p) :
    (cs.substF f).admissible bs a ↔ cs.admissible bs (envF f a) := by
  unfold ConstraintSystem.admissible
  have hmap : (cs.substF f).busInteractions.map (fun bi => bi.eval a)
      = cs.busInteractions.map (fun bi => bi.eval (envF f a)) := by
    simp only [ConstraintSystem.substF, List.map_map]
    exact List.map_congr_left (fun bi _ => bi.eval_substF f a)
  rw [hmap]

/-- `satisfies` transfers across simultaneous substitution. -/
theorem ConstraintSystem.satisfies_substF (cs : ConstraintSystem p)
    (f : Variable → Option (Expression p)) (bs : BusSemantics p) (a : Variable → ZMod p) :
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
    (f : Variable → Option (Expression p)) (bs : BusSemantics p) (a : Variable → ZMod p) :
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

/-- Simultaneous substitution introduces no variable outside `e` and the mapped solutions. -/
theorem Expression.substF_vars (f : Variable → Option (Expression p)) (e : Expression p) :
    ∀ z ∈ (e.substF f).vars, z ∈ e.vars ∨ ∃ y t, f y = some t ∧ z ∈ t.vars := by
  induction e with
  | const n => intro z hz; simp [Expression.substF, Expression.vars] at hz
  | var y =>
      intro z hz
      cases hfy : f y with
      | none => simp only [Expression.substF, hfy] at hz; exact Or.inl hz
      | some t => simp only [Expression.substF, hfy] at hz; exact Or.inr ⟨y, t, hfy, hz⟩
  | add a b iha ihb =>
      intro z hz
      simp only [Expression.substF, Expression.vars, List.mem_append] at hz
      rcases hz with hz | hz
      · exact (iha z hz).imp (List.mem_append.2 <| Or.inl ·) id
      · exact (ihb z hz).imp (List.mem_append.2 <| Or.inr ·) id
  | mul a b iha ihb =>
      intro z hz
      simp only [Expression.substF, Expression.vars, List.mem_append] at hz
      rcases hz with hz | hz
      · exact (iha z hz).imp (List.mem_append.2 <| Or.inl ·) id
      · exact (ihb z hz).imp (List.mem_append.2 <| Or.inr ·) id

/-- If every mapped solution mentions only `cs`'s variables, substitution introduces no new one. -/
theorem ConstraintSystem.substF_vars_subset (cs : ConstraintSystem p)
    (f : Variable → Option (Expression p))
    (hfv : ∀ (y : Variable) (t : Expression p), f y = some t → ∀ z ∈ t.vars, z ∈ cs.vars) :
    ∀ z ∈ (cs.substF f).vars, z ∈ cs.vars := by
  intro z hz
  rw [ConstraintSystem.mem_vars] at hz
  rcases hz with ⟨c, hc, hzc⟩ | ⟨bi, hbi, hzbi⟩
  · simp only [ConstraintSystem.substF, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    rcases Expression.substF_vars f c0 z hzc with h | ⟨y, t, hft, hzt⟩
    · exact ConstraintSystem.mem_vars_of_constraint hc0 h
    · exact hfv y t hft z hzt
  · simp only [ConstraintSystem.substF, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    rcases hzbi with hm | ⟨e, he, hze⟩
    · simp only [BusInteraction.substF] at hm
      rcases Expression.substF_vars f bi0.multiplicity z hm with h | ⟨y, t, hft, hzt⟩
      · exact ConstraintSystem.mem_vars_of_mult hbi0 h
      · exact hfv y t hft z hzt
    · simp only [BusInteraction.substF, List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      rcases Expression.substF_vars f e0 z hze with h | ⟨y, t, hft, hzt⟩
      · exact ConstraintSystem.mem_vars_of_payload hbi0 he0 h
      · exact hfv y t hft z hzt

/-- **Simultaneous-substitution correctness.** If every satisfying assignment of `cs` forces
    `x = t` for every mapped pair `f x = some t`, and every solution mentions only `cs`'s
    variables, then substituting the whole map at once is `PassCorrect`. The batch counterpart of
    `ConstraintSystem.subst_correct`. -/
theorem ConstraintSystem.substF_correct (cs : ConstraintSystem p)
    (f : Variable → Option (Expression p)) (bs : BusSemantics p)
    (H : ∀ env, cs.satisfies bs env → ∀ y t, f y = some t → env y = t.eval env)
    (hfv : ∀ (y : Variable) (t : Expression p), f y = some t → ∀ z ∈ t.vars, z ∈ cs.vars) :
    PassCorrect cs (cs.substF f) [] [] bs := by
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.substF_vars_subset f hfv) ?_
  · -- soundness: (cs.substF f) implies cs
    intro env hsat
    refine ⟨envF f env, (cs.satisfies_substF f bs env).1 hsat, ?_⟩
    rw [cs.sideEffects_substF]
    exact BusState.equiv_refl _
  · -- invariant preservation
    intro hinv env hsat bi hbi
    have hsatcs : cs.satisfies bs (envF f env) := (cs.satisfies_substF f bs env).1 hsat
    simp only [ConstraintSystem.substF, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    simp only [bi0.eval_substF f env]
    exact hinv (envF f env) hsatcs bi0 hbi0
  · -- completeness: cs intended-implies (cs.substF f), witness `env`
    intro env hadm hsat
    have henv : envF f env = env := envF_eq_self f env (H env hsat)
    refine ⟨?_, ?_, ?_⟩
    · rw [cs.satisfies_substF, henv]; exact hsat
    · rw [cs.admissible_substF, henv]; exact hadm
    · rw [cs.sideEffects_substF, henv]; exact BusState.equiv_refl _

/-! ## Substituting the map inside derivations (leanr #64)

When a pass eliminates variables by substituting `x := t`, any derivation whose method reads `x`
must have `x` replaced too, so the emitted methods keep referencing only surviving columns. This is
the "scan the derivations and replace the removed variable" step; it is what keeps a re-encoding
pass's derivations valid even after later passes eliminate more variables. -/

/-- Substitute the map in every expression a computation method reads. -/
def ComputationMethod.substF (f : Variable → Option (Expression p)) :
    ComputationMethod p → ComputationMethod p
  | .const c => .const c
  | .quotientOrZero num den => .quotientOrZero (num.substF f) (den.substF f)
  | .ifEqZero cond thenM elseM => .ifEqZero (cond.substF f) (thenM.substF f) (elseM.substF f)

theorem ComputationMethod.eval_substF (f : Variable → Option (Expression p))
    (cm : ComputationMethod p) (env : Variable → ZMod p) :
    (cm.substF f).eval env = cm.eval (envF f env) := by
  induction cm with
  | const c => rfl
  | quotientOrZero num den =>
      simp only [ComputationMethod.substF, ComputationMethod.eval, Expression.eval_substF]
  | ifEqZero cond thenM elseM iht ihe =>
      simp only [ComputationMethod.substF, ComputationMethod.eval, Expression.eval_substF, iht, ihe]

/-- `methodFor` commutes with substituting every method (the derived-variable keys are untouched). -/
theorem Derivations.methodFor_substF (f : Variable → Option (Expression p)) (ds : Derivations p)
    (w : Variable) :
    Derivations.methodFor (ds.map (fun x => (x.1, x.2.substF f))) w
      = (Derivations.methodFor ds w).map (·.substF f) := by
  induction ds with
  | nil => simp [Derivations.methodFor]
  | cons hd rest ih =>
      obtain ⟨u, cm⟩ := hd
      simp only [List.map_cons, Derivations.methodFor, ih]
      cases hrest : Derivations.methodFor rest w with
      | some m => simp [Option.orElse]
      | none => by_cases huw : u = w <;> simp [Option.orElse, huw]

/-- Variables of a substituted expression: either a solution variable of some mapped variable that
    occurs in `e`, or an unmapped variable of `e`. -/
theorem Expression.substF_vars' (f : Variable → Option (Expression p)) (e : Expression p)
    (z : Variable) (hz : z ∈ (e.substF f).vars) :
    (∃ y ∈ e.vars, ∃ t, f y = some t ∧ z ∈ t.vars) ∨ (f z = none ∧ z ∈ e.vars) := by
  induction e with
  | const n => simp [Expression.substF, Expression.vars] at hz
  | var y =>
      cases hfy : f y with
      | none =>
          simp only [Expression.substF, hfy, Expression.vars, List.mem_singleton] at hz
          subst hz
          exact Or.inr ⟨hfy, by simp [Expression.vars]⟩
      | some t =>
          simp only [Expression.substF, hfy] at hz
          exact Or.inl ⟨y, by simp [Expression.vars], t, hfy, hz⟩
  | add a b iha ihb =>
      simp only [Expression.substF, Expression.vars, List.mem_append] at hz
      rcases hz with h | h
      · exact (iha h).imp (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_left _ hy, t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_left _ hze⟩)
      · exact (ihb h).imp (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_right _ hy, t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_right _ hze⟩)
  | mul a b iha ihb =>
      simp only [Expression.substF, Expression.vars, List.mem_append] at hz
      rcases hz with h | h
      · exact (iha h).imp (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_left _ hy, t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_left _ hze⟩)
      · exact (ihb h).imp (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_right _ hy, t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_right _ hze⟩)

theorem ComputationMethod.substF_vars' (f : Variable → Option (Expression p))
    (cm : ComputationMethod p) (z : Variable) (hz : z ∈ (cm.substF f).vars) :
    (∃ y ∈ cm.vars, ∃ t, f y = some t ∧ z ∈ t.vars) ∨ (f z = none ∧ z ∈ cm.vars) := by
  induction cm with
  | const c => simp [ComputationMethod.substF, ComputationMethod.vars] at hz
  | quotientOrZero num den =>
      simp only [ComputationMethod.substF, ComputationMethod.vars, List.mem_append] at hz
      rcases hz with h | h
      · exact (Expression.substF_vars' f num z h).imp
          (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_left _ hy, t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_left _ hze⟩)
      · exact (Expression.substF_vars' f den z h).imp
          (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_right _ hy, t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_right _ hze⟩)
  | ifEqZero cond thenM elseM iht ihe =>
      simp only [ComputationMethod.substF, ComputationMethod.vars, List.mem_append] at hz
      rcases hz with (h | h) | h
      · exact (Expression.substF_vars' f cond z h).imp
          (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_left _ (List.mem_append_left _ hy), t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_left _ (List.mem_append_left _ hze)⟩)
      · exact (iht h).imp
          (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_left _ (List.mem_append_right _ hze)⟩)
      · exact (ihe h).imp
          (fun ⟨y, hy, t, hft, hzt⟩ => ⟨y, List.mem_append_right _ hy, t, hft, hzt⟩)
          (fun ⟨hfz, hze⟩ => ⟨hfz, List.mem_append_right _ hze⟩)

/-- An unmapped variable of `e` survives substitution. -/
theorem Expression.substF_mem_unmapped (f : Variable → Option (Expression p)) (e : Expression p)
    (z : Variable) (hfz : f z = none) (hz : z ∈ e.vars) : z ∈ (e.substF f).vars := by
  induction e with
  | const n => simp [Expression.vars] at hz
  | var y =>
      simp only [Expression.vars, List.mem_singleton] at hz; subst hz
      simp only [Expression.substF, hfz, Expression.vars, List.mem_singleton]
  | add a b iha ihb =>
      simp only [Expression.vars, List.mem_append] at hz
      simp only [Expression.substF, Expression.vars, List.mem_append]
      exact hz.imp iha ihb
  | mul a b iha ihb =>
      simp only [Expression.vars, List.mem_append] at hz
      simp only [Expression.substF, Expression.vars, List.mem_append]
      exact hz.imp iha ihb

/-- The solution variables of a mapped variable occurring in `e` appear in the substituted `e`. -/
theorem Expression.substF_mem_mapped (f : Variable → Option (Expression p)) (e : Expression p)
    (y z : Variable) (t : Expression p) (hfy : f y = some t) (hy : y ∈ e.vars) (hz : z ∈ t.vars) :
    z ∈ (e.substF f).vars := by
  induction e with
  | const n => simp [Expression.vars] at hy
  | var w =>
      simp only [Expression.vars, List.mem_singleton] at hy; subst hy
      simp only [Expression.substF, hfy]; exact hz
  | add a b iha ihb =>
      simp only [Expression.vars, List.mem_append] at hy
      simp only [Expression.substF, Expression.vars, List.mem_append]
      exact hy.imp iha ihb
  | mul a b iha ihb =>
      simp only [Expression.vars, List.mem_append] at hy
      simp only [Expression.substF, Expression.vars, List.mem_append]
      exact hy.imp iha ihb

/-- An unmapped variable of `cs` survives substitution into the system. -/
theorem ConstraintSystem.substF_mem_unmapped (cs : ConstraintSystem p)
    (f : Variable → Option (Expression p)) (z : Variable) (hfz : f z = none) (hz : z ∈ cs.vars) :
    z ∈ (cs.substF f).vars := by
  rw [ConstraintSystem.mem_vars] at hz ⊢
  rcases hz with ⟨c, hc, hzc⟩ | ⟨bi, hbi, hzbi⟩
  · exact Or.inl ⟨c.substF f, List.mem_map.2 ⟨c, hc, rfl⟩, Expression.substF_mem_unmapped f c z hfz hzc⟩
  · refine Or.inr ⟨bi.substF f, List.mem_map.2 ⟨bi, hbi, rfl⟩, ?_⟩
    rcases hzbi with hmul | ⟨e, he, hze⟩
    · exact Or.inl (Expression.substF_mem_unmapped f bi.multiplicity z hfz hmul)
    · exact Or.inr ⟨e.substF f, List.mem_map.2 ⟨e, he, rfl⟩, Expression.substF_mem_unmapped f e z hfz hze⟩

/-- The solution variables of a mapped variable of `cs` appear in the substituted system. -/
theorem ConstraintSystem.substF_mem_mapped (cs : ConstraintSystem p)
    (f : Variable → Option (Expression p)) (y z : Variable) (t : Expression p)
    (hfy : f y = some t) (hy : y ∈ cs.vars) (hz : z ∈ t.vars) : z ∈ (cs.substF f).vars := by
  rw [ConstraintSystem.mem_vars] at hy ⊢
  rcases hy with ⟨c, hc, hyc⟩ | ⟨bi, hbi, hybi⟩
  · exact Or.inl ⟨c.substF f, List.mem_map.2 ⟨c, hc, rfl⟩, Expression.substF_mem_mapped f c y z t hfy hyc hz⟩
  · refine Or.inr ⟨bi.substF f, List.mem_map.2 ⟨bi, hbi, rfl⟩, ?_⟩
    rcases hybi with hmul | ⟨e, he, hye⟩
    · exact Or.inl (Expression.substF_mem_mapped f bi.multiplicity y z t hfy hmul hz)
    · exact Or.inr ⟨e.substF f, List.mem_map.2 ⟨e, he, rfl⟩, Expression.substF_mem_mapped f e y z t hfy hye hz⟩

/-- **Threaded simultaneous-substitution correctness.** The `Derivations`-carrying version of
    `substF_correct`: substituting the map also inside every incoming derivation keeps them valid —
    each method now reads only columns present in the substituted system. -/
theorem ConstraintSystem.substF_correct_D (cs : ConstraintSystem p)
    (f : Variable → Option (Expression p)) (bs : BusSemantics p) (dIn : Derivations p)
    (H : ∀ env, cs.satisfies bs env → ∀ y t, f y = some t → env y = t.eval env)
    (hfv : ∀ (y : Variable) (t : Expression p), f y = some t → ∀ z ∈ t.vars, z ∈ cs.vars) :
    PassCorrect cs (cs.substF f) dIn (dIn.map (fun x => (x.1, x.2.substF f))) bs := by
  obtain ⟨himpl, hinv, hS, _⟩ := cs.substF_correct f bs H hfv
  refine ⟨himpl, hinv, hS, fun env hadm hsat => ?_⟩
  have henv : envF f env = env := envF_eq_self f env (H env hsat)
  refine ⟨env, ?_, ?_, ?_, fun _ _ => rfl, ?_⟩
  · rw [cs.satisfies_substF, henv]; exact hsat
  · rw [cs.admissible_substF, henv]; exact hadm
  · rw [cs.sideEffects_substF, henv]; exact BusState.equiv_refl _
  · intro hrec w hwout hwnone
    obtain ⟨cm, hcm, hcmv, hcmeval⟩ := hrec w (cs.substF_vars_subset f hfv w hwout) hwnone
    refine ⟨cm.substF f, ?_, ?_, ?_⟩
    · rw [Derivations.methodFor_substF, hcm]; rfl
    · intro z hz
      rcases ComputationMethod.substF_vars' f cm z hz with ⟨y, hy, t, hft, hzt⟩ | ⟨hfz, hze⟩
      · exact cs.substF_mem_mapped f y z t hft (hcmv y hy) hzt
      · exact cs.substF_mem_unmapped f z hfz (hcmv z hze)
    · rw [ComputationMethod.eval_substF, henv]; exact hcmeval
