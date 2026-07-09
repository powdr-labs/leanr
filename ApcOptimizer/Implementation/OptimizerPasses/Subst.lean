import ApcOptimizer.Implementation.OptimizerPasses.Basic

set_option autoImplicit false

/-! # Substitution: the core equivalence machinery for variable elimination

The single most important building block for the optimizer. If a constraint system entails that
some variable `x` always equals an expression `t` (e.g. because it contains a constraint
`x - t = 0`), then substituting `x := t` everywhere yields an *equivalent* system that no longer
mentions `x` — reducing the circuit's variable count by one.

This file provides:

* `Expression.subst` / `Expression.eval_subst` — syntactic substitution and its semantics
  (`(e.subst x t).eval env = e.eval (env with x ↦ t.eval env)`);
* the lifting of substitution to bus interactions and to whole constraint systems
  (`ConstraintSystem.subst`), with `satisfies`/`sideEffects` transfer lemmas;
* `ConstraintSystem.subst_correct` — the payoff: given a proof that satisfying assignments force
  `x = t`, the substituted system is `PassCorrect` (equivalent and invariant-preserving).

Everything here is purely equational — no field/primality assumptions. Passes that *detect* a
suitable `(x, t)` and supply the entailment hypothesis are built on top of this. -/

variable {p : ℕ}

/-! ## Substitution on expressions -/

/-- Substitute variable `x` by expression `t` throughout an expression. -/
def Expression.subst (e : Expression p) (x : Variable) (t : Expression p) : Expression p :=
  match e with
  | .const n => .const n
  | .var y => if y = x then t else .var y
  | .add a b => .add (a.subst x t) (b.subst x t)
  | .mul a b => .mul (a.subst x t) (b.subst x t)

/-- Substitution semantics: substituting `x := t` and evaluating is the same as evaluating in the
    environment with `x` rebound to `t.eval env`. -/
theorem Expression.eval_subst (e : Expression p) (x : Variable) (t : Expression p)
    (env : Variable → ZMod p) :
    (e.subst x t).eval env = e.eval (Function.update env x (t.eval env)) := by
  induction e with
  | const n => simp [Expression.subst, Expression.eval]
  | var y =>
      simp only [Expression.subst]
      by_cases h : y = x
      · subst h; simp [Expression.eval, Function.update_self]
      · rw [if_neg h]; simp [Expression.eval, Function.update_of_ne h]
  | add a b iha ihb => simp only [Expression.subst, Expression.eval, iha, ihb]
  | mul a b iha ihb => simp only [Expression.subst, Expression.eval, iha, ihb]

/-! ## Substitution on bus interactions -/

/-- Substitute `x := t` in every expression of a bus interaction. -/
def BusInteraction.subst (bi : BusInteraction (Expression p)) (x : Variable) (t : Expression p) :
    BusInteraction (Expression p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.subst x t,
    payload := bi.payload.map (·.subst x t) }

theorem BusInteraction.eval_subst (bi : BusInteraction (Expression p)) (x : Variable)
    (t : Expression p) (env : Variable → ZMod p) :
    (bi.subst x t).eval env = bi.eval (Function.update env x (t.eval env)) := by
  simp only [BusInteraction.subst, BusInteraction.eval, Expression.eval_subst, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, Expression.eval_subst]

/-! ## Substitution on constraint systems -/

/-- Substitute `x := t` everywhere in a constraint system. -/
def ConstraintSystem.subst (cs : ConstraintSystem p) (x : Variable) (t : Expression p) :
    ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints.map (·.subst x t),
    busInteractions := cs.busInteractions.map (·.subst x t) }

/-- The evaluated interactions of a substituted system, restricted to one bus, are those of the
    original under the rebound environment (substitution never changes a bus id). -/
theorem ConstraintSystem.msgs_subst (cs : ConstraintSystem p) (x : Variable) (t : Expression p)
    (busId : Nat) (a : Variable → ZMod p) :
    ((cs.subst x t).busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => bi.eval a)
    = (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => bi.eval (Function.update a x (t.eval a))) := by
  simp only [ConstraintSystem.subst]
  rw [List.filter_map]
  rw [List.filter_congr
    (fun bi _ => (rfl :
      ((fun b : BusInteraction (Expression p) => decide (b.busId = busId)) ∘
        (fun b => b.subst x t)) bi = decide (bi.busId = busId)))]
  rw [List.map_map]
  exact List.map_congr_left (fun bi _ => bi.eval_subst x t a)

/-- `admissible` transfers across substitution — generically in the VM predicate, since
    substitution preserves the evaluated messages under the rebound environment. -/
theorem ConstraintSystem.admissible_subst (cs : ConstraintSystem p) (x : Variable)
    (t : Expression p) (bs : BusSemantics p) (a : Variable → ZMod p) :
    (cs.subst x t).admissible bs a
      ↔ cs.admissible bs (Function.update a x (t.eval a)) := by
  unfold ConstraintSystem.admissible
  have hmap : (cs.subst x t).busInteractions.map (fun bi => bi.eval a)
      = cs.busInteractions.map (fun bi => bi.eval (Function.update a x (t.eval a))) := by
    simp only [ConstraintSystem.subst, List.map_map]
    exact List.map_congr_left (fun bi _ => bi.eval_subst x t a)
  rw [hmap]

/-- `satisfies` transfers across substitution: the substituted system is satisfied at `a` exactly
    when the original is satisfied at `a` with `x` rebound to `t.eval a`. -/
theorem ConstraintSystem.satisfies_subst (cs : ConstraintSystem p) (x : Variable) (t : Expression p)
    (bs : BusSemantics p) (a : Variable → ZMod p) :
    (cs.subst x t).satisfies bs a ↔ cs.satisfies bs (Function.update a x (t.eval a)) := by
  simp only [ConstraintSystem.satisfies, ConstraintSystem.subst] at *
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c0 hc0 => ?_, fun bi0 hbi0 => ?_⟩
    · have := hc _ (List.mem_map.2 ⟨c0, hc0, rfl⟩)
      rwa [Expression.eval_subst] at this
    · have := hb _ (List.mem_map.2 ⟨bi0, hbi0, rfl⟩)
      rwa [BusInteraction.eval_subst] at this
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hc' => ?_, fun bi hbi' => ?_⟩
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
      rw [Expression.eval_subst]; exact hc c0 hc0
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
      rw [BusInteraction.eval_subst]; exact hb bi0 hbi0

/-- `sideEffects` transfers across substitution. -/
theorem ConstraintSystem.sideEffects_subst (cs : ConstraintSystem p) (x : Variable)
    (t : Expression p) (bs : BusSemantics p) (a : Variable → ZMod p) :
    (cs.subst x t).sideEffects bs a = cs.sideEffects bs (Function.update a x (t.eval a)) := by
  simp only [ConstraintSystem.sideEffects, ConstraintSystem.subst]
  induction cs.busInteractions with
  | nil => rfl
  | cons bi rest ih =>
      simp only [List.map_cons, List.filter_cons]
      have hbus : bs.isStateful (bi.subst x t).busId = bs.isStateful bi.busId := rfl
      rw [hbus]
      by_cases hstate : bs.isStateful bi.busId = true
      · simp only [if_pos hstate, List.map_cons, ih, BusInteraction.eval_subst]
      · simp only [if_neg hstate, ih]

/-- Substitution introduces no variable outside `e` and `t`. -/
theorem Expression.subst_vars (e : Expression p) (x : Variable) (t : Expression p) :
    ∀ z ∈ (e.subst x t).vars, z ∈ e.vars ∨ z ∈ t.vars := by
  induction e with
  | const n => intro z hz; simp [Expression.subst, Expression.vars] at hz
  | var y =>
      intro z hz
      simp only [Expression.subst] at hz
      by_cases h : y = x
      · rw [if_pos h] at hz; exact Or.inr hz
      · rw [if_neg h] at hz; exact Or.inl hz
  | add a b iha ihb =>
      intro z hz
      simp only [Expression.subst, Expression.vars, List.mem_append] at hz
      rcases hz with hz | hz
      · exact (iha z hz).imp (List.mem_append.2 <| Or.inl ·) id
      · exact (ihb z hz).imp (List.mem_append.2 <| Or.inr ·) id
  | mul a b iha ihb =>
      intro z hz
      simp only [Expression.subst, Expression.vars, List.mem_append] at hz
      rcases hz with hz | hz
      · exact (iha z hz).imp (List.mem_append.2 <| Or.inl ·) id
      · exact (ihb z hz).imp (List.mem_append.2 <| Or.inr ·) id

/-- If `t`'s variables are all in `cs`, substitution introduces no new variable. -/
theorem ConstraintSystem.subst_vars_subset (cs : ConstraintSystem p) (x : Variable)
    (t : Expression p) (htv : ∀ y ∈ t.vars, y ∈ cs.vars) :
    ∀ z ∈ (cs.subst x t).vars, z ∈ cs.vars := by
  intro z hz
  rw [ConstraintSystem.mem_vars] at hz
  rcases hz with ⟨c, hc, hzc⟩ | ⟨bi, hbi, hzbi⟩
  · simp only [ConstraintSystem.subst, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    exact (Expression.subst_vars c0 x t z hzc).elim
      (ConstraintSystem.mem_vars_of_constraint hc0) (htv z)
  · simp only [ConstraintSystem.subst, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    rcases hzbi with hm | ⟨e, he, hze⟩
    · simp only [BusInteraction.subst] at hm
      exact (Expression.subst_vars bi0.multiplicity x t z hm).elim
        (ConstraintSystem.mem_vars_of_mult hbi0) (htv z)
    · simp only [BusInteraction.subst, List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      exact (Expression.subst_vars e0 x t z hze).elim
        (ConstraintSystem.mem_vars_of_payload hbi0 he0) (htv z)

/-- **Substitution correctness.** If every satisfying assignment of `cs` forces `x = t` and `t`
    mentions only `cs`'s variables, then substituting `x := t` everywhere produces a `PassCorrect`
    system: equivalent to `cs`, invariant-preserving, and introducing no new column. This is the
    workhorse behind all variable-elimination passes. -/
theorem ConstraintSystem.subst_correct (cs : ConstraintSystem p) (x : Variable) (t : Expression p)
    (bs : BusSemantics p) (H : ∀ env, cs.satisfies bs env → env x = t.eval env)
    (htv : ∀ y ∈ t.vars, y ∈ cs.vars) :
    PassCorrect cs (cs.subst x t) [] bs := by
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.subst_vars_subset x t htv) ?_
  · -- soundness: (cs.subst x t) implies cs
    intro env hsat
    refine ⟨Function.update env x (t.eval env), (cs.satisfies_subst x t bs env).1 hsat, ?_⟩
    rw [cs.sideEffects_subst]
    exact BusState.equiv_refl _
  · -- invariant preservation
    intro hinv env hsat bi hbi
    have hsatcs : cs.satisfies bs (Function.update env x (t.eval env)) :=
      (cs.satisfies_subst x t bs env).1 hsat
    simp only [ConstraintSystem.subst, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    simp only [bi0.eval_subst x t env]
    exact hinv (Function.update env x (t.eval env)) hsatcs bi0 hbi0
  · -- completeness: cs intended-implies (cs.subst x t), witness `env`
    intro env hadm hsat
    have hx : env x = t.eval env := H env hsat
    have hupd : Function.update env x (t.eval env) = env := by
      rw [← hx]; exact Function.update_eq_self x env
    refine ⟨?_, ?_, ?_⟩
    · rw [cs.satisfies_subst, hupd]; exact hsat
    · rw [cs.admissible_subst, hupd]; exact hadm
    · rw [cs.sideEffects_subst, hupd]; exact BusState.equiv_refl _

/-! ## Building substitution passes from a constraint solver

A *solver* inspects a single algebraic constraint and may report a variable `x` and an expression
`t` such that the constraint (when it evaluates to `0`) forces `x = t`. Given a proof of that
soundness property, `substFromConstraint` builds a `VerifiedPass` that finds the first solvable
constraint and substitutes it (falling back to the identity when none is solvable). All the
correctness work is delegated to `subst_correct`; a concrete pass only supplies a (decidable) solver
and its soundness lemma. -/

/-- Build a substitution pass from a constraint `solve`r and its soundness proof `hsolve`. Searches
    the algebraic constraints for the first one `solve` handles and substitutes `x := t`; identity
    otherwise. Correct by `subst_correct`, since a solved constraint (being satisfied, hence `0`)
    entails `x = t`. -/
def substFromConstraint (solve : Expression p → Option (Variable × Expression p))
    (hsolve : ∀ (c : Expression p) (x : Variable) (t : Expression p), solve c = some (x, t) →
      ∀ env, c.eval env = 0 → env x = t.eval env)
    (hsolveV : ∀ (c : Expression p) (x : Variable) (t : Expression p), solve c = some (x, t) →
      ∀ y ∈ t.vars, y ∈ c.vars) :
    VerifiedPass p := fun cs bs =>
  match hfound : cs.algebraicConstraints.find? (fun c => (solve c).isSome) with
  | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  | some c =>
      have hmem : c ∈ cs.algebraicConstraints := List.mem_of_find?_eq_some hfound
      match hc : solve c with
      | some (x, t) =>
          ⟨cs.subst x t, [], cs.subst_correct x t bs
            (fun env hsat => hsolve c x t hc env (hsat.1 c hmem))
            (fun y hy => ConstraintSystem.mem_vars_of_constraint hmem (hsolveV c x t hc y hy))⟩
      | none => by have hsome := List.find?_some hfound; simp [hc] at hsome
