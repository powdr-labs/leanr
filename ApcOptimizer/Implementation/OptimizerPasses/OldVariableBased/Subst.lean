import ApcOptimizer.Implementation.OptimizerPasses.SubstCore

set_option autoImplicit false

/-! # Building substitution passes from a constraint solver

The core substitution equivalence machinery (`Expression.subst` / `ConstraintSystem.subst` /
`ConstraintSystem.subst_correct` and the transfer lemmas) lives in the neutral
`OptimizerPasses/SubstCore.lean`, imported above; this file builds a `VerifiedPass` on top of it.

A *solver* inspects a single algebraic constraint and may report a variable `x` and an expression
`t` such that the constraint (when it evaluates to `0`) forces `x = t`. Given a proof of that
soundness property, `substFromConstraint` builds a `VerifiedPass` that finds the first solvable
constraint and substitutes it (falling back to the identity when none is solvable). All the
correctness work is delegated to `subst_correct`; a concrete pass only supplies a (decidable) solver
and its soundness lemma. -/

variable {p : ℕ}

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
