import Leanr.Solver
import Leanr.AlgebraicConstraint.Proofs

variable {p : ℕ} [Fact (Nat.Prime p)]

instance instFactPrime13 : Fact (Nat.Prime 13) where
  out := by norm_num

/-! ## Correctness -/

/-- Dropping a constraint whose constant value is 0 preserves satisfiability. -/
theorem toConstant_zero_satisfied {c : AlgebraicConstraint p} {env : String → ZMod p}
    (h : c.toConstant? = some 0) : c.eval env = 0 := by
  cases c with
  | affine e => exact AffineExpression.toConstant?_correct e 0 h env
  | general e =>
    simp [AlgebraicConstraint.toConstant?, Expression.toConstant?] at h
    cases e with
    | const n =>
      simp at h
      simp [AlgebraicConstraint.eval, Expression.eval, h]
    | _ => simp at h

/-! ### Loop invariant helpers -/

/-- Helper: the forIn loop in substitute_all_constraints preserves satisfaction. -/
private theorem subst_forIn_loop_preserves
    (constraints : Array (AlgebraicConstraint p))
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h_map : ∀ x v, m[x]? = some v → env x = v)
    (h_sat : ∀ c ∈ constraints.toList, AlgebraicConstraint.eval c env = 0)
    (i : Nat) (hi : i ≤ constraints.size)
    (acc : Array (AlgebraicConstraint p))
    (h_acc : ∀ c ∈ acc.toList, AlgebraicConstraint.eval c env = 0) :
    ∀ c ∈ (Array.forIn'.loop constraints
      (fun (c : AlgebraicConstraint p) (_ : c ∈ constraints) (r : Array (AlgebraicConstraint p)) =>
        if (c.substituteAll m).toConstant? == some 0 then
          (ForInStep.yield r : Id (ForInStep _))
        else
          (ForInStep.yield (r.push (c.substituteAll m)) : Id (ForInStep _)))
      i hi acc : Id _).toList,
      AlgebraicConstraint.eval c env = 0 := by
  induction i generalizing acc with
  | zero =>
    rw [Array.forIn'.loop.eq_1]; exact h_acc
  | succ n ih =>
    rw [Array.forIn'.loop.eq_2]
    simp only [pure, Pure.pure, bind, Bind.bind]
    split_ifs
    · exact ih (by omega) acc h_acc
    · apply ih (by omega)
      intro c hc
      rw [Array.toList_push, List.mem_append] at hc
      cases hc with
      | inl hc => exact h_acc c hc
      | inr hc =>
        simp at hc; rw [hc, AlgebraicConstraint.substituteAll_eval _ m env h_map]
        exact h_sat _ (Array.getElem_mem_toList (by omega))

/-- Helper: the forIn loop in find_all_assignments preserves the invariant. -/
private theorem find_forIn_loop_preserves
    (constraints : Array (AlgebraicConstraint p))
    (env : String → ZMod p)
    (h_sat : ∀ c ∈ constraints.toList, AlgebraicConstraint.eval c env = 0)
    (i : Nat) (hi : i ≤ constraints.size)
    (acc_a : Array (Assignment (p := p)))
    (acc_r : Array (AlgebraicConstraint p))
    (h_a : ∀ a ∈ acc_a.toList, env a.var = a.value)
    (h_r : ∀ c ∈ acc_r.toList, AlgebraicConstraint.eval c env = 0) :
    let result := Array.forIn'.loop constraints
      (fun (c : AlgebraicConstraint p) (_ : c ∈ constraints)
        (r : MProd (Array (Assignment (p := p))) (Array (AlgebraicConstraint p))) =>
        (match c.solve? with
        | some a => ForInStep.yield ⟨r.fst.push a, r.snd⟩
        | none => ForInStep.yield ⟨r.fst, r.snd.push c⟩ : Id (ForInStep _)))
      i hi ⟨acc_a, acc_r⟩
    (∀ a ∈ result.fst.toList, env a.var = a.value) ∧
    (∀ c ∈ result.snd.toList, AlgebraicConstraint.eval c env = 0) := by
  induction i generalizing acc_a acc_r with
  | zero => rw [Array.forIn'.loop.eq_1]; exact ⟨h_a, h_r⟩
  | succ n ih =>
    simp only [Array.forIn'.loop.eq_2, pure, Pure.pure, bind, Bind.bind]
    have h_lt : constraints.size - 1 - n < constraints.size := by omega
    have h_mem := h_sat _ (Array.getElem_mem_toList h_lt)
    rcases h_solve : (constraints[constraints.size - 1 - n]).solve? with _ | a
    · apply ih (by omega)
      · exact h_a
      · intro c hc; rw [Array.toList_push, List.mem_append] at hc
        rcases hc with hc | hc
        · exact h_r c hc
        · simp at hc; rw [hc]; exact h_mem
    · apply ih (by omega)
      · intro x hx; rw [Array.toList_push, List.mem_append] at hx
        rcases hx with hx | hx
        · exact h_a x hx
        · simp at hx; rw [hx]
          exact AlgebraicConstraint.solve?_sound _ a env h_solve h_mem
      · exact h_r

/-! ### Main correctness theorems -/

/-- substituteAll preserves satisfaction when the map agrees with the environment. -/
theorem substituteAll_preserves_satisfaction
    (constraints : Array (AlgebraicConstraint p))
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h_map : ∀ x v, m[x]? = some v → env x = v)
    (h_sat : ∀ c ∈ constraints.toList, AlgebraicConstraint.eval c env = 0) :
    ∀ c ∈ (substitute_all_constraints constraints m).toList,
      AlgebraicConstraint.eval c env = 0 :=
  subst_forIn_loop_preserves constraints m env h_map h_sat constraints.size (le_refl _)
    (Array.mkEmpty constraints.size) (by intro c hc; simp at hc)

/-- find_all_assignments is sound: found assignments agree with env,
    and remaining constraints are still satisfied. -/
theorem find_all_assignments_sound
    (constraints : Array (AlgebraicConstraint p))
    (env : String → ZMod p)
    (h_sat : ∀ c ∈ constraints.toList, AlgebraicConstraint.eval c env = 0) :
    let (assignments, remaining) := find_all_assignments constraints
    (∀ a ∈ assignments.toList, env a.var = a.value) ∧
    (∀ c ∈ remaining.toList, AlgebraicConstraint.eval c env = 0) := by
  show (∀ a ∈ (find_all_assignments constraints).1.toList, env a.var = a.value) ∧
    (∀ c ∈ (find_all_assignments constraints).2.toList, AlgebraicConstraint.eval c env = 0)
  exact find_forIn_loop_preserves constraints env h_sat constraints.size (le_refl _) #[] #[]
    (by intro a ha; simp at ha) (by intro c hc; simp at hc)

/-! ### HashMap from assignments -/

/-- Helper: List.foldl insert on a HashMap preserves agreement with env. -/
private theorem list_foldl_insert_agrees
    (assignments : List (Assignment (p := p)))
    (env : String → ZMod p)
    (h : ∀ a ∈ assignments, env a.var = a.value)
    (acc : Std.HashMap String (ZMod p))
    (h_acc : ∀ x v, acc[x]? = some v → env x = v) :
    ∀ x v, (assignments.foldl (fun m (a : Assignment (p := p)) => m.insert a.var a.value) acc)[x]? = some v →
      env x = v := by
  induction assignments generalizing acc with
  | nil => simpa using h_acc
  | cons a as ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro b hb; exact h b (List.mem_cons_of_mem _ hb)
    · intro x v hxv
      rw [Std.HashMap.getElem?_insert] at hxv
      split_ifs at hxv with heq
      · cases hxv
        rw [← beq_iff_eq.mp heq]
        exact h a List.mem_cons_self
      · exact h_acc x v hxv

/-- A HashMap built from all assignments agrees with the environment. -/
theorem hashmap_from_assignments_agrees
    (assignments : Array (Assignment (p := p)))
    (env : String → ZMod p)
    (h : ∀ a ∈ assignments.toList, env a.var = a.value) :
    ∀ x v, (assignments.foldl (init := (∅ : Std.HashMap String (ZMod p)))
      fun m a => m.insert a.var a.value)[x]? = some v → env x = v := by
  rw [← Array.foldl_toList]
  exact list_foldl_insert_agrees _ env h _ (by intro x v hxv; simp at hxv)

/-- One round of pure solving preserves satisfiability. -/
theorem solve_round_pure_preserves (system : System (p := p)) (env : String → ZMod p)
    (h_sat : system.satisfies env) :
    (solve_round_pure system).satisfies env := by
  unfold solve_round_pure
  have fas := find_all_assignments_sound system.constraints env h_sat
  rcases h_eq : find_all_assignments system.constraints with ⟨assignments, remaining⟩
  rw [h_eq] at fas
  obtain ⟨h_assign, h_remain⟩ := fas
  simp only
  split_ifs
  · exact h_sat
  · intro c hc
    exact substituteAll_preserves_satisfaction _ _ env
      (hashmap_from_assignments_agrees _ env h_assign) h_remain c hc

/-- The solver preserves satisfiability: if all original constraints are satisfied by `env`,
    then all remaining constraints after solving are also satisfied by `env`. -/
theorem solve_sound (system : System (p := p)) (env : String → ZMod p)
    (h_sat : system.satisfies env) :
    (solve_pure system).satisfies env := by
  rw [solve_pure]
  have h_round := solve_round_pure_preserves system env h_sat
  split_ifs with h
  · exact solve_sound (solve_round_pure system) env h_round
  · exact h_round
  termination_by system.constraints.size
  decreasing_by omega
