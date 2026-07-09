import Leanr.Implementation.OptimizerPasses.FactPass
import Leanr.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Bus payload canonicalization (`payloadCanonPass`)

A bus payload entry is often a *defined* expression: some algebraic constraint `x - e = 0`
(as built by `eqExpr`, e.g. the slot equalities `busUnifyPass` adds for consecutive
same-address memory accesses) pins a variable `x` to the entry's value. This pass rewrites such
payload entries `e` to the equal **variable** `x`.

The value of every message is unchanged under any assignment satisfying the constraints (which
the pass keeps untouched), so satisfaction, side effects, `admissible` and invariants all
transfer with the *same* environment in both directions — a `PassCorrect.ofEnvEq` proof.

Why it matters: passes that compare payload entries *syntactically* — most importantly
`busPairCancelPass`, which cancels a matched send/receive pair only when the payloads are
**equal** — are blocked when one side carries the defining expression and the other the defined
variable (a memory write of a degree-2 value, read back as a fresh column: the write's payload
holds the blend, the read's the variable, and the linking constraint cannot be inlined without
raising degrees). Canonicalizing both to the variable makes the pair syntactically equal, and
the (already-verified) cancellation machinery fires. It also lowers payload degrees, which can
only help the degree guard.

Only non-atomic entries are rewritten (`e` neither a variable nor a constant), so a rewrite
strictly shrinks the payload's total AST size and the pass cannot oscillate under the pipeline's
fixpoint iteration. Field-free and VM-agnostic; the constraints are not modified. -/

variable {p : ℕ}

/-! ## Recognizing defining constraints -/

/-- Is the expression a variable or a constant? (Rewriting those would not shrink anything.) -/
def Expression.isAtomic : Expression p → Bool
  | .var _ => true
  | .const _ => true
  | _ => false

/-- Extract a defining equality from a constraint of the syntactic shape `eqExpr` builds:
    `x - e` (i.e. `.add (.var x) (.mul (.const (-1)) e)`) or `e - x`, giving `(e, x)` —
    "payload entry `e` may be rewritten to `.var x`". -/
def defPattern? : Expression p → Option (Expression p × Variable)
  | .add (.var x) (.mul (.const k) e) => if k = -1 then some (e, x) else none
  | .add e (.mul (.const k) (.var x)) => if k = -1 then some (e, x) else none
  | _ => none

/-- The checked certificate the correctness proof consumes: the defining constraint for `(e, x)`
    is literally present (in either orientation). Holds by construction for pairs produced by
    `defPattern?`, but re-checking keeps the proof independent of the builder. -/
def defWitnessed (constraints : List (Expression p)) (d : Expression p × Variable) : Bool :=
  constraints.any (fun c =>
    decide (c = eqExpr (.var d.2) d.1) || decide (c = eqExpr d.1 (.var d.2)))

theorem defWitnessed_eval (constraints : List (Expression p)) (d : Expression p × Variable)
    (h : defWitnessed constraints d = true) (env : Variable → ZMod p)
    (hzero : ∀ c ∈ constraints, c.eval env = 0) : env d.2 = d.1.eval env := by
  obtain ⟨c, hc, hcform⟩ := List.any_eq_true.1 h
  rcases Bool.or_eq_true _ _ |>.mp hcform with h' | h'
  · have hceq : c = eqExpr (.var d.2) d.1 := of_decide_eq_true h'
    have hz := hzero c hc
    rw [hceq, eqExpr_eval] at hz
    have := sub_eq_zero.mp hz
    simpa [Expression.eval] using this
  · have hceq : c = eqExpr d.1 (.var d.2) := of_decide_eq_true h'
    have hz := hzero c hc
    rw [hceq, eqExpr_eval] at hz
    have := sub_eq_zero.mp hz
    simpa [Expression.eval] using this.symm

/-- The defining variable of a witnessed pair occurs in the witnessing constraint, hence in the
    system. -/
theorem defWitnessed_var_mem (cs : ConstraintSystem p) (d : Expression p × Variable)
    (h : defWitnessed cs.algebraicConstraints d = true) : d.2 ∈ cs.vars := by
  obtain ⟨c, hc, hcform⟩ := List.any_eq_true.1 h
  rcases Bool.or_eq_true _ _ |>.mp hcform with h' | h'
  · refine ConstraintSystem.mem_vars_of_constraint hc ?_
    rw [of_decide_eq_true h']
    simp [eqExpr, Expression.vars]
  · refine ConstraintSystem.mem_vars_of_constraint hc ?_
    rw [of_decide_eq_true h']
    simp [eqExpr, Expression.vars]

/-! ## The rewrite -/

/-- Rewrite `e` to `.var x` when `(e, x)` is a recorded defining pair (first match wins);
    otherwise leave it unchanged. Applied at the top level of each payload entry only. -/
def canonRw (defs : List (Expression p × Variable)) (e : Expression p) : Expression p :=
  match defs.find? (fun d => decide (d.1 = e)) with
  | some d => .var d.2
  | none => e

theorem canonRw_eval (defs : List (Expression p × Variable))
    (constraints : List (Expression p))
    (hall : ∀ d ∈ defs, defWitnessed constraints d = true)
    (env : Variable → ZMod p) (hzero : ∀ c ∈ constraints, c.eval env = 0) :
    ∀ e : Expression p, (canonRw defs e).eval env = e.eval env := by
  intro e
  unfold canonRw
  cases hf : defs.find? (fun d => decide (d.1 = e)) with
  | none => rfl
  | some d =>
    have hmem : d ∈ defs := List.mem_of_find?_eq_some hf
    have hde : d.1 = e := by have := List.find?_some hf; simpa using this
    have hval := defWitnessed_eval constraints d (hall d hmem) env hzero
    show (Expression.var d.2).eval env = e.eval env
    rw [Expression.eval, hval, hde]

/-- Every variable of a rewritten entry occurs in the original entry or is a defining variable. -/
theorem canonRw_vars (defs : List (Expression p × Variable)) (e : Expression p) :
    ∀ v ∈ (canonRw defs e).vars, v ∈ e.vars ∨ ∃ d ∈ defs, v = d.2 := by
  intro v hv
  unfold canonRw at hv
  cases hf : defs.find? (fun d => decide (d.1 = e)) with
  | none => rw [hf] at hv; exact Or.inl hv
  | some d =>
    rw [hf] at hv
    simp only [Expression.vars, List.mem_singleton] at hv
    exact Or.inr ⟨d, List.mem_of_find?_eq_some hf, hv⟩

/-! ## The rewritten system -/

/-- Apply `g` to every payload entry of a bus interaction (multiplicity untouched). -/
def BusInteraction.mapPayload (bi : BusInteraction (Expression p))
    (g : Expression p → Expression p) : BusInteraction (Expression p) :=
  { busId := bi.busId, multiplicity := bi.multiplicity, payload := bi.payload.map g }

/-- Rewrite every payload entry of every bus interaction; constraints untouched. -/
def ConstraintSystem.mapPayload (cs : ConstraintSystem p)
    (g : Expression p → Expression p) : ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints,
    busInteractions := cs.busInteractions.map (·.mapPayload g) }

section EnvFixed

variable {g : Expression p → Expression p} {env : Variable → ZMod p}
  (hg : ∀ e : Expression p, (g e).eval env = e.eval env)

include hg

/-- Under an eval-preserving-at-`env` rewrite, evaluated messages are unchanged. -/
theorem BusInteraction.eval_mapPayload (bi : BusInteraction (Expression p)) :
    (bi.mapPayload g).eval env = bi.eval env := by
  simp only [BusInteraction.mapPayload, BusInteraction.eval, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, hg]

theorem ConstraintSystem.satisfies_mapPayload (cs : ConstraintSystem p) (bs : BusSemantics p) :
    (cs.mapPayload g).satisfies bs env ↔ cs.satisfies bs env := by
  simp only [ConstraintSystem.satisfies, ConstraintSystem.mapPayload]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨hc, fun bi0 hbi0 => ?_⟩
    have := hb _ (List.mem_map.2 ⟨bi0, hbi0, rfl⟩)
    rwa [bi0.eval_mapPayload hg] at this
  · rintro ⟨hc, hb⟩
    refine ⟨hc, fun bi hbi => ?_⟩
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
    rw [bi0.eval_mapPayload hg]
    exact hb bi0 hbi0

theorem ConstraintSystem.sideEffects_mapPayload (cs : ConstraintSystem p) (bs : BusSemantics p) :
    (cs.mapPayload g).sideEffects bs env = cs.sideEffects bs env := by
  simp only [ConstraintSystem.sideEffects, ConstraintSystem.mapPayload]
  induction cs.busInteractions with
  | nil => rfl
  | cons bi rest ih =>
    simp only [List.map_cons, List.filter_cons]
    have hbus : bs.isStateful (bi.mapPayload g).busId = bs.isStateful bi.busId := rfl
    rw [hbus]
    by_cases hstate : bs.isStateful bi.busId = true
    · simp only [if_pos hstate, List.map_cons, ih, bi.eval_mapPayload hg]
    · simp only [if_neg hstate, ih]

theorem ConstraintSystem.admissible_mapPayload (cs : ConstraintSystem p) (bs : BusSemantics p) :
    (cs.mapPayload g).admissible bs env ↔ cs.admissible bs env := by
  unfold ConstraintSystem.admissible
  have hmap : (cs.mapPayload g).busInteractions.map (fun bi => bi.eval env)
      = cs.busInteractions.map (fun bi => bi.eval env) := by
    simp only [ConstraintSystem.mapPayload, List.map_map]
    exact List.map_congr_left (fun bi _ => bi.eval_mapPayload hg)
  rw [hmap]

end EnvFixed

/-! ## Correctness -/

theorem payloadCanon_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (defs : List (Expression p × Variable))
    (hall : defs.all (defWitnessed cs.algebraicConstraints) = true) :
    PassCorrect cs (cs.mapPayload (canonRw defs)) [] bs := by
  have hallmem : ∀ d ∈ defs, defWitnessed cs.algebraicConstraints d = true :=
    fun d hd => List.all_eq_true.mp hall d hd
  -- the rewritten system keeps the constraints, definitionally
  have hcsame : (cs.mapPayload (canonRw defs)).algebraicConstraints
      = cs.algebraicConstraints := rfl
  refine PassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  · -- soundness: the same environment satisfies the input
    intro env hsat
    have hzero : ∀ c ∈ cs.algebraicConstraints, c.eval env = 0 := fun c hc =>
      hsat.1 c (by rw [hcsame]; exact hc)
    have hg := canonRw_eval defs cs.algebraicConstraints hallmem env hzero
    exact ⟨env, (cs.satisfies_mapPayload hg bs).1 hsat,
      by rw [cs.sideEffects_mapPayload hg bs]; exact BusState.equiv_refl _⟩
  · -- invariant preservation
    intro hinv env hsat bi hbi
    have hzero : ∀ c ∈ cs.algebraicConstraints, c.eval env = 0 := fun c hc =>
      hsat.1 c (by rw [hcsame]; exact hc)
    have hg := canonRw_eval defs cs.algebraicConstraints hallmem env hzero
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
    have h := hinv env ((cs.satisfies_mapPayload hg bs).1 hsat) bi0 hbi0
    simpa only [bi0.eval_mapPayload hg] using h
  · -- no new variables
    intro v hv
    rw [ConstraintSystem.mem_vars] at hv
    rcases hv with ⟨c, hc, hxc⟩ | ⟨bi, hbi, hxbi⟩
    · exact ConstraintSystem.mem_vars_of_constraint hc hxc
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      rcases hxbi with hm | ⟨e, he, hxe⟩
      · exact ConstraintSystem.mem_vars_of_mult hbi0 hm
      · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
        rcases canonRw_vars defs e0 v hxe with h | ⟨d, hd, rfl⟩
        · exact ConstraintSystem.mem_vars_of_payload hbi0 he0 h
        · exact defWitnessed_var_mem cs d (hallmem d hd)
  · -- completeness: the same environment satisfies the output
    intro env hadm hsat
    have hg := canonRw_eval defs cs.algebraicConstraints hallmem env hsat.1
    exact ⟨(cs.satisfies_mapPayload hg bs).2 hsat,
      (cs.admissible_mapPayload hg bs).2 hadm,
      by rw [cs.sideEffects_mapPayload hg bs]; exact BusState.equiv_refl _⟩

/-! ## The pass -/

/-- Canonicalize bus payload entries to their defining variables. The rewrite map is rebuilt
    from the current constraints on each invocation; entries that are already atomic are never
    keys, so every rewrite strictly shrinks payload AST size and the pass is trivially a no-op
    at its own fixpoint. -/
def payloadCanonPass : VerifiedPass p := fun cs bs =>
  let defs := (cs.algebraicConstraints.filterMap defPattern?).filter
    (fun d => !d.1.isAtomic)
  if defs.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
  else if hall : defs.all (defWitnessed cs.algebraicConstraints) = true then
    ⟨cs.mapPayload (canonRw defs), [], payloadCanon_correct cs bs defs hall⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
