import ApcOptimizer.Implementation.OptimizerPasses.Reencode

set_option autoImplicit false

/-! # Domain-constant subexpression folding

A powdr-style simplification, split off from the re-encoder's constant-emission logic (see
`Reencode.interpOf`): if a *wholly-in-group* subexpression takes the **same value on every
surviving joint assignment** of a small variable group, replace it by that constant — *without*
introducing bits, dropping the group, or otherwise touching the group's variables.

The canonical instance is OpenVM's destination-register write address `52 − flag_poly`: a degree-2
polynomial in the load/store variant flags that is identically `52` on the flags' constrained
domain. `busUnify`/`addrConstsNeq` only prove two accesses differ when *both* address offsets are
syntactic constants, so the symbolic offset blocks chaining the source-register reads across it;
folding it to `52` unblocks the chain (exactly what powdr's range/domain simplification does, and
what the re-encoder currently achieves only as a side effect of compressing the flags into bits).

Correctness is a pure rewrite (`PassCorrect.ofEnvEq`, `env' = env`, no new variables, no
derivations): every folded subexpression `e` satisfies `e − c = 0` on the group's covered
constraints, which are kept **verbatim** in the output — so any assignment satisfying the output
pins the group to a survivor, under which the rewrite agrees with the identity. The
domain-enumeration certificate (`groupDoms`/`groupSurvivors`) is shared with the re-encoder;
requires prime `p` (for `groupDoms_sound`), gated at runtime like the domain passes. -/

variable {p : ℕ}

/-! ## The domain-constant check -/

/-- `some c` if `e` evaluates to the same constant `c` on every survivor, else `none`.

    Two output-preserving speedups over the naive `e.eval (envOf s) = e.eval (envOf s₀)` form
    (both extensionally equal, so the fold decision and the folded constant are unchanged):
    evaluate through `Expression.evalFast` (field operations derived once per call rather than per
    expression node, `evalFast_eq` — the entry-54 treatment the rest of the pass already uses), and
    compute the reference value `e.evalFast (envOf s₀)` **once** with a `let` instead of
    re-evaluating it against every survivor inside the `.all`. -/
def constOnSurvs (survs : List (List (Variable × ZMod p))) (e : Expression p) : Option (ZMod p) :=
  match survs with
  | [] => none
  | s₀ :: rest =>
    let v₀ := e.evalFast (envOf s₀)
    if (s₀ :: rest).all (fun s => decide (e.evalFast (envOf s) = v₀)) then
      some v₀
    else none

/-- If `constOnSurvs` accepts `e` with value `c`, then `e` evaluates to `c` on every survivor. -/
theorem constOnSurvs_sound (survs : List (List (Variable × ZMod p))) (e : Expression p)
    (c : ZMod p) (h : constOnSurvs survs e = some c) : ∀ s ∈ survs, e.eval (envOf s) = c := by
  intro s hs
  cases survs with
  | nil => exact absurd hs (by simp)
  | cons s₀ rest =>
    simp only [constOnSurvs] at h
    split at h
    · next hall =>
        have hc : e.evalFast (envOf s₀) = c := Option.some.inj h
        have hthis := List.all_eq_true.mp hall s hs
        rw [decide_eq_true_iff] at hthis
        rw [← Expression.evalFast_eq, hthis]; exact hc
    · next => exact absurd h (by simp)

/-- Does the expression mention any variable of `xs`? (No allocation.) -/
def Expression.anyVarIn (xs : List Variable) : Expression p → Bool
  | .const _ => false
  | .var y => containsFast xs y
  | .add a b => a.anyVarIn xs || b.anyVarIn xs
  | .mul a b => a.anyVarIn xs || b.anyVarIn xs

/-- `anyVarIn` finds a genuinely shared variable. -/
theorem Expression.anyVarIn_exists {xs : List Variable} {e : Expression p}
    (h : e.anyVarIn xs = true) : ∃ v ∈ e.vars, v ∈ xs := by
  induction e with
  | const c => simp [Expression.anyVarIn] at h
  | var y =>
    rw [Expression.anyVarIn, containsFast_eq] at h
    exact ⟨y, by simp [Expression.vars], by simpa using h⟩
  | add a b iha ihb =>
    rw [Expression.anyVarIn, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨v, hv, hx⟩ := iha h
      exact ⟨v, by rw [Expression.vars]; exact List.mem_append_left _ hv, hx⟩
    · obtain ⟨v, hv, hx⟩ := ihb h
      exact ⟨v, by rw [Expression.vars]; exact List.mem_append_right _ hv, hx⟩
  | mul a b iha ihb =>
    rw [Expression.anyVarIn, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨v, hv, hx⟩ := iha h
      exact ⟨v, by rw [Expression.vars]; exact List.mem_append_left _ hv, hx⟩
    · obtain ⟨v, hv, hx⟩ := ihb h
      exact ⟨v, by rw [Expression.vars]; exact List.mem_append_right _ hv, hx⟩

/-! ## The fold rewrite -/

/-- The recursive fold core: replace every maximal wholly-in-group subexpression that is constant
    on the survivors by that constant; recurse otherwise. Leaves the group's variables in place
    where they are not folded. -/
def foldRewriteGo (xs : List Variable) (survs : List (List (Variable × ZMod p))) :
    Expression p → Expression p
  | .const c => .const c
  | .var y => .var y
  | .add a b =>
      if (Expression.add a b).varsIn xs then
        match constOnSurvs survs (.add a b) with
        | some c => .const c
        | none => .add (foldRewriteGo xs survs a) (foldRewriteGo xs survs b)
      else .add (foldRewriteGo xs survs a) (foldRewriteGo xs survs b)
  | .mul a b =>
      if (Expression.mul a b).varsIn xs then
        match constOnSurvs survs (.mul a b) with
        | some c => .const c
        | none => .mul (foldRewriteGo xs survs a) (foldRewriteGo xs survs b)
      else .mul (foldRewriteGo xs survs a) (foldRewriteGo xs survs b)

/-- The fold rewrite, gated: an expression sharing no variable with the group is returned
    untouched (as the *same* object — the identity `foldRewrite_eq_self` is what lets the
    index-side `foldOutIdx` skip such expressions without even reaching them). A shared-variable
    expression is walked by the core, which folds every maximal wholly-in-group subexpression —
    including variable-free compound nodes it contains (`varsIn` is vacuous there); purely
    variable-free *items* are left to the constant-fold pass. -/
def foldRewrite (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (e : Expression p) : Expression p :=
  if e.anyVarIn xs then foldRewriteGo xs survs e else e

/-- `foldRewrite` is (definitionally) the identity on an expression sharing no variable with the
    group — the fact that lets the sparse `foldOutIdx` pass untouched items through by position. -/
theorem foldRewrite_eq_self {xs : List Variable} {survs : List (List (Variable × ZMod p))}
    {e : Expression p} (h : e.anyVarIn xs = false) : foldRewrite xs survs e = e := by
  rw [foldRewrite, h]; rfl

/-- Does the expression contain a variable-free `add`/`mul` node? For an expression sharing no
    variable with the group, `hasFoldable` holds iff this does (given a nonempty survivor set). -/
def Expression.hasConstFoldableNode : Expression p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b =>
      !(Expression.add a b).hasVar || a.hasConstFoldableNode || b.hasConstFoldableNode
  | .mul a b =>
      !(Expression.mul a b).hasVar || a.hasConstFoldableNode || b.hasConstFoldableNode

/-- The direct (unindexed) path's fold rewrite — the historical gate: an expression sharing no
    variable with the group *and* containing no variable-free compound node has no node the core
    could fold (a qualifying node is either wholly-in-group with a variable — impossible — or
    variable-free), so it is returned untouched without walking it node-by-node. Kept exactly as
    it always was so the direct path (systems below `domainFoldIndexThreshold`, i.e. everything
    but the keccak/SHA-scale stress cases) is bit-for-bit unchanged; the indexed path uses the
    `anyVarIn`-gated `foldRewrite`, whose identity-off-index property the sparse fold needs. -/
def foldRewriteC (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (e : Expression p) : Expression p :=
  if e.anyVarIn xs || e.hasConstFoldableNode then foldRewriteGo xs survs e else e

/-! ## Agreement with the identity on any survivor-matching environment -/

/-- On an environment that agrees on `xs` with some survivor `s`, `foldRewrite` is
    evaluation-preserving. The folded constants are exactly the survivor-constant values, and `s`'s
    membership pins them; unfolded nodes recurse. -/
theorem foldRewriteGo_agree (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (env : Variable → ZMod p) (s : List (Variable × ZMod p)) (hs : s ∈ survs)
    (hxs : ∀ x ∈ xs, env x = envOf s x) :
    ∀ e : Expression p, (foldRewriteGo xs survs e).eval env = e.eval env := by
  -- For a wholly-in-`xs` expression, `env` and `envOf s` agree on its variables.
  have hcongr : ∀ e : Expression p, e.varsIn xs = true → e.eval env = e.eval (envOf s) := by
    intro e he
    exact Expression.eval_congr e _ _ (fun x hx => hxs x (Expression.varsIn_sound xs e he x hx))
  intro e
  induction e with
  | const c => rfl
  | var y => rfl
  | add a b iha ihb =>
      unfold foldRewriteGo
      by_cases hin : (Expression.add a b).varsIn xs = true
      · rw [if_pos hin]
        cases hc : constOnSurvs survs (.add a b) with
        | none =>
            show (foldRewriteGo xs survs a).eval env + (foldRewriteGo xs survs b).eval env
              = a.eval env + b.eval env
            rw [iha, ihb]
        | some c =>
            show (Expression.const c).eval env = a.eval env + b.eval env
            have h1 : (Expression.add a b).eval env = (Expression.add a b).eval (envOf s) := hcongr _ hin
            have h2 := constOnSurvs_sound survs (.add a b) c hc s hs
            show c = a.eval env + b.eval env
            have : (Expression.add a b).eval env = c := by rw [h1]; exact h2
            simpa [Expression.eval] using this.symm
      · rw [if_neg (by simpa using hin)]
        show (foldRewriteGo xs survs a).eval env + (foldRewriteGo xs survs b).eval env
          = a.eval env + b.eval env
        rw [iha, ihb]
  | mul a b iha ihb =>
      unfold foldRewriteGo
      by_cases hin : (Expression.mul a b).varsIn xs = true
      · rw [if_pos hin]
        cases hc : constOnSurvs survs (.mul a b) with
        | none =>
            show (foldRewriteGo xs survs a).eval env * (foldRewriteGo xs survs b).eval env
              = a.eval env * b.eval env
            rw [iha, ihb]
        | some c =>
            show (Expression.const c).eval env = a.eval env * b.eval env
            have h1 : (Expression.mul a b).eval env = (Expression.mul a b).eval (envOf s) := hcongr _ hin
            have h2 := constOnSurvs_sound survs (.mul a b) c hc s hs
            show c = a.eval env * b.eval env
            have : (Expression.mul a b).eval env = c := by rw [h1]; exact h2
            simpa [Expression.eval] using this.symm
      · rw [if_neg (by simpa using hin)]
        show (foldRewriteGo xs survs a).eval env * (foldRewriteGo xs survs b).eval env
          = a.eval env * b.eval env
        rw [iha, ihb]

/-- On an environment that agrees on `xs` with some survivor, the (gated) fold rewrite is
    evaluation-preserving. -/
theorem foldRewrite_agree (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (env : Variable → ZMod p) (s : List (Variable × ZMod p)) (hs : s ∈ survs)
    (hxs : ∀ x ∈ xs, env x = envOf s x) :
    ∀ e : Expression p, (foldRewrite xs survs e).eval env = e.eval env := by
  intro e
  unfold foldRewrite
  split
  · exact foldRewriteGo_agree xs survs env s hs hxs e
  · rfl

/-- `foldRewrite_agree` for the direct path's `foldRewriteC` (same split on the gate). -/
theorem foldRewriteC_agree (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (env : Variable → ZMod p) (s : List (Variable × ZMod p)) (hs : s ∈ survs)
    (hxs : ∀ x ∈ xs, env x = envOf s x) :
    ∀ e : Expression p, (foldRewriteC xs survs e).eval env = e.eval env := by
  intro e
  unfold foldRewriteC
  split
  · exact foldRewriteGo_agree xs survs env s hs hxs e
  · rfl

/-- Bus-interaction-level agreement, from any expression-level agreement `hag`, applied to the
    multiplicity and every payload slot. -/
theorem mapExpr_eval_of_agree (g : Expression p → Expression p) (env : Variable → ZMod p)
    (hag : ∀ e : Expression p, (g e).eval env = e.eval env) (bi : BusInteraction (Expression p)) :
    (bi.mapExpr g).eval env = bi.eval env := by
  show BusInteraction.eval
    { busId := bi.busId, multiplicity := g bi.multiplicity, payload := bi.payload.map g } env = _
  simp only [BusInteraction.eval, hag bi.multiplicity, List.map_map]
  congr 1
  exact List.map_congr_left (fun e _ => hag e)

/-! ## Variables of the rewrite -/

/-- Folding never introduces a variable: every variable of `foldRewriteGo … e` is a variable of `e`. -/
theorem foldRewriteGo_vars (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (e : Expression p) : ∀ v ∈ (foldRewriteGo xs survs e).vars, v ∈ e.vars := by
  induction e with
  | const c => intro v hv; simp [foldRewriteGo, Expression.vars] at hv
  | var y => intro v hv; exact hv
  | add a b iha ihb =>
      unfold foldRewriteGo
      by_cases hin : (Expression.add a b).varsIn xs = true
      · rw [if_pos hin]
        cases constOnSurvs survs (.add a b) with
        | none =>
            intro v hv
            simp only [Expression.vars, List.mem_append] at hv ⊢
            rcases hv with hv | hv
            · exact Or.inl (iha v hv)
            · exact Or.inr (ihb v hv)
        | some c => intro v hv; simp [Expression.vars] at hv
      · rw [if_neg (by simpa using hin)]
        intro v hv
        simp only [Expression.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · exact Or.inl (iha v hv)
        · exact Or.inr (ihb v hv)
  | mul a b iha ihb =>
      unfold foldRewriteGo
      by_cases hin : (Expression.mul a b).varsIn xs = true
      · rw [if_pos hin]
        cases constOnSurvs survs (.mul a b) with
        | none =>
            intro v hv
            simp only [Expression.vars, List.mem_append] at hv ⊢
            rcases hv with hv | hv
            · exact Or.inl (iha v hv)
            · exact Or.inr (ihb v hv)
        | some c => intro v hv; simp [Expression.vars] at hv
      · rw [if_neg (by simpa using hin)]
        intro v hv
        simp only [Expression.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · exact Or.inl (iha v hv)
        · exact Or.inr (ihb v hv)

/-- Folding never introduces a variable (gated form). -/
theorem foldRewrite_vars (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (e : Expression p) : ∀ v ∈ (foldRewrite xs survs e).vars, v ∈ e.vars := by
  intro v hv
  unfold foldRewrite at hv
  split at hv
  · exact foldRewriteGo_vars xs survs e v hv
  · exact hv

/-- `foldRewrite_vars` for the direct path's `foldRewriteC`. -/
theorem foldRewriteC_vars (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (e : Expression p) : ∀ v ∈ (foldRewriteC xs survs e).vars, v ∈ e.vars := by
  intro v hv
  unfold foldRewriteC at hv
  split at hv
  · exact foldRewriteGo_vars xs survs e v hv
  · exact hv

/-! ## Agreement on any environment satisfying the covered constraints

The survivors were enumerated over the group's constraint-derived domains and filtered by the
covered constraints, so any environment satisfying **all** the covered constraints pins the group
to one of the survivors — under which `foldRewrite` is the identity. -/

/-- If `env` satisfies every covered constraint, the group is pinned to a survivor `env` agrees
    with on `xs`. Prime `p` (for `groupDoms_sound`). Shared by both rewrites' covered-agreement
    lemmas. -/
theorem groupSurvivors_mem_agree [Fact p.Prime] (cs : ConstraintSystem p) (xs : List Variable)
    (doms : List (Variable × List (ZMod p)))
    (hdoms : groupDoms (coveredCsOf cs xs) xs = some doms)
    (env : Variable → ZMod p) (hcov : ∀ c ∈ coveredCsOf cs xs, c.eval env = 0) :
    ∃ s ∈ groupSurvivors cs xs doms, ∀ x ∈ xs, env x = envOf s x := by
  have hkeys : doms.map Prod.fst = xs := groupDoms_fst (coveredCsOf cs xs) xs doms hdoms
  have hmemdoms : ∀ yd ∈ doms, env yd.1 ∈ yd.2 :=
    groupDoms_sound (coveredCsOf cs xs) xs doms hdoms env hcov
  set s := doms.map (fun yd => (yd.1, env yd.1)) with hs_def
  have hsassign : s ∈ assignments doms := mem_assignments doms env hmemdoms
  have hagree : ∀ x ∈ xs, env x = envOf s x := by
    intro x hx
    rw [hs_def, envOf_map doms env x (by rw [hkeys]; exact hx)]
  have hsurv : s ∈ groupSurvivors cs xs doms := by
    simp only [groupSurvivors, groupSurvivorsE_eq, List.mem_filter]
    refine ⟨hsassign, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    rw [decide_eq_true_iff, Expression.evalFast_eq]
    have hcvin : c.varsIn xs = true := by
      have hcb : coveredBy xs c = true := (List.mem_filter.mp hc).2
      rw [coveredBy, Bool.and_eq_true] at hcb
      exact Expression.varsInF_eq xs c ▸ hcb.2
    have heq : c.eval (envOf s) = c.eval env :=
      Expression.eval_congr c _ _
        (fun x hx => (hagree x (Expression.varsIn_sound xs c hcvin x hx)).symm)
    rw [heq]; exact hcov c hc
  exact ⟨s, hsurv, hagree⟩

/-- If `env` satisfies every covered constraint, `foldRewrite` (over the survivors of those
    constraints) is evaluation-preserving on `env`. -/
theorem foldRewrite_agree_covered [Fact p.Prime] (cs : ConstraintSystem p) (xs : List Variable)
    (doms : List (Variable × List (ZMod p)))
    (hdoms : groupDoms (coveredCsOf cs xs) xs = some doms)
    (env : Variable → ZMod p) (hcov : ∀ c ∈ coveredCsOf cs xs, c.eval env = 0) :
    ∀ e : Expression p, (foldRewrite xs (groupSurvivors cs xs doms) e).eval env = e.eval env := by
  obtain ⟨s, hsurv, hagree⟩ := groupSurvivors_mem_agree cs xs doms hdoms env hcov
  intro e
  exact foldRewrite_agree xs (groupSurvivors cs xs doms) env s hsurv hagree e

/-- `foldRewrite_agree_covered` for the direct path's `foldRewriteC`. -/
theorem foldRewriteC_agree_covered [Fact p.Prime] (cs : ConstraintSystem p) (xs : List Variable)
    (doms : List (Variable × List (ZMod p)))
    (hdoms : groupDoms (coveredCsOf cs xs) xs = some doms)
    (env : Variable → ZMod p) (hcov : ∀ c ∈ coveredCsOf cs xs, c.eval env = 0) :
    ∀ e : Expression p, (foldRewriteC xs (groupSurvivors cs xs doms) e).eval env = e.eval env := by
  obtain ⟨s, hsurv, hagree⟩ := groupSurvivors_mem_agree cs xs doms hdoms env hcov
  intro e
  exact foldRewriteC_agree xs (groupSurvivors cs xs doms) env s hsurv hagree e

/-! ## The folded output -/

/-- Fold every non-covered constraint and every bus interaction **in place**; keep the covered
    (domain-pinning) constraints verbatim, also in place (folding them would collapse them and
    lose the domain pin). Order- and length-preserving by construction — positions never move and
    rewrites only ever shrink an expression's variable set — which is what lets the pass keep its
    inverted index across accepted folds instead of rebuilding it (`FoldIdx.refresh`). -/
def foldOut (cs : ConstraintSystem p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) : ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints.map
      (fun c => if coveredBy xs c then c else foldRewrite xs survs c),
    busInteractions := cs.busInteractions.map (·.mapExpr (foldRewrite xs survs)) }

/-- Under an agreeing `env`, the folded system's evaluated stateful side effects are the input's. -/
theorem foldOut_sideEffects_eq (cs : ConstraintSystem p) (bs : BusSemantics p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) (env : Variable → ZMod p)
    (hag : ∀ e : Expression p, (foldRewrite xs survs e).eval env = e.eval env) :
    (foldOut cs xs survs).sideEffects bs env = cs.sideEffects bs env := by
  show ((cs.busInteractions.map (·.mapExpr (foldRewrite xs survs))).filter
      (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity)) = _
  rw [List.filter_map]
  rw [List.filter_congr (fun bi _ => (rfl :
    ((fun b : BusInteraction (Expression p) => bs.isStateful b.busId) ∘
      (fun b => b.mapExpr (foldRewrite xs survs))) bi = bs.isStateful bi.busId))]
  rw [List.map_map]
  exact List.map_congr_left (fun bi _ => by
    simp only [Function.comp_apply, mapExpr_eval_of_agree _ env hag bi])

/-- Under an agreeing `env`, the folded system is admissible iff the input is. -/
theorem foldOut_admissible_iff (cs : ConstraintSystem p) (bs : BusSemantics p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) (env : Variable → ZMod p)
    (hag : ∀ e : Expression p, (foldRewrite xs survs e).eval env = e.eval env) :
    (foldOut cs xs survs).admissible bs env ↔ cs.admissible bs env := by
  unfold ConstraintSystem.admissible
  have hmsg : (foldOut cs xs survs).busInteractions.map (fun bi => bi.eval env)
      = cs.busInteractions.map (fun bi => bi.eval env) := by
    show (cs.busInteractions.map (·.mapExpr (foldRewrite xs survs))).map (fun bi => bi.eval env) = _
    rw [List.map_map]
    exact List.map_congr_left (fun bi _ => mapExpr_eval_of_agree _ env hag bi)
  rw [hmsg]

/-- Folding introduces no variable. -/
theorem foldOut_vars_subset (cs : ConstraintSystem p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) :
    ∀ v ∈ (foldOut cs xs survs).vars, v ∈ cs.vars := by
  intro v hv
  rcases ConstraintSystem.mem_vars.1 hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · simp only [foldOut, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    by_cases hcov : coveredBy xs c0 = true
    · rw [if_pos hcov] at hcv
      exact ConstraintSystem.mem_vars_of_constraint hc0 hcv
    · rw [if_neg hcov] at hcv
      exact ConstraintSystem.mem_vars_of_constraint hc0 (foldRewrite_vars xs survs c0 v hcv)
  · simp only [foldOut, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    rcases hbiv with hmv | ⟨e, he, hev⟩
    · exact ConstraintSystem.mem_vars_of_mult hbi0
        (foldRewrite_vars xs survs bi0.multiplicity v hmv)
    · simp only [BusInteraction.mapExpr] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact ConstraintSystem.mem_vars_of_payload hbi0 he0 (foldRewrite_vars xs survs e0 v hev)

/-- Under an agreeing `env`, the folded system is satisfied iff the input is: every constraint of
    either side is (the rewrite of) a constraint of the other, and the rewrite is
    evaluation-preserving on `env`. -/
theorem foldOut_satisfies_iff (cs : ConstraintSystem p) (bs : BusSemantics p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) (env : Variable → ZMod p)
    (hag : ∀ e : Expression p, (foldRewrite xs survs e).eval env = e.eval env) :
    (foldOut cs xs survs).satisfies bs env ↔ cs.satisfies bs env := by
  have hceval : ∀ c : Expression p,
      (if coveredBy xs c then c else foldRewrite xs survs c).eval env = c.eval env := by
    intro c
    by_cases hcov : coveredBy xs c = true
    · rw [if_pos hcov]
    · rw [if_neg hcov]; exact hag c
  constructor
  · intro hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · have := hsat.1 _ (List.mem_map.2 ⟨c, hc, rfl⟩ :
        (if coveredBy xs c then c else foldRewrite xs survs c)
          ∈ (foldOut cs xs survs).algebraicConstraints)
      rwa [hceval c] at this
    · have := hsat.2 _ (List.mem_map.2 ⟨bi, hbi, rfl⟩ :
        bi.mapExpr (foldRewrite xs survs) ∈ (foldOut cs xs survs).busInteractions)
      rwa [mapExpr_eval_of_agree _ env hag bi] at this
  · intro hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · simp only [foldOut, List.mem_map] at hc
      obtain ⟨c0, hc0, rfl⟩ := hc
      rw [hceval c0]
      exact hsat.1 c0 hc0
    · simp only [foldOut, List.mem_map] at hbi
      obtain ⟨bi0, hbi0, rfl⟩ := hbi
      show ((bi0.mapExpr (foldRewrite xs survs)).eval env).multiplicity ≠ 0 →
        bs.violatesConstraint ((bi0.mapExpr (foldRewrite xs survs)).eval env) = false
      rw [mapExpr_eval_of_agree _ env hag bi0]
      exact hsat.2 bi0 hbi0

/-- **Correctness of one fold.** The folded system refines the input and preserves invariants, with
    the identity witness (`ofEnvEq`): the covered constraints, kept verbatim (in place), pin the
    group so the rewrite agrees with the identity on every assignment satisfying either system. -/
theorem foldOut_correct [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (hdoms : groupDoms (coveredCsOf cs xs) xs = some doms) :
    PassCorrect cs (foldOut cs xs (groupSurvivors cs xs doms)) [] bs := by
  set survs := groupSurvivors cs xs doms with hsurv_def
  -- covered constraints are satisfied by any assignment of the output (kept verbatim, in place)
  -- or the input.
  have hcov_out : ∀ env, (foldOut cs xs survs).satisfies bs env →
      ∀ c ∈ coveredCsOf cs xs, c.eval env = 0 := by
    intro env hsat c hc
    have hcb : coveredBy xs c = true := (List.mem_filter.mp hc).2
    have hmem : c ∈ (foldOut cs xs survs).algebraicConstraints := by
      have hm : (if coveredBy xs c then c else foldRewrite xs survs c)
          ∈ (foldOut cs xs survs).algebraicConstraints :=
        List.mem_map.2 ⟨c, List.mem_of_mem_filter hc, rfl⟩
      rwa [if_pos hcb] at hm
    exact hsat.1 c hmem
  have hcov_cs : ∀ env, cs.satisfies bs env → ∀ c ∈ coveredCsOf cs xs, c.eval env = 0 :=
    fun env hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  refine PassCorrect.ofEnvEq ?hsound ?hinv ?hsub ?hcomp
  case hsub => exact foldOut_vars_subset cs xs survs
  case hsound =>
    intro env hsatout
    have hag := foldRewrite_agree_covered cs xs doms hdoms env (hcov_out env hsatout)
    exact ⟨env, (foldOut_satisfies_iff cs bs xs survs env hag).1 hsatout,
      by rw [foldOut_sideEffects_eq cs bs xs survs env hag]; exact BusState.equiv_refl _⟩
  case hinv =>
    intro hinv env hsatout bi' hbi'
    have hag := foldRewrite_agree_covered cs xs doms hdoms env (hcov_out env hsatout)
    have hsatcs : cs.satisfies bs env :=
      (foldOut_satisfies_iff cs bs xs survs env hag).1 hsatout
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    rw [mapExpr_eval_of_agree (foldRewrite xs survs) env hag bi0]
    exact hinv env hsatcs bi0 hbi0
  case hcomp =>
    intro env hadm hsat
    have hag := foldRewrite_agree_covered cs xs doms hdoms env (hcov_cs env hsat)
    exact ⟨(foldOut_satisfies_iff cs bs xs survs env hag).2 hsat,
      (foldOut_admissible_iff cs bs xs survs env hag).2 hadm,
      by rw [foldOut_sideEffects_eq cs bs xs survs env hag]; exact BusState.equiv_refl _⟩

/-! ## The direct path's folded output (historical, reordering)

The direct (unindexed) path keeps the historical fold verbatim — `foldRewriteC`'s gate and the
rewritten-uncovered ++ covered-verbatim output shape — so systems below
`domainFoldIndexThreshold` (everything but keccak/SHA-scale) produce bit-for-bit the output they
always did. Only the indexed path, where the reorder would invalidate the persistent index's
positions, uses the order-preserving `foldOut`. -/

/-- The historical fold output: rewritten non-covered constraints first, covered constraints
    verbatim at the end. -/
def foldOutC (cs : ConstraintSystem p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) : ConstraintSystem p :=
  { algebraicConstraints :=
      (cs.algebraicConstraints.filter (fun c => !coveredBy xs c)).map (foldRewriteC xs survs)
        ++ coveredCsOf cs xs,
    busInteractions := cs.busInteractions.map (·.mapExpr (foldRewriteC xs survs)) }

/-- Under an agreeing `env`, the folded system's evaluated stateful side effects are the input's. -/
theorem foldOutC_sideEffects_eq (cs : ConstraintSystem p) (bs : BusSemantics p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) (env : Variable → ZMod p)
    (hag : ∀ e : Expression p, (foldRewriteC xs survs e).eval env = e.eval env) :
    (foldOutC cs xs survs).sideEffects bs env = cs.sideEffects bs env := by
  show ((cs.busInteractions.map (·.mapExpr (foldRewriteC xs survs))).filter
      (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity)) = _
  rw [List.filter_map]
  rw [List.filter_congr (fun bi _ => (rfl :
    ((fun b : BusInteraction (Expression p) => bs.isStateful b.busId) ∘
      (fun b => b.mapExpr (foldRewriteC xs survs))) bi = bs.isStateful bi.busId))]
  rw [List.map_map]
  exact List.map_congr_left (fun bi _ => by
    simp only [Function.comp_apply, mapExpr_eval_of_agree _ env hag bi])

/-- Under an agreeing `env`, the folded system is admissible iff the input is. -/
theorem foldOutC_admissible_iff (cs : ConstraintSystem p) (bs : BusSemantics p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) (env : Variable → ZMod p)
    (hag : ∀ e : Expression p, (foldRewriteC xs survs e).eval env = e.eval env) :
    (foldOutC cs xs survs).admissible bs env ↔ cs.admissible bs env := by
  unfold ConstraintSystem.admissible
  have hmsg : (foldOutC cs xs survs).busInteractions.map (fun bi => bi.eval env)
      = cs.busInteractions.map (fun bi => bi.eval env) := by
    show (cs.busInteractions.map (·.mapExpr (foldRewriteC xs survs))).map (fun bi => bi.eval env) = _
    rw [List.map_map]
    exact List.map_congr_left (fun bi _ => mapExpr_eval_of_agree _ env hag bi)
  rw [hmsg]

/-- Folding introduces no variable. -/
theorem foldOutC_vars_subset (cs : ConstraintSystem p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) :
    ∀ v ∈ (foldOutC cs xs survs).vars, v ∈ cs.vars := by
  intro v hv
  rcases ConstraintSystem.mem_vars.1 hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · simp only [foldOutC, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      exact ConstraintSystem.mem_vars_of_constraint (List.mem_of_mem_filter hc0)
        (foldRewriteC_vars xs survs c0 v hcv)
    · exact ConstraintSystem.mem_vars_of_constraint (List.mem_of_mem_filter hc) hcv
  · simp only [foldOutC, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    rcases hbiv with hmv | ⟨e, he, hev⟩
    · exact ConstraintSystem.mem_vars_of_mult hbi0
        (foldRewriteC_vars xs survs bi0.multiplicity v hmv)
    · simp only [BusInteraction.mapExpr] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact ConstraintSystem.mem_vars_of_payload hbi0 he0 (foldRewriteC_vars xs survs e0 v hev)

/-- **Correctness of one fold (direct path).** The folded system refines the input and preserves
    invariants, with the identity witness (`ofEnvEq`): the covered constraints, kept verbatim, pin
    the group so the rewrite agrees with the identity on every assignment satisfying either
    system. -/
theorem foldOutC_correct [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (hdoms : groupDoms (coveredCsOf cs xs) xs = some doms) :
    PassCorrect cs (foldOutC cs xs (groupSurvivors cs xs doms)) [] bs := by
  set survs := groupSurvivors cs xs doms with hsurv_def
  -- covered constraints are satisfied by any assignment of the output (kept verbatim) or the input.
  have hcov_out : ∀ env, (foldOutC cs xs survs).satisfies bs env →
      ∀ c ∈ coveredCsOf cs xs, c.eval env = 0 := by
    intro env hsat c hc
    exact hsat.1 c (by simp only [foldOutC, List.mem_append]; exact Or.inr hc)
  have hcov_cs : ∀ env, cs.satisfies bs env → ∀ c ∈ coveredCsOf cs xs, c.eval env = 0 :=
    fun env hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  refine PassCorrect.ofEnvEq ?hsound ?hinv ?hsub ?hcomp
  case hsub => exact foldOutC_vars_subset cs xs survs
  case hsound =>
    intro env hsatout
    have hag := foldRewriteC_agree_covered cs xs doms hdoms env (hcov_out env hsatout)
    refine ⟨env, ⟨?_, ?_⟩, ?_⟩
    · -- every cs constraint holds
      intro c hc
      by_cases hccov : coveredBy xs c = true
      · exact hcov_out env hsatout c (List.mem_filter.2 ⟨hc, hccov⟩)
      · have hmem : foldRewriteC xs survs c ∈ (foldOutC cs xs survs).algebraicConstraints := by
          simp only [foldOutC, List.mem_append]
          exact Or.inl (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hccov⟩, rfl⟩)
        have := hsatout.1 _ hmem
        rwa [hag c] at this
    · -- no cs bus interaction violates
      intro bi hbi
      have hmem : bi.mapExpr (foldRewriteC xs survs) ∈ (foldOutC cs xs survs).busInteractions :=
        List.mem_map.2 ⟨bi, hbi, rfl⟩
      have hval := mapExpr_eval_of_agree (foldRewriteC xs survs) env hag bi
      have := hsatout.2 _ hmem
      rw [hval] at this; exact this
    · rw [foldOutC_sideEffects_eq cs bs xs survs env hag]; exact BusState.equiv_refl _
  case hinv =>
    intro hinv env hsatout bi' hbi'
    have hag := foldRewriteC_agree_covered cs xs doms hdoms env (hcov_out env hsatout)
    -- env satisfies cs (soundness reasoning inlined)
    have hsatcs : cs.satisfies bs env := by
      refine ⟨?_, ?_⟩
      · intro c hc
        by_cases hccov : coveredBy xs c = true
        · exact hcov_out env hsatout c (List.mem_filter.2 ⟨hc, hccov⟩)
        · have hmem : foldRewriteC xs survs c ∈ (foldOutC cs xs survs).algebraicConstraints := by
            simp only [foldOutC, List.mem_append]
            exact Or.inl (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hccov⟩, rfl⟩)
          have := hsatout.1 _ hmem
          rwa [hag c] at this
      · intro bi hbi
        have hmem : bi.mapExpr (foldRewriteC xs survs) ∈ (foldOutC cs xs survs).busInteractions :=
          List.mem_map.2 ⟨bi, hbi, rfl⟩
        have hval := mapExpr_eval_of_agree (foldRewriteC xs survs) env hag bi
        have := hsatout.2 _ hmem
        rw [hval] at this; exact this
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    rw [mapExpr_eval_of_agree (foldRewriteC xs survs) env hag bi0]
    exact hinv env hsatcs bi0 hbi0
  case hcomp =>
    intro env hadm hsat
    have hag := foldRewriteC_agree_covered cs xs doms hdoms env (hcov_cs env hsat)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- every out constraint holds
      intro c hc
      simp only [foldOutC, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
        rw [hag c0]; exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hsat.1 c (List.mem_of_mem_filter hc)
    · -- no out bus interaction violates
      intro bi hbi
      obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      rw [mapExpr_eval_of_agree (foldRewriteC xs survs) env hag bi0]
      exact hsat.2 bi0 hbi0
    · exact (foldOutC_admissible_iff cs bs xs survs env hag).2 hadm
    · rw [foldOutC_sideEffects_eq cs bs xs survs env hag]; exact BusState.equiv_refl _

/-! ## The pass -/

/-- Whether any expression of the system has a maximal wholly-in-group subexpression that folds to a
    constant (so the fold is not a no-op). Purely an efficiency gate; correctness is unconditional. -/
def Expression.hasFoldable (xs : List Variable) (survs : List (List (Variable × ZMod p))) :
    Expression p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b =>
      ((Expression.add a b).varsIn xs && (constOnSurvs survs (.add a b)).isSome) ||
        Expression.hasFoldable xs survs a || Expression.hasFoldable xs survs b
  | .mul a b =>
      ((Expression.mul a b).varsIn xs && (constOnSurvs survs (.mul a b)).isSome) ||
        Expression.hasFoldable xs survs a || Expression.hasFoldable xs survs b

/-- Does the fold change anything in the system? The no-op gate of the direct (unindexed) path —
    the historical gate, verbatim — with the non-covered constraints (`rest = coveredBy`'s
    complement) precomputed by the caller: the direct path partitions the constraint list once
    per target, so the gate does not re-evaluate `coveredBy` per constraint. Purely an efficiency
    gate. -/
def systemHasFoldableW (cs : ConstraintSystem p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) (rest : List (Expression p)) : Bool :=
  rest.any (fun c => c.hasFoldable xs survs) ||
    cs.busInteractions.any (fun bi =>
      bi.multiplicity.hasFoldable xs survs || bi.payload.any (fun e => e.hasFoldable xs survs))

/-! ### The index-local gate

The full-system no-op scan decomposes exactly: `foldRewrite` only ever rewrites an expression
sharing a variable with the group `xs`, and every item sharing a variable with `xs` is (by bucket
completeness, `FoldIdx.hidx`/`hbis`) reachable through the inverted indexes. So the gate scans
only the bucketed candidate positions for `xs`, re-testing each against the current item arrays —
stale (superset) bucket entries cost a re-test, never a wrong answer. Purely an efficiency gate,
like `systemHasFoldableW`. -/

/-! ### Indexing the per-target covered-constraint scan

`foldStep` gates every target on `groupDoms (coveredCsOf cs xs) xs`, whose `coveredCsOf` is a full
`cs.algebraicConstraints.filter (coveredBy xs)` scan run **once per target** — an
O(#targets × #system) cost that dominates this pass on large circuits (the keccak stress case).
`domainBatch`/`reencode` (log 72) cut the same term with a variable→positions inverted index, but
consumed only the soundness-only `coveredIdx_mem`. Here the covered set is threaded into
`foldOut_correct`, whose statement pins it to `coveredCsOf cs xs` **exactly**, so we need the
genuine equality `coveredIdx … = coveredCsOf cs xs` (`CoveredIndex.coveredIdx_eq_filter`, valid
because a `coveredBy`-item always shares a variable with `xs`). The index is built once per pass
and rebuilt only on an accepted fold (`cs` changes), carrying the proofs tying it to the current
`cs` via `FoldIdx`. Effectiveness is bit-identical (the covered set is unchanged); only the scan is
faster. -/

/-- Per-item variable list with duplicates removed: the index build otherwise inserts one bucket
    entry per *occurrence* (and the per-target gathers then re-deduplicate them). Same membership,
    so bucket completeness is unchanged (`hashedEraseDups_eq` + `mem_eraseDups`). -/
def dedupVarsOf (c : Expression p) : List Variable :=
  HashedDedup.hashedEraseDups (hash ·) c.vars

/-- `dedupVarsOf` for interactions (multiplicity + payload occurrences). -/
def dedupBiVarsOf (bi : BusInteraction (Expression p)) : List Variable :=
  HashedDedup.hashedEraseDups (hash ·) bi.vars

/-- The prebuilt inverted indexes for the current `cs`, carried with **bucket-completeness
    invariants** rather than build-equalities: every item position is bucketed under each of its
    variables (`hidx` for constraints, `hbis` for interactions). Completeness is all any consumer
    needs — the covered-set equality (`coveredCsIdx_eq`, via
    `CoveredIndex.coveredIdx_eq_filter_of_complete`) and the sparse fold (`foldOutIdx_eq`) both
    re-check candidates at use, so *superset* (stale) buckets are harmless. That is the point:
    `foldOut` rewrites items in place and only ever shrinks variable sets, so completeness
    survives an accepted fold and `FoldIdx.refresh` keeps both bucket maps **without any
    rebuild**. -/
structure FoldIdx (cs : ConstraintSystem p) where
  idx : CoveredIndex.CovIndex
  /-- Constraint-side bucket completeness: position `i` is in the bucket of each variable of
      constraint `i`. (Buckets may also contain stale extras; consumers re-check.) -/
  hidx : ∀ (i : Nat) (hi : i < cs.algebraicConstraints.length),
    ∀ v ∈ cs.algebraicConstraints[i].vars, i ∈ idx.buckets.getD v []
  arr : Array (Expression p)
  harr : arr = cs.algebraicConstraints.toArray
  bisIdx : CoveredIndex.CovIndex
  /-- Interaction-side bucket completeness (multiplicity and payload variables). -/
  hbis : ∀ (i : Nat) (hi : i < cs.busInteractions.length),
    ∀ v ∈ (cs.busInteractions[i]).vars, i ∈ bisIdx.buckets.getD v []
  arrBis : Array (BusInteraction (Expression p))

/-- Build the indexes for a system: a fresh `build` is complete (`CoveredIndex.build_complete`;
    membership transports through the per-item dedup). -/
def FoldIdx.mk' (cs : ConstraintSystem p) : FoldIdx cs where
  idx := CoveredIndex.build dedupVarsOf cs.algebraicConstraints
  hidx := fun i hi v hv =>
    CoveredIndex.build_complete dedupVarsOf cs.algebraicConstraints i hi v (by
      rw [dedupVarsOf, HashedDedup.hashedEraseDups_eq]
      exact List.mem_eraseDups.2 hv)
  arr := cs.algebraicConstraints.toArray
  harr := rfl
  bisIdx := CoveredIndex.build dedupBiVarsOf cs.busInteractions
  hbis := fun i hi v hv =>
    CoveredIndex.build_complete dedupBiVarsOf cs.busInteractions i hi v (by
      rw [dedupBiVarsOf, HashedDedup.hashedEraseDups_eq]
      exact List.mem_eraseDups.2 hv)
  arrBis := cs.busInteractions.toArray

/-- A rewrite that introduces no variables per expression keeps an interaction's variables. -/
theorem mapExpr_vars_subset (g : Expression p → Expression p)
    (hg : ∀ (e : Expression p) (v : Variable), v ∈ (g e).vars → v ∈ e.vars)
    (bi : BusInteraction (Expression p)) : ∀ v ∈ (bi.mapExpr g).vars, v ∈ bi.vars := by
  intro v hv
  simp only [BusInteraction.mapExpr, BusInteraction.vars, List.mem_append,
    List.mem_flatMap] at hv ⊢
  rcases hv with hv | ⟨e, he, hv⟩
  · exact Or.inl (hg _ v hv)
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact Or.inr ⟨e0, he0, hg e0 v hv⟩

/-- Refresh the indexes after an accepted fold — **no rebuild**. `foldOut` rewrites items in
    place (order- and length-preserving) and only ever shrinks an expression's variable set
    (`foldRewrite_vars`), so both bucket maps stay complete exactly as they are; only the item
    arrays are re-materialized (O(n) pointer work). Stale bucket entries — positions whose item no
    longer mentions the variable — are harmless: every consumer re-checks candidates against the
    current arrays. The rewritten system is passed in as the already-computed value `ro` (with the
    proof it *is* the fold) so nothing is recomputed here. -/
def FoldIdx.refresh {cs : ConstraintSystem p} (old : FoldIdx cs) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) (ro : ConstraintSystem p)
    (hro : ro = foldOut cs xs survs) : FoldIdx ro where
  idx := old.idx
  hidx := fun i hi v hv => by
    subst hro
    have hlen : i < cs.algebraicConstraints.length := by
      simpa only [foldOut, List.length_map] using hi
    have hv' : v ∈ cs.algebraicConstraints[i].vars := by
      have hgm : (foldOut cs xs survs).algebraicConstraints[i]'hi
          = (if coveredBy xs (cs.algebraicConstraints[i]'hlen) then
              cs.algebraicConstraints[i]'hlen
             else foldRewrite xs survs (cs.algebraicConstraints[i]'hlen)) := by
        simp only [foldOut, List.getElem_map]
      rw [hgm] at hv
      by_cases hcov : coveredBy xs (cs.algebraicConstraints[i]'hlen) = true
      · rwa [if_pos hcov] at hv
      · rw [if_neg hcov] at hv
        exact foldRewrite_vars xs survs _ v hv
    exact old.hidx i hlen v hv'
  arr := ro.algebraicConstraints.toArray
  harr := rfl
  bisIdx := old.bisIdx
  hbis := fun i hi v hv => by
    subst hro
    have hlen : i < cs.busInteractions.length := by
      simpa only [foldOut, List.length_map] using hi
    have hv' : v ∈ (cs.busInteractions[i]'hlen).vars := by
      have hgm : (foldOut cs xs survs).busInteractions[i]'hi
          = (cs.busInteractions[i]'hlen).mapExpr (foldRewrite xs survs) := by
        simp only [foldOut, List.getElem_map]
      rw [hgm] at hv
      exact mapExpr_vars_subset _ (foldRewrite_vars xs survs) _ v hv
    exact old.hbis i hlen v hv'
  arrBis := ro.busInteractions.toArray

/-- The index-local no-op gate (see the section comment above): scan only the items sharing a
    variable with `xs` (through the inverted indexes, candidate positions deduplicated so an item
    sharing several variables is tested once — `hasFoldable` is the expensive part), re-testing
    each against the current arrays. Purely an efficiency gate, so no proof is carried. -/
def systemHasFoldableIdx {cs : ConstraintSystem p} (fidx : FoldIdx cs) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) : Bool :=
  (((xs.flatMap (fun v => fidx.idx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arr.size then
      let c := fidx.arr[i]
      !coveredBy xs c && c.hasFoldable xs survs
    else false)) ||
  (((xs.flatMap (fun v => fidx.bisIdx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arrBis.size then
      let bi := fidx.arrBis[i]
      bi.multiplicity.hasFoldable xs survs || bi.payload.any (fun e => e.hasFoldable xs survs)
    else false))

/-- An expression with any variable has a nonempty variable list. -/
theorem hasVar_vars_ne_nil (c : Expression p) (h : c.hasVar = true) : c.vars ≠ [] := by
  induction c with
  | const n => simp [Expression.hasVar] at h
  | var y => simp [Expression.vars]
  | add a b iha ihb =>
    intro hnil
    rw [Expression.vars, List.append_eq_nil_iff] at hnil
    simp only [Expression.hasVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact iha h hnil.1
    · exact ihb h hnil.2
  | mul a b iha ihb =>
    intro hnil
    rw [Expression.vars, List.append_eq_nil_iff] at hnil
    simp only [Expression.hasVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact iha h hnil.1
    · exact ihb h hnil.2

/-- A `coveredBy`-item shares a variable with the target `xs` (`hasVar` gives one variable;
    `varsInF` puts every one in `xs`) — the completeness hypothesis `coveredIdx_eq_filter` needs. -/
theorem coveredBy_shares_var (xs : List Variable) (c : Expression p) (h : coveredBy xs c = true) :
    ∃ v ∈ c.vars, v ∈ xs := by
  rw [coveredBy, Bool.and_eq_true] at h
  obtain ⟨hhv, hvin⟩ := h
  obtain ⟨v, hmem⟩ := List.exists_mem_of_ne_nil c.vars (hasVar_vars_ne_nil c hhv)
  exact ⟨v, hmem, Expression.varsIn_sound xs c (Expression.varsInF_eq xs c ▸ hvin) v hmem⟩

/-- The index yields exactly `coveredCsOf cs xs` for every target — an equality (not just
    soundness), so the domains it feeds and the `foldOut_correct` proof transport unchanged. Needs
    only the completeness invariant (`hidx`), so it holds for refreshed (possibly stale-superset)
    indexes just as for fresh builds. -/
theorem coveredCsIdx_eq (cs : ConstraintSystem p) (xs : List Variable) (fidx : FoldIdx cs) :
    CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs = coveredCsOf cs xs := by
  rw [fidx.harr, coveredCsOf]
  exact CoveredIndex.coveredIdx_eq_filter_of_complete fidx.idx cs.algebraicConstraints
    (coveredBy xs) xs
    (fun i hi hQ => by
      obtain ⟨v, hv, hvxs⟩ := coveredBy_shares_var xs cs.algebraicConstraints[i] hQ
      exact CoveredIndex.mem_candidates fidx.idx xs v i hvxs (fidx.hidx i hi v hv))

/-! ### The sparse fold

`foldOut` maps `foldRewrite` over the *whole* system, so each accepted fold pays a full
gate walk (`anyVarIn`) over every expression node in the system — the dominant per-accept cost on
fold-heavy circuits. But `foldRewrite` is the identity on any expression sharing no variable with
`xs` (`foldRewrite_eq_self`), and by bucket completeness every item sharing a variable with `xs`
is bucketed under it — so only the bucketed candidate positions can change. `foldOutIdx` walks
the system once by position, passing every non-candidate item through untouched (one O(1)
`Nat`-set probe each, no expression walk), and is provably equal to `foldOut`
(`foldOutIdx_eq`). -/

/-- The deduplicating position set of every bucket entry for a variable of `xs` — the positions
    an accepted fold can possibly touch. -/
def touchedSet (idx : CoveredIndex.CovIndex) (xs : List Variable) : Std.HashSet Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])).foldl (·.insert ·) ∅

/-- Membership in the touched set is membership in some bucket of `xs`. -/
theorem touchedSet_contains_iff (idx : CoveredIndex.CovIndex) (xs : List Variable) (i : Nat) :
    (touchedSet idx xs).contains i = true ↔ ∃ v ∈ xs, i ∈ idx.buckets.getD v [] := by
  rw [← Std.HashSet.mem_iff_contains, touchedSet, CoveredIndex.mem_foldl_insert,
    List.mem_flatMap]
  simp [Std.HashSet.not_mem_empty]

/-- `foldOut`, computed sparsely through the index: only candidate positions (bucketed under a
    variable of `xs`) are rewritten; all others are passed through by position. -/
def foldOutIdx {cs : ConstraintSystem p} (fidx : FoldIdx cs) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) : ConstraintSystem p :=
  let touchedCs : Std.HashSet Nat := touchedSet fidx.idx xs
  let touchedBis : Std.HashSet Nat := touchedSet fidx.bisIdx xs
  { algebraicConstraints := cs.algebraicConstraints.zipIdx.map (fun ci =>
      if touchedCs.contains ci.2 then
        (if coveredBy xs ci.1 then ci.1 else foldRewrite xs survs ci.1)
      else ci.1),
    busInteractions := cs.busInteractions.zipIdx.map (fun bii =>
      if touchedBis.contains bii.2 then bii.1.mapExpr (foldRewrite xs survs) else bii.1) }

/-- An untouched interaction maps to itself under a rewrite that fixes each of its expressions. -/
theorem mapExpr_eq_self {bi : BusInteraction (Expression p)} {g : Expression p → Expression p}
    (hm : g bi.multiplicity = bi.multiplicity) (hp : ∀ e ∈ bi.payload, g e = e) :
    bi.mapExpr g = bi := by
  have hpl : bi.payload.map g = bi.payload :=
    (List.map_congr_left (g := id) hp).trans (List.map_id _)
  cases bi with
  | mk busId mult payload =>
    simp only [BusInteraction.mapExpr] at *
    rw [hm, hpl]

/-- The positional pass-through map equals the plain map when the function fixes the item at
    every position outside `mem`. -/
theorem zipIdx_map_sparse {α : Type _} (l : List α) (f : α → α) (mem : Nat → Bool)
    (hfix : ∀ (i : Nat) (hi : i < l.length), mem i = false → f l[i] = l[i]) :
    l.zipIdx.map (fun ai => if mem ai.2 then f ai.1 else ai.1) = l.map f := by
  rw [show l.map f = l.zipIdx.map (f ∘ Prod.fst) by rw [← List.map_map, List.zipIdx_map_fst]]
  refine List.map_congr_left ?_
  rintro ⟨a, i⟩ hp
  obtain ⟨_, hlt, heq⟩ := List.mem_zipIdx (k := 0) hp
  have hlt' : i < l.length := by simpa using hlt
  have heq' : l[i]'hlt' = a := by simpa using heq.symm
  dsimp only [Function.comp_apply]
  by_cases hm : mem i = true
  · rw [if_pos hm]
  · rw [if_neg hm]
    have := hfix i hlt' (by simpa using hm)
    rw [heq'] at this
    exact this.symm

/-- **The sparse fold is the fold.** Every non-candidate position holds an item sharing no
    variable with `xs` (bucket completeness, contraposed), on which `foldRewrite` is the
    identity — so skipping it is exact. -/
theorem foldOutIdx_eq {cs : ConstraintSystem p} (fidx : FoldIdx cs) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) :
    foldOutIdx fidx xs survs = foldOut cs xs survs := by
  show ConstraintSystem.mk
      (cs.algebraicConstraints.zipIdx.map (fun ci =>
        if (touchedSet fidx.idx xs).contains ci.2 then
          (if coveredBy xs ci.1 then ci.1 else foldRewrite xs survs ci.1)
        else ci.1))
      (cs.busInteractions.zipIdx.map (fun bii =>
        if (touchedSet fidx.bisIdx xs).contains bii.2 then
          bii.1.mapExpr (foldRewrite xs survs)
        else bii.1)) = foldOut cs xs survs
  unfold foldOut
  congr 1
  · -- constraint side
    refine zipIdx_map_sparse cs.algebraicConstraints
      (fun c => if coveredBy xs c then c else foldRewrite xs survs c)
      (fun i => (touchedSet fidx.idx xs).contains i) ?_
    intro i hi hm
    have hm' : (touchedSet fidx.idx xs).contains i = false := hm
    -- `i` is in no bucket of `xs`, so the constraint shares no variable with `xs`.
    have hnb : ¬ ∃ v ∈ xs, i ∈ fidx.idx.buckets.getD v [] := by
      rw [← touchedSet_contains_iff fidx.idx xs i, hm']
      simp
    have hnav : cs.algebraicConstraints[i].anyVarIn xs = false := by
      by_contra hav
      obtain ⟨v, hvc, hvxs⟩ := Expression.anyVarIn_exists (Bool.ne_false_iff.mp hav)
      exact hnb ⟨v, hvxs, fidx.hidx i hi v hvc⟩
    show (if coveredBy xs cs.algebraicConstraints[i] then cs.algebraicConstraints[i]
        else foldRewrite xs survs cs.algebraicConstraints[i]) = cs.algebraicConstraints[i]
    rw [foldRewrite_eq_self hnav, ite_self]
  · -- interaction side
    refine zipIdx_map_sparse cs.busInteractions
      (fun bi => bi.mapExpr (foldRewrite xs survs))
      (fun i => (touchedSet fidx.bisIdx xs).contains i) ?_
    intro i hi hm
    have hm' : (touchedSet fidx.bisIdx xs).contains i = false := hm
    have hnb : ¬ ∃ v ∈ xs, i ∈ fidx.bisIdx.buckets.getD v [] := by
      rw [← touchedSet_contains_iff fidx.bisIdx xs i, hm']
      simp
    have hnoshare : ∀ v ∈ (cs.busInteractions[i]).vars, v ∉ xs := by
      intro v hvbi hvxs
      exact hnb ⟨v, hvxs, fidx.hbis i hi v hvbi⟩
    have hfix : ∀ e : Expression p, (∀ v ∈ e.vars, v ∈ (cs.busInteractions[i]).vars) →
        foldRewrite xs survs e = e := by
      intro e hsub
      refine foldRewrite_eq_self ?_
      by_contra hav
      obtain ⟨v, hvc, hvxs⟩ := Expression.anyVarIn_exists (Bool.ne_false_iff.mp hav)
      exact hnoshare v (hsub v hvc) hvxs
    show (cs.busInteractions[i]).mapExpr (foldRewrite xs survs) = cs.busInteractions[i]
    exact mapExpr_eq_self
      (hfix (cs.busInteractions[i]).multiplicity (fun v hv => by
        rw [BusInteraction.vars]; exact List.mem_append_left _ hv))
      (fun e he => hfix e (fun v hv => by
        rw [BusInteraction.vars]
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, hv⟩)))

/-- One checked fold for a candidate group (identity unless the group has a bounded domain, at least
    one survivor, and some foldable subexpression). The per-target covered scan is served from the
    prebuilt index (`coveredCsIdx_eq`) — and reused for the survivor filter
    (`groupSurvivorsE es`, provably `groupSurvivors cs xs doms` via `hes`) and for the
    index-local no-op gate (`systemHasFoldableIdx`), so no full-system scan remains on the
    per-target path. An accepted fold is computed sparsely (`foldOutIdx`, provably the full fold)
    and the index is *refreshed*, never rebuilt (`FoldIdx.refresh`). Prime `p`; the caller
    supplies `Fact p.Prime`. -/
def foldStep [Fact p.Prime] (bs : BusSemantics p) (cs : ConstraintSystem p) (fidx : FoldIdx cs)
    (xs : List Variable) : Σ' (r : PassResult cs bs), FoldIdx r.out :=
  let es := CoveredIndex.coveredIdx fidx.idx fidx.arr (coveredBy xs) xs
  have hes : es = coveredCsOf cs xs := coveredCsIdx_eq cs xs fidx
  match hdoms : groupDoms es xs with
  | none => ⟨⟨cs, [], PassCorrect.refl cs bs⟩, fidx⟩
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survs := groupSurvivorsE es doms
      if 1 ≤ survs.length && systemHasFoldableIdx fidx xs survs then
        have hsurv : groupSurvivors cs xs doms = survs := by
          show groupSurvivors cs xs doms = groupSurvivorsE es doms
          rw [hes]; rfl
        -- Compute the rewritten system once, sparsely; correctness and the index refresh both
        -- transport along `hro` to the computed value, so nothing is evaluated twice.
        let ro := foldOutIdx fidx xs survs
        have hro : ro = foldOut cs xs survs := foldOutIdx_eq fidx xs survs
        ⟨⟨ro, [], hro ▸ (hsurv ▸ foldOut_correct cs bs xs doms (hes ▸ hdoms) :
            PassCorrect cs (foldOut cs xs survs) [] bs)⟩,
         fidx.refresh xs survs ro hro⟩
      else ⟨⟨cs, [], PassCorrect.refl cs bs⟩, fidx⟩
    else ⟨⟨cs, [], PassCorrect.refl cs bs⟩, fidx⟩

/-- Process the candidate groups sequentially (correctness composes; no derivations). The index is
    threaded and rebuilt by `foldStep` on each accepted fold. -/
def foldLoop [Fact p.Prime] (bs : BusSemantics p) :
    List (List Variable) → (cs : ConstraintSystem p) → FoldIdx cs → PassResult cs bs
  | [], cs, _ => ⟨cs, [], PassCorrect.refl cs bs⟩
  | xs :: rest, cs, fidx =>
    let r1 := foldStep bs cs fidx xs
    let r2 := foldLoop bs rest r1.1.out r1.2
    ⟨r2.out, r1.1.derivs ++ r2.derivs, r1.1.correct.andThen r2.correct⟩

/-! ### Direct (unindexed) path for small systems

The inverted index amortizes the covered-set scan, but its per-target candidate gather
(bucket flat-map + dedup + sort) *loses* on the openvm-eth blocks, whose variables are shared by
hundreds of items each (huge buckets); the plain `coveredCsOf` filter is cheaper there, while
the index wins decisively on the keccak stress case (~28.6k constraints, sparser sharing).
`domainFoldPass` therefore gates on system size. Relative to the pre-index direct path, the
covered set is computed **once** per target and reused for the survivor filter
(`groupSurvivorsE es`, provably `groupSurvivors cs xs doms` — the old code paid the full filter
a second time inside `groupSurvivors`). -/

/-- One checked fold for a candidate group, given the covered set `es = coveredCsOf cs xs` and
    its complement `csRest` (the non-covered constraints, feeding the no-op gate without a second
    `coveredBy` sweep). -/
def foldStepWith [Fact p.Prime] (bs : BusSemantics p) (cs : ConstraintSystem p) (xs : List Variable)
    (es : List (Expression p)) (csRest : List (Expression p))
    (hes : es = coveredCsOf cs xs) : PassResult cs bs :=
  match hdoms : groupDoms es xs with
  | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survs := groupSurvivorsE es doms
      if 1 ≤ survs.length && systemHasFoldableW cs xs survs csRest then
        have hsurv : groupSurvivors cs xs doms = survs := by
          show groupSurvivors cs xs doms = groupSurvivorsE es doms
          rw [hes]; rfl
        ⟨foldOutC cs xs survs, [], hsurv ▸ foldOutC_correct cs bs xs doms (hes ▸ hdoms)⟩
      else ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs, [], PassCorrect.refl cs bs⟩

/-- Direct-path fold loop: one `partition` per target computes the covered set and its complement
    together (no index, and no second `coveredBy` sweep for the gate). -/
def foldLoopDirect [Fact p.Prime] (bs : BusSemantics p) :
    List (List Variable) → (cs : ConstraintSystem p) → PassResult cs bs
  | [], cs => ⟨cs, [], PassCorrect.refl cs bs⟩
  | xs :: rest, cs =>
    match hpr : cs.algebraicConstraints.partition (coveredBy xs) with
    | (es, csRest) =>
      let r1 := foldStepWith bs cs xs es csRest (by
        rw [List.partition_eq_filter_filter] at hpr
        injection hpr with h1 _
        exact h1.symm)
      let r2 := foldLoopDirect bs rest r1.out
      ⟨r2.out, r1.derivs ++ r2.derivs, r1.correct.andThen r2.correct⟩

/-- Systems with at least this many algebraic constraints use the inverted index; smaller ones use
    the direct per-target `coveredCsOf` scan (see the section comment). Purely a runtime gate —
    both paths compute the identical fold. -/
def domainFoldIndexThreshold : Nat := 8192

/-- The domain-constant folding pass: for every constraint's (small) variable group, fold each
    subexpression that is constant on the group's surviving joint values to that constant — keeping
    the group's variables. Recovers the address-constant folding that unblocks memory chaining
    (which the re-encoder currently achieves only as a side effect). Prime `p` only; identity
    otherwise. -/
def domainFoldPass (pw : PrimeWitness p) : VerifiedPass p := fun cs bsem =>
  if hpB : pw.isPrime = true then
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    -- Domains come only from single-variable constraints (`findDomainAlg`/`rootsIn`), and a
    -- single-variable constraint is covered by every group containing its variable — so a group
    -- with a variable that has *no* single-variable constraint anywhere can never pass
    -- `groupDoms`. Skipping those targets up front (one hash lookup per variable) avoids the
    -- per-target covered-set scan for the ubiquitous byte-limb groups, exactly.
    -- Each constraint's deduped variable list is computed once (`hashedDedup_eq` keeps it the
    -- exact `List.dedup` value) and shared between the single-variable set and the target list.
    let csVs := cs.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
    let svSet : Std.HashSet Variable := csVs.foldl (init := ∅) fun s vs =>
      match vs with
      | [x] => s.insert x
      | _ => s
    let targets := dedupHash (csVs.filterMap (fun vs =>
      if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
        some (vs.mergeSort (fun a b => compare a b != .gt))
      else none))
    if domainFoldIndexThreshold ≤ cs.algebraicConstraints.length then
      foldLoop bsem targets cs (FoldIdx.mk' cs)
    else
      foldLoopDirect bsem targets cs
  else ⟨cs, [], PassCorrect.refl cs bsem⟩
