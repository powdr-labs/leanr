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

/-- `some c` if `e` evaluates to the same constant `c` on every survivor, else `none`. -/
def constOnSurvs (survs : List (List (Variable × ZMod p))) (e : Expression p) : Option (ZMod p) :=
  match survs with
  | [] => none
  | s₀ :: rest =>
    if (s₀ :: rest).all (fun s => decide (e.eval (envOf s) = e.eval (envOf s₀))) then
      some (e.eval (envOf s₀))
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
        have hc : e.eval (envOf s₀) = c := Option.some.inj h
        have hthis := List.all_eq_true.mp hall s hs
        rw [decide_eq_true_iff] at hthis
        rw [hthis, hc]
    · next => exact absurd h (by simp)

/-! ## The fold rewrite -/

/-- Replace every maximal wholly-in-group subexpression that is constant on the survivors by that
    constant; recurse otherwise. Leaves the group's variables in place where they are not folded. -/
def foldRewrite (xs : List Variable) (survs : List (List (Variable × ZMod p))) :
    Expression p → Expression p
  | .const c => .const c
  | .var y => .var y
  | .add a b =>
      if (Expression.add a b).varsIn xs then
        match constOnSurvs survs (.add a b) with
        | some c => .const c
        | none => .add (foldRewrite xs survs a) (foldRewrite xs survs b)
      else .add (foldRewrite xs survs a) (foldRewrite xs survs b)
  | .mul a b =>
      if (Expression.mul a b).varsIn xs then
        match constOnSurvs survs (.mul a b) with
        | some c => .const c
        | none => .mul (foldRewrite xs survs a) (foldRewrite xs survs b)
      else .mul (foldRewrite xs survs a) (foldRewrite xs survs b)

/-! ## Agreement with the identity on any survivor-matching environment -/

/-- On an environment that agrees on `xs` with some survivor `s`, `foldRewrite` is
    evaluation-preserving. The folded constants are exactly the survivor-constant values, and `s`'s
    membership pins them; unfolded nodes recurse. -/
theorem foldRewrite_agree (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (env : Variable → ZMod p) (s : List (Variable × ZMod p)) (hs : s ∈ survs)
    (hxs : ∀ x ∈ xs, env x = envOf s x) :
    ∀ e : Expression p, (foldRewrite xs survs e).eval env = e.eval env := by
  -- For a wholly-in-`xs` expression, `env` and `envOf s` agree on its variables.
  have hcongr : ∀ e : Expression p, e.varsIn xs = true → e.eval env = e.eval (envOf s) := by
    intro e he
    exact Expression.eval_congr e _ _ (fun x hx => hxs x (Expression.varsIn_sound xs e he x hx))
  intro e
  induction e with
  | const c => rfl
  | var y => rfl
  | add a b iha ihb =>
      unfold foldRewrite
      by_cases hin : (Expression.add a b).varsIn xs = true
      · rw [if_pos hin]
        cases hc : constOnSurvs survs (.add a b) with
        | none =>
            show (foldRewrite xs survs a).eval env + (foldRewrite xs survs b).eval env
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
        show (foldRewrite xs survs a).eval env + (foldRewrite xs survs b).eval env
          = a.eval env + b.eval env
        rw [iha, ihb]
  | mul a b iha ihb =>
      unfold foldRewrite
      by_cases hin : (Expression.mul a b).varsIn xs = true
      · rw [if_pos hin]
        cases hc : constOnSurvs survs (.mul a b) with
        | none =>
            show (foldRewrite xs survs a).eval env * (foldRewrite xs survs b).eval env
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
        show (foldRewrite xs survs a).eval env * (foldRewrite xs survs b).eval env
          = a.eval env * b.eval env
        rw [iha, ihb]

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

/-- Folding never introduces a variable: every variable of `foldRewrite … e` is a variable of `e`. -/
theorem foldRewrite_vars (xs : List Variable) (survs : List (List (Variable × ZMod p)))
    (e : Expression p) : ∀ v ∈ (foldRewrite xs survs e).vars, v ∈ e.vars := by
  induction e with
  | const c => intro v hv; simp [foldRewrite, Expression.vars] at hv
  | var y => intro v hv; exact hv
  | add a b iha ihb =>
      unfold foldRewrite
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
      unfold foldRewrite
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

/-! ## Agreement on any environment satisfying the covered constraints

The survivors were enumerated over the group's constraint-derived domains and filtered by the
covered constraints, so any environment satisfying **all** the covered constraints pins the group
to one of the survivors — under which `foldRewrite` is the identity. -/

/-- If `env` satisfies every covered constraint, `foldRewrite` (over the survivors of those
    constraints) is evaluation-preserving on `env`. Prime `p` (for `groupDoms_sound`). -/
theorem foldRewrite_agree_covered [Fact p.Prime] (cs : ConstraintSystem p) (xs : List Variable)
    (doms : List (Variable × List (ZMod p)))
    (hdoms : groupDoms (coveredCsOf cs xs) xs = some doms)
    (env : Variable → ZMod p) (hcov : ∀ c ∈ coveredCsOf cs xs, c.eval env = 0) :
    ∀ e : Expression p, (foldRewrite xs (groupSurvivors cs xs doms) e).eval env = e.eval env := by
  have hkeys : doms.map Prod.fst = xs := groupDoms_fst (coveredCsOf cs xs) xs doms hdoms
  have hmemdoms : ∀ yd ∈ doms, env yd.1 ∈ yd.2 :=
    groupDoms_sound (coveredCsOf cs xs) xs doms hdoms env hcov
  set s := doms.map (fun yd => (yd.1, env yd.1)) with hs_def
  have hsassign : s ∈ assignments doms := mem_assignments doms env hmemdoms
  have hagree : ∀ x ∈ xs, env x = envOf s x := by
    intro x hx
    rw [hs_def, envOf_map doms env x (by rw [hkeys]; exact hx)]
  have hsurv : s ∈ groupSurvivors cs xs doms := by
    simp only [groupSurvivors, List.mem_filter]
    refine ⟨hsassign, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    rw [decide_eq_true_iff]
    have hcvin : c.varsIn xs = true := by
      have hcb : coveredBy xs c = true := (List.mem_filter.mp hc).2
      rw [coveredBy, Bool.and_eq_true] at hcb
      exact hcb.2
    have heq : c.eval (envOf s) = c.eval env :=
      Expression.eval_congr c _ _
        (fun x hx => (hagree x (Expression.varsIn_sound xs c hcvin x hx)).symm)
    rw [heq]; exact hcov c hc
  intro e
  exact foldRewrite_agree xs (groupSurvivors cs xs doms) env s hsurv hagree e

/-! ## The folded output -/

/-- Fold every non-covered constraint and every bus interaction; keep the covered (domain-pinning)
    constraints **verbatim** (folding them would collapse them and lose the domain pin). -/
def foldOut (cs : ConstraintSystem p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) : ConstraintSystem p :=
  { algebraicConstraints :=
      (cs.algebraicConstraints.filter (fun c => !coveredBy xs c)).map (foldRewrite xs survs)
        ++ coveredCsOf cs xs,
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
  · simp only [foldOut, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      exact ConstraintSystem.mem_vars_of_constraint (List.mem_of_mem_filter hc0)
        (foldRewrite_vars xs survs c0 v hcv)
    · exact ConstraintSystem.mem_vars_of_constraint (List.mem_of_mem_filter hc) hcv
  · simp only [foldOut, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    rcases hbiv with hmv | ⟨e, he, hev⟩
    · exact ConstraintSystem.mem_vars_of_mult hbi0
        (foldRewrite_vars xs survs bi0.multiplicity v hmv)
    · simp only [BusInteraction.mapExpr] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact ConstraintSystem.mem_vars_of_payload hbi0 he0 (foldRewrite_vars xs survs e0 v hev)

/-- **Correctness of one fold.** The folded system refines the input and preserves invariants, with
    the identity witness (`ofEnvEq`): the covered constraints, kept verbatim, pin the group so the
    rewrite agrees with the identity on every assignment satisfying either system. -/
theorem foldOut_correct [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (hdoms : groupDoms (coveredCsOf cs xs) xs = some doms) :
    PassCorrect cs (foldOut cs xs (groupSurvivors cs xs doms)) [] bs := by
  set survs := groupSurvivors cs xs doms with hsurv_def
  -- covered constraints are satisfied by any assignment of the output (kept verbatim) or the input.
  have hcov_out : ∀ env, (foldOut cs xs survs).satisfies bs env →
      ∀ c ∈ coveredCsOf cs xs, c.eval env = 0 := by
    intro env hsat c hc
    exact hsat.1 c (by simp only [foldOut, List.mem_append]; exact Or.inr hc)
  have hcov_cs : ∀ env, cs.satisfies bs env → ∀ c ∈ coveredCsOf cs xs, c.eval env = 0 :=
    fun env hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  refine PassCorrect.ofEnvEq ?hsound ?hinv ?hsub ?hcomp
  case hsub => exact foldOut_vars_subset cs xs survs
  case hsound =>
    intro env hsatout
    have hag := foldRewrite_agree_covered cs xs doms hdoms env (hcov_out env hsatout)
    refine ⟨env, ⟨?_, ?_⟩, ?_⟩
    · -- every cs constraint holds
      intro c hc
      by_cases hccov : coveredBy xs c = true
      · exact hcov_out env hsatout c (List.mem_filter.2 ⟨hc, hccov⟩)
      · have hmem : foldRewrite xs survs c ∈ (foldOut cs xs survs).algebraicConstraints := by
          simp only [foldOut, List.mem_append]
          exact Or.inl (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hccov⟩, rfl⟩)
        have := hsatout.1 _ hmem
        rwa [hag c] at this
    · -- no cs bus interaction violates
      intro bi hbi
      have hmem : bi.mapExpr (foldRewrite xs survs) ∈ (foldOut cs xs survs).busInteractions :=
        List.mem_map.2 ⟨bi, hbi, rfl⟩
      have hval := mapExpr_eval_of_agree (foldRewrite xs survs) env hag bi
      have := hsatout.2 _ hmem
      rw [hval] at this; exact this
    · rw [foldOut_sideEffects_eq cs bs xs survs env hag]; exact BusState.equiv_refl _
  case hinv =>
    intro hinv env hsatout bi' hbi'
    have hag := foldRewrite_agree_covered cs xs doms hdoms env (hcov_out env hsatout)
    -- env satisfies cs (soundness reasoning inlined)
    have hsatcs : cs.satisfies bs env := by
      refine ⟨?_, ?_⟩
      · intro c hc
        by_cases hccov : coveredBy xs c = true
        · exact hcov_out env hsatout c (List.mem_filter.2 ⟨hc, hccov⟩)
        · have hmem : foldRewrite xs survs c ∈ (foldOut cs xs survs).algebraicConstraints := by
            simp only [foldOut, List.mem_append]
            exact Or.inl (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simpa using hccov⟩, rfl⟩)
          have := hsatout.1 _ hmem
          rwa [hag c] at this
      · intro bi hbi
        have hmem : bi.mapExpr (foldRewrite xs survs) ∈ (foldOut cs xs survs).busInteractions :=
          List.mem_map.2 ⟨bi, hbi, rfl⟩
        have hval := mapExpr_eval_of_agree (foldRewrite xs survs) env hag bi
        have := hsatout.2 _ hmem
        rw [hval] at this; exact this
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    rw [mapExpr_eval_of_agree (foldRewrite xs survs) env hag bi0]
    exact hinv env hsatcs bi0 hbi0
  case hcomp =>
    intro env hadm hsat
    have hag := foldRewrite_agree_covered cs xs doms hdoms env (hcov_cs env hsat)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- every out constraint holds
      intro c hc
      simp only [foldOut, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
        rw [hag c0]; exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hsat.1 c (List.mem_of_mem_filter hc)
    · -- no out bus interaction violates
      intro bi hbi
      obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      rw [mapExpr_eval_of_agree (foldRewrite xs survs) env hag bi0]
      exact hsat.2 bi0 hbi0
    · exact (foldOut_admissible_iff cs bs xs survs env hag).2 hadm
    · rw [foldOut_sideEffects_eq cs bs xs survs env hag]; exact BusState.equiv_refl _

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

/-- Does the fold change anything in the system? -/
def systemHasFoldable (cs : ConstraintSystem p) (xs : List Variable)
    (survs : List (List (Variable × ZMod p))) : Bool :=
  cs.algebraicConstraints.any (fun c => !coveredBy xs c && c.hasFoldable xs survs) ||
    cs.busInteractions.any (fun bi =>
      bi.multiplicity.hasFoldable xs survs || bi.payload.any (fun e => e.hasFoldable xs survs))

/-- One checked fold for a candidate group (identity unless the group has a bounded domain, at least
    one survivor, and some foldable subexpression). Prime `p`; the caller supplies `Fact p.Prime`. -/
def foldStep [Fact p.Prime] (bs : BusSemantics p) (cs : ConstraintSystem p) (xs : List Variable) :
    PassResult cs bs :=
  match hdoms : groupDoms (coveredCsOf cs xs) xs with
  | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survs := groupSurvivors cs xs doms
      if 1 ≤ survs.length && systemHasFoldable cs xs survs then
        ⟨foldOut cs xs survs, [], foldOut_correct cs bs xs doms hdoms⟩
      else ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs, [], PassCorrect.refl cs bs⟩

/-- Process the candidate groups sequentially (correctness composes; no derivations). -/
def foldLoop [Fact p.Prime] (bs : BusSemantics p) :
    List (List Variable) → (cs : ConstraintSystem p) → PassResult cs bs
  | [], cs => ⟨cs, [], PassCorrect.refl cs bs⟩
  | xs :: rest, cs =>
    let r1 := foldStep bs cs xs
    let r2 := foldLoop bs rest r1.out
    ⟨r2.out, r1.derivs ++ r2.derivs, r1.correct.andThen r2.correct⟩

/-- The domain-constant folding pass: for every constraint's (small) variable group, fold each
    subexpression that is constant on the group's surviving joint values to that constant — keeping
    the group's variables. Recovers the address-constant folding that unblocks memory chaining
    (which the re-encoder currently achieves only as a side effect). Prime `p` only; identity
    otherwise. -/
def domainFoldPass : VerifiedPass p := fun cs bsem =>
  if hpr : p.Prime then
    haveI : Fact p.Prime := ⟨hpr⟩
    let targets := dedupHash (cs.algebraicConstraints.filterMap (fun c =>
      let vs := c.vars.dedup
      if 2 ≤ vs.length && vs.length ≤ 8 then some (vs.mergeSort (fun a b => compare a b != .gt))
      else none))
    foldLoop bsem targets cs
  else ⟨cs, [], PassCorrect.refl cs bsem⟩
