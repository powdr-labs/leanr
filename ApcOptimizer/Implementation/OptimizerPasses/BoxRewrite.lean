import ApcOptimizer.Implementation.OptimizerPasses.FlagFold

set_option autoImplicit false

/-! # Box-certified multilinear rewriting

The missing piece of log entry 64: after substituting a degree-2 flag interpolation, the
stateful address payloads and the data-selection constraints hold expressions that exceed the
degree bound *syntactically* while being pointwise equal to legal forms — `b² → b` on the
boolean flags reduces them back within bound. This pass rewrites every **over-bound** expression
of the system to its multilinear reduction, accepting the rewrite only under a decidable
certificate: on every point of the (small) joint domain box of the expression's small-domain
variables, the two expressions **partially evaluate to the same affine form** in the remaining
(symbolic, e.g. data) variables.

The reduction itself is heuristic data — sparse monomial expansion with exponent capping on the
known-small-domain variables — and carries no proof; the certificate re-verifies pointwise.
Expressions with fewer than two distinct variables are never rewritten (they are the
`findDomainAlg` domain sources, giving non-circularity exactly as in `FlagFold.lean`). -/

variable {p : ℕ}

/-! ## The heuristic reducer -/

/-- Merge-insert a monomial into a sorted association list. -/
def addMono (m : List Variable) (c : ZMod p) :
    List (List Variable × ZMod p) → List (List Variable × ZMod p)
  | [] => [(m, c)]
  | (m', c') :: rest =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: addMono m c rest

/-- Multiply two variable multisets, capping exponents of `boolSet` members at one.
    Keeps lists sorted by name for canonical merging. -/
def mulMono (boolSet : List Variable) (a b : List Variable) : List Variable :=
  ((a ++ b).mergeSort (fun u v => decide (u.name ≤ v.name))).foldl
    (fun acc v =>
      match acc.head? with
      | some w => if w = v ∧ v ∈ boolSet then acc else v :: acc
      | none => [v]) []

/-- Sparse monomial expansion (with boolean exponent capping); `none` when the monomial count
    exceeds the cap. Heuristic only. -/
def polyOf (boolSet : List Variable) : Expression p →
    Option (List (List Variable × ZMod p))
  | .const c => some [([], c)]
  | .var v => some [([v], 1)]
  | .add a b => do
    let pa ← polyOf boolSet a
    let pb ← polyOf boolSet b
    let r := pb.foldl (fun acc mc => addMono mc.1 mc.2 acc) pa
    if r.length ≤ 64 then some r else none
  | .mul a b => do
    let pa ← polyOf boolSet a
    let pb ← polyOf boolSet b
    let r := pa.foldl (fun acc ma =>
      pb.foldl (fun acc2 mb =>
        addMono (mulMono boolSet ma.1 mb.1) (ma.2 * mb.2) acc2) acc) []
    if r.length ≤ 64 then some r else none

/-- One monomial as an expression. -/
def monoExpr (mc : List Variable × ZMod p) : Expression p :=
  mc.1.foldl (fun m v => Expression.mul m (Expression.var v)) (Expression.const mc.2)

/-- Rebuild an expression from monomials (dropping zero coefficients). -/
def exprOfPoly (ms : List (List Variable × ZMod p)) : Expression p :=
  match ms.filter (fun mc => !(mc.2 == 0)) with
  | [] => Expression.const 0
  | mc :: rest => rest.foldl (fun acc mc' => Expression.add acc (monoExpr mc')) (monoExpr mc)

/-- The heuristic multilinear reduction. -/
def reduceExpr (boolSet : List Variable) (e : Expression p) : Option (Expression p) :=
  (polyOf boolSet e).map exprOfPoly

/-! ## The certificate -/

/-- Constant-solution map for a box point (used with `substF`). -/
def ptFun (pt : List (Variable × ZMod p)) : Variable → Option (Expression p) :=
  fun v => if pt.any (fun t => t.1 == v) then some (.const (envOf pt v)) else none

/-- Canonical equality of normalized linear forms: equal constants and equal name-sorted term
    lists. -/
def canonEq (l1 l2 : LinExpr p) : Bool :=
  l1.const == l2.const &&
  l1.terms.mergeSort (fun a b => decide (a.1.name ≤ b.1.name))
    == l2.terms.mergeSort (fun a b => decide (a.1.name ≤ b.1.name))

/-- Certificate: on every point of the joint small-domain box, both expressions partially
    evaluate to the same affine form in the remaining symbolic variables. -/
def brCert (singles : List (Expression p)) (e e' : Expression p) : Bool :=
  2 ≤ e.vars.eraseDups.length &&
  (let jv := (e.vars ++ e'.vars).eraseDups
   let boxed := jv.filter (fun v =>
     match findDomainAlg (singles) v with
     | some d => d.length ≤ 2
     | none => false)
   let doms := boxed.filterMap (fun v =>
     (findDomainAlg (singles) v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = boxed) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 16) &&
   (assignments doms).all (fun pt =>
     match linearize (e.substF (ptFun pt)), linearize (e'.substF (ptFun pt)) with
     | some l1, some l2 => canonEq l1.norm l2.norm
     | _, _ => false))

/-- `envF` over a point map is the identity when the point is the environment's own
    restriction. -/
theorem envF_ptFun_self (doms : List (Variable × List (ZMod p))) (env : Variable → ZMod p) :
    envF (ptFun (doms.map (fun vd => (vd.1, env vd.1)))) env = env := by
  funext v
  unfold envF ptFun
  by_cases hin : (doms.map (fun vd => (vd.1, env vd.1))).any (fun t => t.1 == v) = true
  · rw [if_pos hin]
    show (envOf (doms.map (fun vd => (vd.1, env vd.1))) v) = env v
    refine envOf_map doms env v ?_
    obtain ⟨t, ht, htv⟩ := List.any_eq_true.1 hin
    obtain ⟨vd, hvd, rfl⟩ := List.mem_map.1 ht
    have : vd.1 = v := eq_of_beq htv
    rw [← this]
    exact List.mem_map.2 ⟨vd, hvd, rfl⟩
  · rw [if_neg hin]

theorem brCert_sound [Fact p.Prime] (singles : List (Expression p)) (e e' : Expression p)
    (h : brCert singles e e' = true) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval env = 0) : e.eval env = e'.eval env := by
  unfold brCert at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨_h2, ⟨⟨hcover, _hcap⟩, hall⟩⟩ := h
  have hcover' := of_decide_eq_true hcover
  -- the environment restricted to the box is an enumerated point
  set boxed := ((e.vars ++ e'.vars).eraseDups.filter (fun v =>
    match findDomainAlg (singles) v with
    | some d => d.length ≤ 2
    | none => false)) with hboxed
  set doms := (boxed.filterMap (fun v =>
    (findDomainAlg (singles) v).map (fun d => (v, d)))) with hdoms
  have hmemdoms : ∀ vd ∈ doms, env vd.1 ∈ vd.2 := by
    intro vd hvd
    rw [hdoms] at hvd
    obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
    cases hfd : findDomainAlg (singles) v with
    | none => rw [hfd] at hvd'; simp at hvd'
    | some d =>
      rw [hfd] at hvd'
      simp only [Option.map_some, Option.some.injEq] at hvd'
      obtain rfl := hvd'.symm
      exact findDomainAlg_sound (singles) v d hfd env hdom
  have hpt := mem_assignments doms env hmemdoms
  have hcond := List.all_eq_true.mp hall _ hpt
  cases hl1 : linearize (e.substF (ptFun (doms.map (fun vd => (vd.1, env vd.1))))) with
  | none => rw [hl1] at hcond; simp at hcond
  | some l1 =>
    cases hl2 : linearize (e'.substF (ptFun (doms.map (fun vd => (vd.1, env vd.1))))) with
    | none => rw [hl1, hl2] at hcond; simp at hcond
    | some l2 =>
      rw [hl1, hl2] at hcond
      unfold canonEq at hcond
      rw [Bool.and_eq_true] at hcond
      obtain ⟨hconst, hterms⟩ := hcond
      -- partial evaluation agrees with full evaluation
      have hs1 : (e.substF (ptFun (doms.map (fun vd => (vd.1, env vd.1))))).eval env
          = e.eval env := by
        rw [Expression.eval_substF, envF_ptFun_self]
      have hs2 : (e'.substF (ptFun (doms.map (fun vd => (vd.1, env vd.1))))).eval env
          = e'.eval env := by
        rw [Expression.eval_substF, envF_ptFun_self]
      -- the two affine forms evaluate equally (equal constants, permuted equal terms)
      have hsum : ((l1.norm.terms.map (fun t => t.2 * env t.1)).sum)
          = ((l2.norm.terms.map (fun t => t.2 * env t.1)).sum) := by
        have hp1 : List.Perm (l1.norm.terms.map (fun t => t.2 * env t.1))
            ((l1.norm.terms.mergeSort (fun a b => decide (a.1.name ≤ b.1.name))).map
              (fun t => t.2 * env t.1)) :=
          ((List.mergeSort_perm l1.norm.terms _).symm).map _
        have hp2 : List.Perm ((l2.norm.terms.mergeSort
              (fun a b => decide (a.1.name ≤ b.1.name))).map (fun t => t.2 * env t.1))
            (l2.norm.terms.map (fun t => t.2 * env t.1)) :=
          (List.mergeSort_perm l2.norm.terms _).map _
        rw [hp1.sum_eq, eq_of_beq hterms, hp2.sum_eq]
      have hev : l1.norm.eval env = l2.norm.eval env := by
        show l1.norm.const + _ = l2.norm.const + _
        rw [eq_of_beq hconst, hsum]
      rw [← hs1, ← hs2, linearize_eval _ l1 hl1 env, linearize_eval _ l2 hl2 env,
          ← LinExpr.norm_eval l1 env, ← LinExpr.norm_eval l2 env]
      exact hev

/-! ## The pass -/

/-- Per-expression rewrite: only over-bound expressions, only when the reduction is within
    bound, introduces no variable, and is certified. -/
def brRw (singles : List (Expression p)) (bound : Nat) (e : Expression p) : Expression p :=
  if e.degree ≤ bound then e
  else
    let boolSet := e.vars.eraseDups.filter (fun v =>
      match findDomainAlg (singles) v with
      | some d => d.length ≤ 2
      | none => false)
    match reduceExpr boolSet e with
    | some e' =>
      if e'.degree ≤ bound && e'.vars.all (fun v => v ∈ e.vars) && brCert singles e e'
      then e' else e
    | none => e

theorem brRw_sound [Fact p.Prime] (singles : List (Expression p)) (bound : Nat)
    (e : Expression p) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval env = 0) :
    (brRw singles bound e).eval env = e.eval env := by
  simp only [brRw]
  split_ifs with hd
  · rfl
  · cases hr : reduceExpr (e.vars.eraseDups.filter (fun v =>
        match findDomainAlg (singles) v with
        | some d => d.length ≤ 2
        | none => false)) e with
    | none => simp only []
    | some e' =>
      simp only []
      split_ifs with hok
      · rw [Bool.and_eq_true, Bool.and_eq_true] at hok
        exact (brCert_sound singles e e' hok.2 env hdom).symm
      · rfl

theorem brRw_vars (singles : List (Expression p)) (bound : Nat) (e : Expression p) :
    ∀ v ∈ (brRw singles bound e).vars, v ∈ e.vars := by
  intro v hv
  simp only [brRw] at hv
  split_ifs at hv with hd
  · exact hv
  · cases hr : reduceExpr (e.vars.eraseDups.filter (fun v =>
        match findDomainAlg (singles) v with
        | some d => d.length ≤ 2
        | none => false)) e with
    | none => simp only [hr] at hv; exact hv
    | some e' =>
      simp only [hr] at hv
      split_ifs at hv with hok
      · rw [Bool.and_eq_true, Bool.and_eq_true] at hok
        exact of_decide_eq_true (List.all_eq_true.mp hok.1.2 v hv)
      · exact hv

/-- A single-variable expression is never rewritten (the certificate's ≥ 2-variables guard),
    keeping the domain sources intact. -/
theorem brRw_singleVar (singles : List (Expression p)) (bound : Nat) (c : Expression p)
    (hs : c.vars.eraseDups.length ≤ 1) : brRw singles bound c = c := by
  simp only [brRw]
  split_ifs with hd
  · rfl
  · cases hr : reduceExpr (c.vars.eraseDups.filter (fun v =>
        match findDomainAlg (singles) v with
        | some d => d.length ≤ 2
        | none => false)) c with
    | none => simp only []
    | some e' =>
      simp only []
      have hcert : brCert singles c e' = false := by
        unfold brCert
        have h2 : (2 ≤ c.vars.eraseDups.length : Bool) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        rw [h2, Bool.false_and]
      rw [hcert, Bool.and_false, if_neg (by simp)]

/-- The per-interaction rewrite (bus id untouched). -/
def brBi (singles : List (Expression p)) (db : DegreeBound)
    (bi : BusInteraction (Expression p)) : BusInteraction (Expression p) :=
  { busId := bi.busId,
    multiplicity := brRw singles db.busInteractions bi.multiplicity,
    payload := bi.payload.map (brRw singles db.busInteractions) }

/-- Rewrite every over-bound expression of the system to its certified reduction. -/
def ConstraintSystem.boxRewrite (cs : ConstraintSystem p) (b : DegreeBound) :
    ConstraintSystem p :=
  let singles := singleVarCs cs.algebraicConstraints
  { algebraicConstraints := cs.algebraicConstraints.map
      (brRw singles b.identities),
    busInteractions := cs.busInteractions.map (brBi singles b) }

theorem brBi_eval [Fact p.Prime] (singles : List (Expression p)) (db : DegreeBound)
    (bi : BusInteraction (Expression p)) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval env = 0) :
    (brBi singles db bi).eval env = bi.eval env := by
  unfold brBi BusInteraction.eval
  simp only [BusInteraction.mk.injEq]
  refine ⟨trivial, brRw_sound singles _ _ env hdom, ?_⟩
  rw [List.map_map]
  exact List.map_congr_left (fun e _ => brRw_sound singles _ e env hdom)

theorem ConstraintSystem.boxRewrite_correct [Fact p.Prime]
    (cs : ConstraintSystem p) (bs : BusSemantics p) (b : DegreeBound) :
    PassCorrect cs (cs.boxRewrite b) [] bs := by
  -- single-variable domain sources survive verbatim
  have hsingle : ∀ c ∈ singleVarCs cs.algebraicConstraints,
      c ∈ (cs.boxRewrite b).algebraicConstraints := by
    intro c hc
    have hmem := List.mem_of_mem_filter hc
    have hs : c.vars.eraseDups.length ≤ 1 := by
      have h1 := (List.mem_filter.1 hc).2
      rw [HashedDedup.hashedEraseDups_eq] at h1
      have h2 : c.vars.eraseDups.length = 1 := by simpa using h1
      omega
    exact List.mem_map.2 ⟨c, hmem, brRw_singleVar _ _ c hs⟩
  have hdomOut : ∀ env, (cs.boxRewrite b).satisfies bs env →
      ∀ c ∈ singleVarCs cs.algebraicConstraints, c.eval env = 0 :=
    fun env hsat c hc => hsat.1 c (hsingle c hc)
  have hdomIn : ∀ env, cs.satisfies bs env →
      ∀ c ∈ singleVarCs cs.algebraicConstraints, c.eval env = 0 :=
    fun env hsat c hc => hsat.1 c (List.mem_of_mem_filter hc)
  have hiff : ∀ env, (cs.boxRewrite b).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    constructor
    · intro hsat
      have hdom := hdomOut env hsat
      refine ⟨fun c hc => ?_, fun bi hbim => ?_⟩
      · have h0 := hsat.1 _ (List.mem_map.2 ⟨c, hc, rfl⟩)
        rw [brRw_sound _ _ c env hdom] at h0
        exact h0
      · have h0 := hsat.2 _ (List.mem_map.2 ⟨bi, hbim, rfl⟩)
        rw [brBi_eval _ _ bi env hdom] at h0
        exact h0
    · intro hsat
      have hdom := hdomIn env hsat
      refine ⟨fun c' hc' => ?_, fun bi' hbi' => ?_⟩
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
        rw [brRw_sound _ _ c env hdom]
        exact hsat.1 c hc
      · obtain ⟨bi, hbim, rfl⟩ := List.mem_map.1 hbi'
        show (BusInteraction.eval _ env).multiplicity ≠ 0 → _
        rw [brBi_eval _ _ bi env hdom]
        exact hsat.2 bi hbim
  have hside : ∀ env, (∀ c ∈ singleVarCs cs.algebraicConstraints, c.eval env = 0) →
      (cs.boxRewrite b).sideEffects bs env = cs.sideEffects bs env := by
    intro env hdom
    unfold ConstraintSystem.sideEffects
    show ((cs.busInteractions.map (brBi (singleVarCs cs.algebraicConstraints) b)).filter
      (fun bi => bs.isStateful bi.busId)).map _ = _
    induction cs.busInteractions with
    | nil => rfl
    | cons bi rest ih =>
      simp only [List.map_cons, List.filter_cons]
      have hb : bs.isStateful (brBi (singleVarCs cs.algebraicConstraints) b bi).busId
          = bs.isStateful bi.busId := rfl
      rw [hb]
      by_cases hst : bs.isStateful bi.busId = true
      · simp only [hst, if_pos]
        rw [List.map_cons, List.map_cons, ih]
        congr 1
        simp only [brBi_eval _ _ bi env hdom]
      · simp only [hst]
        exact ih
  have hadmEq : ∀ env, (∀ c ∈ singleVarCs cs.algebraicConstraints, c.eval env = 0) →
      ((cs.boxRewrite b).admissible bs env ↔ cs.admissible bs env) := by
    intro env hdom
    unfold ConstraintSystem.admissible
    have hmap : (cs.boxRewrite b).busInteractions.map (fun bi => bi.eval env)
        = cs.busInteractions.map (fun bi => bi.eval env) := by
      show (cs.busInteractions.map (brBi (singleVarCs cs.algebraicConstraints) b)).map
        (fun bi => bi.eval env) = _
      rw [List.map_map]
      exact List.map_congr_left (fun bi _ => brBi_eval _ _ bi env hdom)
    rw [hmap]
  refine PassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  · intro env hsat
    refine ⟨env, (hiff env).1 hsat, ?_⟩
    rw [hside env (hdomOut env hsat)]
    exact BusState.equiv_refl _
  · intro hinv env hsat bi hbi
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
    rw [brBi_eval _ _ bi0 env (hdomOut env hsat)]
    exact hinv env ((hiff env).1 hsat) bi0 hbi0
  · intro v hv
    rw [ConstraintSystem.mem_vars] at hv ⊢
    rcases hv with ⟨c', hc', hvc⟩ | ⟨bi', hbi', hvbi⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      exact Or.inl ⟨c, hc, brRw_vars _ _ c v hvc⟩
    · obtain ⟨bi, hbim, rfl⟩ := List.mem_map.1 hbi'
      rcases hvbi with hm | ⟨e', he', hve⟩
      · exact Or.inr ⟨bi, hbim, Or.inl (brRw_vars _ _ bi.multiplicity v hm)⟩
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
        exact Or.inr ⟨bi, hbim, Or.inr ⟨e, he, brRw_vars _ _ e v hve⟩⟩
  · intro env hadm hsat
    refine ⟨(hiff env).2 hsat, ?_, ?_⟩
    · exact (hadmEq env (hdomIn env hsat)).2 hadm
    · rw [hside env (hdomIn env hsat)]
      exact BusState.equiv_refl _

/-- The rewriter as a standalone (unguarded) pass; prime `p` re-checked at runtime. -/
def boxRewritePass (pw : PrimeWitness p) (b : DegreeBound) : VerifiedPass p := fun cs bs =>
  if hpB : pw.isPrime = true then
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    ⟨cs.boxRewrite b, [], cs.boxRewrite_correct bs b⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

/-- The completed composite (supersedes the `FlagFold.lean` version): substitute the XOR
    component, rewrite the over-bound survivors multilinearly, then collect the tautologies and
    pointwise duplicates. Wired under a single degree guard. -/
def flagFoldPass' (pw : PrimeWitness p) (b : DegreeBound) : VerifiedPassW p :=
  (fxSubstPass pw).andThen (boxRewritePass pw b).withFacts |>.andThen (boxTautoDropPass pw).withFacts
    |>.andThen (pointwiseDupDropPass pw).withFacts
