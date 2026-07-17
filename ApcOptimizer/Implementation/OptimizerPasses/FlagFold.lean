import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify

set_option autoImplicit false

/-! # Folding the XOR flag component (composite pass, part B: box tautologies)

Log entry 63: the last flag component of each unified scaled-check pair relates to the
survivors by XOR — degree 2 as a field polynomial — so substituting it away pushes the
substituted booleanity to degree 4 and the substituted check payload to degree 3. The
composite `flagFoldPass` therefore chains three unguarded sub-passes under a single degree
guard: (A) the entailed nonlinear substitution, (B) **this file's section**: replace multi-
variable constraints that vanish on their variables' proven finite domain box by `0` (the
substituted booleanity `E(E−1)` vanishes on the boolean box), and (C) drop stateless checks
whose message is pointwise equal to a retained one on the box.

Non-circularity for (B): only constraints with **at least two distinct variables** are ever
replaced, and the domain box is justified exclusively from **single-variable** constraints
(`findDomainAlg` sources) — which are therefore never replaced themselves. -/

variable {p : ℕ}

/-! ## Part B: box-tautology replacement -/

/-- The single-variable constraints of a list (the only `findDomainAlg` sources). -/
def singleVarCs (all : List (Expression p)) : List (Expression p) :=
  all.filter (fun c => c.vars.eraseDups.length == 1)

/-- Certificate: `c` mentions ≥ 2 distinct variables, every one carries a proven finite domain
    (from the single-variable constraints), the joint box is small, and `c` vanishes on all of
    it. -/
def btCert (singles : List (Expression p)) (c : Expression p) : Bool :=
  2 ≤ c.vars.eraseDups.length &&
  (let doms := c.vars.eraseDups.filterMap (fun v =>
     (findDomainAlg singles v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = c.vars.eraseDups) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (assignments doms).all (fun pt => decide (c.eval (envOf pt) = 0)))

/-- Cheap mirror of `btCert` over a precomputed (pure, memoized) domain lookup — a prefilter
    only; accepted candidates re-run the real certificate, so the proofs consume `btCert`
    alone. -/
def btPre (domOf : Variable → Option (List (ZMod p))) (c : Expression p) : Bool :=
  2 ≤ c.vars.eraseDups.length &&
  (let doms := c.vars.eraseDups.filterMap (fun v => (domOf v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = c.vars.eraseDups) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (assignments doms).all (fun pt => decide (c.eval (envOf pt) = 0)))

/-- The replacement condition: the memoized prefilter gates the (expensive) certificate.
    `singles` and `domOf` are computed once per pass invocation and passed in — a def-local
    `let` would be re-evaluated per constraint by arity expansion. -/
def btKeep (singles : List (Expression p)) (domOf : Variable → Option (List (ZMod p)))
    (c : Expression p) : Bool :=
  btPre domOf c && btCert singles c

theorem btKeep_cert {singles : List (Expression p)}
    {domOf : Variable → Option (List (ZMod p))} {c : Expression p}
    (h : btKeep singles domOf c = true) : btCert singles c = true := by
  unfold btKeep at h
  rw [Bool.and_eq_true] at h
  exact h.2

theorem btKeep_of_cert_false {singles : List (Expression p)}
    {domOf : Variable → Option (List (ZMod p))} {c : Expression p}
    (h : btCert singles c = false) : btKeep singles domOf c = false := by
  unfold btKeep
  rw [h, Bool.and_false]

/-- Replace certified box tautologies by the trivial constraint (parameterized over the
    precomputed prefilter inputs). -/
def ConstraintSystem.boxTautoReplaceWith (cs : ConstraintSystem p)
    (singles : List (Expression p)) (domOf : Variable → Option (List (ZMod p))) :
    ConstraintSystem p :=
  { cs with algebraicConstraints := cs.algebraicConstraints.map (fun c =>
      if btKeep singles domOf c then Expression.const 0 else c) }

/-- A single-variable constraint is never replaced (it fails the ≥ 2 guard), so it survives
    verbatim into the output — which is what lets the box justification stand on the output's
    own satisfaction. -/
theorem singleVar_mem_boxTautoReplace (cs : ConstraintSystem p)
    (domOf : Variable → Option (List (ZMod p))) (c : Expression p)
    (hc : c ∈ cs.algebraicConstraints) (hs : (c.vars.eraseDups.length == 1) = true) :
    c ∈ (cs.boxTautoReplaceWith (singleVarCs cs.algebraicConstraints) domOf).algebraicConstraints := by
  have hcf : btCert (singleVarCs cs.algebraicConstraints) c = false := by
    unfold btCert
    have h1 : ¬ (2 ≤ c.vars.eraseDups.length) := by
      have := of_decide_eq_true hs
      omega
    simp [h1]
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  rw [btKeep_of_cert_false hcf]
  simp

theorem ConstraintSystem.boxTautoReplace_correct [Fact p.Prime]
    (cs : ConstraintSystem p) (bs : BusSemantics p)
    (domOf : Variable → Option (List (ZMod p))) :
    PassCorrect cs (cs.boxTautoReplaceWith (singleVarCs cs.algebraicConstraints) domOf) [] bs := by
  -- every replaced constraint is zero under any assignment satisfying the output
  have hzero : ∀ env, (cs.boxTautoReplaceWith (singleVarCs cs.algebraicConstraints)
      domOf).satisfies bs env →
      ∀ c ∈ cs.algebraicConstraints, btCert (singleVarCs cs.algebraicConstraints) c = true →
      c.eval env = 0 := by
    intro env hsat c _hc hcert
    unfold btCert at hcert
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcert
    obtain ⟨_h2, ⟨⟨hcover, _hcap⟩, hall⟩⟩ := hcert
    have hcover' := of_decide_eq_true hcover
    have hdom : ∀ c' ∈ singleVarCs cs.algebraicConstraints, c'.eval env = 0 := by
      intro c' hc'
      simp only [singleVarCs] at hc'
      have hmem := List.mem_of_mem_filter hc'
      have hsingle : (c'.vars.eraseDups.length == 1) = true :=
        (List.mem_filter.1 hc').2
      exact hsat.1 c' (singleVar_mem_boxTautoReplace cs domOf c' hmem hsingle)
    have hmemdoms : ∀ vd ∈ c.vars.eraseDups.filterMap (fun v =>
        (findDomainAlg (singleVarCs cs.algebraicConstraints) v).map (fun d => (v, d))),
        env vd.1 ∈ vd.2 := by
      intro vd hvd
      obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
      cases hfd : findDomainAlg (singleVarCs cs.algebraicConstraints) v with
      | none => rw [hfd] at hvd'; simp at hvd'
      | some d =>
        rw [hfd] at hvd'
        simp only [Option.map_some, Option.some.injEq] at hvd'
        obtain rfl := hvd'.symm
        exact findDomainAlg_sound (singleVarCs cs.algebraicConstraints) v d hfd env hdom
    have hpt := mem_assignments (c.vars.eraseDups.filterMap (fun v =>
      (findDomainAlg (singleVarCs cs.algebraicConstraints) v).map (fun d => (v, d)))) env
      hmemdoms
    have hptz := of_decide_eq_true (List.all_eq_true.mp hall _ hpt)
    have hagree : c.eval (envOf ((c.vars.eraseDups.filterMap (fun v =>
        (findDomainAlg (singleVarCs cs.algebraicConstraints) v).map (fun d => (v, d)))).map
          (fun vd => (vd.1, env vd.1)))) = c.eval env := by
      refine Expression.eval_congr c _ env (fun v hv => ?_)
      refine envOf_map _ env v ?_
      rw [show ((c.vars.eraseDups.filterMap (fun v =>
        (findDomainAlg (singleVarCs cs.algebraicConstraints) v).map (fun d => (v, d)))).map
          Prod.fst) = c.vars.eraseDups from hcover']
      exact List.mem_eraseDups.2 hv
    rw [← hagree]; exact hptz
  have hiff : ∀ env, (cs.boxTautoReplaceWith (singleVarCs cs.algebraicConstraints)
      domOf).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    constructor
    · intro hsat
      refine ⟨fun c hc => ?_, hsat.2⟩
      by_cases hcond : btKeep (singleVarCs cs.algebraicConstraints) domOf c = true
      · exact hzero env hsat c hc (btKeep_cert hcond)
      · have h0 := hsat.1 _ (List.mem_map.2 ⟨c, hc, rfl⟩)
        rw [if_neg hcond] at h0
        exact h0
    · intro hsat
      refine ⟨fun c' hc' => ?_, hsat.2⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      by_cases hcond : btKeep (singleVarCs cs.algebraicConstraints) domOf c = true
      · rw [if_pos hcond]; rfl
      · rw [if_neg hcond]; exact hsat.1 c hc
  refine PassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    exact hinv env ((hiff env).1 hsat) bi hbi
  · intro v hv
    rw [ConstraintSystem.mem_vars] at hv ⊢
    rcases hv with ⟨c', hc', hvc⟩ | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      by_cases hcond : btKeep (singleVarCs cs.algebraicConstraints) domOf c = true
      · rw [if_pos hcond] at hvc; simp [Expression.vars] at hvc
      · rw [if_neg hcond] at hvc; exact Or.inl ⟨c, hc, hvc⟩
    · exact Or.inr h
  · intro env hadm hsat
    exact ⟨(hiff env).2 hsat, hadm, BusState.equiv_refl _⟩

/-- Part B as a standalone (unguarded) verified pass; prime `p` re-checked at runtime. -/
def boxTautoDropPass (pw : PrimeWitness p) : VerifiedPass p := fun cs bs =>
  if hpB : pw.isPrime = true then
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    let singles := singleVarCs cs.algebraicConstraints
    -- Build the per-variable domain cache in one linear pass over all occurrences, skipping
    -- variables already seen (a `contains` guard) rather than pre-deduplicating with the quadratic
    -- `List.eraseDups` over the whole ~10⁵-entry occurrence list. `findDomainAlg` is deterministic,
    -- so the resulting map — hence `boxTautoReplaceWith`'s output — is identical; the correctness
    -- theorem takes the oracle as an arbitrary function, so this rebuild is proof-transparent.
    let cache : Std.HashMap Variable (Option (List (ZMod p))) :=
      (cs.algebraicConstraints.flatMap Expression.vars).foldl
        (fun m v => if m.contains v then m else m.insert v (findDomainAlg singles v)) ∅
    ⟨cs.boxTautoReplaceWith singles (fun v => cache.getD v none), [],
     cs.boxTautoReplace_correct bs (fun v => cache.getD v none)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

/-! ## Part C: pointwise-duplicate stateless check removal -/

/-- Dropping bus interactions that are (a) stateless and (b) accepted under every assignment
    *satisfying the filtered system* is equivalence- and invariant-preserving. Generalizes
    `ConstraintSystem.filterBusStateless_correct` (whose `hok` is unconditional); the
    satisfaction halves are re-proved with the hypothesis threaded through. -/
theorem ConstraintSystem.filterBusEntailed_correct (cs : ConstraintSystem p)
    (bs : BusSemantics p) (keep : BusInteraction (Expression p) → Bool)
    (hstateless : ∀ bi ∈ cs.busInteractions, keep bi = false →
      bs.isStateful bi.busId = false)
    (hok : ∀ bi ∈ cs.busInteractions, keep bi = false → ∀ env,
      (cs.filterBus keep).satisfies bs env →
      (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    PassCorrect cs (cs.filterBus keep) [] bs := by
  have hiff : ∀ env, (cs.filterBus keep).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    simp only [ConstraintSystem.satisfies]
    constructor
    · intro hsat
      obtain ⟨hc, hb⟩ := hsat
      refine ⟨hc, fun bi hbimem => ?_⟩
      by_cases hk : keep bi = true
      · exact hb bi (List.mem_filter.2 ⟨hbimem, hk⟩)
      · intro hm; exact hok bi hbimem (by simpa using hk) env ⟨hc, hb⟩ hm
    · rintro ⟨hc, hb⟩
      exact ⟨hc, fun bi hbimem => hb bi (List.mem_filter.1 hbimem).1⟩
  have hfilter : ∀ (bis : List (BusInteraction (Expression p))),
      (∀ bi ∈ bis, keep bi = false → bs.isStateful bi.busId = false) →
      (bis.filter keep).filter (fun bi => bs.isStateful bi.busId)
        = bis.filter (fun bi => bs.isStateful bi.busId) := by
    intro bis
    induction bis with
    | nil => intro _; rfl
    | cons bi rest ih =>
      intro hall
      have hrest := ih (fun b hb hkf => hall b (List.mem_cons_of_mem _ hb) hkf)
      by_cases hk : keep bi = true
      · rw [List.filter_cons_of_pos hk]
        by_cases hst : bs.isStateful bi.busId = true
        · rw [List.filter_cons_of_pos (by simpa using hst),
              List.filter_cons_of_pos (by simpa using hst), hrest]
        · rw [List.filter_cons_of_neg (by simpa using hst),
              List.filter_cons_of_neg (by simpa using hst), hrest]
      · have hst : bs.isStateful bi.busId = false :=
          hall bi (List.mem_cons_self ..) (by simpa using hk)
        rw [List.filter_cons_of_neg hk,
            List.filter_cons_of_neg (by simp [hst]), hrest]
  have hside : ∀ env, (cs.filterBus keep).sideEffects bs env = cs.sideEffects bs env := by
    intro env
    simp only [ConstraintSystem.sideEffects, ConstraintSystem.filterBus]
    rw [hfilter cs.busInteractions hstateless]
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.filterBus_vars_subset keep) ?_
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    have hbimem : bi ∈ cs.busInteractions :=
      (List.mem_filter.1 (by simpa only [ConstraintSystem.filterBus] using hbi)).1
    exact hinv env ((hiff env).1 hsat) bi hbimem
  · intro env hadm hsat
    exact ⟨(hiff env).2 hsat,
      (cs.admissible_filterBus bs keep env
        (fun bi hbi hkf => Or.inr (hstateless bi hbi hkf))).2 hadm,
      by rw [hside]; exact BusState.equiv_refl _⟩


/-- Joint-box agreement: every joint variable of `R`/`R'` has a proven finite domain, the box
    is small, and the two expressions agree at every box point. -/
def boxAgree (singles : List (Expression p)) (R R' : Expression p) : Bool :=
  let jv := (R.vars ++ R'.vars).eraseDups
  let doms := jv.filterMap (fun v =>
    (findDomainAlg singles v).map (fun d => (v, d)))
  decide (doms.map Prod.fst = jv) &&
  decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
  (assignments doms).all (fun pt =>
    decide (R.eval (envOf pt) = R'.eval (envOf pt)))

/-- Slot-pair certificate: the two expressions are syntactically equal, or they decompose over
    the same carrier with the same constant coefficient and their offset difference vanishes on
    the joint (proven, small) domain box of the offset variables. The carrier must appear in
    both expressions — the `mentions` gate is ZMod-free, so the ubiquitous disjoint-variable
    pair costs plain tree walks, never `splitAt`'s per-node ring arithmetic (a carrier absent
    from `e'` could only certify through a fully cancelled coefficient in `e`, which the
    constant folding and normalization ahead of this pass never leave behind). -/
def slotEqCert (singles : List (Expression p)) (e e' : Expression p) : Bool :=
  e == e' ||
  e.vars.eraseDups.any (fun x =>
    e'.mentions x &&
    match e.splitAt x, e'.splitAt x with
    | some (k, R), some (k2, R') => k2 == k && boxAgree singles R R'
    | _, _ => false)

/-- Full-message certificate: same bus, same constant multiplicity, pointwise-equal payloads. -/
def msgEqCert (singles : List (Expression p)) (bi bi' : BusInteraction (Expression p)) : Bool :=
  bi.busId == bi'.busId &&
  (match bi.multiplicity.constValue?, bi'.multiplicity.constValue? with
   | some m, some m' => m == m'
   | _, _ => false) &&
  bi.payload.length == bi'.payload.length &&
  (bi.payload.zip bi'.payload).all (fun ee => slotEqCert singles ee.1 ee.2)

theorem boxAgree_sound [Fact p.Prime] (singles : List (Expression p)) (R R' : Expression p)
    (h : boxAgree singles R R' = true) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval env = 0) : R.eval env = R'.eval env := by
  unfold boxAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hcover, _hcap⟩, hall⟩ := h
  have hmemdoms : ∀ vd ∈ (R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (findDomainAlg singles v).map (fun d => (v, d))), env vd.1 ∈ vd.2 := by
    intro vd hvd
    obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
    cases hfd : findDomainAlg singles v with
    | none => rw [hfd] at hvd'; simp at hvd'
    | some d =>
      rw [hfd] at hvd'
      simp only [Option.map_some, Option.some.injEq] at hvd'
      obtain rfl := hvd'.symm
      exact findDomainAlg_sound singles v d hfd env hdom
  have hpt := mem_assignments ((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
    (findDomainAlg singles v).map (fun d => (v, d)))) env hmemdoms
  have hagree : ∀ v, v ∈ (R.vars ++ R'.vars).eraseDups →
      envOf (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
        (findDomainAlg singles v).map (fun d => (v, d)))).map
          (fun vd => (vd.1, env vd.1))) v = env v := by
    intro v hv
    refine envOf_map _ env v ?_
    rw [show (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (findDomainAlg singles v).map (fun d => (v, d)))).map Prod.fst)
      = (R.vars ++ R'.vars).eraseDups from hcover]
    exact hv
  have hRR := of_decide_eq_true (List.all_eq_true.mp hall _ hpt)
  have hRa : R.eval (envOf (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (findDomainAlg singles v).map (fun d => (v, d)))).map
        (fun vd => (vd.1, env vd.1)))) = R.eval env :=
    Expression.eval_congr R _ env (fun v hv =>
      hagree v (List.mem_eraseDups.2 (List.mem_append_left _ hv)))
  have hRa' : R'.eval (envOf (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (findDomainAlg singles v).map (fun d => (v, d)))).map
        (fun vd => (vd.1, env vd.1)))) = R'.eval env :=
    Expression.eval_congr R' _ env (fun v hv =>
      hagree v (List.mem_eraseDups.2 (List.mem_append_right _ hv)))
  rw [← hRa, ← hRa', hRR]

theorem slotEqCert_sound [Fact p.Prime] (singles : List (Expression p)) (e e' : Expression p)
    (h : slotEqCert singles e e' = true) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval env = 0) : e.eval env = e'.eval env := by
  unfold slotEqCert at h
  rw [Bool.or_eq_true] at h
  rcases h with heq | hany
  · rw [eq_of_beq heq]
  · obtain ⟨x, _hx, hx⟩ := List.any_eq_true.1 hany
    rw [Bool.and_eq_true] at hx
    obtain ⟨_hm, hx⟩ := hx
    cases hsX : e.splitAt x with
    | none => rw [hsX] at hx; simp at hx
    | some kR =>
      obtain ⟨k, R⟩ := kR
      cases hsY : e'.splitAt x with
      | none => rw [hsX, hsY] at hx; simp at hx
      | some kR' =>
        obtain ⟨k2, R'⟩ := kR'
        simp only [hsX, hsY, Bool.and_eq_true] at hx
        obtain ⟨hk2, hba⟩ := hx
        rw [Expression.splitAt_eval x e k R hsX env,
            Expression.splitAt_eval x e' k2 R' hsY env, eq_of_beq hk2,
            boxAgree_sound singles R R' hba env hdom]

theorem msgEqCert_sound [Fact p.Prime] (singles : List (Expression p))
    (bi bi' : BusInteraction (Expression p)) (h : msgEqCert singles bi bi' = true)
    (env : Variable → ZMod p)
    (hdom : ∀ c ∈ singles, c.eval env = 0) : bi.eval env = bi'.eval env := by
  unfold msgEqCert at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hbus, hmult⟩, hlen⟩, hslots⟩ := h
  have hmm : bi.multiplicity.eval env = bi'.multiplicity.eval env := by
    cases hm : bi.multiplicity.constValue? with
    | none => rw [hm] at hmult; simp at hmult
    | some m =>
      cases hm' : bi'.multiplicity.constValue? with
      | none => rw [hm, hm'] at hmult; simp at hmult
      | some m' =>
        rw [hm, hm'] at hmult
        rw [bi.multiplicity.constValue?_sound m hm env,
            bi'.multiplicity.constValue?_sound m' hm' env, eq_of_beq hmult]
  have hpay : bi.payload.map (fun e => e.eval env)
      = bi'.payload.map (fun e => e.eval env) := by
    have hlen' : bi.payload.length = bi'.payload.length := by
      simpa using hlen
    refine List.ext_getElem (by simpa) (fun i h1 h2 => ?_)
    have hi1 : i < bi.payload.length := by simpa using h1
    have hi2 : i < bi'.payload.length := by simpa using h2
    have hz : (bi.payload[i]'hi1, bi'.payload[i]'hi2) ∈ bi.payload.zip bi'.payload := by
      have hzi : (bi.payload.zip bi'.payload)[i]'(by rw [List.length_zip]; omega)
          = (bi.payload[i]'hi1, bi'.payload[i]'hi2) := by
        simp [List.getElem_zip]
      rw [← hzi]
      exact List.getElem_mem _
    have hcert := List.all_eq_true.mp hslots _ hz
    simp only [List.getElem_map]
    exact slotEqCert_sound singles _ _ hcert env hdom
  show bi.eval env = bi'.eval env
  unfold BusInteraction.eval
  rw [eq_of_beq hbus, hmm, hpay]

/-- Is `bi` the first of its pointwise class (no earlier certified twin)? -/
def pdFirst (bs : BusSemantics p) (singles : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (bi : BusInteraction (Expression p)) : Bool :=
  match bis.findIdx? (fun b => b == bi) with
  | none => true
  | some i => (bis.take i).all (fun b => bs.isStateful b.busId || !(msgEqCert singles b bi))

/-- Keep unless a *first-of-class* earlier stateless twin exists (depth-1 rule: the twin that
    justifies a drop is itself provably kept, so no chain induction is needed). -/
def pdKeep (bs : BusSemantics p) (singles : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (bi : BusInteraction (Expression p)) : Bool :=
  bs.isStateful bi.busId ||
  (match bis.findIdx? (fun b => b == bi) with
   | none => true
   | some i =>
     !((bis.take i).any (fun b => !bs.isStateful b.busId && msgEqCert singles b bi
         && pdFirst bs singles bis b)))

/-- A first-of-class interaction is always kept — the depth-1 justification for `pdKeep`. -/
theorem pdFirst_keep (bs : BusSemantics p) (singles : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (b : BusInteraction (Expression p))
    (h : pdFirst bs singles bis b = true) : pdKeep bs singles bis b = true := by
  unfold pdKeep
  rw [Bool.or_eq_true]
  right
  unfold pdFirst at h
  cases hidx : bis.findIdx? (fun x => x == b) with
  | none => simp
  | some i =>
    rw [hidx] at h
    simp only
    rw [Bool.not_eq_true']
    by_contra hany
    have hany' : ((bis.take i).any (fun b' => !bs.isStateful b'.busId
        && msgEqCert singles b' b && pdFirst bs singles bis b')) = true := by
      by_cases hh : ((bis.take i).any (fun b' => !bs.isStateful b'.busId
          && msgEqCert singles b' b && pdFirst bs singles bis b')) = true
      · exact hh
      · exact absurd (by simpa using hh) hany
    obtain ⟨b'', hb''mem, hb''⟩ := List.any_eq_true.1 hany'
    rw [Bool.and_eq_true, Bool.and_eq_true] at hb''
    obtain ⟨⟨hnst, hcert⟩, _⟩ := hb''
    have hall := List.all_eq_true.mp h b'' hb''mem
    rw [Bool.or_eq_true] at hall
    rcases hall with hst | hnc
    · rw [Bool.not_eq_true'] at hnst
      rw [hnst] at hst
      exact absurd hst (by simp)
    · rw [Bool.not_eq_true'] at hnc
      rw [hcert] at hnc
      exact absurd hnc (by simp)

/-! ### The fast duplicate analysis

`pdKeep` per interaction pays an O(#interactions) `findIdx?` (with deep structural equality)
plus a prefix scan of `msgEqCert`s — O(n²) certificate evaluations per invocation, the dominant
cost of this pass on interaction-heavy circuits. The analysis below computes the *same* drop
set in one left-to-right sweep: interactions are bucketed by the certificate's necessary
invariants (bus id, constant multiplicity, payload length — `msgEqCert` fails outright across
buckets), candidate pairs are prefiltered by per-slot structural hashes and variable Bloom
masks (`slotEqCert` needs syntactic equality or a shared variable per slot), and the
first-of-class check is memoized per bucket entry. The result is consumed as a *prefilter*
only: `pointwiseDupDropPass` re-verifies every flagged drop through the original `pdKeep`, so
the analysis carries no proof and a false flag can only cost time, never a wrong drop. -/

/-- A 64-bit Bloom mask of the expression's variables (for the shared-variable prefilter). -/
def Expression.pdVarBloom : Expression p → UInt64
  | .const _ => 0
  | .var y => (1 : UInt64) <<< (UInt64.ofNat ((mixHash (hash y.name) (hash y.powdrId?)).toNat % 64))
  | .add a b => a.pdVarBloom ||| b.pdVarBloom
  | .mul a b => a.pdVarBloom ||| b.pdVarBloom

/-- Structural hash of an expression (order-sensitive), for the slot-equality prefilter. -/
def Expression.pdStructHash : Expression p → UInt64
  | .const n => mixHash 11 (UInt64.ofNat n.val)
  | .var y => mixHash 13 (mixHash (hash y.name) (hash y.powdrId?))
  | .add a b => mixHash 17 (mixHash a.pdStructHash b.pdStructHash)
  | .mul a b => mixHash 19 (mixHash a.pdStructHash b.pdStructHash)

/-- Necessary condition for `msgEqCert` on two payloads, from the precomputed per-slot
    signatures: each slot pair is syntactically equal (hash) or shares a variable (Blooms). -/
def pdSigsCompatible (a b : Array (UInt64 × UInt64)) : Bool :=
  Array.isEqv a b (fun x y => x.1 == y.1 || (x.2 &&& y.2) != 0)

/-- Full-value hash of an interaction, for the dropped-value buckets. -/
def pdValHash (bi : BusInteraction (Expression p)) : UInt64 :=
  mixHash (hash bi.busId) (mixHash bi.multiplicity.pdStructHash
    (bi.payload.foldl (fun h e => mixHash h e.pdStructHash) 7))

/-- One bucket entry of the sweep: position, the interaction, its slot signatures, and whether
    it was kept. -/
structure PdEntry (p : ℕ) where
  pos : Nat
  bi : BusInteraction (Expression p)
  sigs : Array (UInt64 × UInt64)
  kept : Bool

/-- The value-keyed set of interactions the sweep decides to drop — exactly `pdKeep`'s drop set
    (drops are value-based there too: `findIdx?` evaluates every duplicate at its first
    occurrence). -/
def pdDropSet (bs : BusSemantics p) (singles : List (Expression p))
    (bis : List (BusInteraction (Expression p))) :
    Std.HashMap UInt64 (List (BusInteraction (Expression p))) := Id.run do
  let mut buckets : Std.HashMap UInt64 (List (PdEntry p)) := ∅
  let mut firstMemo : Std.HashMap Nat Bool := ∅
  let mut drops : Std.HashMap UInt64 (List (BusInteraction (Expression p))) := ∅
  let mut pos := 0
  for bi in bis do
    if !bs.isStateful bi.busId then
      match bi.multiplicity.constValue? with
      | none => pure ()   -- can neither be dropped nor certify a drop
      | some m =>
        let key := mixHash (hash bi.busId) (mixHash (hash m.val) (hash bi.payload.length))
        let sigs : Array (UInt64 × UInt64) :=
          (bi.payload.map (fun e => (e.pdStructHash, e.pdVarBloom))).toArray
        let entries := buckets.getD key []
        -- an exact duplicate mirrors its first occurrence's decision (findIdx? semantics)
        match entries.find? (fun e => decide (e.bi = bi)) with
        | some e =>
          if !e.kept then
            let vk := pdValHash bi
            drops := drops.insert vk (bi :: (drops.getD vk []))
        | none =>
          -- drop iff an earlier kept, first-of-class, certified twin exists
          let mut dropped := false
          for e in entries do
            if !dropped && e.kept && pdSigsCompatible e.sigs sigs then
              if msgEqCert singles e.bi bi then
                -- lazily decide whether `e` is first of its class
                let isFirst ← do
                  match firstMemo[e.pos]? with
                  | some b => pure b
                  | none =>
                    let b := entries.all (fun e' =>
                      !(e'.pos < e.pos && pdSigsCompatible e'.sigs e.sigs
                        && msgEqCert singles e'.bi e.bi))
                    firstMemo := firstMemo.insert e.pos b
                    pure b
                if isFirst then
                  dropped := true
          if dropped then
            let vk := pdValHash bi
            drops := drops.insert vk (bi :: (drops.getD vk []))
          buckets := buckets.insert key ({ pos, bi, sigs, kept := !dropped } :: entries)
    pos := pos + 1
  return drops

/-- Was `bi` flagged by the sweep? (`false` = flagged as a drop candidate.) -/
def pdFastKeep (drops : Std.HashMap UInt64 (List (BusInteraction (Expression p))))
    (bi : BusInteraction (Expression p)) : Bool :=
  match drops[pdValHash bi]? with
  | some l => !(l.any (fun b => decide (b = bi)))
  | none => true

/-- Part C as a standalone (unguarded) pass: drop stateless interactions pointwise-equal to an
    earlier first-of-class one. Stated over an arbitrary *prefilter* `fast`: the kept set is
    `fast bi || pdKeep … bi`, so a drop requires `pdKeep … = false` (the certified condition)
    and keeping more is always sound. `pointwiseDupDropPass` instantiates `fast` with the sweep
    above, which flags exactly `pdKeep`'s drop set — the expensive certified scan then runs only
    on the few genuine drops. -/
theorem ConstraintSystem.pointwiseDupDrop_correct [Fact p.Prime]
    (cs : ConstraintSystem p) (bs : BusSemantics p)
    (fast : BusInteraction (Expression p) → Bool) :
    PassCorrect cs
      (cs.filterBus
        (fun bi => fast bi || pdKeep bs (singleVarCs cs.algebraicConstraints) cs.busInteractions bi))
      [] bs :=
  cs.filterBusEntailed_correct bs _
       (by
         intro bi _ hkf
         rw [Bool.or_eq_false_iff] at hkf
         have hkf' := hkf.2
         unfold pdKeep at hkf'
         rw [Bool.or_eq_false_iff] at hkf'
         simpa using hkf'.1)
       (by
         intro bi hbimem hkf env hsat hm
         rw [Bool.or_eq_false_iff] at hkf
         have hkf' := hkf.2
         unfold pdKeep at hkf'
         rw [Bool.or_eq_false_iff] at hkf'
         obtain ⟨_hst, hmatch⟩ := hkf'
         cases hidx : cs.busInteractions.findIdx? (fun x => x == bi) with
         | none => rw [hidx] at hmatch; simp at hmatch
         | some i =>
           rw [hidx] at hmatch
           simp only [Bool.not_eq_false'] at hmatch
           obtain ⟨b, hbmem, hb⟩ := List.any_eq_true.1 hmatch
           rw [Bool.and_eq_true, Bool.and_eq_true] at hb
           obtain ⟨⟨hnst, hcert⟩, hfirst⟩ := hb
           have hbcs : b ∈ cs.busInteractions := List.mem_of_mem_take hbmem
           have hbkeep : pdKeep bs (singleVarCs cs.algebraicConstraints)
               cs.busInteractions b = true :=
             pdFirst_keep bs (singleVarCs cs.algebraicConstraints) cs.busInteractions b hfirst
           have hbout : b ∈ (cs.filterBus
               (fun bi => fast bi || pdKeep bs (singleVarCs cs.algebraicConstraints)
                 cs.busInteractions bi)).busInteractions :=
             List.mem_filter.2 ⟨hbcs, by simp [hbkeep]⟩
           have hdom : ∀ c ∈ singleVarCs cs.algebraicConstraints, c.eval env = 0 := by
             intro c hc
             exact hsat.1 c (List.mem_of_mem_filter hc)
           have heq : b.eval env = bi.eval env :=
             msgEqCert_sound (singleVarCs cs.algebraicConstraints) b bi hcert env hdom
           have hob := hsat.2 b hbout
           rw [heq] at hob
           exact hob hm)

def pointwiseDupDropPass (pw : PrimeWitness p) : VerifiedPass p := fun cs bs =>
  if hpB : pw.isPrime = true then
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    let singles := singleVarCs cs.algebraicConstraints
    -- The fast sweep flags exactly `pdKeep`'s drop set; the certified `pdKeep` re-verifies each
    -- flagged drop (short-circuited away for the unflagged rest by the `||`).
    let drops := pdDropSet bs singles cs.busInteractions
    ⟨cs.filterBus (fun bi => pdFastKeep drops bi || pdKeep bs singles cs.busInteractions bi), [],
     cs.pointwiseDupDrop_correct bs (pdFastKeep drops)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

/-! ## Part A: the entailed nonlinear substitution -/

/-- Boolean indicator product `∏ (v or 1−v)` selecting one point of the box. Heuristic data —
    the certificate validates its values pointwise, so the construction carries no proof. -/
def indicatorProd (others : List Variable) (pt : List (Variable × ZMod p)) : Expression p :=
  others.foldl (fun acc v =>
    if envOf pt v = 1 then Expression.mul acc (Expression.var v)
    else Expression.mul acc (Expression.add (Expression.const 1)
      (Expression.mul (Expression.const (-1)) (Expression.var v)))) (Expression.const 1)

/-- Interpolate the target's value over the survivor-side flags from the compatible points. -/
def buildE (d : FuData p) (vy : Variable) : Expression p :=
  let others := d.rxVars.eraseDups.filter (fun v => v != vy)
  d.pts.foldl (fun acc ptb =>
    if ptb.2 && (envOf ptb.1 vy == 1) then
      Expression.add acc (indicatorProd others ptb.1)
    else acc) (Expression.const 0)

/-- Per-target certificate: `vy` is a Y-side flag, the candidate solution `E` mentions neither
    `vy` nor anything outside the survivor's payload, and at every offset-compatible point the
    target equals `E`. -/
def fxCheckWith (d : FuData p) (E : Expression p) (vy : Variable) : Bool :=
  decide (vy ∈ d.ryVars) && !(E.mentions vy) &&
  decide (E.vars.all (fun v => v ∈ d.rxVars ∨ v ∈ d.ryVars)) &&
  decide (E.vars.all (fun v => v ∈ d.payXVars)) &&
  d.pts.all (fun ptb => !ptb.2 || decide (envOf ptb.1 vy = E.eval (envOf ptb.1)))

/-- The full certificate, defined through the shared pair data (as `fuCheck`). -/
def fxCheck (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (Expression p))
    (biX biY : BusInteraction (Expression p)) (x : Variable) (E : Expression p)
    (vy : Variable) : Bool :=
  match fuPairData? bs facts domCs biX biY x with
  | some d => fxCheckWith d E vy
  | none => false

theorem fxCheck_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (biX biY : BusInteraction (Expression p))
    (x : Variable) (E : Expression p) (vy : Variable)
    (h : fxCheck bs facts domCs biX biY x E vy = true) :
    ∀ v ∈ E.vars, v ∈ biX.payload.flatMap Expression.vars := by
  intro v hv
  unfold fxCheck at h
  cases hd : fuPairData? bs facts domCs biX biY x with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    have hpay : d.payXVars = biX.payload.flatMap Expression.vars := by
      unfold fuPairData? at hd
      cases hmx : biX.multiplicity.constValue? with
      | none => rw [hmx] at hd; simp at hd
      | some mx =>
        cases hmy : biY.multiplicity.constValue? with
        | none => rw [hmx, hmy] at hd; simp at hd
        | some my =>
          simp only [hmx, hmy] at hd
          split_ifs at hd
          cases hOX : biX.payload[0]? with
          | none => simp [hOX] at hd
          | some OX =>
            cases hOY : biY.payload[0]? with
            | none => simp [hOX, hOY] at hd
            | some OY =>
              simp only [hOX, hOY] at hd
              cases hbX : facts.slotBound biX.busId mx
                  (biX.payload.map Expression.constValue?) 0 with
              | none => simp [hbX] at hd
              | some bX =>
                cases hbY : facts.slotBound biY.busId my
                    (biY.payload.map Expression.constValue?) 0 with
                | none => simp [hbX, hbY] at hd
                | some bY =>
                  simp only [hbX, hbY] at hd
                  cases hsX : OX.splitAt x with
                  | none => simp [hsX] at hd
                  | some kRX =>
                    obtain ⟨k, RX⟩ := kRX
                    cases hsY : OY.splitAt x with
                    | none => simp [hsX, hsY] at hd
                    | some kRY =>
                      obtain ⟨k2, RY⟩ := kRY
                      simp only [hsX, hsY] at hd
                      split_ifs at hd
                      simp only [Option.some.injEq] at hd
                      rw [← hd]
    unfold fxCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact hpay ▸ of_decide_eq_true (List.all_eq_true.mp h.1.2 v hv)

theorem fxCheck_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (biX biY : BusInteraction (Expression p))
    (x : Variable) (E : Expression p) (vy : Variable)
    (h : fxCheck bs facts domCs biX biY x E vy = true)
    (env : Variable → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval env = 0)
    (hobX : (biX.eval env).multiplicity ≠ 0 → bs.violatesConstraint (biX.eval env) = false)
    (hobY : (biY.eval env).multiplicity ≠ 0 → bs.violatesConstraint (biY.eval env) = false) :
    env vy = E.eval env := by
  unfold fxCheck at h
  cases hd : fuPairData? bs facts domCs biX biY x with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    unfold fxCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hvyR', _hEm⟩, hEjoint⟩, _hEpay⟩, hcw⟩ := h
    unfold fuPairData? at hd
    cases hmx : biX.multiplicity.constValue? with
    | none => rw [hmx] at hd; simp at hd
    | some mx =>
      cases hmy : biY.multiplicity.constValue? with
      | none => rw [hmx, hmy] at hd; simp at hd
      | some my =>
        simp only [hmx, hmy] at hd
        split_ifs at hd with hmx0 hmy0
        cases hOX : biX.payload[0]? with
        | none => simp [hOX] at hd
        | some OX =>
          cases hOY : biY.payload[0]? with
          | none => simp [hOX, hOY] at hd
          | some OY =>
            simp only [hOX, hOY] at hd
            cases hbX : facts.slotBound biX.busId mx
                (biX.payload.map Expression.constValue?) 0 with
            | none => simp [hbX] at hd
            | some bX =>
              cases hbY : facts.slotBound biY.busId my
                  (biY.payload.map Expression.constValue?) 0 with
              | none => simp [hbX, hbY] at hd
              | some bY =>
                simp only [hbX, hbY] at hd
                cases hsX : OX.splitAt x with
                | none => simp [hsX] at hd
                | some kRX =>
                  obtain ⟨k, RX⟩ := kRX
                  cases hsY : OY.splitAt x with
                  | none => simp [hsX, hsY] at hd
                  | some kRY =>
                    obtain ⟨k2, RY⟩ := kRY
                    simp only [hsX, hsY] at hd
                    split_ifs at hd with hconds hcov hall
                    obtain ⟨hk2, hunit, hwrapX, hwrapY⟩ := hconds
                    obtain ⟨hcover, _hcap⟩ := hcov
                    simp only [Option.some.injEq] at hd
                    subst hd
                    simp only at hvyR' hEjoint hcw
                    -- acceptance and slot-value bounds
                    have hmXe : (biX.eval env).multiplicity = mx :=
                      biX.multiplicity.constValue?_sound mx hmx env
                    have hmYe : (biY.eval env).multiplicity = my :=
                      biY.multiplicity.constValue?_sound my hmy env
                    have hviolX : bs.violatesConstraint (biX.eval env) = false :=
                      hobX (by rw [hmXe]; exact hmx0)
                    have hviolY : bs.violatesConstraint (biY.eval env) = false :=
                      hobY (by rw [hmYe]; exact hmy0)
                    have hgetX : (biX.eval env).payload[0]? = some (OX.eval env) := by
                      show (biX.payload.map (fun e => e.eval env))[0]? = _
                      rw [List.getElem?_map, hOX]; rfl
                    have hgetY : (biY.eval env).payload[0]? = some (OY.eval env) := by
                      show (biY.payload.map (fun e => e.eval env))[0]? = _
                      rw [List.getElem?_map, hOY]; rfl
                    have hbXv : (OX.eval env).val < bX :=
                      facts.slotBound_sound (biX.eval env)
                        (biX.payload.map Expression.constValue?) 0 bX (OX.eval env)
                        (by rw [(rfl : (biX.eval env).busId = biX.busId), hmXe]; exact hbX)
                        (matches_evalPattern biX.payload env) hviolX hgetX
                    have hbYv : (OY.eval env).val < bY :=
                      facts.slotBound_sound (biY.eval env)
                        (biY.payload.map Expression.constValue?) 0 bY (OY.eval env)
                        (by rw [(rfl : (biY.eval env).busId = biY.busId), hmYe]; exact hbY)
                        (matches_evalPattern biY.payload env) hviolY hgetY
                    -- field decomposition `x = m·u + W`, both sides
                    set m := k⁻¹ with hm
                    have hOXe : OX.eval env = k * env x + RX.eval env :=
                      Expression.splitAt_eval x OX k RX hsX env
                    have hOYe : OY.eval env = k * env x + RY.eval env := by
                      have h0 := Expression.splitAt_eval x OY k2 RY hsY env
                      rw [hk2] at h0; exact h0
                    have hxX : env x = m * OX.eval env + (-m) * RX.eval env := by
                      have h1 : m * OX.eval env = m * k * env x + m * RX.eval env := by
                        rw [hOXe]; ring
                      rw [mul_comm m k, hunit, one_mul] at h1
                      linear_combination -h1
                    have hxY : env x = m * OY.eval env + (-m) * RY.eval env := by
                      have h1 : m * OY.eval env = m * k * env x + m * RY.eval env := by
                        rw [hOYe]; ring
                      rw [mul_comm m k, hunit, one_mul] at h1
                      linear_combination -h1
                    -- the environment restricted to the joint flag box is an enumerated point
                    have hmemdoms : ∀ vd ∈ (RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                        (findDomainAlg domCs v).map (fun d => (v, d))), env vd.1 ∈ vd.2 := by
                      intro vd hvd
                      obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
                      cases hfd : findDomainAlg domCs v with
                      | none => rw [hfd] at hvd'; simp at hvd'
                      | some dm =>
                        rw [hfd] at hvd'
                        simp only [Option.map_some, Option.some.injEq] at hvd'
                        obtain rfl := hvd'.symm
                        exact findDomainAlg_sound domCs v dm hfd env hdom
                    have hpt := mem_assignments ((RX.vars ++ RY.vars).eraseDups.filterMap
                      (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))) env hmemdoms
                    have hagree : ∀ v, v ∈ (RX.vars ++ RY.vars).eraseDups →
                        envOf (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))) v = env v := by
                      intro v hv
                      refine envOf_map _ env v ?_
                      rw [show (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                        (findDomainAlg domCs v).map (fun d => (v, d)))).map Prod.fst)
                        = (RX.vars ++ RY.vars).eraseDups from hcover]
                      exact hv
                    have hRXagree : RX.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                        (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                          (fun vd => (vd.1, env vd.1)))) = RX.eval env :=
                      Expression.eval_congr RX _ env (fun v hv =>
                        hagree v (List.mem_eraseDups.2 (List.mem_append_left _ hv)))
                    have hRYagree : RY.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                        (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                          (fun vd => (vd.1, env vd.1)))) = RY.eval env :=
                      Expression.eval_congr RY _ env (fun v hv =>
                        hagree v (List.mem_eraseDups.2 (List.mem_append_right _ hv)))
                    -- pair-level point bounds, at the environment's own point
                    have hpair := List.all_eq_true.mp hall _ hpt
                    rw [Bool.and_eq_true] at hpair
                    have hWXlt : ((-m) * RX.eval env).val < m.val := by
                      rw [← hRXagree]; exact of_decide_eq_true hpair.1
                    have hWYlt : ((-m) * RY.eval env).val < m.val := by
                      rw [← hRYagree]; exact of_decide_eq_true hpair.2
                    -- integer decomposition of `x.val` through both checks
                    have hbX1 : (OX.eval env).val ≤ bX - 1 := by omega
                    have hbY1 : (OY.eval env).val ≤ bY - 1 := by omega
                    have hle1 : m.val * (OX.eval env).val ≤ m.val * (bX - 1) :=
                      Nat.mul_le_mul_left _ hbX1
                    have hle2 : m.val * (OY.eval env).val ≤ m.val * (bY - 1) :=
                      Nat.mul_le_mul_left _ hbY1
                    have hMuX : (m * OX.eval env).val = m.val * (OX.eval env).val :=
                      ZMod.val_mul_of_lt (by omega)
                    have hMuY : (m * OY.eval env).val = m.val * (OY.eval env).val :=
                      ZMod.val_mul_of_lt (by omega)
                    have hsumX : (m * OX.eval env).val + ((-m) * RX.eval env).val < p := by
                      rw [hMuX]; omega
                    have hsumY : (m * OY.eval env).val + ((-m) * RY.eval env).val < p := by
                      rw [hMuY]; omega
                    have hvalX : (env x).val
                        = m.val * (OX.eval env).val + ((-m) * RX.eval env).val := by
                      rw [hxX, ZMod.val_add_of_lt hsumX, hMuX]
                    have hvalY : (env x).val
                        = m.val * (OY.eval env).val + ((-m) * RY.eval env).val := by
                      rw [hxY, ZMod.val_add_of_lt hsumY, hMuY]
                    have hres : ((-m) * RX.eval env).val = ((-m) * RY.eval env).val :=
                      residue_uniq m.val (OX.eval env).val (OY.eval env).val _ _
                        (hvalX.symm.trans hvalY) hWXlt hWYlt
                    -- the target condition at the environment's point
                    have hmempts : (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1)),
                        decide (((-m) * RX.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val
                          = ((-m) * RY.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val))
                        ∈ (assignments ((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (findDomainAlg domCs v).map (fun d => (v, d))))).map
                            (fun pt => (pt, decide (((-m) * RX.eval (envOf pt)).val
                              = ((-m) * RY.eval (envOf pt)).val))) :=
                      List.mem_map.2 ⟨_, hpt, rfl⟩
                    have horb := List.all_eq_true.mp hcw _ hmempts
                    have hb : decide (((-m) * RX.eval (envOf (((RX.vars
                        ++ RY.vars).eraseDups.filterMap (fun v =>
                          (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val
                        = ((-m) * RY.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val) = true :=
                      decide_eq_true (by rw [hRXagree, hRYagree]; exact hres)
                    simp only [hb, Bool.not_true, Bool.false_or, decide_eq_true_eq] at horb
                    have hEagree : E.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                        (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                          (fun vd => (vd.1, env vd.1)))) = E.eval env := by
                      refine Expression.eval_congr E _ env (fun v hv => ?_)
                      refine hagree v (List.mem_eraseDups.2 ?_)
                      rcases of_decide_eq_true (List.all_eq_true.mp hEjoint v hv) with h1 | h1
                      · exact List.mem_append_left _ h1
                      · exact List.mem_append_right _ h1
                    rw [← hagree vy (List.mem_eraseDups.2 (List.mem_append_right _ hvyR')),
                        ← hEagree]
                    exact horb

/-! ## The scan loop and the composite pass -/

/-- Scan for matched scaled-check pairs (reusing `fuCandidates`/`FUSeen`) and adopt every
    certified interpolation `vy := E`. The certificate is re-checked inside the adoption
    proof through `fxCheck`'s definition. -/
def fxLoop [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) →
    Std.HashMap UInt64 (List (FUSeen p cs)) → Solved p cs bs → Solved p cs bs
  | [], _, _, σ => σ
  | c :: rest, hmem, seen, σ =>
    have hc : c ∈ cs.busInteractions := hmem c (List.mem_cons_self ..)
    let hrest := fun c' h' => hmem c' (List.mem_cons_of_mem _ h')
    let cands := fuCandidates c
    match cands.findSome? (fun xk =>
        (seen.getD (fuKeyHash xk.2) []).findSome? (fun e => if e.key == xk.2 then some (e, xk.1) else none)) with
    | some ex =>
        match hdata : fuPairData? bs facts cs.algebraicConstraints ex.1.bi c ex.2 with
        | none =>
            fxLoop cs bs facts rest hrest
              (fuInsertAll seen (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩))) σ
        | some d =>
        let pairs := (d.ryVars.eraseDups.filter (fun v => !(v ∈ d.rxVars))).filterMap (fun vy =>
          if fxCheckWith d (buildE d vy) vy
          then some (vy, buildE d vy) else none)
        have hpairs : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env := by
          intro env hsat yt hyt
          obtain ⟨vy, _hvy, hif⟩ := List.mem_filterMap.1 hyt
          by_cases hck : fxCheckWith d (buildE d vy) vy = true
          · rw [if_pos hck] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            show env vy = (buildE d vy).eval env
            have hfc : fxCheck bs facts cs.algebraicConstraints ex.1.bi c ex.2
                (buildE d vy) vy = true := by
              unfold fxCheck; rw [hdata]; exact hck
            exact fxCheck_sound bs facts cs.algebraicConstraints ex.1.bi c ex.2
              (buildE d vy) vy hfc env
              (fun c' hc' => hsat.1 c' hc')
              (fun hmult => hsat.2 ex.1.bi ex.1.mem hmult)
              (fun hmult => hsat.2 c hc hmult)
          · rw [if_neg hck] at hif
            exact absurd hif (by simp)
        have hpairsV : ∀ yt ∈ pairs, ∀ z ∈ yt.2.vars, z ∈ cs.vars := by
          intro yt hyt z hz
          obtain ⟨vy, _hvy, hif⟩ := List.mem_filterMap.1 hyt
          by_cases hck : fxCheckWith d (buildE d vy) vy = true
          · rw [if_pos hck] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            have hfc : fxCheck bs facts cs.algebraicConstraints ex.1.bi c ex.2
                (buildE d vy) vy = true := by
              unfold fxCheck; rw [hdata]; exact hck
            obtain ⟨e', he', hv'⟩ := List.mem_flatMap.1
              (fxCheck_vars bs facts cs.algebraicConstraints ex.1.bi c ex.2
                (buildE d vy) vy hfc z hz)
            exact ConstraintSystem.mem_vars_of_payload ex.1.mem he' hv'
          · rw [if_neg hck] at hif
            exact absurd hif (by simp)
        fxLoop cs bs facts rest hrest
          (fuInsertAll seen (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩)))
          (σ.insertAll pairs hpairs hpairsV)
    | none =>
        fxLoop cs bs facts rest hrest
          (fuInsertAll seen (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩))) σ

/-- Part A as a standalone (unguarded) pass: substitute every certified interpolation. -/
def fxSubstPass (pw : PrimeWitness p) : VerifiedPassW p := fun cs bs facts =>
  if hpB : pw.isPrime = true then
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    let σ := fxLoop cs bs facts cs.busInteractions (fun _ h => h) ∅ Solved.empty
    if σ.map.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs.substF σ.fn, [],
      cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)
        (fun y t hyt => σ.varsIn y t hyt)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

/-- The composite: substitute the XOR component, then collect the two degree overshoots the
    substitution creates — the boxed-out booleanity (part B) and the pointwise-duplicate scaled
    check (part C). Intermediate states exceed the degree bound by design; the composite is
    wired under a single `guardDegree`. -/
def flagFoldPass (pw : PrimeWitness p) : VerifiedPassW p :=
  (fxSubstPass pw).andThen (boxTautoDropPass pw).withFacts
    |>.andThen (pointwiseDupDropPass pw).withFacts
