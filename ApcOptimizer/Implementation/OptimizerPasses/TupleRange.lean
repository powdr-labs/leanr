import ApcOptimizer.Implementation.OptimizerPasses.BytePack

set_option autoImplicit false

/-! # Tuple-range packing (`tupleRangePass`)

A tuple range checker (OpenVM's `TupleRangeChecker (s1, s2)`) accepts the 2-ary message `[x, y]`
iff `x < s1 ∧ y < s2`. When `s1 = 256`, that is *exactly* the conjunction of a single-value byte
check `[x, x, 0, 1]` on a bitwise-lookup bus and a variable range check `[y, bits]` with
`2 ^ bits = s2` — so the two stateless interactions pack into **one**, with the identical
satisfying set. This is powdr's byte + memory-pointer-limb packing (e.g. a byte operand paired
with a 13-bit `mem_ptr_limbs` check into `TupleRangeChecker (256, 8192)`).

All three table equivalences are proven `BusFacts` fields (`byteCheck`, `varRangeBus`,
`tupleRangeBus`, discharged for OpenVM in `ApcOptimizer/Implementation/OpenVmFacts.lean`); the pass is
VM-agnostic and degrades to a no-op under `BusFacts.trivial`. The target tuple bus typically has
*no* interactions in the input circuit, so its id cannot be read off `cs` — the pass probes the
fact function over a bounded id range instead. One pair is packed per invocation;
`iterateToFixpoint` drains them (the bus length strictly drops by one each time).

The correctness core (`mergeStateless2_correct`) is stated for *any* stateless two-for-one swap
whose replacement carries the conjunction of the replaced obligations — the byte-pair packing of
`BytePack.lean` is the same shape (kept as is). -/

variable {p : ℕ}

/-- Range check `[y, b]` (multiplicity `1`) on a variable-range-checker bus. -/
def rangeCheck1 (busId : Nat) (y b : Expression p) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1, payload := [y, b] }

/-- Tuple check `[x, y]` (multiplicity `1`). -/
def tupleCheck (busId : Nat) (x y : Expression p) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1, payload := [x, y] }

theorem rangeCheck1_eval (busId : Nat) (y b : Expression p) (env : Variable → ZMod p) :
    (rangeCheck1 busId y b).eval env
      = { busId := busId, multiplicity := 1, payload := [y.eval env, b.eval env] } := rfl

theorem tupleCheck_eval (busId : Nat) (x y : Expression p) (env : Variable → ZMod p) :
    (tupleCheck busId x y).eval env
      = { busId := busId, multiplicity := 1, payload := [x.eval env, y.eval env] } := rfl

/-! ## Correctness of a stateless two-for-one swap -/

/-- Replacing two stateless multiplicity-1 interactions `D₁`, `D₂` by one stateless
    multiplicity-1 interaction `C` whose obligation is exactly their conjunction (`hkey`) is
    `PassCorrect`: the satisfying set is unchanged, all three are outside the stateful side
    effects and the `admissible` filter, `C` breaks no invariant (`hbrk`), and its variables
    come from the replaced pair (`hvars`). -/
theorem mergeStateless2_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (hp1 : (1 : ZMod p) ≠ 0) (D₁ D₂ C : BusInteraction (Expression p))
    (hst1 : bs.isStateful D₁.busId = false) (hst2 : bs.isStateful D₂.busId = false)
    (hstC : bs.isStateful C.busId = false)
    (hm1 : D₁.multiplicity = .const 1) (hm2 : D₂.multiplicity = .const 1)
    (hmC : C.multiplicity = .const 1)
    (hkey : ∀ env, bs.violatesConstraint (C.eval env) = false ↔
        bs.violatesConstraint (D₁.eval env) = false ∧
          bs.violatesConstraint (D₂.eval env) = false)
    (hbrk : ∀ env, bs.breaksInvariant (C.eval env) = false)
    (hvars : ∀ v ∈ C.vars, v ∈ D₁.vars ∨ v ∈ D₂.vars)
    (pre mid post : List (BusInteraction (Expression p)))
    (hsplit : cs.busInteractions = pre ++ D₁ :: mid ++ D₂ :: post) :
    PassCorrect cs { cs with busInteractions := pre ++ C :: mid ++ post } [] bs := by
  set out : ConstraintSystem p :=
    { cs with busInteractions := pre ++ C :: mid ++ post } with hout
  have houtb : out.busInteractions = pre ++ C :: mid ++ post := rfl
  -- evaluated multiplicities are `1`
  have hme1 : ∀ env, (D₁.eval env).multiplicity = 1 := fun env => by
    show D₁.multiplicity.eval env = 1; rw [hm1]; rfl
  have hme2 : ∀ env, (D₂.eval env).multiplicity = 1 := fun env => by
    show D₂.multiplicity.eval env = 1; rw [hm2]; rfl
  have hmeC : ∀ env, (C.eval env).multiplicity = 1 := fun env => by
    show C.multiplicity.eval env = 1; rw [hmC]; rfl
  -- the obligation predicate that appears in `satisfies`
  set P : (Variable → ZMod p) → BusInteraction (Expression p) → Prop :=
    fun env bi => (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false
    with hP
  have hP1 : ∀ env, (P env D₁ ↔ bs.violatesConstraint (D₁.eval env) = false) := fun env =>
    ⟨fun h => h (by rw [hme1 env]; exact hp1), fun h _ => h⟩
  have hP2 : ∀ env, (P env D₂ ↔ bs.violatesConstraint (D₂.eval env) = false) := fun env =>
    ⟨fun h => h (by rw [hme2 env]; exact hp1), fun h _ => h⟩
  have hPC : ∀ env, (P env C ↔ bs.violatesConstraint (C.eval env) = false) := fun env =>
    ⟨fun h => h (by rw [hmeC env]; exact hp1), fun h _ => h⟩
  -- satisfaction equivalence
  have hsatiff : ∀ env, cs.satisfies bs env ↔ out.satisfies bs env := by
    intro env
    have hbus : (∀ bi ∈ cs.busInteractions, P env bi) ↔
        (∀ bi ∈ out.busInteractions, P env bi) := by
      rw [hsplit, houtb]
      simp only [List.forall_mem_append, List.forall_mem_cons]
      have hc := hPC env; have h1 := hP1 env; have h2 := hP2 env
      have hk := hkey env
      tauto
    exact ⟨fun ⟨hcons, hb⟩ => ⟨hcons, hbus.1 hb⟩, fun ⟨hcons, hb⟩ => ⟨hcons, hbus.2 hb⟩⟩
  -- the stateful-filtered interaction lists coincide
  have hfilt : cs.busInteractions.filter (fun bi => bs.isStateful bi.busId)
      = out.busInteractions.filter (fun bi => bs.isStateful bi.busId) := by
    rw [hsplit, houtb]
    simp only [List.filter_append, List.filter_cons, hst1, hst2, hstC, Bool.false_eq_true,
      if_false]
  have hside : ∀ env, cs.sideEffects bs env = out.sideEffects bs env := by
    intro env
    simp only [ConstraintSystem.sideEffects, hfilt]
  -- the active∧stateful evaluated messages coincide too
  have hstE1 : ∀ env, bs.isStateful (D₁.eval env).busId = false := fun _ => hst1
  have hstE2 : ∀ env, bs.isStateful (D₂.eval env).busId = false := fun _ => hst2
  have hstEC : ∀ env, bs.isStateful (C.eval env).busId = false := fun _ => hstC
  have hadmarg : ∀ env,
      (cs.busInteractions.map (fun bi => bi.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = (out.busInteractions.map (fun bi => bi.eval env)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
    intro env
    rw [hsplit, houtb]
    simp only [List.map_append, List.map_cons, List.filter_append, List.filter_cons,
      hstE1 env, hstE2 env, hstEC env, Bool.and_false, Bool.false_eq_true, if_false]
  have hadm : ∀ env, cs.admissible bs env ↔ out.admissible bs env := by
    intro env
    simp only [ConstraintSystem.admissible, hadmarg]
  -- membership: `out`'s variables come from `cs`'s
  have hmem1 : D₁ ∈ cs.busInteractions := by
    rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
  have hmem2 : D₂ ∈ cs.busInteractions := by
    rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
  have hsub : ∀ v ∈ out.vars, v ∈ cs.vars := by
    intro v hv
    rw [ConstraintSystem.mem_vars] at hv ⊢
    rcases hv with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hvbi⟩
    · exact Or.inl ⟨c, hc, hvc⟩
    · rw [houtb] at hbi
      simp only [List.mem_append, List.mem_cons] at hbi
      rcases hbi with (h | rfl | h) | h
      · exact Or.inr ⟨bi, by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto, hvbi⟩
      · have hv' : v ∈ bi.vars := by
          rw [BusInteraction.vars, List.mem_append]
          rcases hvbi with hm | ⟨e, he, hve⟩
          · exact Or.inl hm
          · exact Or.inr (List.mem_flatMap.2 ⟨e, he, hve⟩)
        have hback : ∀ (D : BusInteraction (Expression p)), v ∈ D.vars →
            v ∈ D.multiplicity.vars ∨ ∃ e ∈ D.payload, v ∈ e.vars := by
          intro D hD
          rw [BusInteraction.vars, List.mem_append] at hD
          rcases hD with h | h
          · exact Or.inl h
          · obtain ⟨e, he, hve⟩ := List.mem_flatMap.1 h
            exact Or.inr ⟨e, he, hve⟩
        rcases hvars v hv' with h | h
        · exact Or.inr ⟨D₁, hmem1, hback D₁ h⟩
        · exact Or.inr ⟨D₂, hmem2, hback D₂ h⟩
      · exact Or.inr ⟨bi, by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto, hvbi⟩
      · exact Or.inr ⟨bi, by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto, hvbi⟩
  refine PassCorrect.ofEnvEq ?_ ?_ hsub ?_
  · intro env hsat
    exact ⟨env, (hsatiff env).2 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    rw [houtb] at hbi
    simp only [List.mem_append, List.mem_cons] at hbi
    rcases hbi with (h | rfl | h) | h
    · exact hinv env ((hsatiff env).2 hsat) bi
        (by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto)
    · exact fun _ => hbrk env
    · exact hinv env ((hsatiff env).2 hsat) bi
        (by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto)
    · exact hinv env ((hsatiff env).2 hsat) bi
        (by rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto)
  · intro env hadmE hsat
    exact ⟨(hsatiff env).1 hsat, (hadm env).1 hadmE, by rw [hside]; exact BusState.equiv_refl _⟩

/-! ## The tuple-packing key: byte check + exact-width range check = tuple check -/

/-- The tuple check's obligation is exactly the byte check's and the range check's together,
    given `s1 = 256`, a supported constant width, and `2 ^ b.val = s2`. -/
theorem tupleKey (bs : BusSemantics p) (facts : BusFacts p bs)
    (bcBus vrBus trBus : Nat) (s1 s2 : Nat)
    (hbc : facts.byteCheck bcBus = true) (hvr : facts.varRangeBus vrBus = true)
    (htr : facts.tupleRangeBus trBus = some (s1, s2))
    (hs1 : s1 = 256) (b : ZMod p) (hble : b.val ≤ 25) (hs2 : 2 ^ b.val = s2)
    (x y : Expression p) :
    ∀ env, bs.violatesConstraint ((tupleCheck trBus x y).eval env) = false ↔
      bs.violatesConstraint ((byteCheck1 bcBus x).eval env) = false ∧
        bs.violatesConstraint ((rangeCheck1 vrBus y (.const b)).eval env) = false := by
  intro env
  obtain ⟨-, -, htriff⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
  obtain ⟨-, -, hbciff⟩ := facts.byteCheck_sound bcBus hbc
  obtain ⟨-, hvriff⟩ := facts.varRangeBus_sound vrBus hvr
  rw [tupleCheck_eval, byteCheck1_eval, rangeCheck1_eval]
  rw [htriff (x.eval env) (y.eval env) 1, hbciff (x.eval env) 1]
  have hB : bs.violatesConstraint
      { busId := vrBus, multiplicity := 1,
        payload := [y.eval env, (Expression.const b).eval env] } = false ↔
      (b.val ≤ 25 ∧ (y.eval env).val < 2 ^ b.val) :=
    hvriff (y.eval env) b 1
  rw [hB, hs1, ← hs2]
  constructor
  · rintro ⟨hx, hy⟩; exact ⟨hx, hble, hy⟩
  · rintro ⟨hx, -, hy⟩; exact ⟨hx, hy⟩

/-! ## The pass: find and pack one (byte, range) pair per invocation -/

/-- If `bi` is a single-value byte check `[e, e, 0, 1]` (multiplicity `1`) on a `byteCheck`
    bus, return the checked value. -/
def matchByteSingle {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  if facts.byteCheck bi.busId then
    match bi.multiplicity, bi.payload with
    | .const c, [e, e', z, op] =>
        if decide (c = 1) && decide (e = e') && decide (z = .const 0) && decide (op = .const 1)
        then some e else none
    | _, _ => none
  else none

/-- If `bi` is a range check `[y, b]` (multiplicity `1`, constant supported width, exact size
    `2 ^ b = s2`) on a `varRangeBus`, return `(y, b)`. -/
def matchRangeCheck {bs : BusSemantics p} (facts : BusFacts p bs) (s2 : Nat)
    (bi : BusInteraction (Expression p)) : Option (Expression p × ZMod p) :=
  if facts.varRangeBus bi.busId then
    match bi.multiplicity, bi.payload with
    | .const c, [y, .const b] =>
        if decide (c = 1) && decide (b.val ≤ 25) && decide (2 ^ b.val = s2)
        then some (y, b) else none
    | _, _ => none
  else none

/-- The declared tuple buses with a byte-sized first slot, probed over a bounded id range (the
    target bus typically carries no interaction in the input circuit, so its id cannot be read
    off `cs`). -/
def tupleBusCandidates {bs : BusSemantics p} (facts : BusFacts p bs) (maxId : Nat) :
    List (Nat × Nat × Nat) :=
  (List.range maxId).filterMap (fun k =>
    match facts.tupleRangeBus k with
    | some (s1, s2) => if s1 = 256 then some (k, s1, s2) else none
    | none => none)

/-- Scan for the complementary partner: given the first element's kind, find the second and
    return `(mid, second, post)`-style data. `which = true` looks for a range check (the first
    element was a byte check); `which = false` looks for a byte check. -/
def findPartner {bs : BusSemantics p} (facts : BusFacts p bs) (s2 : Nat) (which : Bool) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    Option (List (BusInteraction (Expression p)) × BusInteraction (Expression p) ×
      List (BusInteraction (Expression p)))
  | _, [] => none
  | revMid, b :: rest =>
    if which then
      match matchRangeCheck facts s2 b with
      | some _ => some (revMid.reverse, b, rest)
      | none => findPartner facts s2 which (b :: revMid) rest
    else
      match matchByteSingle facts b with
      | some _ => some (revMid.reverse, b, rest)
      | none => findPartner facts s2 which (b :: revMid) rest

/-- Try to pack, for one tuple bus `(trBus, s1, s2)`, the first (byte, range) or (range, byte)
    pair. The split equation and every fact are re-verified for the chosen candidate. -/
def findTuplePackGo (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (trBus s1 s2 : Nat)
    (revPre : List (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) → Option (PassResult cs bs)
  | [] => none
  | a :: rest =>
    let next := fun (_ : Unit) => findTuplePackGo cs bs facts hp1 trBus s1 s2 (a :: revPre) rest
    match matchByteSingle facts a with
    | some x =>
      match findPartner facts s2 true [] rest with
      | some (mid, second, post) =>
        match matchRangeCheck facts s2 second with
        | some (y, b) =>
          if hfacts : facts.byteCheck a.busId = true ∧ facts.varRangeBus second.busId = true
              ∧ facts.tupleRangeBus trBus = some (s1, s2) ∧ s1 = 256
              ∧ (b.val ≤ 25) ∧ (2 ^ b.val = s2) then
            if hsplit : cs.busInteractions = revPre.reverse ++ byteCheck1 a.busId x :: mid
                ++ rangeCheck1 second.busId y (.const b) :: post then
              some ⟨{ cs with busInteractions :=
                        revPre.reverse ++ tupleCheck trBus x y :: mid ++ post }, [],
                    by
                      obtain ⟨hbc, hvr, htr, hs1, hble, hs2⟩ := hfacts
                      obtain ⟨hstT, hbrkT, -⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
                      obtain ⟨hstB, -, -⟩ := facts.byteCheck_sound a.busId hbc
                      obtain ⟨hstR, -⟩ := facts.varRangeBus_sound second.busId hvr
                      refine mergeStateless2_correct cs bs hp1
                        (byteCheck1 a.busId x) (rangeCheck1 second.busId y (.const b))
                        (tupleCheck trBus x y) hstB hstR hstT rfl rfl rfl
                        (tupleKey bs facts a.busId second.busId trBus s1 s2 hbc hvr htr hs1 b
                          hble hs2 x y)
                        (fun env => by rw [tupleCheck_eval]; exact hbrkT (x.eval env) (y.eval env))
                        ?_ revPre.reverse mid post hsplit
                      intro v hv
                      rw [BusInteraction.vars, List.mem_append] at hv
                      rcases hv with hm | he
                      · exact absurd hm (by
                          rw [show (tupleCheck trBus x y).multiplicity.vars = [] from rfl]; simp)
                      · obtain ⟨e, he', hve⟩ := List.mem_flatMap.1 he
                        have : e = x ∨ e = y := by simpa [tupleCheck] using he'
                        rcases this with rfl | rfl
                        · exact Or.inl (by
                            rw [BusInteraction.vars, List.mem_append]
                            exact Or.inr (List.mem_flatMap.2 ⟨e, by
                              show e ∈ [e, e, Expression.const 0, Expression.const 1]
                              exact List.mem_cons_self .., hve⟩))
                        · exact Or.inr (by
                            rw [BusInteraction.vars, List.mem_append]
                            exact Or.inr (List.mem_flatMap.2 ⟨e, by
                              show e ∈ [e, Expression.const b]
                              exact List.mem_cons_self .., hve⟩))⟩
            else next ()
          else next ()
        | none => next ()
      | none => next ()
    | none =>
      match matchRangeCheck facts s2 a with
      | some (y, b) =>
        match findPartner facts s2 false [] rest with
        | some (mid, second, post) =>
          match matchByteSingle facts second with
          | some x =>
            if hfacts : facts.byteCheck second.busId = true ∧ facts.varRangeBus a.busId = true
                ∧ facts.tupleRangeBus trBus = some (s1, s2) ∧ s1 = 256
                ∧ (b.val ≤ 25) ∧ (2 ^ b.val = s2) then
              if hsplit : cs.busInteractions = revPre.reverse
                  ++ rangeCheck1 a.busId y (.const b) :: mid
                  ++ byteCheck1 second.busId x :: post then
                some ⟨{ cs with busInteractions :=
                          revPre.reverse ++ tupleCheck trBus x y :: mid ++ post }, [],
                      by
                        obtain ⟨hbc, hvr, htr, hs1, hble, hs2⟩ := hfacts
                        obtain ⟨hstT, hbrkT, -⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
                        obtain ⟨hstB, -, -⟩ := facts.byteCheck_sound second.busId hbc
                        obtain ⟨hstR, -⟩ := facts.varRangeBus_sound a.busId hvr
                        refine mergeStateless2_correct cs bs hp1
                          (rangeCheck1 a.busId y (.const b)) (byteCheck1 second.busId x)
                          (tupleCheck trBus x y) hstR hstB hstT rfl rfl rfl
                          (fun env => by
                            rw [tupleKey bs facts second.busId a.busId trBus s1 s2 hbc hvr htr
                              hs1 b hble hs2 x y env]
                            exact and_comm)
                          (fun env => by
                            rw [tupleCheck_eval]; exact hbrkT (x.eval env) (y.eval env))
                          ?_ revPre.reverse mid post hsplit
                        intro v hv
                        rw [BusInteraction.vars, List.mem_append] at hv
                        rcases hv with hm | he
                        · exact absurd hm (by
                            rw [show (tupleCheck trBus x y).multiplicity.vars = [] from rfl]
                            simp)
                        · obtain ⟨e, he', hve⟩ := List.mem_flatMap.1 he
                          have : e = x ∨ e = y := by simpa [tupleCheck] using he'
                          rcases this with rfl | rfl
                          · exact Or.inr (by
                              rw [BusInteraction.vars, List.mem_append]
                              exact Or.inr (List.mem_flatMap.2 ⟨e, by
                                show e ∈ [e, e, Expression.const 0, Expression.const 1]
                                exact List.mem_cons_self .., hve⟩))
                          · exact Or.inl (by
                              rw [BusInteraction.vars, List.mem_append]
                              exact Or.inr (List.mem_flatMap.2 ⟨e, by
                                show e ∈ [e, Expression.const b]
                                exact List.mem_cons_self .., hve⟩))⟩
              else next ()
            else next ()
          | none => next ()
        | none => next ()
      | none => next ()

/-- Pack one byte check and one exact-width range check into a tuple check, for the first
    declared tuple bus that fits. `iterateToFixpoint` drains all packable pairs. -/
def tupleRangePass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    let maxId := (cs.busInteractions.map (fun bi => bi.busId)).foldl max 0 + 65
    let rec tryBuses : List (Nat × Nat × Nat) → Option (PassResult cs bs)
      | [] => none
      | (trBus, s1, s2) :: rest =>
        match findTuplePackGo cs bs facts hp1 trBus s1 s2 [] cs.busInteractions with
        | some r => some r
        | none => tryBuses rest
    match tryBuses (tupleBusCandidates facts maxId) with
    | some r => r
    | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
