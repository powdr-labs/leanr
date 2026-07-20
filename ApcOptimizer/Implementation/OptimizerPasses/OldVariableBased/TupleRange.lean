import ApcOptimizer.Implementation.OptimizerPasses.BytePack
import ApcOptimizer.Implementation.OptimizerPasses.ListSplit

set_option autoImplicit false

/-! # Tuple-range packing (`tupleRangePass`)

A tuple range checker (OpenVM's `TupleRangeChecker (s1, s2)`) accepts the 2-ary message `[x, y]`
iff `x < s1 ∧ y < s2`. When `s1 = 256`, that is *exactly* the conjunction of a single-value byte
check (`mkByteCheck`, recognized through `byteXorSpec`) and a variable range check `[y, bits]` with
`2 ^ bits = s2` — so the two stateless interactions pack into **one**, with the identical
satisfying set. This is powdr's byte + memory-pointer-limb packing (e.g. a byte operand paired
with a 13-bit `mem_ptr_limbs` check into `TupleRangeChecker (256, 8192)`).

All three table equivalences are proven `BusFacts` fields (`byteXorSpec`, `varRangeBus`,
`tupleRangeBus`, discharged for OpenVM in `ApcOptimizer/Implementation/OpenVmFacts.lean`); the pass is
VM-agnostic and degrades to a no-op under `BusFacts.trivial`. The target tuple bus typically has
*no* interactions in the input circuit, so its id cannot be read off `cs` — the pass probes the
fact function over a bounded id range instead. All packable pairs are drained in **one**
invocation (the internal loop recurses on the strictly-dropping interaction count), and each
accepted pack's split equation `cs.busInteractions = pre ++ D₁ :: mid ++ D₂ :: post` holds by
construction from the array extracts (`split_of_extracts`, as in `BusPairCancel`) rather than by
an O(#interactions) deep structural comparison per accept.

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
    (bcBus vrBus trBus : Nat) (s1 s2 : Nat) (spec : ByteXorSpec p)
    (hspec : facts.byteXorSpec bcBus = some spec) (hbound : spec.bound = 256)
    (hvr : facts.varRangeBus vrBus = true)
    (htr : facts.tupleRangeBus trBus = some (s1, s2))
    (hs1 : s1 = 256) (b : ZMod p) (hble : b.val ≤ 17) (hs2 : 2 ^ b.val = s2)
    (x y : Expression p) :
    ∀ env, bs.violatesConstraint ((tupleCheck trBus x y).eval env) = false ↔
      bs.violatesConstraint ((mkByteCheck spec bcBus x).eval env) = false ∧
        bs.violatesConstraint ((rangeCheck1 vrBus y (.const b)).eval env) = false := by
  intro env
  obtain ⟨-, -, htriff⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
  obtain ⟨-, hvriff⟩ := facts.varRangeBus_sound vrBus hvr
  rw [tupleCheck_eval, rangeCheck1_eval,
    mkByteCheck_accepted bs facts spec bcBus hspec x env, hbound]
  rw [htriff (x.eval env) (y.eval env) 1]
  have hB : bs.violatesConstraint
      { busId := vrBus, multiplicity := 1,
        payload := [y.eval env, (Expression.const b).eval env] } = false ↔
      (b.val ≤ 17 ∧ (y.eval env).val < 2 ^ b.val) :=
    hvriff (y.eval env) b 1
  rw [hB, hs1, ← hs2]
  constructor
  · rintro ⟨hx, hy⟩; exact ⟨hx, hble, hy⟩
  · rintro ⟨hx, -, hy⟩; exact ⟨hx, hy⟩

/-! ## The pass: find and pack every (byte, range) pair in one invocation -/

/-- If `bi` is a single-value byte check (decoded op `= xorOp`, `o₁ = o₂`, result `0`, multiplicity
    `1`) on a `byteXorSpec` bus with byte bound `256`, return the bus spec and checked value. -/
def matchByteSingle {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (ByteXorSpec p × Expression p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
          if bi.multiplicity = .const 1 ∧ op = .const spec.xorOp ∧ o1 = o2 ∧ r = .const 0
          then some (spec, o1) else none
      | none => none
    else none

/-- If `bi` is a range check `[y, b]` (multiplicity `1`, constant supported width, exact size
    `2 ^ b = s2`) on a `varRangeBus`, return `(y, b)`. -/
def matchRangeCheck {bs : BusSemantics p} (facts : BusFacts p bs) (s2 : Nat)
    (bi : BusInteraction (Expression p)) : Option (Expression p × ZMod p) :=
  if facts.varRangeBus bi.busId then
    match bi.multiplicity, bi.payload with
    | .const c, [y, .const b] =>
        if decide (c = 1) && decide (b.val ≤ 17) && decide (2 ^ b.val = s2)
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

/-! ## Matcher soundness: a successful match pins the canonical shape by construction -/

/-- A `matchByteSingle` hit *is* the canonical single-value byte check `mkByteCheck spec busId x`
    (on a `byteXorSpec` bus with byte bound `256`) — the accepted split equation follows with no
    runtime comparison. -/
theorem matchByteSingle_eq {bs : BusSemantics p} {facts : BusFacts p bs}
    {bi : BusInteraction (Expression p)} {spec : ByteXorSpec p} {x : Expression p}
    (h : matchByteSingle facts bi = some (spec, x)) :
    bi = mkByteCheck spec bi.busId x ∧ facts.byteXorSpec bi.busId = some spec ∧
      spec.bound = 256 := by
  obtain ⟨busId, mult, payload⟩ := bi
  unfold matchByteSingle at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec' hspec
    split at h
    · rename_i hb
      split at h
      · rename_i op o1 o2 r hdec
        split_ifs at h with hc
        obtain ⟨hm, hop, ho12, hr⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, hspec, of_decide_eq_true hb⟩
        have hpay : payload = spec'.encode (.const spec'.xorOp) o1 o1 (.const 0) := by
          have he := spec'.decode_eq_encode payload op o1 o2 r hdec
          rw [hop, ← ho12, hr] at he; exact he
        have hm' : mult = Expression.const 1 := hm
        show ({ busId := busId, multiplicity := mult, payload := payload } :
          BusInteraction (Expression p)) = mkByteCheck spec' busId o1
        rw [hm', hpay]; rfl
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- A `matchRangeCheck` hit *is* the canonical range check, and carries the width facts the
    packing key needs. -/
theorem matchRangeCheck_eq {bs : BusSemantics p} {facts : BusFacts p bs} {s2 : Nat}
    {bi : BusInteraction (Expression p)} {y : Expression p} {b : ZMod p}
    (h : matchRangeCheck facts s2 bi = some (y, b)) :
    bi = rangeCheck1 bi.busId y (.const b) ∧ facts.varRangeBus bi.busId = true ∧
      b.val ≤ 17 ∧ 2 ^ b.val = s2 := by
  obtain ⟨busId, mult, payload⟩ := bi
  simp only [matchRangeCheck] at h
  split at h
  · rename_i hvr
    split at h
    · rename_i c y' b'
      split at h
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨rfl, hble⟩, hs2⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hvr, hble, hs2⟩
      · cases h
    · cases h
  · cases h

/-! ## Indexed partner scans -/

/-- First position `≥ i` holding an exact-size range check, with its data and the matching
    fact (the enclosing scan turns the position into a split equation by construction). -/
def findRangeIdx {bs : BusSemantics p} (facts : BusFacts p bs) (s2 : Nat)
    (arr : Array (BusInteraction (Expression p))) (i : Nat) :
    Option ((j : Nat) ×' (y : Expression p) ×' (b : ZMod p) ×'
      (i ≤ j ∧ ∃ hj : j < arr.size, matchRangeCheck facts s2 arr[j] = some (y, b))) :=
  if hi : i < arr.size then
    match hm : matchRangeCheck facts s2 arr[i] with
    | some (y, b) => some ⟨i, y, b, Nat.le_refl i, hi, hm⟩
    | none =>
      match findRangeIdx facts s2 arr (i + 1) with
      | some ⟨j, y, b, h⟩ => some ⟨j, y, b, Nat.le_of_succ_le h.1, h.2⟩
      | none => none
  else none
  termination_by arr.size - i

/-- First position `≥ i` holding a single-value byte check, with its data and the matching
    fact. -/
def findByteIdx {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (Expression p))) (i : Nat) :
    Option ((j : Nat) ×' (spec : ByteXorSpec p) ×' (x : Expression p) ×'
      (i ≤ j ∧ ∃ hj : j < arr.size, matchByteSingle facts arr[j] = some (spec, x))) :=
  if hi : i < arr.size then
    match hm : matchByteSingle facts arr[i] with
    | some (spec, x) => some ⟨i, spec, x, Nat.le_refl i, hi, hm⟩
    | none =>
      match findByteIdx facts arr (i + 1) with
      | some ⟨j, spec, x, h⟩ => some ⟨j, spec, x, Nat.le_of_succ_le h.1, h.2⟩
      | none => none
  else none
  termination_by arr.size - i

/-! ## The accept certificates (one per pair orientation) -/

/-- Packing a byte check (first) with a range check (second) into a tuple check is
    `PassCorrect`, given the canonical split equation and the matched facts. -/
theorem packByteFirst_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (trBus s1 s2 bcBus vrBus : Nat)
    (htr : facts.tupleRangeBus trBus = some (s1, s2)) (hs1 : s1 = 256)
    (x y : Expression p) (b : ZMod p) (spec : ByteXorSpec p)
    (hspec : facts.byteXorSpec bcBus = some spec) (hbound : spec.bound = 256)
    (hvr : facts.varRangeBus vrBus = true) (hble : b.val ≤ 17) (hs2 : 2 ^ b.val = s2)
    (pre mid post : List (BusInteraction (Expression p)))
    (hsplit : cs.busInteractions
      = pre ++ mkByteCheck spec bcBus x :: mid ++ rangeCheck1 vrBus y (.const b) :: post) :
    PassCorrect cs
      { cs with busInteractions := pre ++ tupleCheck trBus x y :: mid ++ post } [] bs := by
  obtain ⟨hstT, hbrkT, -⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
  have hstB : bs.isStateful bcBus = false := (facts.byteXorSpec_sound bcBus spec hspec).1
  obtain ⟨hstR, -⟩ := facts.varRangeBus_sound vrBus hvr
  refine mergeStateless2_correct cs bs hp1
    (mkByteCheck spec bcBus x) (rangeCheck1 vrBus y (.const b))
    (tupleCheck trBus x y) hstB hstR hstT rfl rfl rfl
    (tupleKey bs facts bcBus vrBus trBus s1 s2 spec hspec hbound hvr htr hs1 b hble hs2 x y)
    (fun env => by rw [tupleCheck_eval]; exact hbrkT (x.eval env) (y.eval env))
    ?_ pre mid post hsplit
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
        exact Or.inr (List.mem_flatMap.2 ⟨e, mkByteCheck_operand_mem spec bcBus e, hve⟩))
    · exact Or.inr (by
        rw [BusInteraction.vars, List.mem_append]
        exact Or.inr (List.mem_flatMap.2 ⟨e, by
          show e ∈ [e, Expression.const b]
          exact List.mem_cons_self .., hve⟩))

/-- Packing a range check (first) with a byte check (second) into a tuple check is
    `PassCorrect` — the mirrored orientation. -/
theorem packRangeFirst_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (trBus s1 s2 bcBus vrBus : Nat)
    (htr : facts.tupleRangeBus trBus = some (s1, s2)) (hs1 : s1 = 256)
    (x y : Expression p) (b : ZMod p) (spec : ByteXorSpec p)
    (hspec : facts.byteXorSpec bcBus = some spec) (hbound : spec.bound = 256)
    (hvr : facts.varRangeBus vrBus = true) (hble : b.val ≤ 17) (hs2 : 2 ^ b.val = s2)
    (pre mid post : List (BusInteraction (Expression p)))
    (hsplit : cs.busInteractions
      = pre ++ rangeCheck1 vrBus y (.const b) :: mid ++ mkByteCheck spec bcBus x :: post) :
    PassCorrect cs
      { cs with busInteractions := pre ++ tupleCheck trBus x y :: mid ++ post } [] bs := by
  obtain ⟨hstT, hbrkT, -⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
  have hstB : bs.isStateful bcBus = false := (facts.byteXorSpec_sound bcBus spec hspec).1
  obtain ⟨hstR, -⟩ := facts.varRangeBus_sound vrBus hvr
  refine mergeStateless2_correct cs bs hp1
    (rangeCheck1 vrBus y (.const b)) (mkByteCheck spec bcBus x)
    (tupleCheck trBus x y) hstR hstB hstT rfl rfl rfl
    (fun env => by
      rw [tupleKey bs facts bcBus vrBus trBus s1 s2 spec hspec hbound hvr htr hs1 b hble hs2 x y env]
      exact and_comm)
    (fun env => by rw [tupleCheck_eval]; exact hbrkT (x.eval env) (y.eval env))
    ?_ pre mid post hsplit
  intro v hv
  rw [BusInteraction.vars, List.mem_append] at hv
  rcases hv with hm | he
  · exact absurd hm (by
      rw [show (tupleCheck trBus x y).multiplicity.vars = [] from rfl]; simp)
  · obtain ⟨e, he', hve⟩ := List.mem_flatMap.1 he
    have : e = x ∨ e = y := by simpa [tupleCheck] using he'
    rcases this with rfl | rfl
    · exact Or.inr (by
        rw [BusInteraction.vars, List.mem_append]
        exact Or.inr (List.mem_flatMap.2 ⟨e, mkByteCheck_operand_mem spec bcBus e, hve⟩))
    · exact Or.inl (by
        rw [BusInteraction.vars, List.mem_append]
        exact Or.inr (List.mem_flatMap.2 ⟨e, by
          show e ∈ [e, Expression.const b]
          exact List.mem_cons_self .., hve⟩))

/-- Indexed left-to-right scan for the first packable pair for tuple bus `trBus`, starting at
    position `i`: at each position, a byte check looks right for the first exact-size range
    check, a range check looks right for the first byte check. The split equation holds by
    construction (`split_of_extracts`) rather than by an O(#interactions) whole-list
    comparison, and the result carries the strict interaction-count decrease the drain loop
    recurses on. -/
def findTuplePackIdx (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (trBus s1 s2 : Nat)
    (htr : facts.tupleRangeBus trBus = some (s1, s2)) (hs1 : s1 = 256)
    (arr : Array (BusInteraction (Expression p)))
    (harr : arr = cs.busInteractions.toArray) (i : Nat) :
    Option ((r : PassResult cs bs) ×'
      r.out.busInteractions.length < cs.busInteractions.length) :=
  if hi : i < arr.size then
    let next := fun (_ : Unit) =>
      findTuplePackIdx cs bs facts hp1 trBus s1 s2 htr hs1 arr harr (i + 1)
    match hmb : matchByteSingle facts arr[i] with
    | some (spec, x) =>
      match findRangeIdx facts s2 arr (i + 1) with
      | some ⟨j, y, b, hj⟩ =>
        match hR : arr[j]? with
        | some R =>
          have hij : i < j := Nat.lt_of_succ_le hj.1
          have hmr : matchRangeCheck facts s2 R = some (y, b) := by
            obtain ⟨hjs, hm⟩ := hj.2
            rw [Array.getElem?_eq_getElem hjs, Option.some.injEq] at hR
            exact hR ▸ hm
          have hbe := matchByteSingle_eq (facts := facts) hmb
          have hre := matchRangeCheck_eq (facts := facts) hmr
          have hsplit : cs.busInteractions
              = (arr.extract 0 i).toList ++ mkByteCheck spec (arr[i]).busId x ::
                (arr.extract (i + 1) j).toList
                ++ rangeCheck1 R.busId y (.const b) :: (arr.extract (j + 1) arr.size).toList := by
            have h0 := split_of_extracts harr hij hi hR
            rw [hbe.1, hre.1] at h0
            exact h0
          have hlt : ((arr.extract 0 i).toList ++ tupleCheck trBus x y ::
              (arr.extract (i + 1) j).toList ++ (arr.extract (j + 1) arr.size).toList).length
              < cs.busInteractions.length := by
            rw [hsplit]
            simp only [List.length_append, List.length_cons]
            omega
          some ⟨⟨{ cs with busInteractions :=
                    (arr.extract 0 i).toList ++ tupleCheck trBus x y ::
                    (arr.extract (i + 1) j).toList ++ (arr.extract (j + 1) arr.size).toList },
                 [],
                 packByteFirst_correct cs bs facts hp1 trBus s1 s2 (arr[i]).busId R.busId
                   htr hs1 x y b spec hbe.2.1 hbe.2.2 hre.2.1 hre.2.2.1 hre.2.2.2 _ _ _ hsplit⟩,
               hlt⟩
        | none => next ()
      | none => next ()
    | none =>
      match hmrf : matchRangeCheck facts s2 arr[i] with
      | some (y, b) =>
        match findByteIdx facts arr (i + 1) with
        | some ⟨j, spec, x, hj⟩ =>
          match hR : arr[j]? with
          | some R =>
            have hij : i < j := Nat.lt_of_succ_le hj.1
            have hmb2 : matchByteSingle facts R = some (spec, x) := by
              obtain ⟨hjs, hm⟩ := hj.2
              rw [Array.getElem?_eq_getElem hjs, Option.some.injEq] at hR
              exact hR ▸ hm
            have hre := matchRangeCheck_eq (facts := facts) hmrf
            have hbe := matchByteSingle_eq (facts := facts) hmb2
            have hsplit : cs.busInteractions
                = (arr.extract 0 i).toList ++ rangeCheck1 (arr[i]).busId y (.const b) ::
                  (arr.extract (i + 1) j).toList
                  ++ mkByteCheck spec R.busId x :: (arr.extract (j + 1) arr.size).toList := by
              have h0 := split_of_extracts harr hij hi hR
              rw [hre.1, hbe.1] at h0
              exact h0
            have hlt : ((arr.extract 0 i).toList ++ tupleCheck trBus x y ::
                (arr.extract (i + 1) j).toList ++ (arr.extract (j + 1) arr.size).toList).length
                < cs.busInteractions.length := by
              rw [hsplit]
              simp only [List.length_append, List.length_cons]
              omega
            some ⟨⟨{ cs with busInteractions :=
                      (arr.extract 0 i).toList ++ tupleCheck trBus x y ::
                      (arr.extract (i + 1) j).toList ++ (arr.extract (j + 1) arr.size).toList },
                   [],
                   packRangeFirst_correct cs bs facts hp1 trBus s1 s2 R.busId (arr[i]).busId
                     htr hs1 x y b spec hbe.2.1 hbe.2.2 hre.2.1 hre.2.2.1 hre.2.2.2 _ _ _ hsplit⟩,
                 hlt⟩
          | none => next ()
        | none => next ()
      | none => next ()
  else none
  termination_by arr.size - i

/-- Try each candidate tuple bus in order (the order the fixpoint-wrapped single-pack pass
    observed): the first bus with a packable pair wins. The candidate facts are re-established
    once per bus, so the packing scan itself carries no runtime fact decides. -/
def tryTupleBuses (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (arr : Array (BusInteraction (Expression p)))
    (harr : arr = cs.busInteractions.toArray) :
    List (Nat × Nat × Nat) →
    Option ((r : PassResult cs bs) ×'
      r.out.busInteractions.length < cs.busInteractions.length)
  | [] => none
  | (trBus, s1, s2) :: rest =>
    if h : facts.tupleRangeBus trBus = some (s1, s2) ∧ s1 = 256 then
      match findTuplePackIdx cs bs facts hp1 trBus s1 s2 h.1 h.2 arr harr 0 with
      | some r => some r
      | none => tryTupleBuses cs bs facts hp1 arr harr rest
    else tryTupleBuses cs bs facts hp1 arr harr rest

/-- Drain every packable pair: pack the first (bus-major, then position-major) pair, recompute
    the candidate buses on the shrunken system, repeat. One invocation replaces the enclosing
    per-pair fixpoint — and its two full-system size recomputations per drained pair.
    Terminates because every pack strictly drops the interaction count. -/
def drainTuplePacks (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) : PassResult cs bs :=
  let maxId := (cs.busInteractions.map (fun bi => bi.busId)).foldl max 0 + 65
  match tryTupleBuses cs bs facts hp1 cs.busInteractions.toArray rfl
      (tupleBusCandidates facts maxId) with
  | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  | some ⟨r, _hlt⟩ =>
    let r2 := drainTuplePacks r.out bs facts hp1
    ⟨r2.out, r.derivs ++ r2.derivs, r.correct.andThen r2.correct⟩
  termination_by cs.busInteractions.length
  decreasing_by exact _hlt

/-- Pack byte checks and exact-width range checks into tuple checks, draining every packable
    pair in one invocation. -/
def tupleRangePass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then drainTuplePacks cs bs facts hp1
  else ⟨cs, [], PassCorrect.refl cs bs⟩
