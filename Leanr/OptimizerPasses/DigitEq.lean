import Leanr.OptimizerPasses.MemoryUnifyBatch

set_option autoImplicit false

/-! # Digit-uniqueness equalities (bounded decomposition matching)

After register chaining, two accesses to the same runtime memory address leave a constraint
of the form `x₀ + 65536·x₁ − y₀ − 65536·y₁ = 0` between their (separately witnessed) pointer
limb decompositions. With the limbs fact-bounded (`x₀,y₀ < 2¹⁶`, `x₁,y₁ < 2¹³`), the
decomposition is *unique*: `x₀ = y₀` and `x₁ = y₁`. Substituting those equalities makes the
two heap addresses syntactically equal, which in turn lets the memory-chain passes unify the
accesses' data.

Generally: a linear constraint whose normalized terms pair up as `Σᵢ magᵢ·(xᵢ − yᵢ) = 0`
(equal-magnitude opposite-sign coefficient pairs, no constant), where every variable is
fact-bounded and the magnitudes dominate the lower partial sums
(`Σ_{j<i} mag_j·(B_j − 1) < mag_i`, and the total stays below `p` so values do not wrap),
entails `xᵢ = yᵢ` for every pair — by the standard top-digit argument, carried out over `ℕ`.
The pass adds the pairwise equalities; Gauss substitutes them. -/

variable {p : ℕ}

/-! ## Pairing the terms -/

/-- Remove the first term with variable ≠ both of a pair… helper: find and remove a term
    with coefficient `c`. -/
def extractCoeff (c : ZMod p) :
    List (String × ZMod p) → Option (String × List (String × ZMod p))
  | [] => none
  | (y, b) :: rest =>
    if b = c then some (y, rest)
    else match extractCoeff c rest with
      | some (z, rest') => some (z, (y, b) :: rest')
      | none => none

theorem extractCoeff_perm (c : ZMod p) (ts : List (String × ZMod p)) (y : String)
    (rest : List (String × ZMod p)) (h : extractCoeff c ts = some (y, rest)) :
    List.Perm ts ((y, c) :: rest) := by
  induction ts generalizing rest with
  | nil => simp [extractCoeff] at h
  | cons t ts' ih =>
    obtain ⟨z, b⟩ := t
    rw [extractCoeff] at h
    split_ifs at h with hb
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hb
      exact List.Perm.refl _
    · split at h
      · rename_i w rest' hw
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact List.Perm.trans ((ih rest' hw).cons _) (List.Perm.swap _ _ _)
      · exact absurd h (by simp)

/-- Pair every term `(x, a)` with a term carrying coefficient `−a` (fuel-based recursion;
    the fuel is the list length). Returns `(x, y, a)` triples. -/
def pairTermsAux : Nat → List (String × ZMod p) → Option (List (String × String × ZMod p))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, (x, a) :: rest =>
    match extractCoeff (-a) rest with
    | none => none
    | some (y, rest') =>
      match pairTermsAux fuel rest' with
      | some ps => some ((x, y, a) :: ps)
      | none => none

def pairTerms (ts : List (String × ZMod p)) : Option (List (String × String × ZMod p)) :=
  pairTermsAux ts.length ts

/-- The evaluation of a term list, given a pairing, is the paired combination. -/
theorem pairTermsAux_eval (env : String → ZMod p) :
    ∀ (fuel : Nat) (ts : List (String × ZMod p)) (ps : List (String × String × ZMod p)),
    pairTermsAux fuel ts = some ps →
    (ts.map (fun t => t.2 * env t.1)).sum
      = (ps.map (fun q => q.2.2 * env q.1 - q.2.2 * env q.2.1)).sum := by
  intro fuel
  induction fuel with
  | zero =>
      intro ts ps h
      cases ts with
      | nil =>
          simp only [pairTermsAux, Option.some.injEq] at h
          subst h
          simp
      | cons t rest => simp [pairTermsAux] at h
  | succ fuel ih =>
      intro ts ps h
      cases ts with
      | nil =>
          simp only [pairTermsAux, Option.some.injEq] at h
          subst h
          simp
      | cons t rest =>
        obtain ⟨x, a⟩ := t
        rw [pairTermsAux] at h
        split at h
        · exact absurd h (by simp)
        · rename_i y rest' hex
          split at h
          · rename_i ps' hps
            simp only [Option.some.injEq] at h
            subst h
            have hperm := extractCoeff_perm (-a) rest y rest' hex
            have hsum : (rest.map (fun t => t.2 * env t.1)).sum
                = (((y, -a) :: rest').map (fun t => t.2 * env t.1)).sum :=
              (hperm.map _).sum_eq
            simp only [List.map_cons, List.sum_cons, hsum, ih rest' ps' hps]
            ring
          · exact absurd h (by simp)

theorem pairTerms_eval (env : String → ZMod p) (ts : List (String × ZMod p))
    (ps : List (String × String × ZMod p)) (h : pairTerms ts = some ps) :
    (ts.map (fun t => t.2 * env t.1)).sum
      = (ps.map (fun q => q.2.2 * env q.1 - q.2.2 * env q.2.1)).sum :=
  pairTermsAux_eval env ts.length ts ps h

/-! ## The bounded digit-uniqueness core (over ℕ) -/

/-- Head-dominance: each entry's magnitude strictly dominates the sum of the maximal lower
    contributions. Entries are `((magnitude, bound), x-value, y-value)`, DESCENDING. -/
def domB : List ((Nat × Nat) × Nat × Nat) → Bool
  | [] => true
  | e :: rest =>
    decide ((rest.map (fun r => r.1.1 * (r.1.2 - 1))).sum < e.1.1) && domB rest

/-- Top-digit argument over ℕ: under head-dominance and value bounds, equal combinations
    force equal digits, pair by pair. -/
theorem digits_unique :
    ∀ (l : List ((Nat × Nat) × Nat × Nat)),
    domB l = true →
    (∀ e ∈ l, e.2.1 < e.1.2 ∧ e.2.2 < e.1.2) →
    (l.map (fun e => e.1.1 * e.2.1)).sum = (l.map (fun e => e.1.1 * e.2.2)).sum →
    ∀ e ∈ l, e.2.1 = e.2.2 := by
  intro l
  induction l with
  | nil => intro _ _ _ e he; exact absurd he (by simp)
  | cons e0 rest ih =>
    intro hdom hbnd hsum e he
    rw [domB, Bool.and_eq_true] at hdom
    obtain ⟨⟨mag, bound⟩, x, y⟩ := e0
    have hdomhead : (rest.map (fun r => r.1.1 * (r.1.2 - 1))).sum < mag :=
      of_decide_eq_true hdom.1
    have hx := (hbnd _ (List.mem_cons_self ..)).1
    have hy := (hbnd _ (List.mem_cons_self ..)).2
    have hTX : (rest.map (fun e => e.1.1 * e.2.1)).sum
        ≤ (rest.map (fun r => r.1.1 * (r.1.2 - 1))).sum := by
      apply List.sum_le_sum
      intro r hr
      exact Nat.mul_le_mul_left _ (by
        have := (hbnd r (List.mem_cons_of_mem _ hr)).1
        omega)
    have hTY : (rest.map (fun e => e.1.1 * e.2.2)).sum
        ≤ (rest.map (fun r => r.1.1 * (r.1.2 - 1))).sum := by
      apply List.sum_le_sum
      intro r hr
      exact Nat.mul_le_mul_left _ (by
        have := (hbnd r (List.mem_cons_of_mem _ hr)).2
        omega)
    have hsum' : mag * x + (rest.map (fun e => e.1.1 * e.2.1)).sum
        = mag * y + (rest.map (fun e => e.1.1 * e.2.2)).sum := by
      simpa using hsum
    have hxy : x = y := by
      rcases Nat.le_total x y with hle | hle
      · by_contra hne
        have hyx : 1 ≤ y - x := by omega
        have hmul : mag ≤ mag * (y - x) := by
          calc mag = mag * 1 := by omega
            _ ≤ mag * (y - x) := Nat.mul_le_mul_left _ hyx
        have hdist : mag * (y - x) = mag * y - mag * x := Nat.mul_sub ..
        have hmxy : mag * x ≤ mag * y := Nat.mul_le_mul_left _ hle
        omega
      · by_contra hne
        have hyx : 1 ≤ x - y := by omega
        have hmul : mag ≤ mag * (x - y) := by
          calc mag = mag * 1 := by omega
            _ ≤ mag * (x - y) := Nat.mul_le_mul_left _ hyx
        have hdist : mag * (x - y) = mag * x - mag * y := Nat.mul_sub ..
        have hmxy : mag * y ≤ mag * x := Nat.mul_le_mul_left _ hle
        omega
    rcases List.mem_cons.1 he with rfl | he'
    · exact hxy
    · have htails : (rest.map (fun e => e.1.1 * e.2.1)).sum
          = (rest.map (fun e => e.1.1 * e.2.2)).sum := by
        subst hxy
        omega
      exact ih hdom.2 (fun e' he'' => hbnd e' (List.mem_cons_of_mem _ he'')) htails e he'

/-! ## From the field equation to ℕ, and the pass -/

/-- Pairwise orientation check: `es` lists `((mag, bound), x', y')` where `(x', y', mag)` is
    the pair oriented so the magnitude is the smaller representative of `±a`. -/
def orientOk : List (String × String × ZMod p) → List ((Nat × Nat) × String × String) → Bool
  | [], [] => true
  | (x, y, a) :: ps, ((mag, _), x', y') :: es =>
    ((decide (a.val ≤ (-a).val) && decide (mag = a.val) && decide (x' = x) &&
        decide (y' = y)) ||
     (decide ((-a).val < a.val) && decide (mag = (-a).val) && decide (x' = y) &&
        decide (y' = x))) &&
    orientOk ps es
  | _, _ => false

/-- The paired combination equals the difference of the two ℕ-combinations, cast to the
    field (`p > 0`). -/
theorem orient_eval [NeZero p] (env : String → ZMod p) :
    ∀ (ps : List (String × String × ZMod p)) (es : List ((Nat × Nat) × String × String)),
    orientOk ps es = true →
    (ps.map (fun q => q.2.2 * env q.1 - q.2.2 * env q.2.1)).sum
      = (((es.map (fun e => e.1.1 * (env e.2.1).val)).sum : ℕ) : ZMod p)
        - (((es.map (fun e => e.1.1 * (env e.2.2).val)).sum : ℕ) : ZMod p) := by
  intro ps
  induction ps with
  | nil =>
      intro es h
      cases es with
      | nil => simp
      | cons e es' => simp [orientOk] at h
  | cons q ps' ih =>
    intro es h
    obtain ⟨x, y, a⟩ := q
    cases es with
    | nil => simp [orientOk] at h
    | cons e es' =>
      obtain ⟨⟨mag, bound⟩, x', y'⟩ := e
      rw [orientOk, Bool.and_eq_true] at h
      obtain ⟨hhead, hrest⟩ := h
      have htail := ih es' hrest
      simp only [List.map_cons, List.sum_cons, htail]
      rw [Bool.or_eq_true] at hhead
      have hcast : ∀ v : ZMod p, ((v.val : ℕ) : ZMod p) = v := fun v =>
        ZMod.natCast_rightInverse v
      rcases hhead with hcase | hcase
      · simp only [Bool.and_eq_true] at hcase
        obtain ⟨⟨⟨_, hmag⟩, hx⟩, hy⟩ := hcase
        rw [of_decide_eq_true hmag, of_decide_eq_true hx, of_decide_eq_true hy]
        push_cast
        rw [hcast (env x), hcast (env y), hcast a]
        ring
      · simp only [Bool.and_eq_true] at hcase
        obtain ⟨⟨⟨_, hmag⟩, hx⟩, hy⟩ := hcase
        rw [of_decide_eq_true hmag, of_decide_eq_true hx, of_decide_eq_true hy]
        push_cast
        rw [hcast (env y), hcast (env x), hcast (-a)]
        ring

/-- `domB` over the check-time entry list (values irrelevant). -/
def domB0 : List ((Nat × Nat) × String × String) → Bool
  | [] => true
  | e :: rest =>
    decide ((rest.map (fun r => r.1.1 * (r.1.2 - 1))).sum < e.1.1) && domB0 rest

theorem domB0_bridge (env : String → ZMod p) :
    ∀ (es : List ((Nat × Nat) × String × String)), domB0 es = true →
    domB (es.map (fun e => (e.1, (env e.2.1).val, (env e.2.2).val))) = true := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro h
    rw [domB0, Bool.and_eq_true] at h
    rw [List.map_cons, domB, Bool.and_eq_true]
    refine ⟨?_, ih h.2⟩
    rw [decide_eq_true_iff]
    have := of_decide_eq_true h.1
    simpa [List.map_map, Function.comp_def] using this

/-- Bounds check: both variables of every entry are `B`-bounded by the entry's bound. -/
def boundsOk (B : Std.HashMap String Nat) :
    List ((Nat × Nat) × String × String) → Bool
  | [] => true
  | ((_, bound), x, y) :: rest =>
    (match B[x]? with | some bx => decide (bx ≤ bound) | none => false) &&
    (match B[y]? with | some by' => decide (by' ≤ bound) | none => false) &&
    boundsOk B rest

theorem boundsOk_sound (B : Std.HashMap String Nat) (env : String → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    ∀ (es : List ((Nat × Nat) × String × String)), boundsOk B es = true →
    ∀ e ∈ (es.map (fun e => (e.1, (env e.2.1).val, (env e.2.2).val))),
      e.2.1 < e.1.2 ∧ e.2.2 < e.1.2 := by
  intro es
  induction es with
  | nil => intro _ e he; exact absurd he (by simp)
  | cons e0 rest ih =>
    intro h e he
    obtain ⟨⟨mag, bound⟩, x, y⟩ := e0
    rw [boundsOk, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hx, hy⟩, hrest⟩ := h
    rcases List.mem_cons.1 he with rfl | he'
    · constructor
      · split at hx
        · rename_i bx hbx
          exact lt_of_lt_of_le (hB x bx hbx) (of_decide_eq_true hx)
        · exact absurd hx (by simp)
      · split at hy
        · rename_i by' hby
          exact lt_of_lt_of_le (hB y by' hby) (of_decide_eq_true hy)
        · exact absurd hy (by simp)
    · exact ih hrest e he'

/-- The full per-constraint certificate. -/
def digitCheck (B : Std.HashMap String Nat) (c : Expression p)
    (psS : List (String × String × ZMod p))
    (es : List ((Nat × Nat) × String × String)) : Bool :=
  match linearize c with
  | none => false
  | some l =>
    decide (l.norm.const = 0) &&
    (match pairTerms l.norm.terms with
     | none => false
     | some ps => ps.isPerm psS) &&
    orientOk psS es &&
    domB0 es &&
    decide ((es.map (fun e => e.1.1 * (e.1.2 - 1))).sum < p) &&
    boundsOk B es

/-- The entailed pairwise equalities. -/
def digitEqs (es : List ((Nat × Nat) × String × String)) : List (Expression p) :=
  es.map (fun e => eqExpr (.var e.2.1) (.var e.2.2))

theorem digitCheck_sound (B : Std.HashMap String Nat) (c : Expression p)
    (psS : List (String × String × ZMod p))
    (es : List ((Nat × Nat) × String × String))
    (hchk : digitCheck B c psS es = true) (env : String → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound)
    (hc : c.eval env = 0) : ∀ q ∈ digitEqs (p := p) es, q.eval env = 0 := by
  unfold digitCheck at hchk
  split at hchk
  · exact absurd hchk (by simp)
  rename_i l hl
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨hc0, hpair⟩, horient⟩, hdom⟩, htot⟩, hbounds⟩ := hchk
  have hc0 := of_decide_eq_true hc0
  have htot := of_decide_eq_true htot
  have hp : 0 < p := by omega
  haveI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ps, hps, hperm⟩ : ∃ ps, pairTerms l.norm.terms = some ps ∧
      ps.isPerm psS = true := by
    split at hpair
    · exact absurd hpair (by simp)
    · rename_i ps hps
      exact ⟨ps, hps, hpair⟩
  -- the normalized linear form vanishes, hence so does the paired combination
  have hl0 : (l.norm.terms.map (fun t => t.2 * env t.1)).sum = 0 := by
    have h1 : l.norm.eval env = 0 := by
      rw [l.norm_eval, ← linearize_eval c l hl]
      exact hc
    have h2 : l.norm.const + (l.norm.terms.map (fun t => t.2 * env t.1)).sum = 0 := by
      simpa [LinExpr.eval] using h1
    rw [hc0] at h2
    simpa using h2
  have hps0 : (ps.map (fun q => q.2.2 * env q.1 - q.2.2 * env q.2.1)).sum = 0 := by
    rw [← pairTerms_eval env l.norm.terms ps hps]
    exact hl0
  have hperm' : List.Perm ps psS := List.isPerm_iff.mp hperm
  have hpsS0 : (psS.map (fun q => q.2.2 * env q.1 - q.2.2 * env q.2.1)).sum = 0 := by
    rw [← (hperm'.map _).sum_eq]
    exact hps0
  -- the two ℕ-combinations agree in the field, and are below `p`
  have horiented := orient_eval env psS es horient
  rw [hpsS0] at horiented
  have hcasteq :
      ((((es.map (fun e => e.1.1 * (env e.2.1).val)).sum : ℕ)) : ZMod p)
        = ((((es.map (fun e => e.1.1 * (env e.2.2).val)).sum : ℕ)) : ZMod p) :=
    sub_eq_zero.mp horiented.symm
  have hboundsS := boundsOk_sound B env hB es hbounds
  have hSXle : (es.map (fun e => e.1.1 * (env e.2.1).val)).sum
      ≤ (es.map (fun e => e.1.1 * (e.1.2 - 1))).sum := by
    apply List.sum_le_sum
    intro e he
    have hlt : (env e.2.1).val < e.1.2 := (hboundsS _ (List.mem_map.2 ⟨e, he, rfl⟩)).1
    exact Nat.mul_le_mul_left _ (by omega)
  have hSYle : (es.map (fun e => e.1.1 * (env e.2.2).val)).sum
      ≤ (es.map (fun e => e.1.1 * (e.1.2 - 1))).sum := by
    apply List.sum_le_sum
    intro e he
    have hlt : (env e.2.2).val < e.1.2 := (hboundsS _ (List.mem_map.2 ⟨e, he, rfl⟩)).2
    exact Nat.mul_le_mul_left _ (by omega)
  have hSXSY : (es.map (fun e => e.1.1 * (env e.2.1).val)).sum
      = (es.map (fun e => e.1.1 * (env e.2.2).val)).sum := by
    have h1 := congrArg ZMod.val hcasteq
    rwa [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at h1
  -- digit uniqueness
  have hdig := digits_unique (es.map (fun e => (e.1, (env e.2.1).val, (env e.2.2).val)))
    (domB0_bridge env es hdom) hboundsS
    (by simpa [List.map_map, Function.comp_def] using hSXSY)
  intro q hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
  have hval : (env e.2.1).val = (env e.2.2).val :=
    hdig (e.1, (env e.2.1).val, (env e.2.2).val) (List.mem_map.2 ⟨e, he, rfl⟩)
  have hxy : env e.2.1 = env e.2.2 := by
    have := congrArg (fun n : ℕ => (n : ZMod p)) hval
    simpa [ZMod.natCast_rightInverse (env e.2.1),
      ZMod.natCast_rightInverse (env e.2.2)] using this
  rw [eqExpr_eval]
  show env e.2.1 - env e.2.2 = 0
  rw [hxy]
  ring

/-! ## The builder (proof-free) and the pass -/

/-- Orient one pair and attach its bound. -/
def orientPair (B : Std.HashMap String Nat) (q : String × String × ZMod p) :
    Option ((String × String × ZMod p) × ((Nat × Nat) × String × String)) :=
  match q with
  | (x, y, a) =>
    match (if a.val ≤ (-a).val then (x, y, a.val) else (y, x, (-a).val)) with
    | (x', y', mag) =>
      match B[x']?, B[y']? with
      | some bx, some by' => some ((x, y, a), ((mag, max bx by'), x', y'))
      | _, _ => none

/-- Build sorted certificate data for one constraint. -/
def buildDigit (B : Std.HashMap String Nat) (c : Expression p) :
    Option (List (String × String × ZMod p) × List ((Nat × Nat) × String × String)) :=
  match linearize c with
  | none => none
  | some l =>
    if l.norm.const = 0 && decide (l.norm.terms.length ≤ 8) then
      match pairTerms l.norm.terms with
      | none => none
      | some ps =>
        match ps.mapM (orientPair B) with
        | none => none
        | some zipped =>
          let sorted := zipped.mergeSort (fun a b => b.2.1.1 ≤ a.2.1.1)
          some (sorted.map Prod.fst, sorted.map Prod.snd)
    else none

/-- Collect all checked digit equalities across the constraints. -/
def collectDigitEqs (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (hB : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, B[x]? = some b → (env x).val < b) :
    (pending : List (Expression p)) → (∀ c ∈ pending, c ∈ cs.algebraicConstraints) →
    { out : List (Expression p) //
        ∀ env, cs.satisfies bs env → ∀ q ∈ out, q.eval env = 0 }
  | [], _ => ⟨[], fun _ _ _ hq => absurd hq (by simp)⟩
  | c :: rest, hmem =>
    let ⟨acc, hacc⟩ := collectDigitEqs cs bs B hB rest
      (fun c' h => hmem c' (List.mem_cons_of_mem _ h))
    match buildDigit B c with
    | none => ⟨acc, hacc⟩
    | some (psS, es) =>
      if hchk : digitCheck B c psS es = true then
        ⟨digitEqs es ++ acc, by
          intro env hsat q hq
          rcases List.mem_append.1 hq with h | h
          · exact digitCheck_sound B c psS es hchk env
              (hB env (fun bi hbi => hsat.2.1 bi hbi))
              (hsat.1 c (hmem c (List.mem_cons_self ..))) q h
          · exact hacc env hsat q h⟩
      else ⟨acc, hacc⟩

/-- The digit-uniqueness pass: add pairwise equalities entailed by bounded decomposition
    matching. -/
def digitEqPass : VerifiedPassW p := fun cs bs facts =>
  let Bm : BoundsMap p cs bs := BoundsMap.build facts
  let ⟨eqs, heqs⟩ := collectDigitEqs cs bs Bm.map Bm.sound cs.algebraicConstraints
    (fun _ h => h)
  let new := eqs.filter
    (fun c => !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c)
  if new.isEmpty then ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
  else
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new },
     cs.addConstraints_correct bs new (fun env hsat c hc =>
       heqs env hsat c (List.mem_of_mem_filter hc))⟩
