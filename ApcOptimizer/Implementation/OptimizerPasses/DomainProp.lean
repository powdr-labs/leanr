import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus
import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Utils.Size
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-! # Finite-domain propagation (boolean/one-hot case analysis, bus-fact domains)

The first pass that uses the *field* structure of `ZMod p` (`p` prime — decided at runtime, so
the optimizer's signature stays modulus-agnostic; for non-prime `p` the pass is the identity).

Many circuit variables are pinned to a *finite domain*:

* by a constraint that is a product of affine factors in that single variable:
  `x * (x - 1) = 0` forces `x ∈ {0, 1}` (booleanity), `c * (255 - c) = 0` forces
  `c ∈ {0, 255}`. Over an integral domain a product is zero only if a factor is, and an affine
  factor `a·x + b` with `a ≠ 0` has the single root `-b/a` — this is where primality is needed;
* by a **bus obligation** together with a proven `BusFacts` bound (`ApcOptimizer/Implementation/BusFacts.lean`): an
  interaction with constant nonzero multiplicity whose payload carries `x` in a slot the
  semantics range-checks gives `x.val < bound`, i.e. `x ∈ [0, bound)`.

Once domains are known, any constraint — or any bus interaction's `violatesConstraint`
obligation, probed pointwise on the (small) domain product — whose variables all have finite
domains can be decided by exhaustive enumeration. If all surviving assignments agree that some
variable `x` equals `c`, then `x = c` is entailed by the whole system, and the proven
`ConstraintSystem.subst_correct` eliminates `x`. This is SAT-style unit propagation done
natively on field elements; e.g. it resolves one-hot selector residues like
`(1 + x + 2y + 3z) * (x + 2y + 3z) = 0` over booleans (only `x = y = z = 0` survives), pins
`(c₀, c₁) = (1, 0)` from a byte-bounded two-line constraint, and — after other passes rewrite a
range lookup's argument — pins decomposition limbs like `wdec` from their probed lookups.

The enumeration is capped (`maxEnumSize`), everything is decidable, and the checked
certificates (`checkForced`/`checkForcedBi`) are all the correctness proof consumes — the
candidate search itself carries no proof obligation. -/

variable {p : ℕ}

/-! ## Evaluation depends only on an expression's variables -/

theorem Expression.eval_congr (e : Expression p) (env1 env2 : Variable → ZMod p)
    (h : ∀ x ∈ e.vars, env1 x = env2 x) : e.eval env1 = e.eval env2 := by
  induction e with
  | const n => rfl
  | var x => exact h x (by simp [Expression.vars])
  | add a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun x hx => h x (by simp [Expression.vars, hx])),
          ihb (fun x hx => h x (by simp [Expression.vars, hx]))]
  | mul a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun x hx => h x (by simp [Expression.vars, hx])),
          ihb (fun x hx => h x (by simp [Expression.vars, hx]))]

theorem BusInteraction.eval_congr (bi : BusInteraction (Expression p))
    (env1 env2 : Variable → ZMod p) (h : ∀ x ∈ bi.vars, env1 x = env2 x) :
    bi.eval env1 = bi.eval env2 := by
  have hmult : bi.multiplicity.eval env1 = bi.multiplicity.eval env2 :=
    bi.multiplicity.eval_congr env1 env2
      (fun x hx => h x (by simp [BusInteraction.vars, hx]))
  have hpay : bi.payload.map (fun e => e.eval env1) = bi.payload.map (fun e => e.eval env2) := by
    apply List.map_congr_left
    intro e he
    exact e.eval_congr env1 env2
      (fun x hx => h x (by
        simp only [BusInteraction.vars, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨e, he, hx⟩))
  simp only [BusInteraction.eval, hmult, hpay]

/-! ## Allocation-free "all variables lie in a set" checks

`Expression.vars` materializes a fresh list on every call; predicates like "are all of `c`'s
variables in `xs`?" that are probed once *per target* (the covered-item scans in `DomainBatch`,
the group scans in `Reencode`) then rebuild that list for every (target, item) pair — an
allocation storm on large machines. `Expression.varsIn` / `BusInteraction.varsIn` decide the same
predicate by recursion, allocating nothing. Their soundness (`… = true → every variable is in
`xs`) is all the enumeration proofs consume. -/

/-- Do all the expression's variables lie in `xs`? (No allocation — recurses over the tree.) -/
def Expression.varsIn (xs : List Variable) : Expression p → Bool
  | .const _ => true
  | .var y => xs.contains y
  | .add a b => a.varsIn xs && b.varsIn xs
  | .mul a b => a.varsIn xs && b.varsIn xs

theorem Expression.varsIn_sound (xs : List Variable) (e : Expression p)
    (h : e.varsIn xs = true) : ∀ v ∈ e.vars, v ∈ xs := by
  induction e with
  | const n => simp [Expression.vars]
  | var y =>
      intro v hv
      simp only [Expression.vars, List.mem_singleton] at hv
      subst hv
      exact List.contains_iff_mem.mp (by simpa [Expression.varsIn] using h)
  | add a b iha ihb =>
      rw [Expression.varsIn, Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv
  | mul a b iha ihb =>
      rw [Expression.varsIn, Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv

/-- Do all a bus interaction's variables (multiplicity and payload) lie in `xs`? (No allocation.) -/
def BusInteraction.varsIn (xs : List Variable) (bi : BusInteraction (Expression p)) : Bool :=
  bi.multiplicity.varsIn xs && bi.payload.all (fun e => e.varsIn xs)

theorem BusInteraction.varsIn_sound (xs : List Variable) (bi : BusInteraction (Expression p))
    (h : bi.varsIn xs = true) : ∀ v ∈ bi.vars, v ∈ xs := by
  rw [BusInteraction.varsIn, Bool.and_eq_true] at h
  intro v hv
  rw [BusInteraction.vars, List.mem_append] at hv
  rcases hv with hv | hv
  · exact Expression.varsIn_sound xs bi.multiplicity h.1 v hv
  · obtain ⟨e, he, hev⟩ := List.mem_flatMap.1 hv
    exact Expression.varsIn_sound xs e (List.all_eq_true.mp h.2 e he) v hev

/-! ## Deriving a finite domain for a variable from one constraint -/

/-- Root list for the equation `c + Σ terms = 0`: `[]` for a nonzero constant (never zero),
    the unique root for a single term `a·x` with `a ≠ 0`, `none` otherwise ("cannot bound `x`").
    The root is computed with the ring's `Inv` and then *re-checked* (`a * r + c = 0`), so
    soundness never depends on inversion behaving well. -/
def rootsOfTerms (x : Variable) (c : ZMod p) : List (Variable × ZMod p) → Option (List (ZMod p))
  | [] => if c = 0 then none else some []
  | [(y, a)] =>
      let r := -(a⁻¹ * c)
      if y = x ∧ a ≠ 0 ∧ a * r + c = 0 then some [r] else none
  | _ :: _ :: _ => none

theorem rootsOfTerms_sound [Fact p.Prime] (x : Variable) (c : ZMod p)
    (ts : List (Variable × ZMod p)) (roots : List (ZMod p))
    (h : rootsOfTerms x c ts = some roots) (env : Variable → ZMod p)
    (hsum : c + (ts.map (fun t => t.2 * env t.1)).sum = 0) : env x ∈ roots := by
  rcases ts with _ | ⟨⟨y, a⟩, _ | ⟨t2, rest⟩⟩
  · -- no terms: a constant; `hsum` contradicts the nonzero guard
    simp only [rootsOfTerms] at h
    split_ifs at h with hc
    -- (the `c = 0` branch is closed by `split_ifs` itself: `h` is `none = some _`)
    exact absurd (by simpa using hsum) hc
  · -- a single term `a * y`: the unique (re-checked) root
    simp only [rootsOfTerms] at h
    split_ifs at h with hcond
    obtain ⟨rfl, ha, hr⟩ := hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
    have hxy : a * env y + c = 0 := by linear_combination hsum
    have hcancel : a * env y = a * (-(a⁻¹ * c)) := by
      rw [eq_neg_of_add_eq_zero_left hxy, ← eq_neg_of_add_eq_zero_left hr]
    simpa using mul_left_cancel₀ ha hcancel
  · exact absurd h (by simp [rootsOfTerms])

/-- Roots of an expression that is affine in (at most) the single variable `x`. -/
def affineRootsIn (x : Variable) (e : Expression p) : Option (List (ZMod p)) :=
  (linearize e).bind (fun l => rootsOfTerms x l.norm.const l.norm.terms)

theorem affineRootsIn_sound [Fact p.Prime] (x : Variable) (e : Expression p)
    (roots : List (ZMod p)) (h : affineRootsIn x e = some roots)
    (env : Variable → ZMod p) (he : e.eval env = 0) : env x ∈ roots := by
  simp only [affineRootsIn, Option.bind_eq_some_iff] at h
  obtain ⟨l, hlin, hroot⟩ := h
  have heval : l.norm.const + (l.norm.terms.map (fun t => t.2 * env t.1)).sum = 0 := by
    have h1 : l.norm.eval env = 0 := by
      rw [LinExpr.norm_eval, ← linearize_eval e l hlin]; exact he
    simpa [LinExpr.eval] using h1
  exact rootsOfTerms_sound x l.norm.const l.norm.terms roots hroot env heval

/-- Roots of a constraint viewed as a product of affine factors in the single variable `x`:
    if the constraint is zero, one factor is zero (integral domain), so `x` is one of the
    collected roots. `none` when a factor cannot be bounded. -/
def rootsIn (x : Variable) : Expression p → Option (List (ZMod p))
  | .const n => affineRootsIn x (.const n)
  | .var y => affineRootsIn x (.var y)
  | .add a b => affineRootsIn x (.add a b)
  | .mul a b =>
    match affineRootsIn x (.mul a b) with
    | some r => some r
    | none =>
      match rootsIn x a, rootsIn x b with
      | some ra, some rb => some (ra ++ rb)
      | _, _ => none

theorem rootsIn_sound [Fact p.Prime] (x : Variable) (e : Expression p) (roots : List (ZMod p))
    (h : rootsIn x e = some roots) (env : Variable → ZMod p) (he : e.eval env = 0) :
    env x ∈ roots := by
  induction e generalizing roots with
  | const n => exact affineRootsIn_sound x _ roots h env he
  | var y => exact affineRootsIn_sound x _ roots h env he
  | add a b _ _ => exact affineRootsIn_sound x _ roots h env he
  | mul a b iha ihb =>
    rw [rootsIn] at h
    split at h
    · rename_i r haff
      simp only [Option.some.injEq] at h
      subst h
      exact affineRootsIn_sound x _ _ haff env he
    · rename_i haff
      split at h
      · rename_i ra rb hra hrb
        simp only [Option.some.injEq] at h
        subst h
        have he' : a.eval env * b.eval env = 0 := he
        rcases mul_eq_zero.mp he' with hz | hz
        · exact List.mem_append.2 (Or.inl (iha ra hra hz))
        · exact List.mem_append.2 (Or.inr (ihb rb hrb hz))
      all_goals exact absurd h (by simp)

/-- The finite domain of `x` derived from the first constraint that bounds it. Constraints not
    mentioning `x` are skipped without linearizing (`rootsIn` runs `linearize` per constraint —
    the ungated scan dominated whole passes); a non-mentioning constraint can only produce a
    root list via the unsatisfiable-constant case, so the gate never loses a live domain. -/
def findDomainAlg (all : List (Expression p)) (x : Variable) : Option (List (ZMod p)) :=
  match all with
  | [] => none
  | c :: rest =>
    if c.mentions x then
      match rootsIn x c with
      | some d => some d
      | none => findDomainAlg rest x
    else findDomainAlg rest x

theorem findDomainAlg_sound [Fact p.Prime] (all : List (Expression p)) (x : Variable)
    (d : List (ZMod p)) (h : findDomainAlg all x = some d) (env : Variable → ZMod p)
    (hall : ∀ c ∈ all, c.eval env = 0) : env x ∈ d := by
  induction all with
  | nil => exact absurd h (by simp [findDomainAlg])
  | cons c rest ih =>
    rw [findDomainAlg] at h
    split_ifs at h with hm
    · cases hr : rootsIn x c with
      | some d' =>
          rw [hr] at h
          simp only [Option.some.injEq] at h
          exact h ▸ rootsIn_sound x c d' hr env (hall c (List.mem_cons_self ..))
      | none =>
          rw [hr] at h
          exact ih h (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))
    · exact ih h (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))

/-! ## Deriving a finite domain from a bus obligation and a proven fact -/

/-- Cap on fact-derived domain sizes (a `2^17` range bound is real but not enumerable).
    `2^16` is included so that base-`2^16` digit decompositions (e.g. `to_pc_limbs`) can be
    pinned by probing the rewritten range lookup once the other digit is affine-eliminated. -/
def maxDomainBound : Nat := 65536

/-- Is this expression literally the variable `x`? -/
def isVarOf (x : Variable) : Expression p → Bool
  | .var y => y = x
  | _ => false

theorem isVarOf_sound (x : Variable) (e : Expression p) (h : isVarOf x e = true) :
    e = .var x := by
  cases e with
  | var y =>
      simp only [isVarOf, decide_eq_true_eq] at h
      rw [h]
  | const n => exact absurd h (by simp [isVarOf])
  | add a b => exact absurd h (by simp [isVarOf])
  | mul a b => exact absurd h (by simp [isVarOf])

/-- The first payload slot that is literally the variable `x`. -/
def varSlot (x : Variable) : List (Expression p) → Option Nat
  | [] => none
  | e :: rest => if isVarOf x e then some 0 else (varSlot x rest).map (· + 1)

theorem varSlot_sound (x : Variable) (payload : List (Expression p)) (slot : Nat)
    (h : varSlot x payload = some slot) : payload[slot]? = some (.var x) := by
  induction payload generalizing slot with
  | nil => exact absurd h (by simp [varSlot])
  | cons e rest ih =>
    rw [varSlot] at h
    split_ifs at h with hv
    · simp only [Option.some.injEq] at h
      subst h
      simpa using isVarOf_sound x e hv
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨s, hs, rfl⟩ := h
      simpa using ih s hs

/-- The evaluated payload matches the pattern of its own constant entries. -/
theorem matches_evalPattern (payload : List (Expression p)) (env : Variable → ZMod p) :
    Matches (payload.map (fun e => e.eval env)) (payload.map Expression.constValue?) := by
  refine ⟨by simp, ?_⟩
  intro slot c hc
  rw [List.getElem?_map] at hc
  rw [List.getElem?_map]
  cases he : payload[slot]? with
  | none => rw [he] at hc; simp at hc
  | some e =>
      rw [he] at hc
      simp only [Option.map_some, Option.some.injEq] at hc ⊢
      exact e.constValue?_sound c hc env

theorem mem_range_cast [NeZero p] (v : ZMod p) (bound : Nat) (h : v.val < bound) :
    v ∈ (List.range bound).map (Nat.cast : Nat → ZMod p) :=
  List.mem_map.2 ⟨v.val, List.mem_range.2 h, ZMod.natCast_rightInverse v⟩

/-- A value bound for `x` from one bus obligation: the interaction has constant nonzero
    multiplicity (so its obligation is active under every assignment) and carries `x` as a raw
    payload entry in a slot bounded by a proven fact. -/
def interactionBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) : Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match varSlot x bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) slot

/-- `interactionBound` with the multiplicity constant and the constant-payload pattern computed
    once by the caller — they are per-*interaction* values, and callers that query every payload
    variable of an interaction would otherwise recompute the pattern (a full payload fold) per
    variable. Definitionally the same function at the canonical arguments
    (`interactionBoundPat_eq`). -/
def interactionBoundPat (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (mval? : Option (ZMod p))
    (pat : List (Option (ZMod p))) (x : Variable) : Option Nat :=
  match mval? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match varSlot x bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval pat slot

theorem interactionBoundPat_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) :
    interactionBoundPat bs facts bi bi.multiplicity.constValue?
      (bi.payload.map Expression.constValue?) x = interactionBound bs facts bi x := rfl

theorem interactionBound_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (bound : Nat)
    (h : interactionBound bs facts bi x = some bound) (env : Variable → ZMod p)
    (hob : (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) :
    (env x).val < bound := by
  unfold interactionBound at h
  split at h
  · exact absurd h (by simp)
  · rename_i mval hm
    split_ifs at h with hmz
    split at h
    · exact absurd h (by simp)
    · rename_i slot hslot
      -- the obligation is active: the multiplicity is the nonzero constant `mval`
      have hmeval : (bi.eval env).multiplicity = mval :=
        bi.multiplicity.constValue?_sound mval hm env
      have hviol : bs.violatesConstraint (bi.eval env) = false := by
        apply hob; rw [hmeval]; exact hmz
      -- the slot of the evaluated payload holds `env x`
      have hgete : bi.payload[slot]? = some (.var x) := varSlot_sound x bi.payload slot hslot
      have hget : (bi.eval env).payload[slot]? = some (env x) := by
        show (bi.payload.map (fun e => e.eval env))[slot]? = some (env x)
        rw [List.getElem?_map, hgete]
        rfl
      -- apply the proven fact (the fact was looked up at the constant multiplicity `mval`,
      -- which is the evaluated message's multiplicity)
      rw [← hmeval] at h
      exact facts.slotBound_sound (bi.eval env)
        (bi.payload.map Expression.constValue?) slot bound (env x) h
        (matches_evalPattern bi.payload env) hviol hget

/-! ## Probed slot bounds

A bound for `x` that no single `slotBound` fact states, derived by *probing* a functional
dependence (`slotFun`) against the payload's own syntax. The motivating instance is OpenVM's
6-bit top-limb bound on pc-derived byte decompositions, which ships as a genuine-XOR identity
`[x, 192, 192 + x, 1]` rather than a range check: the accepted message forces
`x ⊕ 192 = x + 192`, which only bytes `< 64` satisfy. Generically: if payload slot `j` is an
affine function `l.const + c·x` of a variable `x` sitting raw in slot `i`, every other slot is
a constant, and a `slotFun` fact computes slot `j` from the rest of the payload, then `x`'s
value must be a *survivor* of the probe `f (payload with x := v, slot j zeroed) = l.const + c·v`
over `v < B₀` (the slot-fact bound for `x` itself, capped at 256 probes). The returned bound is
one plus the largest survivor. No bus specifics — any `slotFun` instance works. -/

/-- One plus the largest `v < n` passing `test` (`0` if none) — the least strict upper bound on
    the survivors of a probe. -/
def probeMax (test : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if test n then n + 1 else probeMax test n

theorem probeMax_lt (test : Nat → Bool) :
    ∀ (n v : Nat), v < n → test v = true → v < probeMax test n
  | 0, v, hv, _ => absurd hv (by omega)
  | n + 1, v, hv, htest => by
    rw [probeMax]
    split
    · omega
    · rename_i hn
      have hvn : v ≠ n := fun h => by rw [h] at htest; rw [htest] at hn; exact hn rfl
      exact probeMax_lt test n v (by omega) htest

/-- The probe payload: constant slots at their constants, slot `i` at the candidate value,
    non-constant slots at `0`. -/
def probeBase (payload : List (Expression p)) (i : Nat) (v : ZMod p) : List (ZMod p) :=
  (payload.map (fun e => (e.constValue?).getD 0)).set i v

/-- With slot `i` a raw variable, slot `j` arbitrary, and every other slot a constant, the
    evaluated payload with slot `j` zeroed *is* the probe payload at `env x`. -/
theorem probeBase_eq_set (payload : List (Expression p)) (env : Variable → ZMod p)
    (i j : Nat) (hij : i ≠ j) (x : Variable)
    (hi : payload[i]? = some (.var x))
    (hconst : ∀ k, k ≠ i → k ≠ j → ∀ e', payload[k]? = some e' → (e'.constValue?).isSome) :
    ((payload.map (fun e => e.eval env)).set j 0)
      = (probeBase payload i (env x)).set j 0 := by
  have hilen : i < payload.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hi
    exact absurd hi (by simp)
  apply List.ext_getElem?
  intro k
  by_cases hkj : k = j
  · subst hkj
    rw [List.getElem?_set, List.getElem?_set]
    simp [probeBase]
  · rw [List.getElem?_set_ne (fun h => hkj h.symm), List.getElem?_set_ne (fun h => hkj h.symm)]
    by_cases hki : k = i
    · subst hki
      rw [List.getElem?_map, hi, probeBase, List.getElem?_set, if_pos rfl]
      rw [List.length_map, if_pos hilen]
      rfl
    · rw [List.getElem?_map, probeBase, List.getElem?_set_ne (fun h => hki h.symm),
        List.getElem?_map]
      cases hk : payload[k]? with
      | none => rfl
      | some e' =>
        have hcv := hconst k hki hkj e' hk
        obtain ⟨cv, hcveq⟩ := Option.isSome_iff_exists.1 hcv
        simp only [Option.map_some]
        rw [e'.constValue?_sound cv hcveq env, hcveq]
        rfl

/-- `some bnd` exactly when it strictly improves on the base bound. -/
def capBound (bnd B₀ : Nat) : Option Nat := if bnd < B₀ then some bnd else none

/-- The probed bound for `x` from interaction `bi` with output slot `j` (see the section
    header): the capped `probeMax` when the shape matches. -/
def probedSlotBoundAt (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (j : Nat) : Option Nat :=
  if p = 0 then none
  else
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match varSlot x bi.payload with
      | none => none
      | some i =>
        if i = j then none
        else
          match facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) i with
          | none => none
          | some B₀ =>
            if 256 < B₀ then none
            else
              match facts.slotFun bi.busId (bi.payload.map Expression.constValue?) j with
              | none => none
              | some f =>
                match bi.payload[j]? with
                | none => none
                | some e =>
                  match linearize e with
                  | none => none
                  | some l =>
                    match l.terms with
                    | [(y, c)] =>
                      if y = x ∧ (List.range bi.payload.length).all (fun k =>
                          k == i || k == j ||
                            ((bi.payload[k]?.map
                              (fun e' => (e'.constValue?).isSome)).getD false)) then
                        capBound (probeMax (fun v =>
                          f ((probeBase bi.payload i ((v : ℕ) : ZMod p)).set j 0)
                            == l.const + c * ((v : ℕ) : ZMod p)) B₀) B₀
                      else none
                    | _ => none

theorem probedSlotBoundAt_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (j : Nat) (bound : Nat)
    (h : probedSlotBoundAt bs facts bi x j = some bound) (env : Variable → ZMod p)
    (hob : (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) :
    (env x).val < bound := by
  unfold probedSlotBoundAt at h
  split_ifs at h with hp0
  haveI : NeZero p := ⟨hp0⟩
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i mval hm
  split_ifs at h with hmz
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i i hslot
  split_ifs at h with hij
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i B₀ hB
  split_ifs at h with hcap
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i f hf
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i e hj
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i l hlin
  split at h
  any_goals simp only [reduceCtorEq] at h
  rename_i y c heq_terms
  split_ifs at h with hcond
  obtain ⟨hyx, hall⟩ := hcond
  rw [hyx] at heq_terms
  unfold capBound at h
  split_ifs at h with hbnd
  simp only [Option.some.injEq] at h
  subst h
  -- the obligation is active
  have hmeval : (bi.eval env).multiplicity = mval :=
    bi.multiplicity.constValue?_sound mval hm env
  have hviol : bs.violatesConstraint (bi.eval env) = false := by
    apply hob; rw [hmeval]; exact hmz
  have hpat : Matches (bi.eval env).payload
      (bi.payload.map Expression.constValue?) :=
    matches_evalPattern bi.payload env
  -- base bound for x
  have hgeti : bi.payload[i]? = some (.var x) := varSlot_sound x bi.payload i hslot
  have hgetiE : (bi.eval env).payload[i]? = some (env x) := by
    show (bi.payload.map (fun e' => e'.eval env))[i]? = some (env x)
    rw [List.getElem?_map, hgeti]
    rfl
  have hB' : facts.slotBound (bi.eval env).busId (bi.eval env).multiplicity
      (bi.payload.map Expression.constValue?) i = some B₀ := by
    rw [hmeval]; exact hB
  have hbase : (env x).val < B₀ :=
    facts.slotBound_sound (bi.eval env) (bi.payload.map Expression.constValue?)
      i B₀ (env x) hB' hpat hviol hgetiE
  -- functional dependence at slot j
  have hgetjE : (bi.eval env).payload[j]? = some (e.eval env) := by
    show (bi.payload.map (fun e' => e'.eval env))[j]? = some (e.eval env)
    rw [List.getElem?_map, hj]
    rfl
  have hf' : facts.slotFun (bi.eval env).busId
      (bi.payload.map Expression.constValue?) j = some f := hf
  have hfun : e.eval env = f ((bi.eval env).payload.set j 0) :=
    facts.slotFun_sound (bi.eval env) (bi.payload.map Expression.constValue?)
      j f (e.eval env) hf' hpat hviol hgetjE
  -- the zeroed evaluated payload is the probe payload at env x
  have hconst : ∀ k, k ≠ i → k ≠ j → ∀ e',
      bi.payload[k]? = some e' → (e'.constValue?).isSome := by
    intro k hki hkj e' hk
    have hklen : k < bi.payload.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hk
      exact absurd hk (by simp)
    have := List.all_eq_true.1 hall k (List.mem_range.2 hklen)
    simp only [beq_iff_eq, Bool.or_eq_true] at this
    rcases this with (h' | h') | h'
    · exact absurd h' hki
    · exact absurd h' hkj
    · rw [hk] at h'
      simpa using h'
  have hpay : ((bi.eval env).payload).set j 0
      = (probeBase bi.payload i (env x)).set j 0 := by
    show ((bi.payload.map (fun e' => e'.eval env)).set j 0)
        = (probeBase bi.payload i (env x)).set j 0
    exact probeBase_eq_set bi.payload env i j hij x hgeti hconst
  -- the value equation e = l.const + c·x
  have heval : e.eval env = l.const + c * env x := by
    rw [linearize_eval e l hlin]
    simp [LinExpr.eval, heq_terms]
  -- the test passes at v = (env x).val
  have henvx : (((env x).val : ℕ) : ZMod p) = env x :=
    ZMod.natCast_rightInverse (env x)
  have htest : (f ((probeBase bi.payload i (((env x).val : ℕ) : ZMod p)).set j 0)
      == l.const + c * (((env x).val : ℕ) : ZMod p)) = true := by
    rw [beq_iff_eq, henvx, ← hpay, ← hfun, heval]
  exact probeMax_lt _ B₀ (env x).val hbase htest

/-- The value bound of `x` derived from the first bus obligation that bounds it. -/
def findVarBound (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (Expression p)) → Variable → Option Nat
  | [], _ => none
  | bi :: rest, x =>
    match interactionBound bs facts bi x with
    | some bound => some bound
    | none => findVarBound bs facts rest x

theorem findVarBound_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (x : Variable) (bound : Nat)
    (h : findVarBound bs facts bis x = some bound) (env : Variable → ZMod p)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : (env x).val < bound := by
  induction bis with
  | nil => exact absurd h (by simp [findVarBound])
  | cons bi rest ih =>
    rw [findVarBound] at h
    cases hr : interactionBound bs facts bi x with
    | some bound' =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        exact h ▸ interactionBound_sound bs facts bi x bound' hr env
          (hbus bi (List.mem_cons_self ..))
    | none =>
        rw [hr] at h
        exact ih h (fun bi' hbi' => hbus bi' (List.mem_cons_of_mem _ hbi'))

/-- A finite domain for `x` from one bus obligation (capped bound, materialized as a list). -/
def interactionDomain (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) : Option (List (ZMod p)) :=
  match interactionBound bs facts bi x with
  | none => none
  | some bound =>
    if bound ≤ maxDomainBound then
      some ((List.range bound).map (Nat.cast : Nat → ZMod p))
    else none

theorem interactionDomain_sound [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (d : List (ZMod p))
    (h : interactionDomain bs facts bi x = some d) (env : Variable → ZMod p)
    (hob : (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) :
    env x ∈ d := by
  unfold interactionDomain at h
  split at h
  · exact absurd h (by simp)
  · rename_i bound hB
    split_ifs at h with hcap
    simp only [Option.some.injEq] at h
    subst h
    exact mem_range_cast (env x) bound
      (interactionBound_sound bs facts bi x bound hB env hob)

/-- The finite domain of `x` derived from the first bus obligation that bounds it. -/
def findDomainBus (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (Expression p)) → Variable → Option (List (ZMod p))
  | [], _ => none
  | bi :: rest, x =>
    match interactionDomain bs facts bi x with
    | some d => some d
    | none => findDomainBus bs facts rest x

theorem findDomainBus_sound [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (x : Variable) (d : List (ZMod p))
    (h : findDomainBus bs facts bis x = some d) (env : Variable → ZMod p)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : env x ∈ d := by
  induction bis with
  | nil => exact absurd h (by simp [findDomainBus])
  | cons bi rest ih =>
    rw [findDomainBus] at h
    cases hr : interactionDomain bs facts bi x with
    | some d' =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        exact h ▸ interactionDomain_sound bs facts bi x d' hr env
          (hbus bi (List.mem_cons_self ..))
    | none =>
        rw [hr] at h
        exact ih h (fun bi' hbi' => hbus bi' (List.mem_cons_of_mem _ hbi'))

/-- The finite domain of `x`: from a constraint if possible, else from a bus obligation. -/
def findDomain (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (x : Variable) : Option (List (ZMod p)) :=
  match findDomainAlg all x with
  | some d => some d
  | none => findDomainBus bs facts bis x

theorem findDomain_sound [Fact p.Prime] [NeZero p] (all : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs) (bis : List (BusInteraction (Expression p)))
    (x : Variable) (d : List (ZMod p)) (h : findDomain all bs facts bis x = some d)
    (env : Variable → ZMod p) (hall : ∀ c ∈ all, c.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : env x ∈ d := by
  unfold findDomain at h
  cases ha : findDomainAlg all x with
  | some d' =>
      rw [ha] at h
      simp only [Option.some.injEq] at h
      exact h ▸ findDomainAlg_sound all x d' ha env hall
  | none =>
      rw [ha] at h
      exact findDomainBus_sound bs facts bis x d h env hbus

/-- Domains for a list of variables, all-or-nothing. -/
def buildDoms (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) :
    List Variable → Option (List (Variable × List (ZMod p)))
  | [] => some []
  | x :: xs =>
    match findDomain all bs facts bis x, buildDoms all bs facts bis xs with
    | some d, some rest => some ((x, d) :: rest)
    | _, _ => none

theorem buildDoms_fst (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (xs : List Variable)
    (doms : List (Variable × List (ZMod p))) (h : buildDoms all bs facts bis xs = some doms) :
    doms.map Prod.fst = xs := by
  induction xs generalizing doms with
  | nil => simp only [buildDoms, Option.some.injEq] at h; subst h; rfl
  | cons x rest ih =>
    rw [buildDoms] at h
    cases hd : findDomain all bs facts bis x with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : buildDoms all bs facts bis rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some doms' =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [ih doms' hr]

theorem buildDoms_sound [Fact p.Prime] [NeZero p] (all : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs) (bis : List (BusInteraction (Expression p)))
    (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (h : buildDoms all bs facts bis xs = some doms) (env : Variable → ZMod p)
    (hall : ∀ c ∈ all, c.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    ∀ yd ∈ doms, env yd.1 ∈ yd.2 := by
  induction xs generalizing doms with
  | nil => simp only [buildDoms, Option.some.injEq] at h; subst h; simp
  | cons x rest ih =>
    rw [buildDoms] at h
    cases hd : findDomain all bs facts bis x with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : buildDoms all bs facts bis rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some doms' =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        intro yd hyd
        rcases List.mem_cons.1 hyd with rfl | hyd
        · exact findDomain_sound all bs facts bis x d hd env hall hbus
        · exact ih doms' hr yd hyd

/-! ## Exhaustive enumeration over domain products -/

/-- All assignments in the cartesian product of the domains. -/
def assignments : List (Variable × List (ZMod p)) → List (List (Variable × ZMod p))
  | [] => [[]]
  | (x, d) :: rest => (assignments rest).flatMap (fun a => d.map (fun v => (x, v) :: a))

/-- Read an assignment as an environment (`0` for unassigned variables). -/
def envOf : List (Variable × ZMod p) → Variable → ZMod p
  | [], _ => 0
  | (x, v) :: rest, y => if y = x then v else envOf rest y

/-- The pointwise-in-domain restriction of `f` is one of the enumerated assignments. -/
theorem mem_assignments (doms : List (Variable × List (ZMod p))) (f : Variable → ZMod p)
    (h : ∀ yd ∈ doms, f yd.1 ∈ yd.2) :
    doms.map (fun yd => (yd.1, f yd.1)) ∈ assignments doms := by
  induction doms with
  | nil => simp [assignments]
  | cons yd rest ih =>
    obtain ⟨x, d⟩ := yd
    simp only [List.map_cons, assignments, List.mem_flatMap]
    refine ⟨rest.map (fun yd => (yd.1, f yd.1)),
            ih (fun yd hyd => h yd (List.mem_cons_of_mem _ hyd)), ?_⟩
    exact List.mem_map.2 ⟨f x, h (x, d) (List.mem_cons_self ..), rfl⟩

/-- On its own variables, the restriction environment agrees with `f`. -/
theorem envOf_map (doms : List (Variable × List (ZMod p))) (f : Variable → ZMod p) (y : Variable)
    (hy : y ∈ doms.map Prod.fst) :
    envOf (doms.map (fun yd => (yd.1, f yd.1))) y = f y := by
  induction doms with
  | nil => simp at hy
  | cons yd rest ih =>
    simp only [List.map_cons, envOf]
    by_cases hyx : y = yd.1
    · rw [if_pos hyx, hyx]
    · rw [if_neg hyx]
      refine ih ?_
      simp only [List.map_cons] at hy
      rcases List.mem_cons.1 hy with h | h
      · exact absurd h hyx
      · exact h

/-- Cap on the number of enumerated assignments, to keep the pass cheap. -/
def maxEnumSize : Nat := 65536

/-! ### Enumeration target: an algebraic constraint -/

/-- The checked certificate: every enumerated assignment either falsifies the constraint or
    assigns `c` to `x`. -/
def checkForced (doms : List (Variable × List (ZMod p))) (e : Expression p) (x : Variable)
    (c : ZMod p) : Bool :=
  (assignments doms).all
    (fun a => !(decide (e.eval (envOf a) = 0)) || decide (envOf a x = c))

/-- Candidate search (proof-free; `checkForced` re-verifies): the value of each variable in the
    first surviving assignment, if all survivors agree on it. -/
def pickForced (doms : List (Variable × List (ZMod p))) (e : Expression p) :
    Option (Variable × ZMod p) :=
  match (assignments doms).filter (fun a => decide (e.eval (envOf a) = 0)) with
  | [] => (doms.map Prod.fst).head?.map (fun x => (x, 0))
  | a₀ :: survivors =>
    (doms.map Prod.fst).findSome? (fun x =>
      if survivors.all (fun a => decide (envOf a x = envOf a₀ x)) then some (x, envOf a₀ x)
      else none)

/-- Try to derive a forced value from one constraint: bound all its variables by finite domains
    (found anywhere in the system), enumerate, and return a *checked* forced `(x, c)`. -/
def tryConstraint (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (e : Expression p) :
    Option (Variable × ZMod p) :=
  match buildDoms all bs facts bis e.vars.dedup with
  | none => none
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ maxEnumSize then
      match pickForced doms e with
      | some (x, c) =>
          if decide (x ∈ doms.map Prod.fst) && checkForced doms e x c then some (x, c)
          else none
      | none => none
    else none

theorem tryConstraint_sound [Fact p.Prime] [NeZero p] (all : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs) (bis : List (BusInteraction (Expression p)))
    (e : Expression p) (x : Variable) (c : ZMod p)
    (h : tryConstraint all bs facts bis e = some (x, c)) (he : e ∈ all)
    (env : Variable → ZMod p) (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : env x = c := by
  unfold tryConstraint at h
  split at h
  · exact absurd h (by simp)
  · rename_i doms hbd
    split_ifs at h with hsize
    · split at h
      · rename_i x' c' hpf
        split_ifs at h with hcheck
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [Bool.and_eq_true] at hcheck
          obtain ⟨hxmem, hforced⟩ := hcheck
          have hx := of_decide_eq_true hxmem
          -- the restriction of `env` to the domains is an enumerated assignment
          have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
            mem_assignments doms env (buildDoms_sound all bs facts bis _ doms hbd env hall hbus)
          -- the constraint evaluates the same under the restriction
          have hcover : ∀ y ∈ e.vars, y ∈ doms.map Prod.fst := by
            rw [buildDoms_fst all bs facts bis _ doms hbd]
            intro y hy
            exact List.mem_dedup.2 hy
          have heval : e.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = e.eval env :=
            Expression.eval_congr e _ _ (fun y hy => envOf_map doms env y (hcover y hy))
          -- consume the certificate at the restriction
          have hcert := List.all_eq_true.mp hforced _ hmem
          have he0 : e.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = 0 := by
            rw [heval]; exact hall e he
          rcases (Bool.or_eq_true _ _).mp hcert with hbad | hgood
          · rw [Bool.not_eq_true'] at hbad
            exact absurd he0 (of_decide_eq_false hbad)
          · have hxc := of_decide_eq_true hgood
            rw [envOf_map doms env _ hx] at hxc
            exact hxc
      · exact absurd h (by simp)

/-! ### Enumeration target: a bus interaction's obligation -/

/-- Does the assignment survive the interaction's obligation (inactive, or accepted)? -/
def interactionSurvives (bs : BusSemantics p) (bi : BusInteraction (Expression p))
    (a : List (Variable × ZMod p)) : Bool :=
  decide ((bi.eval (envOf a)).multiplicity = 0) || !bs.violatesConstraint (bi.eval (envOf a))

/-- The checked certificate for an interaction target. -/
def checkForcedBi (bs : BusSemantics p) (doms : List (Variable × List (ZMod p)))
    (bi : BusInteraction (Expression p)) (x : Variable) (c : ZMod p) : Bool :=
  (assignments doms).all
    (fun a => !interactionSurvives bs bi a || decide (envOf a x = c))

/-- Candidate search for an interaction target (proof-free). -/
def pickForcedBi (bs : BusSemantics p) (doms : List (Variable × List (ZMod p)))
    (bi : BusInteraction (Expression p)) : Option (Variable × ZMod p) :=
  match (assignments doms).filter (interactionSurvives bs bi) with
  | [] => (doms.map Prod.fst).head?.map (fun x => (x, 0))
  | a₀ :: survivors =>
    (doms.map Prod.fst).findSome? (fun x =>
      if survivors.all (fun a => decide (envOf a x = envOf a₀ x)) then some (x, envOf a₀ x)
      else none)

/-- Try to derive a forced value from one bus interaction's obligation, probing
    `violatesConstraint` pointwise on the domain product. -/
def tryInteraction (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (bi : BusInteraction (Expression p)) :
    Option (Variable × ZMod p) :=
  match buildDoms all bs facts bis bi.vars.dedup with
  | none => none
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ maxEnumSize then
      match pickForcedBi bs doms bi with
      | some (x, c) =>
          if decide (x ∈ doms.map Prod.fst) && checkForcedBi bs doms bi x c then some (x, c)
          else none
      | none => none
    else none

theorem tryInteraction_sound [Fact p.Prime] [NeZero p] (all : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs) (bis : List (BusInteraction (Expression p)))
    (bi : BusInteraction (Expression p)) (x : Variable) (c : ZMod p)
    (h : tryInteraction all bs facts bis bi = some (x, c)) (hbi : bi ∈ bis)
    (env : Variable → ZMod p) (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi' ∈ bis, (bi'.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi'.eval env) = false) : env x = c := by
  unfold tryInteraction at h
  split at h
  · exact absurd h (by simp)
  · rename_i doms hbd
    split_ifs at h with hsize
    · split at h
      · rename_i x' c' hpf
        split_ifs at h with hcheck
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [Bool.and_eq_true] at hcheck
          obtain ⟨hxmem, hforced⟩ := hcheck
          have hx := of_decide_eq_true hxmem
          have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
            mem_assignments doms env (buildDoms_sound all bs facts bis _ doms hbd env hall hbus)
          have hcover : ∀ y ∈ bi.vars, y ∈ doms.map Prod.fst := by
            rw [buildDoms_fst all bs facts bis _ doms hbd]
            intro y hy
            exact List.mem_dedup.2 hy
          have heval : bi.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = bi.eval env :=
            BusInteraction.eval_congr bi _ _ (fun y hy => envOf_map doms env y (hcover y hy))
          -- the restriction survives the obligation
          have hsurv : interactionSurvives bs bi (doms.map (fun yd => (yd.1, env yd.1))) = true := by
            unfold interactionSurvives
            rw [heval]
            by_cases hm : (bi.eval env).multiplicity = 0
            · simp [hm]
            · simp [hm, hbus bi hbi hm]
          have hcert := List.all_eq_true.mp hforced _ hmem
          rcases (Bool.or_eq_true _ _).mp hcert with hbad | hgood
          · rw [Bool.not_eq_true'] at hbad
            rw [hsurv] at hbad
            exact absurd hbad (by simp)
          · have hxc := of_decide_eq_true hgood
            rw [envOf_map doms env _ hx] at hxc
            exact hxc
      · exact absurd h (by simp)

/-! ## The pass -/

/-- Scan the constraints for the first checked forced value. -/
def findForcedC (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) :
    List (Expression p) → Option (Variable × ZMod p)
  | [] => none
  | e :: rest =>
    match tryConstraint all bs facts bis e with
    | some r => some r
    | none => findForcedC all bs facts bis rest

theorem findForcedC_sound [Fact p.Prime] [NeZero p] (all sub : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs) (bis : List (BusInteraction (Expression p)))
    (x : Variable) (c : ZMod p) (h : findForcedC all bs facts bis sub = some (x, c))
    (hsub : ∀ e ∈ sub, e ∈ all) (env : Variable → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : env x = c := by
  induction sub with
  | nil => exact absurd h (by simp [findForcedC])
  | cons e rest ih =>
    rw [findForcedC] at h
    cases htc : tryConstraint all bs facts bis e with
    | some r =>
        rw [htc] at h
        simp only [Option.some.injEq] at h
        subst h
        exact tryConstraint_sound all bs facts bis e x c htc (hsub e (List.mem_cons_self ..))
          env hall hbus
    | none =>
        rw [htc] at h
        exact ih h (fun e' he' => hsub e' (List.mem_cons_of_mem _ he'))

/-- Scan the interactions for the first checked forced value. -/
def findForcedI (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) → Option (Variable × ZMod p)
  | [] => none
  | bi :: rest =>
    match tryInteraction all bs facts bis bi with
    | some r => some r
    | none => findForcedI all bs facts bis rest

theorem findForcedI_sound [Fact p.Prime] [NeZero p] (all : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis sub : List (BusInteraction (Expression p))) (x : Variable) (c : ZMod p)
    (h : findForcedI all bs facts bis sub = some (x, c)) (hsub : ∀ bi ∈ sub, bi ∈ bis)
    (env : Variable → ZMod p) (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : env x = c := by
  induction sub with
  | nil => exact absurd h (by simp [findForcedI])
  | cons bi rest ih =>
    rw [findForcedI] at h
    cases htc : tryInteraction all bs facts bis bi with
    | some r =>
        rw [htc] at h
        simp only [Option.some.injEq] at h
        subst h
        exact tryInteraction_sound all bs facts bis bi x c htc (hsub bi (List.mem_cons_self ..))
          env hall hbus
    | none =>
        rw [htc] at h
        exact ih h (fun bi' hbi' => hsub bi' (List.mem_cons_of_mem _ hbi'))

/-- Scan constraints, then interaction obligations, for a checked forced value. -/
def findForced (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) : Option (Variable × ZMod p) :=
  match findForcedC all bs facts bis all with
  | some r => some r
  | none => findForcedI all bs facts bis bis

theorem findForced_sound [Fact p.Prime] [NeZero p] (all : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs) (bis : List (BusInteraction (Expression p)))
    (x : Variable) (c : ZMod p) (h : findForced all bs facts bis = some (x, c))
    (env : Variable → ZMod p) (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : env x = c := by
  unfold findForced at h
  cases hc : findForcedC all bs facts bis all with
  | some r =>
      rw [hc] at h
      simp only [Option.some.injEq] at h
      subst h
      exact findForcedC_sound all all bs facts bis x c hc (fun _ he => he) env hall hbus
  | none =>
      rw [hc] at h
      exact findForcedI_sound all bs facts bis bis x c h (fun _ hbi => hbi) env hall hbus

/-- The finite-domain propagation pass: substitute one variable whose value is forced by
    domain enumeration (over constraints or probed bus obligations). Requires `p` prime
    (decided at runtime; identity otherwise). -/
def domainPropPass : VerifiedPassW p := fun cs bs facts =>
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    match hf : findForced cs.algebraicConstraints bs facts cs.busInteractions with
    | some (x, c) =>
        ⟨cs.subst x (.const c), [],
         cs.subst_correct x (.const c) bs
           (fun env hsat =>
             findForced_sound cs.algebraicConstraints bs facts cs.busInteractions x c hf
               env (fun c' hc' => hsat.1 c' hc') (fun bi hbi => hsat.2 bi hbi))
           (fun y hy => by simp [Expression.vars] at hy)⟩
    | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
