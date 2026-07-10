import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp

set_option autoImplicit false

/-! # Two-root decomposition unification (bounded-integer reasoning)

Memory-pointer decompositions pin each limb by a **two-root carry constraint**
`(A + k·x) · (A + δ + k·x) = 0` — the two cases of the address wraparound — plus a range check
keeping `x` inside a window smaller than the root gap. Two accesses at the *same* address
produce two such constraints with the **same** `A`, `k`, `δ` but distinct limb variables `x`,
`y`: each variable independently picks a root, so no purely algebraic pass can equate them. The
bounded-integer argument closes it: both roots differ by `g = k⁻¹·δ`; if `x.val < B` and
`y.val < B` with `B ≤ g.val` and `B ≤ p − g.val`, the field difference `x − y = ±g` is
impossible over the integers, so `x = y`. powdr eliminates exactly these duplicates (apc_005:
258 limb variables kept here vs powdr's 130 before this pass).

The entailed equality `y = x` feeds the same proof-carrying `Solved` map as `Gauss.lean`
(solutions are bare variables, so no degree gate and no resolution is needed) and one final
`ConstraintSystem.substF`. Bounds come from retained range-check interactions via
`findVarBound` (`DomainProp.lean`), conditional on the system's own satisfaction — every
justifying interaction is retained, so `hsat.2` supplies acceptance. Prime `p` only (root
membership needs an integral domain); the pass re-checks `decide p.Prime` at runtime like
`busPairCancelPass`. -/

variable {p : ℕ}

/-! ## The core field lemmas -/

/-- Membership in the root pair: a satisfied two-root constraint puts `x` at one of the two
    roots, `g = k⁻¹·δ` apart. -/
theorem twoRoot_mem [Fact p.Prime] (k a δ x : ZMod p) (hunit : k * k⁻¹ = 1)
    (h : (a + k * x) * (a + δ + k * x) = 0) :
    x = -(k⁻¹ * a) ∨ x = -(k⁻¹ * a) - k⁻¹ * δ := by
  rcases mul_eq_zero.1 h with h0 | h0
  · left; linear_combination k⁻¹ * h0 - x * hunit
  · right; linear_combination k⁻¹ * h0 - x * hunit

/-- Two values in the same root pair, both bounded below the root gap (and its complement),
    are equal: their field difference is `0` or `±g`, and `±g` is out of integer reach. -/
theorem rootPair_eq [Fact p.Prime] (r g x y : ZMod p)
    (hx : x = r ∨ x = r - g) (hy : y = r ∨ y = r - g)
    (B : Nat) (hxB : x.val < B) (hyB : y.val < B)
    (h1 : B ≤ g.val) (h2 : B ≤ p - g.val) : x = y := by
  have key : ∀ u v : ZMod p, u.val < B → v.val < B → u = v - g → False := by
    intro u v hu hv huv
    have hvg : v = u + g := by rw [huv]; ring
    have hval : v.val = (u.val + g.val) % p := by rw [hvg, ZMod.val_add]
    by_cases hlt : u.val + g.val < p
    · rw [Nat.mod_eq_of_lt hlt] at hval
      omega
    · -- `u.val ≥ p − g.val ≥ B` contradicts `u.val < B`
      have hgp : g.val < p := ZMod.val_lt g
      omega
  rcases hx with rfl | rfl
  · rcases hy with h | h
    · exact h.symm
    · exact (key y x hyB hxB h).elim
  · rcases hy with h | h
    · exact (key (r - g) r hxB (h ▸ hyB) rfl).elim
    · exact h.symm

/-! ## Recognizing a two-root constraint -/

/-- Two normalized linear forms with equal term lists evaluate a constant apart. -/
theorem LinExpr.eval_of_terms_eq (a b : LinExpr p) (h : b.terms = a.terms)
    (env : Variable → ZMod p) : b.eval env = a.eval env + (b.const - a.const) := by
  simp only [LinExpr.eval, h]; ring

/-- The two-root decomposition of a constraint relative to `x`: `some (k, A, δ)` when the
    constraint is a product of two affine factors, both linear in `x` with the same nonzero
    coefficient `k`, whose `x`-free parts differ by the constant `δ` — i.e. the constraint
    evaluates as `(A.eval + k·x) · (A.eval + δ + k·x)`. -/
def twoRootOf? (c : Expression p) (x : Variable) : Option (ZMod p × LinExpr p × ZMod p) :=
  match c with
  | .mul f1 f2 =>
    match linearize f1, linearize f2 with
    | some l1, some l2 =>
      let k := l1.coeff x
      let A := (l1.others x).norm
      let A2 := (l2.others x).norm
      if k ≠ 0 ∧ l2.coeff x = k ∧ A2.terms = A.terms then some (k, A, A2.const - A.const)
      else none
    | _, _ => none
  | _ => none

theorem twoRootOf?_sound [Fact p.Prime] (c : Expression p) (x : Variable)
    (k : ZMod p) (A : LinExpr p) (δ : ZMod p) (h : twoRootOf? c x = some (k, A, δ))
    (hk : k * k⁻¹ = 1) (env : Variable → ZMod p) (hc : c.eval env = 0) :
    env x = -(k⁻¹ * A.eval env) ∨ env x = -(k⁻¹ * A.eval env) - k⁻¹ * δ := by
  unfold twoRootOf? at h
  split at h
  case h_2 => exact absurd h (by simp)
  case h_1 f1 f2 =>
    cases hl1 : linearize f1 with
    | none => rw [hl1] at h; exact absurd h (by simp)
    | some l1 =>
      cases hl2 : linearize f2 with
      | none => rw [hl1, hl2] at h; simp at h
      | some l2 =>
        simp only [hl1, hl2] at h
        split_ifs at h with hcond
        obtain ⟨hk0, hcoeff, hterms⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        -- both factors evaluate as `A.eval + (shift) + k·x`
        have hf1 : f1.eval env = ((l1.others x).norm).eval env + l1.coeff x * env x := by
          rw [linearize_eval f1 l1 hl1 env, l1.eval_split x]
          have := LinExpr.norm_eval (l1.others x) env
          rw [this]; ring
        have hf2 : f2.eval env
            = ((l1.others x).norm).eval env + ((l1.others x).norm.const - ((l2.others x).norm.const)
              - ((l1.others x).norm.const - (l2.others x).norm.const)) * 0
              + ((l2.others x).norm.const - (l1.others x).norm.const) + l1.coeff x * env x := by
          rw [linearize_eval f2 l2 hl2 env, l2.eval_split x, hcoeff]
          have h2 := LinExpr.norm_eval (l2.others x) env
          have h3 := LinExpr.eval_of_terms_eq (l1.others x).norm (l2.others x).norm hterms env
          rw [← h2, h3]
          have h1 := LinExpr.norm_eval (l1.others x) env
          ring
        have hprod : (((l1.others x).norm).eval env + l1.coeff x * env x)
            * (((l1.others x).norm).eval env + ((l2.others x).norm.const - (l1.others x).norm.const)
              + l1.coeff x * env x) = 0 := by
          rw [← hf1]
          have : f2.eval env = ((l1.others x).norm).eval env
              + ((l2.others x).norm.const - (l1.others x).norm.const)
              + l1.coeff x * env x := by rw [hf2]; ring
          rw [← this]
          exact hc
        exact twoRoot_mem (l1.coeff x) (((l1.others x).norm).eval env) _ (env x) hk hprod

/-- `x` genuinely occurs in a recognized constraint (needed for `Solved.varsIn`). -/
def twoRootVarsOk (c : Expression p) (x : Variable) : Bool :=
  decide (x ∈ c.vars)

/-! ## Constant-coefficient decomposition

`e = k·x + r` with `k` a field constant and `r` an `x`-free expression — unlike `linearize`,
the remainder may be *nonlinear* (the flag polynomial inside a scaled range-check slot), so
this succeeds exactly where the affine machinery gives up. -/

/-- Decompose `e` as `k·x + r`: `k` a field constant, `r` not mentioning `x` (by construction).
    Succeeds iff every occurrence of `x` in `e` sits additively under multiplications by
    constant-foldable factors. `x`-free subtrees are kept opaque (coefficient `0`). -/
def Expression.splitAt (x : Variable) : Expression p → Option (ZMod p × Expression p)
  | .const n => some (0, .const n)
  | .var y => if y = x then some (1, .const 0) else some (0, .var y)
  | .add a b =>
      match a.splitAt x, b.splitAt x with
      | some (ca, ra), some (cb, rb) => some (ca + cb, .add ra rb)
      | _, _ => none
  | .mul a b =>
      if a.mentions x || b.mentions x then
        match a.constValue? with
        | some k =>
            match b.splitAt x with
            | some (cb, rb) => some (k * cb, .mul a rb)
            | none => none
        | none =>
            match b.constValue? with
            | some k =>
                match a.splitAt x with
                | some (ca, ra) => some (k * ca, .mul ra b)
                | none => none
            | none => none
      else some (0, .mul a b)

/-- The decomposition is exact: `e` evaluates as `k·x + r`. -/
theorem Expression.splitAt_eval (x : Variable) (e : Expression p) (k : ZMod p)
    (r : Expression p) (h : e.splitAt x = some (k, r)) (env : Variable → ZMod p) :
    e.eval env = k * env x + r.eval env := by
  induction e generalizing k r with
  | const n =>
      simp only [splitAt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Expression.eval]
  | var y =>
      simp only [splitAt] at h
      split_ifs at h with hyx
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hyx
        simp [Expression.eval]
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [Expression.eval]
  | add a b iha ihb =>
      cases ha : a.splitAt x with
      | none => simp [splitAt, ha] at h
      | some pa =>
          cases hb : b.splitAt x with
          | none => simp [splitAt, ha, hb] at h
          | some pb =>
              obtain ⟨ca, ra⟩ := pa
              obtain ⟨cb, rb⟩ := pb
              simp only [splitAt, ha, hb, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [Expression.eval, iha ca ra ha, ihb cb rb hb]
              ring
  | mul a b iha ihb =>
      simp only [splitAt] at h
      split_ifs at h with hm
      · cases hka : a.constValue? with
        | some ka =>
            cases hb : b.splitAt x with
            | none => simp [hka, hb] at h
            | some pb =>
                obtain ⟨cb, rb⟩ := pb
                simp only [hka, hb, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hae : a.eval env = ka := a.constValue?_sound ka hka env
                simp only [Expression.eval, hae, ihb cb rb hb]
                ring
        | none =>
            cases hkb : b.constValue? with
            | none => simp [hka, hkb] at h
            | some kb =>
                cases ha : a.splitAt x with
                | none => simp [hka, hkb, ha] at h
                | some pa =>
                    obtain ⟨ca, ra⟩ := pa
                    simp only [hka, hkb, ha, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hbe : b.eval env = kb := b.constValue?_sound kb hkb env
                    simp only [Expression.eval, hbe, iha ca ra ha]
                    ring
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [Expression.eval]


/-! ## Bounds through scaled range checks

The low mem-ptr limb's range check does not carry the limb raw: the checked slot is
`4⁻¹·(x − F)` for a small flag polynomial `F`. The slot *value* is still fact-bounded, so
`x = k⁻¹·slot − k⁻¹·R` is bounded once the offset part enumerates over its (tiny, provable)
flag domains: `x.val < m.val·(bound−1) + Wmax + 1`, provided nothing wraps `p`. -/

/-- `LinExpr.eval` only reads the term variables. -/
theorem LinExpr.eval_congr_vars (l : LinExpr p) (f g : Variable → ZMod p)
    (h : ∀ v ∈ l.terms.map Prod.fst, f v = g v) : l.eval f = l.eval g := by
  simp only [LinExpr.eval]
  congr 1
  refine congrArg List.sum ?_
  refine List.map_congr_left (fun t ht => ?_)
  rw [h t.1 (List.mem_map.2 ⟨t, ht, rfl⟩)]

/-- The seed is at most the `foldl max` accumulation. -/
theorem init_le_foldl_max (l : List Nat) : ∀ b : Nat, b ≤ l.foldl max b := by
  induction l with
  | nil => intro b; simp
  | cons c rest ih => intro b; exact le_trans (le_max_left b c) (ih (max b c))

/-- Everything in a list is at most its `foldl max` accumulation. -/
theorem le_foldl_max (l : List Nat) : ∀ (b : Nat), ∀ a ∈ l, a ≤ l.foldl max b := by
  induction l with
  | nil => intro b a ha; simp at ha
  | cons c rest ih =>
    intro b a ha
    rcases List.mem_cons.1 ha with rfl | h
    · exact le_trans (le_max_right b a) (init_le_foldl_max rest (max b a))
    · exact ih (max b c) a h

/-- Bound `x` through one interaction: find a slot whose expression is affine in `x` with a
    unit coefficient and a bus-fact value bound; enumerate the remaining variables' proven
    finite domains for the offset part. Returns `B` with `x.val < B` under acceptance. -/
def scaledSlotBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (bi : BusInteraction (Expression p)) (x : Variable) :
    Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none else
    (List.range bi.payload.length).findSome? (fun slot =>
      match bi.payload[slot]? with
      | none => none
      | some O =>
        match facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) slot with
        | none => none
        | some bound =>
          match O.splitAt x with
          | none => none
          | some (k, R) =>
            let m := k⁻¹
            let others := R.vars.eraseDups
            let doms := others.filterMap (fun v =>
              (findDomainAlg domCs v).map (fun d => (v, d)))
            if k * m = 1 ∧ doms.map Prod.fst = others ∧
                (doms.map (fun vd => vd.2.length)).prod ≤ 16 then
              if m.val * (bound - 1) + ((assignments doms).map
                    (fun pt => ((-m) * R.eval (envOf pt)).val)).foldl max 0 < p then
                some (m.val * (bound - 1) + ((assignments doms).map
                  (fun pt => ((-m) * R.eval (envOf pt)).val)).foldl max 0 + 1)
              else none
            else none)

theorem scaledSlotBound_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (bi : BusInteraction (Expression p)) (x : Variable)
    (B : Nat) (h : scaledSlotBound bs facts domCs bi x = some B) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval env = 0)
    (hob : (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) :
    (env x).val < B := by
  unfold scaledSlotBound at h
  cases hmv : bi.multiplicity.constValue? with
  | none => rw [hmv] at h; simp at h
  | some mval =>
    simp only [hmv] at h
    split_ifs at h with hmz
    obtain ⟨slot, _hslot, hs⟩ := List.exists_of_findSome?_eq_some h
    cases hO : bi.payload[slot]? with
    | none => simp [hO] at hs
    | some O =>
      simp only [hO] at hs
      cases hfact : facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) slot with
      | none => simp [hfact] at hs
      | some bound =>
        simp only [hfact] at hs
        cases hlin : O.splitAt x with
        | none => simp [hlin] at hs
        | some kR =>
          obtain ⟨k, R⟩ := kR
          simp only [hlin] at hs
          split_ifs at hs with hcond hwrap
          simp only [Option.some.injEq] at hs
          obtain ⟨hunit, hcover, _hcap⟩ := hcond
          -- acceptance and the fact bound on the slot value
          have hmeval : (bi.eval env).multiplicity = mval :=
            bi.multiplicity.constValue?_sound mval hmv env
          have hviol : bs.violatesConstraint (bi.eval env) = false :=
            hob (by rw [hmeval]; exact hmz)
          have hget : (bi.eval env).payload[slot]? = some (O.eval env) := by
            show (bi.payload.map (fun e => e.eval env))[slot]? = _
            rw [List.getElem?_map, hO]; rfl
          have hOb : (O.eval env).val < bound := by
            have := facts.slotBound_sound (bi.eval env)
              (bi.payload.map Expression.constValue?) slot bound (O.eval env)
              (by rw [(rfl : (bi.eval env).busId = bi.busId), hmeval]; exact hfact)
              (matches_evalPattern bi.payload env) hviol hget
            exact this
          -- the field identity `x = m·O − m·R`
          set m := k⁻¹ with hm
          have hOx : O.eval env = k * env x + R.eval env :=
            Expression.splitAt_eval x O k R hlin env
          have hxid : env x = m * O.eval env + (-m) * R.eval env := by
            have : m * O.eval env = m * k * env x + m * R.eval env := by
              rw [hOx]; ring
            rw [mul_comm m k] at this
            rw [hunit, one_mul] at this
            linear_combination -this
          -- the offset part is one of the enumerated points
          have hmemdoms : ∀ vd ∈ R.vars.eraseDups.filterMap (fun v =>
              (findDomainAlg domCs v).map (fun d => (v, d))), env vd.1 ∈ vd.2 := by
            intro vd hvd
            obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
            cases hfd : findDomainAlg domCs v with
            | none => rw [hfd] at hvd'; simp at hvd'
            | some d =>
              rw [hfd] at hvd'
              simp only [Option.map_some, Option.some.injEq] at hvd'
              obtain rfl := hvd'.symm
              exact findDomainAlg_sound domCs v d hfd env hdom
          have hpt := mem_assignments (R.vars.eraseDups.filterMap (fun v =>
            (findDomainAlg domCs v).map (fun d => (v, d)))) env hmemdoms
          have hWagree : R.eval (envOf ((R.vars.eraseDups.filterMap (fun v =>
              (findDomainAlg domCs v).map (fun d => (v, d)))).map
                (fun vd => (vd.1, env vd.1)))) = R.eval env := by
            refine Expression.eval_congr R _ env (fun v hv => ?_)
            refine envOf_map _ env v ?_
            rw [show ((R.vars.eraseDups.filterMap (fun v =>
              (findDomainAlg domCs v).map (fun d => (v, d)))).map Prod.fst)
              = R.vars.eraseDups from hcover]
            exact List.mem_eraseDups.2 hv
          have hWle : ((-m) * R.eval env).val
              ≤ ((assignments (R.vars.eraseDups.filterMap (fun v =>
                (findDomainAlg domCs v).map (fun d => (v, d))))).map
                  (fun pt => ((-m) * R.eval (envOf pt)).val)).foldl max 0 := by
            refine le_foldl_max _ 0 _ ?_
            refine List.mem_map.2 ⟨_, hpt, ?_⟩
            rw [hWagree]
          -- integer arithmetic without wraparound
          have hu : (m * O.eval env).val = m.val * (O.eval env).val := by
            refine ZMod.val_mul_of_lt ?_
            calc m.val * (O.eval env).val ≤ m.val * (bound - 1) := by
                  have := hOb; exact Nat.mul_le_mul_left _ (by omega)
              _ < p := by omega
          have hsum : (m * O.eval env).val + ((-m) * R.eval env).val < p := by
            rw [hu]
            have h1 : m.val * (O.eval env).val ≤ m.val * (bound - 1) :=
              Nat.mul_le_mul_left _ (by omega)
            omega
          rw [hxid, ZMod.val_add_of_lt hsum, hu]
          have h1 : m.val * (O.eval env).val ≤ m.val * (bound - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega

/-- Bound `x` from a raw slot (`findVarBound`) or, failing that, through a scaled slot. -/
def anyVarBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (domCs : List (Expression p))
    (x : Variable) : Option Nat :=
  match findVarBound bs facts bis x with
  | some B => some B
  | none => bis.findSome? (fun bi => scaledSlotBound bs facts domCs bi x)

theorem anyVarBound_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (domCs : List (Expression p))
    (x : Variable) (B : Nat) (h : anyVarBound bs facts bis domCs x = some B)
    (env : Variable → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) : (env x).val < B := by
  unfold anyVarBound at h
  cases hfb : findVarBound bs facts bis x with
  | some B' =>
    simp only [hfb, Option.some.injEq] at h
    exact h ▸ findVarBound_sound bs facts bis x B' hfb env hbus
  | none =>
    simp only [hfb] at h
    obtain ⟨bi, hbi, hsb⟩ := List.exists_of_findSome?_eq_some h
    exact scaledSlotBound_sound bs facts domCs bi x B hsb env hdom (hbus bi hbi)

/-! ## The pair certificate -/

/-- Decidable certificate that constraints `cX` (in `x`) and `cY` (in `y`) are two-root twins
    and both variables are range-bounded below the root gap — hence provably equal under every
    satisfying assignment. Re-checked inside the adoption proof, so the scan can stay
    proof-free. -/
def rpCheckPair (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (domCs : List (Expression p))
    (cX cY : Expression p) (x y : Variable) : Bool :=
  match twoRootOf? cX x, twoRootOf? cY y with
  | some (k, A, δ), some (k', A', δ') =>
    decide (k' = k) && decide (A'.terms = A.terms) && decide (A'.const = A.const) &&
    decide (δ' = δ) && decide (k * k⁻¹ = 1) &&
    decide (x ∈ cX.vars) && decide (y ∈ cY.vars) &&
    (match anyVarBound bs facts bis domCs x, anyVarBound bs facts bis domCs y with
     | some Bx, some By =>
       decide (max Bx By ≤ (k⁻¹ * δ).val) && decide (max Bx By ≤ p - (k⁻¹ * δ).val)
     | _, _ => false)
  | _, _ => false

theorem rpCheckPair_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (domCs : List (Expression p))
    (cX cY : Expression p) (x y : Variable)
    (h : rpCheckPair bs facts bis domCs cX cY x y = true) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval env = 0)
    (hcX : cX.eval env = 0) (hcY : cY.eval env = 0)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    env x = env y := by
  unfold rpCheckPair at h
  cases hx : twoRootOf? cX x with
  | none => rw [hx] at h; simp at h
  | some t =>
    obtain ⟨k, A, δ⟩ := t
    cases hy : twoRootOf? cY y with
    | none => rw [hx, hy] at h; simp at h
    | some t' =>
      obtain ⟨k', A', δ'⟩ := t'
      rw [hx, hy] at h
      cases hbx : anyVarBound bs facts bis domCs x with
      | none => rw [hbx] at h; simp at h
      | some Bx =>
        cases hby : anyVarBound bs facts bis domCs y with
        | none => rw [hbx, hby] at h; simp at h
        | some By =>
          rw [hbx, hby] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨⟨⟨⟨hk', hAt⟩, hAc⟩, hδ'⟩, hunit⟩, _hxv⟩, _hyv⟩, hB1, hB2⟩ := h
          have hxr := twoRootOf?_sound cX x k A δ hx hunit env hcX
          have hyr := twoRootOf?_sound cY y k' A' δ' hy (by rw [hk']; exact hunit) env hcY
          -- `A'` evaluates like `A` (equal terms and consts), so the root pairs coincide
          have hAeq : A'.eval env = A.eval env := by
            rw [LinExpr.eval_of_terms_eq A A' hAt env, hAc]; ring
          rw [hk', hAeq, hδ'] at hyr
          exact rootPair_eq (-(k⁻¹ * A.eval env)) (k⁻¹ * δ) (env x) (env y)
            hxr hyr
            (max Bx By)
            (lt_of_lt_of_le (anyVarBound_sound bs facts bis domCs x Bx hbx env hdom hbus)
              (le_max_left _ _))
            (lt_of_lt_of_le (anyVarBound_sound bs facts bis domCs y By hby env hdom hbus)
              (le_max_right _ _))
            hB1 hB2

/-- Extract the variable memberships from a passed certificate. -/
theorem rpCheckPair_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) (domCs : List (Expression p))
    (cX cY : Expression p) (x y : Variable)
    (h : rpCheckPair bs facts bis domCs cX cY x y = true) : x ∈ cX.vars ∧ y ∈ cY.vars := by
  unfold rpCheckPair at h
  cases hx : twoRootOf? cX x with
  | none => rw [hx] at h; simp at h
  | some t =>
    obtain ⟨k, A, δ⟩ := t
    cases hy : twoRootOf? cY y with
    | none => rw [hx, hy] at h; simp at h
    | some t' =>
      obtain ⟨k', A', δ'⟩ := t'
      rw [hx, hy] at h
      cases hbx : anyVarBound bs facts bis domCs x with
      | none => rw [hbx] at h; simp at h
      | some Bx =>
        cases hby : anyVarBound bs facts bis domCs y with
        | none => rw [hbx, hby] at h; simp at h
        | some By =>
          rw [hbx, hby] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨h.1.1.2, h.1.2⟩

/-! ## The scan loop and the pass -/

/-- A previously seen two-root constraint: the constraint (with membership), its variable, and
    the matching key `(k, A.terms, A.const, δ)`. Keys are compared before the (expensive)
    certificate is attempted. -/
structure RPSeen (p : ℕ) (cs : ConstraintSystem p) where
  c : Expression p
  mem : c ∈ cs.algebraicConstraints
  x : Variable
  key : ZMod p × List (Variable × ZMod p) × ZMod p × ZMod p

/-- The two-root candidates of one constraint, with their matching keys. Candidates whose root
    gap `g = k⁻¹·δ` is tiny are dropped up front: the pair condition `B ≤ min(g.val, p − g.val)`
    can never hold for a useful bound `B`, and booleanity constraints `b(b−1) = 0` would
    otherwise make every boolean variable a (never-unifiable, expensive-to-reject) candidate. -/
def rpCandidates (c : Expression p) :
    List (Variable × (ZMod p × List (Variable × ZMod p) × ZMod p × ZMod p)) :=
  c.vars.eraseDups.filterMap (fun x =>
    match twoRootOf? c x with
    | some (k, A, δ) =>
      if 256 ≤ min (k⁻¹ * δ).val (p - (k⁻¹ * δ).val) then
        some (x, (k, A.terms, A.const, δ))
      else none
    | none => none)

/-- Scan the constraints: for each two-root candidate, look for an earlier twin with the same
    key whose pair certificate passes, and adopt the entailed equality into the solution map.
    The certificate is re-checked inside the proof, so the scan itself carries no obligations. -/
def rpLoop [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (domCs : List (Expression p))
    (hdomCs : ∀ c ∈ domCs, c ∈ cs.algebraicConstraints) :
    (pending : List (Expression p)) → (∀ c ∈ pending, c ∈ cs.algebraicConstraints) →
    List (RPSeen p cs) → Solved p cs bs → Solved p cs bs
  | [], _, _, σ => σ
  | c :: rest, hmem, seen, σ =>
    have hc : c ∈ cs.algebraicConstraints := hmem c (List.mem_cons_self ..)
    let hrest := fun c' h' => hmem c' (List.mem_cons_of_mem _ h')
    let cands := rpCandidates c
    match hfound : cands.findSome? (fun xk =>
        seen.findSome? (fun e =>
          if e.key == xk.2 && e.x != xk.1 &&
              rpCheckPair bs facts cs.busInteractions domCs e.c c e.x xk.1
          then some (e, xk.1) else none)) with
    | some ex =>
        have hcert : rpCheckPair bs facts cs.busInteractions domCs ex.1.c c ex.1.x ex.2 = true := by
          obtain ⟨xk, _hxk, hinner⟩ := List.exists_of_findSome?_eq_some hfound
          obtain ⟨e, _he, hif⟩ := List.exists_of_findSome?_eq_some hinner
          by_cases hcnd : (e.key == xk.2 && e.x != xk.1 &&
              rpCheckPair bs facts cs.busInteractions domCs e.c c e.x xk.1) = true
          · rw [if_pos hcnd] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            rw [Bool.and_eq_true] at hcnd
            exact hcnd.2
          · rw [if_neg hcnd] at hif
            exact absurd hif (by simp)
        have hpairs : ∀ env, cs.satisfies bs env →
            ∀ yt ∈ [(ex.2, Expression.var ex.1.x)], env yt.1 = yt.2.eval env := by
          intro env hsat yt hyt
          obtain rfl : yt = (ex.2, Expression.var ex.1.x) := by simpa using hyt
          show env ex.2 = env ex.1.x
          exact (rpCheckPair_sound bs facts cs.busInteractions domCs ex.1.c c ex.1.x ex.2
            hcert env (fun c' hc' => hsat.1 c' (hdomCs c' hc'))
            (hsat.1 ex.1.c ex.1.mem) (hsat.1 c hc)
            (fun bi hbi hmult => hsat.2 bi hbi hmult)).symm
        have hpairsV : ∀ yt ∈ [(ex.2, Expression.var ex.1.x)],
            ∀ z ∈ yt.2.vars, z ∈ cs.vars := by
          intro yt hyt z hz
          obtain rfl : yt = (ex.2, Expression.var ex.1.x) := by simpa using hyt
          obtain rfl : z = ex.1.x := by simpa [Expression.vars] using hz
          exact ConstraintSystem.mem_vars_of_constraint ex.1.mem
            (rpCheckPair_vars bs facts cs.busInteractions domCs ex.1.c c ex.1.x ex.2 hcert).1
        rpLoop cs bs facts domCs hdomCs rest hrest
          ((cands.filter (fun xk => xk.1 != ex.2)).map (fun xk => ⟨c, hc, xk.1, xk.2⟩) ++ seen)
          (σ.insertAll [(ex.2, Expression.var ex.1.x)] hpairs hpairsV)
    | none =>
        rpLoop cs bs facts domCs hdomCs rest hrest
          (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩) ++ seen) σ

/-- Two-root decomposition unification. Prime `p` only (re-checked at runtime, as in
    `busPairCancelPass`). One sweep; the cleanup fixpoint iterates the pass, so chains resolve
    across cycles (the high limbs' root expressions become equal only after the low limbs
    unify). Solutions are bare variables, so substitution can never grow a degree. -/
def rootPairUnifyPass : VerifiedPassW p := fun cs bs facts =>
  if hp : (decide p.Prime) = true then
    haveI : Fact p.Prime := ⟨of_decide_eq_true hp⟩
    let σ := rpLoop cs bs facts cs.algebraicConstraints (fun _ h => h)
      cs.algebraicConstraints (fun _ h => h) [] Solved.empty
    if σ.map.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs.substF σ.fn, [],
      cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)
        (fun y t hyt => σ.varsIn y t hyt)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

