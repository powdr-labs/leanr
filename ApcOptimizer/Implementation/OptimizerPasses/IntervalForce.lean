import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Interval forcing: integer-window analysis of bounded affine slots

A bus slot with a proven value bound `B` (`BusFacts.slotBound`) whose expression is *affine* in
range-bounded variables carries far more information than the field-level bound suggests: choosing
the signed minimal-magnitude integer representative for each coefficient, the slot's value is an
**integer** `S = c̃₀ + Σ c̃ᵢ·xᵢ` confined to the window `[lo, hi]` spanned by the variable bounds.
If that window is narrow enough that only the residues `[0, B)` themselves survive the reduction
mod `p` (`hi ≤ p − 1` and `lo ≥ B − p`), then `S ∈ [0, B)` holds **over ℤ** — and integer
reasoning on the coefficients forces facts no single field-level bound can see:

* **pair arm** — terms `+g·v` and `−g·w` whose companion window `R ∈ [Rlo, Rhi]` satisfies
  `B ≤ g + Rlo` and `Rhi < g` force `v = w` (any `v − w ≥ 1` pushes `S ≥ B`, any `≤ −1` pushes
  `S < 0`);
* **zero arm** — a term `g·v` with `0 < g` and `B ≤ g + Rlo` (or `g < 0` and `Rhi + g < 0`)
  forces `v = 0`.

The motivating SP1 shapes (KoalaBear, `8323072 = −1/256`): the op-6 checks
`r₀ + 256·r₁ − 256·h < 2⁸` force `h = r₁` (the `higher_limb` clusters powdr substitutes away), the
byte slots `r₂ + 256·r₃ + 8323072·(c − h) − 256·h'` force `c = h`, and the 16-bit memory data
slots `256·r₂ + 65536·r₃ + h − 65536·h'` force `h' = r₃` — after which the memory payloads become
plain affine byte recompositions that `busPairCancel` can justify and telescope.

This pass **generalizes and replaces `ScaledZero`**: the single scaled variable (`k·v < B₂`,
`k ≥ B₂`, no wrap) and the two-term slot (`k·v − k·w`) are exactly the one- and two-term instances
of the window argument. Algebraic constraints are consumed as bound-`1` slots (an equality pins
the window to `{0}`), so the same arms fire on constraint ladders before Gauss consumes their
pivots.

Every derived fact is seeded as an algebraic constraint (`v − w = 0` / `v = 0`) via
`ConstraintSystem.addConstraints_correct`; Gauss substitutes them and the fold/byte-check/memory
passes cascade. Purely arithmetic on proven bounds — no primality, no VM specifics beyond
`slotBound`. -/

namespace IntervalForce

variable {p : ℕ}

/-! ## Signed representatives and processed terms -/

/-- Signed minimal-magnitude integer representative of a field element: `c.val` when
    `c.val ≤ (p−1)/2`, else `c.val − p`. Scaled differences like `256·a − 256·b` thus get the
    small-magnitude coefficients `(256, −256)` rather than `(256, p−256)`. -/
def srep (c : ZMod p) : Int :=
  if c.val ≤ (p - 1) / 2 then (c.val : Int) else (c.val : Int) - (p : Int)

theorem srep_cast [NeZero p] (c : ZMod p) : ((srep c : Int) : ZMod p) = c := by
  unfold srep
  split_ifs
  · rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  · push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self, sub_zero]

/-- A processed affine term: signed integer coefficient, a proven strict bound for the variable's
    value, and the variable itself. -/
structure PTerm where
  sc : Int
  bnd : Nat
  v : Variable

/-- Pair every term of a linear form with its variable's proven bound; `none` if any variable is
    unbounded. -/
def procTerms (bnd : Variable → Option Nat) : List (Variable × ZMod p) → Option (List PTerm)
  | [] => some []
  | (v, c) :: rest =>
    match bnd v, procTerms bnd rest with
    | some B, some pts => some (⟨srep c, B, v⟩ :: pts)
    | _, _ => none

/-- The integer value of a processed term list under an assignment. -/
def intEval (env : Variable → ZMod p) (pts : List PTerm) : Int :=
  (pts.map (fun t => t.sc * ((env t.v).val : Int))).sum

/-- Upper window bound: each term contributes `max (sc·(B−1)) 0`. -/
def maxSum (pts : List PTerm) : Int :=
  (pts.map (fun t => max (t.sc * ((t.bnd : Int) - 1)) 0)).sum

/-- Lower window bound: each term contributes `min (sc·(B−1)) 0`. -/
def minSum (pts : List PTerm) : Int :=
  (pts.map (fun t => min (t.sc * ((t.bnd : Int) - 1)) 0)).sum

theorem procTerms_cast [NeZero p] (bnd : Variable → Option Nat)
    (terms : List (Variable × ZMod p)) (pts : List PTerm)
    (h : procTerms bnd terms = some pts) (env : Variable → ZMod p) :
    ((intEval env pts : Int) : ZMod p) = (terms.map (fun t => t.2 * env t.1)).sum := by
  induction terms generalizing pts with
  | nil =>
    simp only [procTerms, Option.some.injEq] at h
    subst h
    simp [intEval]
  | cons t rest ih =>
    obtain ⟨v, c⟩ := t
    simp only [procTerms] at h
    cases hb : bnd v with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some B =>
      cases hr : procTerms bnd rest with
      | none => simp only [hb, hr] at h; exact absurd h (by simp)
      | some pts' =>
        simp only [hb, hr, Option.some.injEq] at h
        subst h
        have hstep : intEval env (⟨srep c, B, v⟩ :: pts')
            = srep c * ((env v).val : Int) + intEval env pts' := by
          simp [intEval]
        rw [hstep, Int.cast_add, Int.cast_mul, Int.cast_natCast, srep_cast,
          ZMod.natCast_val, ZMod.cast_id, ih pts' hr, List.map_cons, List.sum_cons]

theorem procTerms_bounds (bnd : Variable → Option Nat)
    (terms : List (Variable × ZMod p)) (pts : List PTerm)
    (h : procTerms bnd terms = some pts) (env : Variable → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (env v).val < b) :
    ∀ t ∈ pts, ((env t.v).val : Int) < (t.bnd : Int) := by
  induction terms generalizing pts with
  | nil =>
    simp only [procTerms, Option.some.injEq] at h
    subst h
    intro t ht
    exact absurd ht (by simp)
  | cons t0 rest ih =>
    obtain ⟨v, c⟩ := t0
    simp only [procTerms] at h
    cases hb : bnd v with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some B =>
      cases hr : procTerms bnd rest with
      | none => simp only [hb, hr] at h; exact absurd h (by simp)
      | some pts' =>
        simp only [hb, hr, Option.some.injEq] at h
        subst h
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact_mod_cast hbnd v B hb
        · exact ih pts' hr t ht'

/-- Per-term window: `0 ≤ d < B` confines `sc·d` between `min (sc·(B−1)) 0` and
    `max (sc·(B−1)) 0`. -/
theorem term_window (sc d B : Int) (h0 : 0 ≤ d) (hd : d < B) :
    min (sc * (B - 1)) 0 ≤ sc * d ∧ sc * d ≤ max (sc * (B - 1)) 0 := by
  rcases le_or_gt 0 sc with hsc | hsc
  · exact ⟨le_trans (min_le_right _ _) (mul_nonneg hsc h0),
      le_trans (mul_le_mul_of_nonneg_left (by omega) hsc) (le_max_left _ _)⟩
  · refine ⟨le_trans (min_le_left _ _)
      (mul_le_mul_of_nonpos_left (by omega) (le_of_lt hsc)), ?_⟩
    have h1 : sc * d ≤ sc * 0 := mul_le_mul_of_nonpos_left h0 (le_of_lt hsc)
    rw [mul_zero] at h1
    exact le_trans h1 (le_max_right _ _)

theorem intEval_window (env : Variable → ZMod p) (pts : List PTerm)
    (hb : ∀ t ∈ pts, ((env t.v).val : Int) < (t.bnd : Int)) :
    minSum pts ≤ intEval env pts ∧ intEval env pts ≤ maxSum pts := by
  induction pts with
  | nil => simp [intEval, minSum, maxSum]
  | cons t rest ih =>
    have hrest := ih (fun t' ht' => hb t' (List.mem_cons_of_mem _ ht'))
    have ht := term_window t.sc ((env t.v).val : Int) (t.bnd : Int)
      (Int.natCast_nonneg _) (hb t (List.mem_cons_self ..))
    simp only [intEval, minSum, maxSum, List.map_cons, List.sum_cons] at *
    omega

/-! ## The integer window argument -/

/-- If the signed-representative integer value `S` reduces to a field element `x` with
    `x.val < B`, and the window `[lo, hi] ∋ S` satisfies `hi ≤ p − 1` and `lo ≥ B − p`, then
    `S = x.val` holds over ℤ — in particular `0 ≤ S < B`. -/
theorem int_window [NeZero p] (S : Int) (B : Nat) (x : ZMod p)
    (hcast : ((S : Int) : ZMod p) = x) (hx : x.val < B)
    (hlo : (B : Int) - (p : Int) ≤ S) (hhi : S ≤ (p : Int) - 1) : S = (x.val : Int) := by
  have hdvd : (p : Int) ∣ (S - (x.val : Int)) := by
    have hz : ((S - (x.val : Int) : Int) : ZMod p) = 0 := by
      push_cast
      rw [hcast, ZMod.natCast_val, ZMod.cast_id, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  obtain ⟨k, hk⟩ := hdvd
  have hxv : (0 : Int) ≤ (x.val : Int) := Int.natCast_nonneg _
  have hxvB : ((x.val : Int)) < (B : Int) := by exact_mod_cast hx
  have hp : (0 : Int) < (p : Int) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  -- `S − x.val = p·k` with `S − x.val ∈ (−p, p)` forces `k = 0`.
  rcases lt_trichotomy k 0 with hkn | rfl | hkp
  · exfalso
    have h2 : (p : Int) * k ≤ (p : Int) * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp)
    rw [mul_neg_one] at h2
    generalize hX : (p : Int) * k = X at hk h2
    omega
  · omega
  · exfalso
    have h2 : (p : Int) * 1 ≤ (p : Int) * k :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp)
    rw [mul_one] at h2
    generalize hX : (p : Int) * k = X at hk h2
    omega

/-! ## Seed extraction -/

/-- `v − w` as an expression (`v + (−1)·w`). -/
def pairDiff (v w : Variable) : Expression p :=
  Expression.add (Expression.var v) (Expression.mul (Expression.const (-1)) (Expression.var w))

theorem pairDiff_eval (v w : Variable) (env : Variable → ZMod p) :
    (pairDiff v w).eval env = env v - env w := by
  simp only [pairDiff, Expression.eval]; ring

/-- First term with signed coefficient `g`, and the list without it. -/
def findPartner (g : Int) : List PTerm → Option (PTerm × List PTerm)
  | [] => none
  | t :: rest =>
    if t.sc = g then some (t, rest)
    else
      match findPartner g rest with
      | some (t', rest') => some (t', t :: rest')
      | none => none

theorem findPartner_spec (g : Int) :
    ∀ (pts : List PTerm) (t : PTerm) (rest : List PTerm),
      findPartner g pts = some (t, rest) → t.sc = g ∧ pts.Perm (t :: rest) := by
  intro pts
  induction pts with
  | nil => intro t rest h; exact absurd h (by simp [findPartner])
  | cons t0 rest0 ih =>
    intro t rest h
    unfold findPartner at h
    split_ifs at h with hsc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hsc, List.Perm.refl _⟩
    · cases hr : findPartner g rest0 with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some tr =>
        obtain ⟨t', rest'⟩ := tr
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hg, hperm⟩ := ih t' rest' hr
        exact ⟨hg, (hperm.cons t0).trans (List.Perm.swap t' t0 rest')⟩

/-- The walk over the term list: at each term, try the zero arm (against all other terms) and,
    for a positive coefficient, the pair arm against the first `−g` partner among the other
    terms. `seen` accumulates the already-visited terms so partners behind the cursor are
    found. -/
def walk (B : Nat) (c0 : Int) : List PTerm → List PTerm → List (Expression p)
  | _, [] => []
  | seen, t :: rest =>
    (if (0 < t.sc ∧ (B : Int) ≤ t.sc + (c0 + minSum (seen ++ rest))) ∨
        (t.sc < 0 ∧ c0 + maxSum (seen ++ rest) + t.sc < 0) then
      [Expression.var t.v]
    else []) ++
    (if 0 < t.sc then
      match findPartner (-t.sc) (seen ++ rest) with
      | some (t', others') =>
        if (B : Int) ≤ t.sc + (c0 + minSum others') ∧
           c0 + maxSum others' - t.sc < 0 ∧ t.v ≠ t'.v then
          [pairDiff t.v t'.v]
        else []
      | none => []
    else []) ++
    walk B c0 (t :: seen) rest

theorem intEval_perm (env : Variable → ZMod p) {l1 l2 : List PTerm} (h : l1.Perm l2) :
    intEval env l1 = intEval env l2 :=
  List.Perm.sum_eq (List.Perm.map _ h)

theorem walk_sound [NeZero p] (B : Nat) (c0 : Int) (env : Variable → ZMod p)
    (pts0 : List PTerm)
    (hbnds : ∀ t ∈ pts0, ((env t.v).val : Int) < (t.bnd : Int))
    (hS0 : 0 ≤ c0 + intEval env pts0) (hSB : c0 + intEval env pts0 < (B : Int)) :
    ∀ (seen cur : List PTerm), (seen ++ cur).Perm pts0 →
      ∀ e ∈ walk B c0 seen cur, e.eval env = 0 := by
  intro seen cur
  induction cur generalizing seen with
  | nil => intro _ e he; exact absurd he (by simp [walk])
  | cons t rest ih =>
    intro hperm e he
    -- `pts0 ~ t :: others` with `others = seen ++ rest`
    have hperm' : (t :: (seen ++ rest)).Perm pts0 :=
      (List.perm_middle (a := t) (l₁ := seen) (l₂ := rest)).symm.trans hperm
    have hsplit : intEval env pts0
        = t.sc * ((env t.v).val : Int) + intEval env (seen ++ rest) := by
      rw [← intEval_perm env hperm']
      simp [intEval]
    have hbnds' : ∀ t' ∈ seen ++ rest, ((env t'.v).val : Int) < (t'.bnd : Int) := fun t' ht' =>
      hbnds t' (hperm'.subset (List.mem_cons_of_mem _ ht'))
    have hbt : ((env t.v).val : Int) < (t.bnd : Int) :=
      hbnds t (hperm'.subset (List.mem_cons_self ..))
    have hwother := intEval_window env (seen ++ rest) hbnds'
    unfold walk at he
    simp only [List.mem_append] at he
    rcases he with (hz | hp) | hrec
    · -- zero arm
      split_ifs at hz with hcond
      swap
      · exact absurd hz (by simp)
      rw [List.mem_singleton] at hz
      subst hz
      show env t.v = 0
      rw [← ZMod.val_eq_zero]
      by_contra hne
      have hd1 : (1 : Int) ≤ ((env t.v).val : Int) := by
        have h1 : 1 ≤ (env t.v).val := Nat.one_le_iff_ne_zero.mpr hne
        exact_mod_cast h1
      rcases hcond with ⟨hsc, hcnd⟩ | ⟨hsc, hcnd⟩
      · -- positive coefficient: S ≥ sc + c0 + minSum ≥ B
        have hscd : t.sc ≤ t.sc * ((env t.v).val : Int) :=
          le_mul_of_one_le_right (le_of_lt hsc) hd1
        generalize hX : t.sc * ((env t.v).val : Int) = X at hsplit hscd
        omega
      · -- negative coefficient: S ≤ sc + c0 + maxSum < 0
        have hscd : t.sc * ((env t.v).val : Int) ≤ t.sc := by
          have h1 : t.sc * ((env t.v).val : Int) ≤ t.sc * 1 :=
            mul_le_mul_of_nonpos_left hd1 (le_of_lt hsc)
          rwa [mul_one] at h1
        generalize hX : t.sc * ((env t.v).val : Int) = X at hsplit hscd
        omega
    · -- pair arm
      split_ifs at hp with hsc
      swap
      · exact absurd hp (by simp)
      cases hfp : findPartner (-t.sc) (seen ++ rest) with
      | none => simp only [hfp] at hp; exact absurd hp (by simp)
      | some tr =>
        obtain ⟨t', others'⟩ := tr
        simp only [hfp] at hp
        split_ifs at hp with hcond
        swap
        · exact absurd hp (by simp)
        rw [List.mem_singleton] at hp
        subst hp
        obtain ⟨hc1, hc2, _hne⟩ := hcond
        obtain ⟨hg, hpp⟩ := findPartner_spec (-t.sc) (seen ++ rest) t' others' hfp
        have hsplit2 : intEval env (seen ++ rest)
            = t'.sc * ((env t'.v).val : Int) + intEval env others' := by
          rw [intEval_perm env hpp]
          simp [intEval]
        have hbnds'' : ∀ u ∈ others', ((env u.v).val : Int) < (u.bnd : Int) := fun u hu =>
          hbnds' u (hpp.symm.subset (List.mem_cons_of_mem _ hu))
        have hwother' := intEval_window env others' hbnds''
        have hcomb : intEval env pts0
            = t.sc * (((env t.v).val : Int) - ((env t'.v).val : Int)) + intEval env others' := by
          rw [hsplit, hsplit2, hg]
          ring
        show (pairDiff t.v t'.v).eval env = 0
        rw [pairDiff_eval]
        have hveq : (env t.v).val = (env t'.v).val := by
          by_contra hnev
          rcases Nat.lt_or_ge (env t.v).val (env t'.v).val with hlt | hge
          · -- dj < dk: S ≤ c0 − g + maxSum others' < 0
            have hdlt : ((env t.v).val : Int) - ((env t'.v).val : Int) ≤ -1 := by
              have h1 : (env t.v).val + 1 ≤ (env t'.v).val := hlt
              have h2 : ((env t.v).val : Int) + 1 ≤ ((env t'.v).val : Int) := by exact_mod_cast h1
              omega
            have hXle : t.sc * (((env t.v).val : Int) - ((env t'.v).val : Int)) ≤ -t.sc := by
              have h1 : t.sc * (((env t.v).val : Int) - ((env t'.v).val : Int)) ≤ t.sc * (-1) :=
                mul_le_mul_of_nonneg_left hdlt (le_of_lt hsc)
              rwa [mul_neg_one] at h1
            generalize hX : t.sc * (((env t.v).val : Int) - ((env t'.v).val : Int)) = X
              at hcomb hXle
            omega
          · -- dj > dk: S ≥ c0 + g + minSum others' ≥ B
            have hdgt : (1 : Int) ≤ ((env t.v).val : Int) - ((env t'.v).val : Int) := by
              have h1 : (env t'.v).val + 1 ≤ (env t.v).val := by omega
              have h2 : ((env t'.v).val : Int) + 1 ≤ ((env t.v).val : Int) := by exact_mod_cast h1
              omega
            have hXge : t.sc ≤ t.sc * (((env t.v).val : Int) - ((env t'.v).val : Int)) :=
              le_mul_of_one_le_right (le_of_lt hsc) hdgt
            generalize hX : t.sc * (((env t.v).val : Int) - ((env t'.v).val : Int)) = X
              at hcomb hXge
            omega
        rw [show env t.v = env t'.v from ZMod.val_injective p hveq, sub_self]
    · -- recursive call: `(t :: seen) ++ rest = t :: (seen ++ rest) ~ pts0`
      exact ih (t :: seen) (by simpa using hperm') e hrec

/-! ## Per-slot seeds -/

/-- Cap on the number of affine terms analyzed per slot (the walk is quadratic). -/
def maxTerms : Nat := 32

/-- All seeds forced by one bounded slot: linearize, merge like terms, pair each variable with
    its proven bound, check the integer window, and extract the pair/zero arms. -/
def slotSeeds (bnd : Variable → Option Nat) (B : Nat) (e : Expression p) :
    List (Expression p) :=
  if p = 0 then []
  else
    match linearize e with
    | none => []
    | some l =>
      if l.norm.terms.length ≤ maxTerms then
        match procTerms bnd l.norm.terms with
        | none => []
        | some pts =>
          if srep l.norm.const + maxSum pts ≤ (p : Int) - 1 ∧
             (B : Int) - (p : Int) ≤ srep l.norm.const + minSum pts then
            walk B (srep l.norm.const) [] pts
          else []
      else []

theorem slotSeeds_sound (bnd : Variable → Option Nat) (B : Nat) (e : Expression p)
    (env : Variable → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (env v).val < b)
    (hB : (e.eval env).val < B) :
    ∀ s ∈ slotSeeds bnd B e, s.eval env = 0 := by
  intro s hs
  unfold slotSeeds at hs
  split_ifs at hs with hp0
  · exact absurd hs (by simp)
  haveI : NeZero p := ⟨hp0⟩
  cases hl : linearize e with
  | none => simp only [hl] at hs; exact absurd hs (by simp)
  | some l =>
    simp only [hl] at hs
    split_ifs at hs with hlen
    swap
    · exact absurd hs (by simp)
    cases hpt : procTerms bnd l.norm.terms with
    | none => simp only [hpt] at hs; exact absurd hs (by simp)
    | some pts =>
      simp only [hpt] at hs
      split_ifs at hs with hwin
      swap
      · exact absurd hs (by simp)
      obtain ⟨hhi, hlo⟩ := hwin
      have hbnds : ∀ t ∈ pts, ((env t.v).val : Int) < (t.bnd : Int) :=
        procTerms_bounds bnd l.norm.terms pts hpt env hbnd
      have hcast : (((srep l.norm.const + intEval env pts : Int)) : ZMod p) = e.eval env := by
        push_cast
        rw [srep_cast, procTerms_cast bnd l.norm.terms pts hpt env,
          linearize_eval e l hl env, ← LinExpr.norm_eval]
        rfl
      have hwindow := intEval_window env pts hbnds
      have hS := int_window (srep l.norm.const + intEval env pts) B (e.eval env) hcast hB
        (by omega) (by omega)
      have hSB : srep l.norm.const + intEval env pts < (B : Int) := by
        rw [hS]
        exact_mod_cast hB
      have hS0 : 0 ≤ srep l.norm.const + intEval env pts := by
        rw [hS]
        exact Int.natCast_nonneg _
      exact walk_sound B (srep l.norm.const) env pts hbnds hS0 hSB [] pts (by simp) s hs

/-! ## The per-invocation bounds index

`findVarBound` scans the interaction list per queried variable; this pass queries every variable
of every affine slot, so it builds the variable→bound map once per invocation (the proof-carrying
`VarCsIdx` pattern: each recorded bound is witnessed by a member interaction). -/

structure BoundIdx (p : ℕ) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) where
  map : Std.HashMap Variable Nat
  sound : ∀ (x : Variable) (B : Nat), map[x]? = some B →
    ∃ bi ∈ bis, interactionBound bs facts bi x = some B

namespace BoundIdx

variable {bs : BusSemantics p} {facts : BusFacts p bs}
variable {bis : List (BusInteraction (Expression p))}

def empty : BoundIdx p bs facts bis where
  map := ∅
  sound := by
    intro x B h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)

/-- Record the bound `interactionBound bi x` (if any), keeping the smaller of duplicates. -/
def insertVar (I : BoundIdx p bs facts bis) (bi : BusInteraction (Expression p))
    (hbi : bi ∈ bis) (x : Variable) : BoundIdx p bs facts bis :=
  match hb : interactionBound bs facts bi x with
  | none => I
  | some B =>
    if (match I.map[x]? with
        | some old => decide (B < old)
        | none => true) then
      { map := I.map.insert x B,
        sound := by
          intro y B' h
          rw [Std.HashMap.getElem?_insert] at h
          by_cases hxy : (x == y) = true
          · rw [if_pos hxy] at h
            simp only [Option.some.injEq] at h
            have hxy' : x = y := by simpa using hxy
            subst hxy'
            exact ⟨bi, hbi, h ▸ hb⟩
          · rw [if_neg hxy] at h
            exact I.sound y B' h }
    else I

/-- Record every bare-variable slot bound of one interaction. -/
def addBi (I : BoundIdx p bs facts bis) (bi : BusInteraction (Expression p))
    (hbi : bi ∈ bis) : BoundIdx p bs facts bis :=
  (bi.payload.filterMap (fun e =>
    match e with
    | .var x => some x
    | _ => none)).foldl (fun I x => I.insertVar bi hbi x) I

def addAll : BoundIdx p bs facts bis → (rest : List (BusInteraction (Expression p))) →
    (∀ bi ∈ rest, bi ∈ bis) → BoundIdx p bs facts bis
  | I, [], _ => I
  | I, bi :: rest, hmem =>
    addAll (I.addBi bi (hmem bi (List.mem_cons_self ..))) rest
      (fun bi' h => hmem bi' (List.mem_cons_of_mem _ h))

def build (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (Expression p))) : BoundIdx p bs facts bis :=
  addAll empty bis (fun _ h => h)

/-- The bound lookup is sound on any assignment where every interaction's obligation holds. -/
theorem lookup_sound (I : BoundIdx p bs facts bis) (env : Variable → ZMod p)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    ∀ v B, I.map[v]? = some B → (env v).val < B := by
  intro v B h
  obtain ⟨bi, hbi, hib⟩ := I.sound v B h
  exact interactionBound_sound bs facts bi v B hib env (hbus bi hbi)

end BoundIdx

/-! ## The pass -/

/-- All seeds of one interaction: every payload slot with a `slotBound`. -/
def interactionSeeds {bs : BusSemantics p} (facts : BusFacts p bs)
    (bnd : Variable → Option Nat) (bi : BusInteraction (Expression p)) :
    List (Expression p) :=
  match bi.multiplicity.constValue? with
  | none => []
  | some mval =>
    if mval = 0 then []
    else
      (List.range bi.payload.length).flatMap (fun i =>
        match bi.payload[i]?,
              facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) i with
        | some e, some B => slotSeeds bnd B e
        | _, _ => [])

theorem interactionSeeds_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bnd : Variable → Option Nat) (bi : BusInteraction (Expression p))
    (env : Variable → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (env v).val < b)
    (hviol : (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) :
    ∀ s ∈ interactionSeeds facts bnd bi, s.eval env = 0 := by
  intro s hs
  unfold interactionSeeds at hs
  cases hmc : bi.multiplicity.constValue? with
  | none => simp only [hmc] at hs; exact absurd hs (by simp)
  | some mval =>
    simp only [hmc] at hs
    by_cases hmz : mval = 0
    · rw [if_pos hmz] at hs
      exact absurd hs (by simp)
    rw [if_neg hmz] at hs
    rw [List.mem_flatMap] at hs
    obtain ⟨i, _, hsi⟩ := hs
    cases hpe : bi.payload[i]? with
    | none => simp only [hpe] at hsi; exact absurd hsi (by simp)
    | some e =>
      cases hsb : facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) i with
      | none => simp only [hpe, hsb] at hsi; exact absurd hsi (by simp)
      | some B =>
        simp only [hpe, hsb] at hsi
        -- the interaction is active at the constant multiplicity, hence accepted
        have hmeval : (bi.eval env).multiplicity = mval :=
          bi.multiplicity.constValue?_sound mval hmc env
        have hv : bs.violatesConstraint (bi.eval env) = false := by
          apply hviol
          rw [hmeval]
          exact hmz
        have hget : (bi.eval env).payload[i]? = some (e.eval env) := by
          show (bi.payload.map (fun t => t.eval env))[i]? = some (e.eval env)
          rw [List.getElem?_map, hpe]
          rfl
        have hsb' : facts.slotBound (bi.eval env).busId (bi.eval env).multiplicity
            (bi.payload.map Expression.constValue?) i = some B := by
          show facts.slotBound bi.busId (bi.eval env).multiplicity _ i = some B
          rw [hmeval]
          exact hsb
        have hbound : (e.eval env).val < B :=
          facts.slotBound_sound (bi.eval env) (bi.payload.map Expression.constValue?) i B
            (e.eval env) hsb' (matches_evalPattern bi.payload env) hv hget
        exact slotSeeds_sound bnd B e env hbnd hbound s hsi

/-- All seeds over the system: every bounded interaction slot, plus every algebraic constraint
    consumed as a bound-`1` slot (an equality pins the integer window to `{0}`). -/
def allSeeds {bs : BusSemantics p} (facts : BusFacts p bs) (bnd : Variable → Option Nat)
    (cs : ConstraintSystem p) : List (Expression p) :=
  (cs.busInteractions.flatMap (interactionSeeds facts bnd) ++
    cs.algebraicConstraints.flatMap (fun c => slotSeeds bnd 1 c)).eraseDups

theorem allSeeds_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bnd : Variable → Option Nat) (cs : ConstraintSystem p) (env : Variable → ZMod p)
    (hbnd : ∀ v b, bnd v = some b → (env v).val < b)
    (hsat : cs.satisfies bs env) :
    ∀ s ∈ allSeeds facts bnd cs, s.eval env = 0 := by
  intro s hs
  unfold allSeeds at hs
  rcases List.mem_append.1 (List.mem_eraseDups.1 hs) with h | h
  · obtain ⟨bi, hbi, hsi⟩ := List.mem_flatMap.1 h
    exact interactionSeeds_sound facts bnd bi env hbnd (hsat.2 bi hbi) s hsi
  · obtain ⟨c, hc, hsi⟩ := List.mem_flatMap.1 h
    by_cases hp0 : p = 0
    · exfalso
      unfold slotSeeds at hsi
      rw [if_pos hp0] at hsi
      exact absurd hsi (by simp)
    · haveI : NeZero p := ⟨hp0⟩
      have hc0 : (c.eval env).val < 1 := by
        rw [hsat.1 c hc, ZMod.val_zero]
        omega
      exact slotSeeds_sound bnd 1 c env hbnd hc0 s hsi

/-- The pass: seed every equality/zero forced by the integer-window analysis of the system's
    bounded affine slots (and its constraints); Gauss consumes the seeds in the same cleanup
    cycle. -/
def intervalForcePass : VerifiedPassW p := fun cs bs facts =>
  let idx := BoundIdx.build bs facts cs.busInteractions
  let seeds := allSeeds facts (fun v => idx.map[v]?) cs
  let new := (seeds.filter (fun e => e.vars.all (fun z => cs.vars.contains z))).filter
    (fun e => !cs.algebraicConstraints.contains e)
  if new.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
  else
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
     cs.addConstraints_correct bs new
       (fun env _ hsat e he =>
         allSeeds_sound facts (fun v => idx.map[v]?) cs env
           (fun v b hb => idx.lookup_sound env (fun bi hbi => hsat.2 bi hbi) v b hb)
           hsat e (List.mem_of_mem_filter (List.mem_of_mem_filter he)))
       (fun e he z hz => by
         have hp := (List.mem_filter.1 (List.mem_of_mem_filter he)).2
         simp only [List.all_eq_true] at hp
         exact List.contains_iff_mem.mp (hp z hz))⟩

end IntervalForce
