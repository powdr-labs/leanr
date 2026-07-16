import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.Reencode

set_option autoImplicit false

/-! # Range re-split: re-encode a two-limb range decomposition at the byte boundary

A value `D < 2^(a+b)` proven by two solo variable-range checks `[x, a]`, `[y, b]` — with `x`, `y`
occurring elsewhere **only** through the composed linear form `x + 2^a·y` — is re-encoded with
fresh limbs split at the byte boundary: `b' = D mod 256` (a byte, packable at density two by the
byte-check packers) and `h' = D / 256` (one solo check of width `a + b − 8`). Both encodings are
*bijective* digit decompositions of the same interval `[0, 2^(a+b))`, so the transformation is a
refinement in both directions; the fresh limbs are derived columns computed by the
`ComputationMethod.floorMod` / `.floorDiv` digit extractors.

The measured target is the OpenVM timestamp-lt decomposition (`(17, 12)` on the eth corpus):
its two full-width solo checks become one width-21 check plus one byte obligation, and the byte
packers then pair the bytes two-per-interaction — about −0.5 bus interactions per boundary
memory address, variable-neutral.

Key facts making the proof clean:

* The digit-reconstruction identity `n % d + d·(n / d) = n` means the two encodings determine
  each other *unconditionally* — the env mappings below satisfy the coherence equation
  `x + 2^a·y = b' + 256·h'` on the nose, with no range assumptions; range bounds are needed
  exactly where the checks bind (multiplicity ≠ 0), and both check families carry the same
  multiplicity expression.
* Replaced interactions swap in place (`cx ↦ newB`, `cy ↦ newH`), and all four touched
  interactions live on the same *stateless* bus, so the stateful message lists — side effects
  and the `admissible` argument — are untouched positionally.
* Soundness of adding the two fresh checks' messages uses the `varRangeBusInv_sound` fact:
  on a variable-range bus, invariant breaking depends only on the multiplicity, which the fresh
  checks inherit from the replaced ones. -/

variable {p : ℕ}

namespace RangeResplit

/-- Does the expression avoid variable `v`? (Complement of `Expression.mentions`.) -/
theorem not_mem_vars_of_mentions_false {v : Variable} {e : Expression p}
    (h : e.mentions v = false) : v ∉ e.vars := by
  induction e with
  | const c => simp [Expression.vars]
  | var y =>
      simp only [Expression.mentions, beq_eq_false_iff_ne, ne_eq] at h
      simp only [Expression.vars, List.mem_singleton]
      exact fun hy => h (hy ▸ rfl)
  | add a b iha ihb =>
      simp only [Expression.mentions, Bool.or_eq_false_iff] at h
      simp only [Expression.vars, List.mem_append]
      rintro (hv | hv)
      · exact iha h.1 hv
      · exact ihb h.2 hv
  | mul a b iha ihb =>
      simp only [Expression.mentions, Bool.or_eq_false_iff] at h
      simp only [Expression.vars, List.mem_append]
      rintro (hv | hv)
      · exact iha h.1 hv
      · exact ihb h.2 hv

/-- Variables of a substituted expression: each comes from the original or from an inserted
    solution. -/
theorem substF_vars {f : Variable → Option (Expression p)} {e : Expression p} {v : Variable}
    (hv : v ∈ (e.substF f).vars) : v ∈ e.vars ∨ ∃ u t, f u = some t ∧ v ∈ t.vars := by
  induction e with
  | const c => simp [Expression.substF, Expression.vars] at hv
  | var y =>
      simp only [Expression.substF] at hv
      cases hy : f y with
      | none =>
          rw [hy] at hv
          exact Or.inl hv
      | some t =>
          rw [hy] at hv
          exact Or.inr ⟨y, t, hy, hv⟩
  | add a b iha ihb =>
      simp only [Expression.substF, Expression.vars, List.mem_append] at hv ⊢
      rcases hv with hv | hv
      · rcases iha hv with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihb hv with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | mul a b iha ihb =>
      simp only [Expression.substF, Expression.vars, List.mem_append] at hv ⊢
      rcases hv with hv | hv
      · rcases iha hv with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihb hv with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

/-- `Derivations.methodFor` over an append: entries of the second list win (they are later). -/
theorem methodFor_append (l1 l2 : Derivations p) (v : Variable) :
    Derivations.methodFor (l1 ++ l2) v
      = (Derivations.methodFor l2 v).orElse (fun _ => Derivations.methodFor l1 v) := by
  induction l1 with
  | nil =>
      simp only [List.nil_append]
      cases h : Derivations.methodFor l2 v with
      | none => simp [Option.orElse, Derivations.methodFor]
      | some cm => simp [Option.orElse]
  | cons hd tl ih =>
      obtain ⟨u, cm⟩ := hd
      simp only [List.cons_append, Derivations.methodFor, ih]
      cases h2 : Derivations.methodFor l2 v with
      | none => simp [Option.orElse]
      | some cm2 => simp [Option.orElse]

/-! ## The pair data and the transformed system -/

/-- A candidate re-split: the two bare-variable range checks `cx = [x, wxc]`, `cy = [y, wyc]`
    (on the same variable-range bus, same multiplicity), and the fresh limbs `b`, `h`. -/
structure Pair (p : ℕ) where
  cx : BusInteraction (Expression p)
  cy : BusInteraction (Expression p)
  x : Variable
  y : Variable
  wxc : ZMod p
  wyc : ZMod p
  b : Variable
  h : Variable

/-- Low width (bits) of the original split. -/
def Pair.wxv (P : Pair p) : Nat := P.wxc.val
/-- High width (bits) of the original split. -/
def Pair.wyv (P : Pair p) : Nat := P.wyc.val
/-- Width (bits) of the fresh high limb: total minus the byte. -/
def Pair.wW (P : Pair p) : Nat := P.wxv + P.wyv - 8

/-- `2^wxv` as a field constant. -/
def Pair.c2wx (P : Pair p) : ZMod p := ((2 ^ P.wxv : ℕ) : ZMod p)
/-- `256` as a field constant. -/
def c256 : ZMod p := ((256 : ℕ) : ZMod p)
/-- `8` as a field constant. -/
def c8 : ZMod p := ((8 : ℕ) : ZMod p)
/-- The fresh high limb's width as a field constant. -/
def Pair.cW (P : Pair p) : ZMod p := ((P.wW : ℕ) : ZMod p)

/-- The composed value `x + 2^wxv·y` as an expression (reads the two original limbs). -/
def Pair.composed (P : Pair p) : Expression p :=
  .add (.var P.x) (.mul (.const P.c2wx) (.var P.y))

/-- The substitution `x ↦ b + 256·h − 2^wxv·y`; under the coherence equation this is exactly
    `x`'s value, and the `y`-term cancels the composed form's own `2^wxv·y`. -/
def Pair.sigma (P : Pair p) : Variable → Option (Expression p) := fun v =>
  if v = P.x then
    some (.add (.add (.var P.b) (.mul (.const c256) (.var P.h)))
               (.mul (.const (-P.c2wx)) (.var P.y)))
  else none

/-- Rewrite an expression: substitute `x` (then normalize, cancelling `y`); expressions not
    mentioning `x` are returned untouched (syntactically identical). -/
def Pair.rewriteE (P : Pair p) (e : Expression p) : Expression p :=
  if e.mentions P.x then (e.substF P.sigma).normalize else e

/-- Rewrite an interaction's expressions. -/
def Pair.rewriteBI (P : Pair p) (bi : BusInteraction (Expression p)) :
    BusInteraction (Expression p) :=
  { busId := bi.busId,
    multiplicity := P.rewriteE bi.multiplicity,
    payload := bi.payload.map P.rewriteE }

/-- The fresh byte check `[b, 8]`, multiplicity inherited from `cx`. -/
def Pair.newB (P : Pair p) : BusInteraction (Expression p) :=
  { busId := P.cx.busId, multiplicity := P.cx.multiplicity,
    payload := [.var P.b, .const c8] }

/-- The fresh high check `[h, wxv+wyv−8]`, multiplicity inherited from `cx`. -/
def Pair.newH (P : Pair p) : BusInteraction (Expression p) :=
  { busId := P.cx.busId, multiplicity := P.cx.multiplicity,
    payload := [.var P.h, .const P.cW] }

/-- Map one interaction of the input system: the two original checks swap in place for the
    fresh ones; everything else is rewritten. -/
def Pair.mapBI (P : Pair p) (bi : BusInteraction (Expression p)) :
    BusInteraction (Expression p) :=
  if bi = P.cx then P.newB else if bi = P.cy then P.newH else P.rewriteBI bi

/-- The transformed system. -/
def Pair.outOf (P : Pair p) (cs : ConstraintSystem p) : ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints.map P.rewriteE,
    busInteractions := cs.busInteractions.map P.mapBI }

/-- The derivations for the fresh limbs: digit extractors on the composed value. -/
def Pair.derivs (P : Pair p) : Derivations p :=
  [(P.b, .floorMod P.composed 256), (P.h, .floorDiv P.composed 256)]

/-- No expression of the system mentions `v`. -/
def systemAvoids (cs : ConstraintSystem p) (v : Variable) : Bool :=
  cs.algebraicConstraints.all (fun c => !c.mentions v) &&
  cs.busInteractions.all (fun bi =>
    !bi.multiplicity.mentions v && bi.payload.all (fun e => !e.mentions v))

/-! ## Validity -/

/-- The full validity check for a candidate pair against the current system. All conjuncts are
    decidable; the pass only fires when this returns `true`, and the correctness proof consumes
    the conjuncts. -/
def Pair.valid {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (P : Pair p) : Bool :=
  -- shape
  facts.varRangeBus P.cx.busId &&
  decide (P.cy.busId = P.cx.busId) &&
  decide (P.cx ∈ cs.busInteractions) &&
  decide (P.cy ∈ cs.busInteractions) &&
  decide (P.cx ≠ P.cy) &&
  decide (P.cx.payload = [.var P.x, .const P.wxc]) &&
  decide (P.cy.payload = [.var P.y, .const P.wyc]) &&
  decide (P.x ≠ P.y) &&
  P.x.powdrId?.isSome && P.y.powdrId?.isSome &&
  decide (P.cx.multiplicity = P.cy.multiplicity) &&
  decide (P.cx.multiplicity.mentions P.x = false) &&
  decide (P.cx.multiplicity.mentions P.y = false) &&
  -- widths
  decide (1 ≤ P.wxv) && decide (P.wxv ≤ 25) && decide (1 ≤ P.wyv) && decide (P.wyv ≤ 25) &&
  decide (9 ≤ P.wxv + P.wyv) && decide (P.wxv + P.wyv - 8 ≤ 25) &&
  decide (2 ^ (P.wxv + P.wyv) < p) && decide (P.wxv ≠ 8) &&
  -- freshness
  decide (P.b ∉ cs.vars) && decide (P.h ∉ cs.vars) && decide (P.b ≠ P.h) &&
  P.b.powdrId?.isNone && P.h.powdrId?.isNone &&
  -- the rewrite eliminated both original limbs everywhere
  systemAvoids (P.outOf cs) P.x && systemAvoids (P.outOf cs) P.y

variable {bs : BusSemantics p}

/-! ## Core evaluation lemmas -/

/-- The coherence equation between the two encodings under an environment. -/
def Pair.coh (P : Pair p) (env : Variable → ZMod p) : Prop :=
  env P.x + P.c2wx * env P.y = env P.b + c256 * env P.h

/-- Under coherence, a rewritten expression evaluates like the original. -/
theorem Pair.rewriteE_eval (P : Pair p) (e : Expression p) (env : Variable → ZMod p)
    (hco : P.coh env) : (P.rewriteE e).eval env = e.eval env := by
  unfold Pair.rewriteE
  split
  · rw [Expression.normalize_eval, Expression.eval_substF, envF_eq_self]
    intro v t hv
    unfold Pair.sigma at hv
    split at hv
    · next hvx =>
        injection hv with h
        subst h
        subst hvx
        simp only [Expression.eval]
        unfold Pair.coh at hco
        linear_combination hco
    · exact absurd hv (by simp)
  · rfl

/-- Under coherence, a rewritten interaction evaluates like the original. -/
theorem Pair.rewriteBI_eval (P : Pair p) (bi : BusInteraction (Expression p))
    (env : Variable → ZMod p) (hco : P.coh env) : (P.rewriteBI bi).eval env = bi.eval env := by
  unfold Pair.rewriteBI BusInteraction.eval
  simp only [List.map_map]
  refine congrArg₂ (fun m pl => BusInteraction.mk bi.busId m pl) ?_ ?_
  · exact P.rewriteE_eval bi.multiplicity env hco
  · exact List.map_congr_left (fun e _ => P.rewriteE_eval e env hco)

/-- The digit-reconstruction identity in the field: for `2^k`-splitting any value `a`,
    `(a.val % m) + m·(a.val / m) = a` (as field elements), for any modulus constant `m`. -/
theorem digit_recon [NeZero p] (a : ZMod p) (m : ℕ) :
    ((a.val % m : ℕ) : ZMod p) + ((m : ℕ) : ZMod p) * ((a.val / m : ℕ) : ZMod p) = a := by
  rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div, ZMod.natCast_val, ZMod.cast_id]

/-! ## The two coherent environments -/

/-- Completeness witness: extend the input environment with the fresh limbs' digit values.
    Coherent for *every* input environment — no range assumptions. -/
def Pair.envC (P : Pair p) (env : Variable → ZMod p) : Variable → ZMod p := fun v =>
  if v = P.b then (((P.composed.eval env).val % 256 : ℕ) : ZMod p)
  else if v = P.h then (((P.composed.eval env).val / 256 : ℕ) : ZMod p)
  else env v

/-- Soundness witness: rebuild the original limbs' digit values from the fresh encoding.
    Coherent for *every* output environment — no range assumptions. -/
def Pair.envS (P : Pair p) (env : Variable → ZMod p) : Variable → ZMod p := fun v =>
  if v = P.x then (((env P.b + c256 * env P.h).val % 2 ^ P.wxv : ℕ) : ZMod p)
  else if v = P.y then (((env P.b + c256 * env P.h).val / 2 ^ P.wxv : ℕ) : ZMod p)
  else env v

/-- The composed value evaluates to `x + 2^wxv·y`. -/
theorem Pair.composed_eval (P : Pair p) (env : Variable → ZMod p) :
    P.composed.eval env = env P.x + P.c2wx * env P.y := by
  simp [Pair.composed, Expression.eval]

/-- The composed expression reads exactly the two original limbs. -/
theorem Pair.composed_vars (P : Pair p) : P.composed.vars = [P.x, P.y] := by
  simp [Pair.composed, Expression.vars]

theorem Pair.coh_envC [NeZero p] (P : Pair p) (env : Variable → ZMod p)
    (hbx : P.b ≠ P.x) (hby : P.b ≠ P.y) (hhx : P.h ≠ P.x) (hhy : P.h ≠ P.y) (hbh : P.b ≠ P.h) :
    P.coh (P.envC env) := by
  unfold Pair.coh Pair.envC
  rw [if_neg (Ne.symm hbx), if_neg (Ne.symm hhx), if_neg (Ne.symm hby), if_neg (Ne.symm hhy),
    if_pos rfl, if_neg (Ne.symm hbh), if_pos rfl]
  have h : (((P.composed.eval env).val % 256 : ℕ) : ZMod p)
      + c256 * (((P.composed.eval env).val / 256 : ℕ) : ZMod p) = P.composed.eval env :=
    digit_recon (P.composed.eval env) 256
  rw [P.composed_eval] at h
  exact h.symm

theorem Pair.coh_envS [NeZero p] (P : Pair p) (env : Variable → ZMod p)
    (hxy : P.x ≠ P.y) (hbx : P.b ≠ P.x) (hby : P.b ≠ P.y) (hhx : P.h ≠ P.x) (hhy : P.h ≠ P.y) :
    P.coh (P.envS env) := by
  unfold Pair.coh Pair.envS
  rw [if_pos rfl, if_neg (Ne.symm hxy), if_pos rfl, if_neg hbx, if_neg hby, if_neg hhx,
    if_neg hhy]
  exact digit_recon (env P.b + c256 * env P.h) (2 ^ P.wxv)

/-- `envC` agrees with the input environment away from the fresh limbs. -/
theorem Pair.envC_eq (P : Pair p) (env : Variable → ZMod p) {v : Variable}
    (hb : v ≠ P.b) (hh : v ≠ P.h) : P.envC env v = env v := by
  unfold Pair.envC
  rw [if_neg hb, if_neg hh]

/-- `envS` agrees with the output environment away from the original limbs. -/
theorem Pair.envS_eq (P : Pair p) (env : Variable → ZMod p) {v : Variable}
    (hx : v ≠ P.x) (hy : v ≠ P.y) : P.envS env v = env v := by
  unfold Pair.envS
  rw [if_neg hx, if_neg hy]

/-! ## List transfer lemmas (side effects and admissible message lists) -/

variable {bs : BusSemantics p}

/-- Stateful side-effect entries survive a busId-preserving map with pointwise-equal evals on
    stateful members. -/
theorem filter_se_eq (F : BusInteraction (Expression p) → BusInteraction (Expression p))
    (evA evB : Variable → ZMod p) :
    ∀ (l : List (BusInteraction (Expression p))),
      (∀ bi ∈ l, (F bi).busId = bi.busId) →
      (∀ bi ∈ l, bs.isStateful bi.busId = true → (F bi).eval evB = bi.eval evA) →
      ((l.filter (fun bi => bs.isStateful bi.busId)).map (fun bi =>
          (((bi.eval evA).busId, (bi.eval evA).payload), (bi.eval evA).multiplicity)))
        = (((l.map F).filter (fun bi => bs.isStateful bi.busId)).map (fun bi =>
          (((bi.eval evB).busId, (bi.eval evB).payload), (bi.eval evB).multiplicity)))
  | [], _, _ => rfl
  | bi :: rest, hbusid, hpt => by
      have hid : (F bi).busId = bi.busId := hbusid bi (List.mem_cons_self ..)
      have ihs := filter_se_eq F evA evB rest
        (fun b hb => hbusid b (List.mem_cons_of_mem _ hb))
        (fun b hb hs => hpt b (List.mem_cons_of_mem _ hb) hs)
      simp only [List.map_cons, List.filter_cons]
      rw [hid]
      by_cases hst : bs.isStateful bi.busId = true
      · rw [if_pos hst, if_pos hst]
        simp only [List.map_cons]
        rw [hpt bi (List.mem_cons_self ..) hst, ihs]
      · rw [if_neg hst, if_neg hst]
        exact ihs

/-- Active-stateful message lists survive the map: replaced members are stateless on both
    sides, other members evaluate equal. -/
theorem filter_msgs_eq (F : BusInteraction (Expression p) → BusInteraction (Expression p))
    (evA evB : Variable → ZMod p) :
    ∀ (l : List (BusInteraction (Expression p))),
      (∀ bi ∈ l, ((F bi).eval evB = bi.eval evA) ∨
        (bs.isStateful bi.busId = false ∧ bs.isStateful (F bi).busId = false)) →
      ((l.map (fun bi => bi.eval evA)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
        = (((l.map F).map (fun bi => bi.eval evB)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
  | [], _ => rfl
  | bi :: rest, hpt => by
      have ihs := filter_msgs_eq F evA evB rest
        (fun b hb => hpt b (List.mem_cons_of_mem _ hb))
      simp only [List.map_cons, List.filter_cons]
      rcases hpt bi (List.mem_cons_self ..) with heq | ⟨hsA, hsB⟩
      · rw [heq, ihs]
      · have hA : (bs.isStateful (bi.eval evA).busId) = false := by
          show bs.isStateful bi.busId = false
          exact hsA
        have hB : (bs.isStateful ((F bi).eval evB).busId) = false := by
          show bs.isStateful (F bi).busId = false
          exact hsB
        rw [hA, hB]
        simpa using ihs

/-- Unpack `systemAvoids` into per-site `mentions = false` facts. -/
theorem systemAvoids_spec {cs : ConstraintSystem p} {v : Variable}
    (h : systemAvoids cs v = true) :
    (∀ c ∈ cs.algebraicConstraints, c.mentions v = false) ∧
    (∀ bi ∈ cs.busInteractions, bi.multiplicity.mentions v = false ∧
      ∀ e ∈ bi.payload, e.mentions v = false) := by
  unfold systemAvoids at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun c hc => by simpa using h.1 c hc, fun bi hbi => ?_⟩
  have := h.2 bi hbi
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨by simpa using this.1, fun e he => by simpa using this.2 e he⟩

/-! ## The verified transformation for one accepted pair -/

/-- The `PassCorrect` proof for one accepted pair. -/
theorem Pair.applyPair_correct {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p) (P : Pair p) (hv : P.valid facts cs = true) :
    PassCorrect cs (P.outOf cs) P.derivs bs := by
  simp only [Pair.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hvr, hcyb⟩, hcxm⟩, hcym⟩, hcxcy⟩, hpx⟩, hpy⟩,
    hxy⟩, hxpow⟩, hypow⟩, hmeq⟩, hmx⟩, hmy⟩, hw1x⟩, hwx25⟩, hw1y⟩, hwy25⟩, hw9⟩, hwW25⟩,
    hplt⟩, hwx8⟩, hbf⟩, hhf⟩, hbh⟩, hbpow⟩, hhpow⟩, hax⟩, hay⟩ := hv
  obtain ⟨hstateless, hiff⟩ := facts.varRangeBus_sound P.cx.busId hvr
  have hinvind := facts.varRangeBusInv_sound P.cx.busId hvr
  -- arithmetic context
  have h512 : 512 < p := by
    have h29 : (512 : ℕ) ≤ 2 ^ (P.wxv + P.wyv) := by
      calc (512 : ℕ) = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ (P.wxv + P.wyv) := Nat.pow_le_pow_right (by norm_num) hw9
    omega
  haveI : NeZero p := ⟨by omega⟩
  have h2wxlt : 2 ^ P.wxv < p :=
    lt_trans (Nat.pow_lt_pow_right one_lt_two (by omega)) hplt
  have hc8val : (c8 (p := p)).val = 8 := ZMod.val_natCast_of_lt (by omega)
  have hcWval : P.cW.val = P.wW := ZMod.val_natCast_of_lt (by unfold Pair.wW; omega)
  have hsum8 : P.wW + 8 = P.wxv + P.wyv := by unfold Pair.wW; omega
  have h2sum : (2 : ℕ) ^ P.wW * 256 = 2 ^ (P.wxv + P.wyv) := by
    rw [← hsum8, pow_add]; norm_num
  -- membership and distinctness
  have hxmem : P.x ∈ cs.vars :=
    ConstraintSystem.mem_vars_of_payload hcxm (by rw [hpx]; exact List.mem_cons_self ..)
      (by simp [Expression.vars])
  have hymem : P.y ∈ cs.vars :=
    ConstraintSystem.mem_vars_of_payload hcym (by rw [hpy]; exact List.mem_cons_self ..)
      (by simp [Expression.vars])
  have hbx : P.b ≠ P.x := fun h => hbf (h ▸ hxmem)
  have hby : P.b ≠ P.y := fun h => hbf (h ▸ hymem)
  have hhx : P.h ≠ P.x := fun h => hhf (h ▸ hxmem)
  have hhy : P.h ≠ P.y := fun h => hhf (h ▸ hymem)
  obtain ⟨haxC, haxB⟩ := systemAvoids_spec hax
  obtain ⟨hayC, hayB⟩ := systemAvoids_spec hay
  -- the fresh/original limbs' values under the two environments
  have hxdefS : ∀ env, P.envS env P.x
      = (((env P.b + c256 * env P.h).val % 2 ^ P.wxv : ℕ) : ZMod p) := by
    intro env; unfold Pair.envS; rw [if_pos rfl]
  have hydefS : ∀ env, P.envS env P.y
      = (((env P.b + c256 * env P.h).val / 2 ^ P.wxv : ℕ) : ZMod p) := by
    intro env; unfold Pair.envS; rw [if_neg (Ne.symm hxy), if_pos rfl]
  have hbdefC : ∀ env, P.envC env P.b
      = (((P.composed.eval env).val % 256 : ℕ) : ZMod p) := by
    intro env; unfold Pair.envC; rw [if_pos rfl]
  have hhdefC : ∀ env, P.envC env P.h
      = (((P.composed.eval env).val / 256 : ℕ) : ZMod p) := by
    intro env; unfold Pair.envC; rw [if_neg (Ne.symm hbh), if_pos rfl]
  -- an original-system expression is insensitive to the fresh limbs
  have hcsAvoid : ∀ {e : Expression p}, (∀ v ∈ e.vars, v ∈ cs.vars) →
      ∀ env, e.eval (P.envC env) = e.eval env := by
    intro e hsub env
    refine Expression.eval_congr e _ _ (fun v hvv => ?_)
    exact P.envC_eq env (fun h => hbf (h ▸ hsub v hvv)) (fun h => hhf (h ▸ hsub v hvv))
  -- an output expression is insensitive to the original limbs
  have houtAvoid : ∀ {e : Expression p}, e.mentions P.x = false → e.mentions P.y = false →
      ∀ env, e.eval (P.envS env) = e.eval env := by
    intro e hex hey env
    refine Expression.eval_congr e _ _ (fun v hvv => ?_)
    exact P.envS_eq env (fun h => not_mem_vars_of_mentions_false hex (h ▸ hvv))
      (fun h => not_mem_vars_of_mentions_false hey (h ▸ hvv))
  have hcohC : ∀ env, P.coh (P.envC env) := fun env => P.coh_envC env hbx hby hhx hhy hbh
  have hcohS : ∀ env, P.coh (P.envS env) := fun env => P.coh_envS env hxy hbx hby hhx hhy
  -- the shared multiplicity is insensitive to all four limbs
  have hmevalS : ∀ env, P.cx.multiplicity.eval (P.envS env) = P.cx.multiplicity.eval env :=
    fun env => houtAvoid hmx hmy env
  have hmevalC : ∀ env, P.cx.multiplicity.eval (P.envC env) = P.cx.multiplicity.eval env :=
    fun env => hcsAvoid (fun v hvv => ConstraintSystem.mem_vars_of_mult hcxm hvv) env
  -- pointwise interaction transfers away from the replaced pair
  have hmsgS : ∀ env, ∀ bi ∈ cs.busInteractions, bi ≠ P.cx → bi ≠ P.cy →
      (P.rewriteBI bi).eval env = bi.eval (P.envS env) := by
    intro env bi hbi hnx hny
    have hmemout : P.rewriteBI bi ∈ (P.outOf cs).busInteractions := by
      unfold Pair.outOf
      refine List.mem_map.mpr ⟨bi, hbi, ?_⟩
      unfold Pair.mapBI
      rw [if_neg hnx, if_neg hny]
    have hbix := haxB _ hmemout
    have hbiy := hayB _ hmemout
    have h1 : (P.rewriteBI bi).eval env = (P.rewriteBI bi).eval (P.envS env) := by
      unfold BusInteraction.eval
      refine congrArg₂ (fun m pl => BusInteraction.mk (P.rewriteBI bi).busId m pl)
        (houtAvoid hbix.1 hbiy.1 env).symm ?_
      exact List.map_congr_left (fun e he =>
        (houtAvoid (hbix.2 e he) (hbiy.2 e he) env).symm)
    rw [h1, P.rewriteBI_eval bi (P.envS env) (hcohS env)]
  have hmsgC : ∀ env, ∀ bi ∈ cs.busInteractions,
      (P.rewriteBI bi).eval (P.envC env) = bi.eval env := by
    intro env bi hbi
    rw [P.rewriteBI_eval bi (P.envC env) (hcohC env)]
    unfold BusInteraction.eval
    refine congrArg₂ (fun m pl => BusInteraction.mk bi.busId m pl)
      (hcsAvoid (fun v hvv => ConstraintSystem.mem_vars_of_mult hbi hvv) env) ?_
    exact List.map_congr_left (fun e he =>
      hcsAvoid (fun v hvv => ConstraintSystem.mem_vars_of_payload hbi he hvv) env)
  -- constraint transfers
  have hconS : ∀ env, ∀ c ∈ cs.algebraicConstraints,
      (P.rewriteE c).eval env = c.eval (P.envS env) := by
    intro env c hc
    have hmemout : P.rewriteE c ∈ (P.outOf cs).algebraicConstraints :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    rw [← houtAvoid (haxC _ hmemout) (hayC _ hmemout) env]
    exact P.rewriteE_eval c (P.envS env) (hcohS env)
  have hconC : ∀ env, ∀ c ∈ cs.algebraicConstraints,
      (P.rewriteE c).eval (P.envC env) = c.eval env := by
    intro env c hc
    rw [P.rewriteE_eval c (P.envC env) (hcohC env)]
    exact hcsAvoid (fun v hvv => ConstraintSystem.mem_vars_of_constraint hc hvv) env
  -- the fresh checks sit at the replaced positions
  have hmapcx : P.mapBI P.cx = P.newB := by unfold Pair.mapBI; rw [if_pos rfl]
  have hmapcy : P.mapBI P.cy = P.newH := by
    unfold Pair.mapBI
    rw [if_neg (fun h => hcxcy h.symm), if_pos rfl]
  have hnewBmem : P.newB ∈ (P.outOf cs).busInteractions :=
    List.mem_map.mpr ⟨P.cx, hcxm, hmapcx⟩
  have hnewHmem : P.newH ∈ (P.outOf cs).busInteractions :=
    List.mem_map.mpr ⟨P.cy, hcym, hmapcy⟩
  -- evaluated shapes of the four checks
  have hmsgX : ∀ env : Variable → ZMod p, P.cx.eval env
      = BusInteraction.mk P.cx.busId (P.cx.multiplicity.eval env) [env P.x, P.wxc] := by
    intro env
    show BusInteraction.eval _ _ = _
    unfold BusInteraction.eval
    rw [hpx]
    rfl
  have hmsgY : ∀ env : Variable → ZMod p, P.cy.eval env
      = BusInteraction.mk P.cx.busId (P.cx.multiplicity.eval env) [env P.y, P.wyc] := by
    intro env
    show BusInteraction.eval _ _ = _
    unfold BusInteraction.eval
    rw [hpy, hcyb, ← hmeq]
    rfl
  have hmsgB : ∀ env : Variable → ZMod p, P.newB.eval env
      = BusInteraction.mk P.cx.busId (P.cx.multiplicity.eval env) [env P.b, c8] :=
    fun _ => rfl
  have hmsgH : ∀ env : Variable → ZMod p, P.newH.eval env
      = BusInteraction.mk P.cx.busId (P.cx.multiplicity.eval env) [env P.h, P.cW] :=
    fun _ => rfl
  -- the D'-value bound from the fresh checks' acceptance
  have hDbound' : ∀ env : Variable → ZMod p, (env P.b).val < 256 → (env P.h).val < 2 ^ P.wW →
      (env P.b + c256 * env P.h).val = (env P.b).val + 256 * (env P.h).val ∧
      (env P.b + c256 * env P.h).val < 2 ^ (P.wxv + P.wyv) := by
    intro env hbval hhval
    have hcast : env P.b + c256 * env P.h
        = (((env P.b).val + 256 * (env P.h).val : ℕ) : ZMod p) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val,
        ZMod.cast_id, ZMod.cast_id]
      rfl
    have hb256 : 256 * (env P.h).val ≤ 256 * (2 ^ P.wW - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmulsub : 256 * (2 ^ P.wW - 1) + 256 = 256 * 2 ^ P.wW := by
      rw [← Nat.mul_succ]
      congr 1
      have : 0 < 2 ^ P.wW := Nat.pow_pos (by norm_num)
      omega
    have h2sum' : (256 : ℕ) * 2 ^ P.wW = 2 ^ (P.wxv + P.wyv) := by
      rw [Nat.mul_comm]; exact h2sum
    have hlt : (env P.b).val + 256 * (env P.h).val < 2 ^ (P.wxv + P.wyv) := by omega
    constructor
    · rw [hcast]; exact ZMod.val_natCast_of_lt (by omega)
    · rw [hcast, ZMod.val_natCast_of_lt (by omega)]; exact hlt
  -- the D-value bound from the original checks' acceptance
  have hDbound : ∀ env : Variable → ZMod p, (env P.x).val < 2 ^ P.wxv → (env P.y).val < 2 ^ P.wyv →
      (P.composed.eval env).val = (env P.x).val + 2 ^ P.wxv * (env P.y).val ∧
      (P.composed.eval env).val < 2 ^ (P.wxv + P.wyv) := by
    intro env hxval hyval
    have hDcast : P.composed.eval env
        = (((env P.x).val + 2 ^ P.wxv * (env P.y).val : ℕ) : ZMod p) := by
      rw [P.composed_eval, Nat.cast_add, Nat.cast_mul, ZMod.natCast_val,
        ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
      rfl
    have hmul : 2 ^ P.wxv * (env P.y).val ≤ 2 ^ P.wxv * (2 ^ P.wyv - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmulsub : 2 ^ P.wxv * (2 ^ P.wyv - 1) + 2 ^ P.wxv = 2 ^ P.wxv * 2 ^ P.wyv := by
      rw [← Nat.mul_succ]
      congr 1
      have : 0 < 2 ^ P.wyv := Nat.pow_pos (by norm_num)
      omega
    have hpowadd : (2 : ℕ) ^ P.wxv * 2 ^ P.wyv = 2 ^ (P.wxv + P.wyv) :=
      (pow_add 2 P.wxv P.wyv).symm
    have hlt : (env P.x).val + 2 ^ P.wxv * (env P.y).val < 2 ^ (P.wxv + P.wyv) := by omega
    constructor
    · rw [hDcast]; exact ZMod.val_natCast_of_lt (by omega)
    · rw [hDcast, ZMod.val_natCast_of_lt (by omega)]; exact hlt
  -- variables of a rewritten expression: original vars or {b, h, y}
  have hEvars : ∀ {e : Expression p}, ∀ w ∈ (P.rewriteE e).vars,
      w ∈ e.vars ∨ w = P.b ∨ w = P.h ∨ w = P.y := by
    intro e w hw
    unfold Pair.rewriteE at hw
    split at hw
    · have hw2 := Expression.normalize_vars _ _ hw
      rcases substF_vars hw2 with h | ⟨u, t, hu, hwt⟩
      · exact Or.inl h
      · unfold Pair.sigma at hu
        split at hu
        · injection hu with h'
          subst h'
          simp only [Expression.vars, List.mem_append, List.mem_singleton,
            List.nil_append] at hwt
          rcases hwt with (h | h) | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        · exact absurd hu (by simp)
    · exact Or.inl hw
  -- every output variable is a fresh limb or an input variable
  have houtv : ∀ v ∈ (P.outOf cs).vars, v = P.b ∨ v = P.h ∨ v ∈ cs.vars := by
    intro v hvv
    rcases ConstraintSystem.mem_vars.mp hvv with ⟨c', hc', hvc⟩ | ⟨bi', hbi', hvbi⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
      rcases hEvars _ hvc with h | h | h | h
      · exact Or.inr (Or.inr (ConstraintSystem.mem_vars_of_constraint hc h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (h ▸ hymem))
    · obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hbi'
      unfold Pair.mapBI at hvbi
      by_cases h1 : bi = P.cx
      · rw [if_pos h1] at hvbi
        rcases hvbi with hvm | ⟨e, he, hve⟩
        · exact Or.inr (Or.inr (ConstraintSystem.mem_vars_of_mult hcxm hvm))
        · rcases List.mem_cons.mp he with rfl | he2
          · simp only [Expression.vars, List.mem_singleton] at hve
            exact Or.inl hve
          · rcases List.mem_cons.mp he2 with rfl | he3
            · simp [Expression.vars] at hve
            · exact absurd he3 (by simp)
      by_cases h2 : bi = P.cy
      · rw [if_neg h1, if_pos h2] at hvbi
        rcases hvbi with hvm | ⟨e, he, hve⟩
        · exact Or.inr (Or.inr (ConstraintSystem.mem_vars_of_mult hcxm hvm))
        · rcases List.mem_cons.mp he with rfl | he2
          · simp only [Expression.vars, List.mem_singleton] at hve
            exact Or.inr (Or.inl hve)
          · rcases List.mem_cons.mp he2 with rfl | he3
            · simp [Expression.vars] at hve
            · exact absurd he3 (by simp)
      · rw [if_neg h1, if_neg h2] at hvbi
        rcases hvbi with hvm | ⟨e, he, hve⟩
        · rcases hEvars _ hvm with h | h | h | h
          · exact Or.inr (Or.inr (ConstraintSystem.mem_vars_of_mult hbi h))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (h ▸ hymem))
        · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
          rcases hEvars _ hve with h | h | h | h
          · exact Or.inr (Or.inr (ConstraintSystem.mem_vars_of_payload hbi he0 h))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (h ▸ hymem))
  -- soundness-direction satisfaction
  have hsatS : ∀ env, (P.outOf cs).satisfies bs env → cs.satisfies bs (P.envS env) := by
    intro env hsat'
    constructor
    · intro c hc
      rw [← hconS env c hc]
      exact hsat'.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    · intro bi hbi
      show (bi.eval (P.envS env)).multiplicity ≠ 0
        → bs.violatesConstraint (bi.eval (P.envS env)) = false
      intro hm0
      by_cases hbcx : bi = P.cx
      · rw [hbcx] at hm0 ⊢
        rw [hmsgX (P.envS env)]
        refine (hiff _ _ _).mpr ⟨hwx25, ?_⟩
        rw [hxdefS env, ZMod.val_natCast_of_lt
          (lt_trans (Nat.mod_lt _ (Nat.pow_pos (by norm_num))) h2wxlt)]
        exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      by_cases hbcy : bi = P.cy
      · rw [hbcy] at hm0 ⊢
        have hm0' : P.cx.multiplicity.eval env ≠ 0 := by
          rw [hmsgY (P.envS env), hmevalS env] at hm0
          exact hm0
        have hBacc := hsat'.2 P.newB hnewBmem (by
          rw [hmsgB env]; exact hm0')
        have hHacc := hsat'.2 P.newH hnewHmem (by
          rw [hmsgH env]; exact hm0')
        rw [hmsgB env] at hBacc
        rw [hmsgH env] at hHacc
        have hBiff := (hiff (env P.b) c8 (P.cx.multiplicity.eval env)).mp hBacc
        have hHiff := (hiff (env P.h) P.cW (P.cx.multiplicity.eval env)).mp hHacc
        have hbval : (env P.b).val < 256 := by
          have h2 := hBiff.2
          rwa [hc8val, show (2 : ℕ) ^ 8 = 256 by norm_num] at h2
        have hhval : (env P.h).val < 2 ^ P.wW := by
          have h2 := hHiff.2
          rwa [hcWval] at h2
        obtain ⟨-, hD'lt⟩ := hDbound' env hbval hhval
        rw [hmsgY (P.envS env)]
        refine (hiff _ _ _).mpr ⟨hwy25, ?_⟩
        rw [hydefS env, ZMod.val_natCast_of_lt
          (lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt _))]
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
        calc (env P.b + c256 * env P.h).val < 2 ^ (P.wxv + P.wyv) := hD'lt
          _ = 2 ^ P.wyv * 2 ^ P.wxv := by rw [← pow_add, Nat.add_comm]
      · have heq := hmsgS env bi hbi hbcx hbcy
        have hmemout : P.rewriteBI bi ∈ (P.outOf cs).busInteractions := by
          unfold Pair.outOf
          refine List.mem_map.mpr ⟨bi, hbi, ?_⟩
          unfold Pair.mapBI
          rw [if_neg hbcx, if_neg hbcy]
        have hm0' : ((P.rewriteBI bi).eval env).multiplicity ≠ 0 := by
          rw [heq]; exact hm0
        have hacc := hsat'.2 _ hmemout hm0'
        rwa [heq] at hacc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- soundness: `out.implies cs`
    intro env hsat'
    refine ⟨P.envS env, hsatS env hsat', ?_⟩
    have hse : cs.sideEffects bs (P.envS env) = (P.outOf cs).sideEffects bs env := by
      show ((cs.busInteractions.filter _).map _)
          = (((cs.busInteractions.map P.mapBI).filter _).map _)
      refine filter_se_eq P.mapBI (P.envS env) env cs.busInteractions ?_ ?_
      · intro bi _
        unfold Pair.mapBI
        by_cases h1 : bi = P.cx
        · rw [if_pos h1, h1]; rfl
        by_cases h2 : bi = P.cy
        · rw [if_neg h1, if_pos h2, h2]
          show P.cx.busId = P.cy.busId
          exact hcyb.symm
        · rw [if_neg h1, if_neg h2]; rfl
      · intro bi hbi hst
        have hbcx : bi ≠ P.cx := fun h => by
          rw [h, hstateless] at hst; exact Bool.false_ne_true hst
        have hbcy : bi ≠ P.cy := fun h => by
          rw [h, show P.cy.busId = P.cx.busId from hcyb, hstateless] at hst
          exact Bool.false_ne_true hst
        unfold Pair.mapBI
        rw [if_neg hbcx, if_neg hbcy]
        exact hmsgS env bi hbi hbcx hbcy
    rw [← hse]
    exact BusState.equiv_refl _
  · -- invariants
    intro hg env hsat' bi' hbi'
    show (bi'.eval env).multiplicity ≠ 0 → bs.breaksInvariant (bi'.eval env) = false
    intro hm0
    have hsatcs := hsatS env hsat'
    obtain ⟨bi, hbi, hmap⟩ := List.mem_map.mp hbi'
    by_cases hbcx : bi = P.cx
    · rw [← hmap, hbcx, hmapcx] at hm0 ⊢
      rw [hmsgB env] at hm0 ⊢
      have hbrk := hg (P.envS env) hsatcs P.cx hcxm (by
        rw [hmsgX (P.envS env), hmevalS env]; exact hm0)
      rw [hmsgX (P.envS env), hmevalS env] at hbrk
      rw [hinvind (env P.b) c8 (P.envS env P.x) P.wxc (P.cx.multiplicity.eval env)]
      exact hbrk
    by_cases hbcy : bi = P.cy
    · rw [← hmap, hbcy, hmapcy] at hm0 ⊢
      rw [hmsgH env] at hm0 ⊢
      have hbrk := hg (P.envS env) hsatcs P.cy hcym (by
        rw [hmsgY (P.envS env), hmevalS env]; exact hm0)
      rw [hmsgY (P.envS env), hmevalS env] at hbrk
      rw [hinvind (env P.h) P.cW (P.envS env P.y) P.wyc (P.cx.multiplicity.eval env)]
      exact hbrk
    · have hmap' : P.mapBI bi = P.rewriteBI bi := by
        unfold Pair.mapBI
        rw [if_neg hbcx, if_neg hbcy]
      rw [← hmap, hmap'] at hm0 ⊢
      have heq := hmsgS env bi hbi hbcx hbcy
      rw [heq] at hm0 ⊢
      exact hg (P.envS env) hsatcs bi hbi hm0
  · -- no new powdr-ID columns
    intro v hvv hvpow
    rcases houtv v hvv with h | h | h
    · subst h
      rw [Option.isNone_iff_eq_none.mp hbpow] at hvpow
      simp at hvpow
    · subst h
      rw [Option.isNone_iff_eq_none.mp hhpow] at hvpow
      simp at hvpow
    · exact h
  · -- completeness
    intro env hadm hsat
    refine ⟨P.envC env, ?_, ?_, ?_, ?_, ?_⟩
    · -- the output is satisfied
      constructor
      · intro c' hc'
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        rw [hconC env c hc]
        exact hsat.1 c hc
      · intro bi' hbi'
        show (bi'.eval (P.envC env)).multiplicity ≠ 0
          → bs.violatesConstraint (bi'.eval (P.envC env)) = false
        intro hm0
        obtain ⟨bi, hbi, hmap⟩ := List.mem_map.mp hbi'
        by_cases h1 : bi = P.cx
        · rw [← hmap, h1, hmapcx] at hm0 ⊢
          rw [hmsgB (P.envC env)] at hm0 ⊢
          refine (hiff _ _ _).mpr ⟨by rw [hc8val]; omega, ?_⟩
          rw [hbdefC env, hc8val, show (2 : ℕ) ^ 8 = 256 by norm_num,
            ZMod.val_natCast_of_lt (by omega)]
          exact Nat.mod_lt _ (by norm_num)
        by_cases h2 : bi = P.cy
        · rw [← hmap, h2, hmapcy] at hm0 ⊢
          rw [hmsgH (P.envC env)] at hm0 ⊢
          have hm0' : P.cx.multiplicity.eval env ≠ 0 := by
            rw [hmevalC env] at hm0
            exact hm0
          have hXacc := hsat.2 P.cx hcxm (by
            rw [hmsgX env]; exact hm0')
          have hYacc := hsat.2 P.cy hcym (by
            rw [hmsgY env]; exact hm0')
          rw [hmsgX env] at hXacc
          rw [hmsgY env] at hYacc
          have hXiff := (hiff (env P.x) P.wxc (P.cx.multiplicity.eval env)).mp hXacc
          have hYiff := (hiff (env P.y) P.wyc (P.cx.multiplicity.eval env)).mp hYacc
          obtain ⟨-, hDlt⟩ := hDbound env hXiff.2 hYiff.2
          refine (hiff _ _ _).mpr ⟨by rw [hcWval]; unfold Pair.wW; omega, ?_⟩
          rw [hhdefC env, hcWval, ZMod.val_natCast_of_lt
            (lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt _))]
          rw [Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 256)]
          have h2sum' : (2 : ℕ) ^ P.wW * 256 = 2 ^ (P.wxv + P.wyv) := h2sum
          omega
        · have hmap' : P.mapBI bi = P.rewriteBI bi := by
            unfold Pair.mapBI
            rw [if_neg h1, if_neg h2]
          rw [← hmap, hmap'] at hm0 ⊢
          rw [hmsgC env bi hbi] at hm0 ⊢
          exact hsat.2 bi hbi hm0
    · -- the output is admissible
      have hlists : ((cs.busInteractions.map (fun bi => bi.eval env)).filter
            (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
          = (((cs.busInteractions.map P.mapBI).map (fun bi => bi.eval (P.envC env))).filter
            (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := by
        refine filter_msgs_eq P.mapBI env (P.envC env) cs.busInteractions ?_
        intro bi hbi
        by_cases h1 : bi = P.cx
        · refine Or.inr ⟨?_, ?_⟩
          · rw [h1]; exact hstateless
          · rw [h1, hmapcx]; exact hstateless
        by_cases h2 : bi = P.cy
        · refine Or.inr ⟨?_, ?_⟩
          · rw [h2]
            show bs.isStateful P.cy.busId = false
            rw [hcyb]; exact hstateless
          · rw [h2, hmapcy]; exact hstateless
        · refine Or.inl ?_
          have hmap' : P.mapBI bi = P.rewriteBI bi := by
            unfold Pair.mapBI
            rw [if_neg h1, if_neg h2]
          rw [hmap']
          exact hmsgC env bi hbi
      unfold ConstraintSystem.admissible at hadm
      show bs.admissible (((cs.busInteractions.map P.mapBI).map
          (fun bi => bi.eval (P.envC env))).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
      rw [← hlists]
      exact hadm
    · -- side effects agree
      have hse : cs.sideEffects bs env = (P.outOf cs).sideEffects bs (P.envC env) := by
        show ((cs.busInteractions.filter _).map _)
            = (((cs.busInteractions.map P.mapBI).filter _).map _)
        refine filter_se_eq P.mapBI env (P.envC env) cs.busInteractions ?_ ?_
        · intro bi _
          unfold Pair.mapBI
          by_cases h1 : bi = P.cx
          · rw [if_pos h1, h1]; rfl
          by_cases h2 : bi = P.cy
          · rw [if_neg h1, if_pos h2, h2]
            show P.cx.busId = P.cy.busId
            exact hcyb.symm
          · rw [if_neg h1, if_neg h2]; rfl
        · intro bi hbi hst
          have hbcx : bi ≠ P.cx := fun h => by
            rw [h, hstateless] at hst; exact Bool.false_ne_true hst
          have hbcy : bi ≠ P.cy := fun h => by
            rw [h, show P.cy.busId = P.cx.busId from hcyb, hstateless] at hst
            exact Bool.false_ne_true hst
          unfold Pair.mapBI
          rw [if_neg hbcx, if_neg hbcy]
          exact hmsgC env bi hbi
      rw [hse]
      exact BusState.equiv_refl _
    · -- powdr-ID variables keep their values
      intro v hvpow
      refine P.envC_eq env (fun h => ?_) (fun h => ?_)
      · rw [h, Option.isNone_iff_eq_none.mp hbpow] at hvpow
        simp at hvpow
      · rw [h, Option.isNone_iff_eq_none.mp hhpow] at hvpow
        simp at hvpow
    · -- reconstruction
      intro inputVars hpowIn dsIn hrec v hvv hvnone
      have hcompC : P.composed.eval (P.envC env) = P.composed.eval env := by
        refine hcsAvoid (fun w hw => ?_) env
        rw [P.composed_vars] at hw
        rcases List.mem_cons.mp hw with rfl | hw2
        · exact hxmem
        · rcases List.mem_cons.mp hw2 with rfl | hw3
          · exact hymem
          · exact absurd hw3 (by simp)
      have hcomppow : ∀ w ∈ P.composed.vars, w.powdrId?.isSome := by
        intro w hw
        rw [P.composed_vars] at hw
        rcases List.mem_cons.mp hw with rfl | hw2
        · exact hxpow
        · rcases List.mem_cons.mp hw2 with rfl | hw3
          · exact hypow
          · exact absurd hw3 (by simp)
      have hcompin : ∀ w ∈ P.composed.vars, w ∈ inputVars := by
        intro w hw
        rw [P.composed_vars] at hw
        rcases List.mem_cons.mp hw with rfl | hw2
        · exact hpowIn _ hxmem hxpow
        · rcases List.mem_cons.mp hw2 with rfl | hw3
          · exact hpowIn _ hymem hypow
          · exact absurd hw3 (by simp)
      by_cases hveqb : v = P.b
      · subst hveqb
        refine ⟨.floorMod P.composed 256, ?_, hcomppow, hcompin, ?_⟩
        · rw [methodFor_append]
          have hloc : Derivations.methodFor P.derivs P.b
              = some (.floorMod P.composed 256) := by
            show Derivations.methodFor
              [(P.b, ComputationMethod.floorMod P.composed 256),
               (P.h, ComputationMethod.floorDiv P.composed 256)] P.b = _
            simp [Derivations.methodFor, Ne.symm hbh]
          rw [hloc]
          rfl
        · show (((P.composed.eval (P.envC env)).val % 256 : ℕ) : ZMod p) = P.envC env P.b
          rw [hcompC, hbdefC env]
      by_cases hveqh : v = P.h
      · subst hveqh
        refine ⟨.floorDiv P.composed 256, ?_, hcomppow, hcompin, ?_⟩
        · rw [methodFor_append]
          have hloc : Derivations.methodFor P.derivs P.h
              = some (.floorDiv P.composed 256) := by
            show Derivations.methodFor
              [(P.b, ComputationMethod.floorMod P.composed 256),
               (P.h, ComputationMethod.floorDiv P.composed 256)] P.h = _
            simp [Derivations.methodFor]
          rw [hloc]
          rfl
        · show (((P.composed.eval (P.envC env)).val / 256 : ℕ) : ZMod p) = P.envC env P.h
          rw [hcompC, hhdefC env]
      · -- an untouched derived variable: covered by the incoming derivations
        have hvcs : v ∈ cs.vars := by
          rcases houtv v hvv with h | h | h
          · exact absurd h hveqb
          · exact absurd h hveqh
          · exact h
        obtain ⟨cm, hmf, hpowv, hinv, heval⟩ := hrec v hvcs hvnone
        refine ⟨cm, ?_, hpowv, hinv, ?_⟩
        · rw [methodFor_append]
          have hloc : Derivations.methodFor P.derivs v = none := by
            show Derivations.methodFor
              [(P.b, ComputationMethod.floorMod P.composed 256),
               (P.h, ComputationMethod.floorDiv P.composed 256)] v = _
            simp [Derivations.methodFor, Ne.symm hveqb, Ne.symm hveqh]
          rw [hloc]
          show Derivations.methodFor dsIn v = some cm
          exact hmf
        · have hcm : cm.eval (P.envC env) = cm.eval env := by
            refine ComputationMethod.eval_congr cm _ _ (fun w hw => ?_)
            refine P.envC_eq env (fun h => ?_) (fun h => ?_)
            · have hp := hpowv w hw
              rw [h, Option.isNone_iff_eq_none.mp hbpow] at hp
              simp at hp
            · have hp := hpowv w hw
              rw [h, Option.isNone_iff_eq_none.mp hhpow] at hp
              simp at hp
          rw [hcm, heval]
          exact (P.envC_eq env hveqb hveqh).symm

/-- Package one accepted pair as a `PassResult`. -/
def Pair.apply {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (P : Pair p) (hv : P.valid facts cs = true) : PassResult cs bs :=
  ⟨P.outOf cs, P.derivs, P.applyPair_correct facts cs hv⟩

/-! ## Discovery -/

/-- Recognise a bare-variable range check `[x, w]` on a `varRangeBus` bus. -/
def bareCheck? {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Variable × ZMod p) :=
  if facts.varRangeBus bi.busId then
    match bi.payload with
    | [.var x, .const w] => some (x, w)
    | _ => none
  else none

/-- The first expression outside `cx` that mentions `x` (a constraint, a multiplicity, or a
    payload slot). The composed linear form lives there. -/
def firstSite (cs : ConstraintSystem p) (cx : BusInteraction (Expression p)) (x : Variable) :
    Option (Expression p) :=
  (cs.algebraicConstraints.find? (fun c => c.mentions x)).orElse (fun _ =>
    cs.busInteractions.findSome? (fun bi =>
      if bi == cx then none
      else if bi.multiplicity.mentions x then some bi.multiplicity
      else bi.payload.find? (fun e => e.mentions x)))

/-- Find the re-split partner for a candidate low check: linearize the first occurrence site,
    read off the variable carrying coefficient `2^wxv · coeff(x)`, and locate its own bare
    check with the same multiplicity on the same bus. -/
def findPartner {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (cx : BusInteraction (Expression p)) : Option (Pair p) := do
  let (x, wxc) ← bareCheck? facts cx
  let e ← firstSite cs cx x
  let l ← linearize e
  let ln := l.norm
  let cX ← (ln.terms.find? (fun t => t.1 == x)).map (·.2)
  let target := cX * ((2 ^ wxc.val : ℕ) : ZMod p)
  ln.terms.findSome? (fun t =>
    if t.1 == x || t.2 != target then none
    else
      cs.busInteractions.findSome? (fun cy =>
        if cy == cx then none
        else match bareCheck? facts cy with
        | some (y, wyc) =>
            if y == t.1 && cy.busId == cx.busId
                && cy.multiplicity == cx.multiplicity then
              -- The low limb's powdr ID is unique per column (and validity demands it exists),
              -- so it alone makes the fresh names distinct across pairs; collisions with
              -- preexisting names are caught by the freshness conjunct of `Pair.valid`.
              let tag := toString (x.powdrId?.getD 0)
              some { cx := cx, cy := cy, x := x, y := y, wxc := wxc, wyc := wyc,
                     b := ⟨"resplit_byte_" ++ tag, none⟩,
                     h := ⟨"resplit_high_" ++ tag, none⟩ }
            else none
        | none => none))

/-- Try to re-split around one candidate check in the current system. -/
def tryCheck {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (c : BusInteraction (Expression p)) : Option (PassResult cs bs) :=
  match findPartner facts cs c with
  | none => none
  | some P =>
      if hv : P.valid facts cs = true then some (Pair.apply facts cs P hv) else none

/-- Drain the candidate list, applying each accepted re-split to the current system. -/
def drainGo {bs : BusSemantics p} (facts : BusFacts p bs) :
    List (BusInteraction (Expression p)) → (cs : ConstraintSystem p) → PassResult cs bs
  | [], cs => ⟨cs, [], PassCorrect.refl cs bs⟩
  | c :: rest, cs =>
    match tryCheck facts cs c with
    | none => drainGo facts rest cs
    | some r =>
        let r2 := drainGo facts rest r.out
        ⟨r2.out, r.derivs ++ r2.derivs, r.correct.andThen r2.correct⟩

end RangeResplit

/-- The range re-split pass: re-encode two-limb range decompositions at the byte boundary so
    the byte parts join the byte-packing pool. Candidates are the bare-variable range checks of
    the input system; each accepted pair swaps the two solo checks for a byte check plus one
    narrower solo check, variable-neutrally. Runs once in the coda, before the packers. -/
def rangeResplitPass : VerifiedPassW p := fun cs _bs facts =>
  RangeResplit.drainGo facts
    (cs.busInteractions.filter (fun bi => (RangeResplit.bareCheck? facts bi).isSome)) cs
