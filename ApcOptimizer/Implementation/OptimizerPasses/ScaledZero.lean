import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Scaled-byte-forces-zero

A variable pinned to `0` by two range obligations that are individually satisfiable but jointly
force `v = 0`. The motivating shape is SP1's byte-lookup **range-check trick**: an operand byte `v`
is checked both bare (`v < 256`) and *scaled* (`k·v < 256`, e.g. `k = 8323072 = 127·2¹⁶`, its shifted
copy on the byte bus). A byte whose large-scaled copy is *also* a byte must be `0` — for any
`v ∈ [1, 256)`, `k·v ≥ k ≥ 256` (and `k·(256−1) < p`, so no wraparound hides it). This is exactly the
fact powdr uses to drop the upper bytes of a `lbu; xor; sb` chain: the loaded operands are bytes, so
the XOR chip's upper operand bytes are `0`, the upper results are `0`, and the whole upper cluster
disconnects.

apc has both range obligations (as `slotBound` facts on the byte bus) but never intersected them.
This pass seeds the entailed `v = 0` (`ConstraintSystem.addConstraints_correct`); Gauss and the
fold/`slotFun`/disconnected passes do the rest. Purely arithmetic on the two proven bounds — no bus
specifics beyond `slotBound`, no primality; the `k·(B−1) < p` no-wrap side condition is decided at
runtime against the concrete field. -/

namespace ScaledZero

variable {p : ℕ}

/-- Coefficient `c` when `e` linearizes to a single scaled variable `c·v` (no constant term). -/
def scaledCoeff? (e : Expression p) (v : Variable) : Option (ZMod p) :=
  match linearize e with
  | some ⟨cst, [(w, c)]⟩ => if decide (w = v) && decide (cst = 0) then some c else none
  | _ => none

theorem scaledCoeff?_eval (e : Expression p) (v : Variable) (c : ZMod p)
    (h : scaledCoeff? e v = some c) (env : Variable → ZMod p) : e.eval env = c * env v := by
  unfold scaledCoeff? at h
  cases hL : linearize e with
  | none => simp [hL] at h
  | some L =>
    obtain ⟨cst, terms⟩ := L
    cases terms with
    | nil => simp [hL] at h
    | cons t rest =>
      cases rest with
      | cons _ _ => simp [hL] at h
      | nil =>
        obtain ⟨w, c'⟩ := t
        simp only [hL] at h
        by_cases hcond : (decide (w = v) && decide (cst = 0)) = true
        · rw [if_pos hcond] at h
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨rfl, rfl⟩ := hcond
          have he2 := linearize_eval e _ hL env
          simp only [LinExpr.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            add_zero, zero_add] at he2
          exact he2
        · rw [if_neg hcond] at h; exact absurd h (by simp)

/-- Search a payload (indices `< i`) for a slot holding `c·v` with a `slotBound`; returns `(c, B)`. -/
def scanScaled {bs : BusSemantics p} (facts : BusFacts p bs) (busId : Nat) (mval : ZMod p)
    (pattern : List (Option (ZMod p))) (payload : List (Expression p)) (v : Variable) :
    Nat → Option (ZMod p × Nat)
  | 0 => none
  | i + 1 =>
    match payload[i]? with
    | some e =>
      match scaledCoeff? e v, facts.slotBound busId mval pattern i with
      -- only a *genuinely scaled* slot (`b ≤ c.val`) helps: it skips the bare occurrence `c = 1`.
      | some c, some b =>
        if b ≤ c.val then some (c, b) else scanScaled facts busId mval pattern payload v i
      | _, _ => scanScaled facts busId mval pattern payload v i
    | none => scanScaled facts busId mval pattern payload v i

/-- If `scanScaled` succeeds, the scaled value `c·env v` is bounded by `B` on any assignment where
    the interaction's obligation is active and satisfied. -/
theorem scanScaled_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (v : Variable) (c : ZMod p) (B : Nat) (mval : ZMod p)
    (hmc : bi.multiplicity.constValue? = some mval)
    (env : Variable → ZMod p)
    (hviol : (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) :
    ∀ n, scanScaled facts bi.busId mval (bi.payload.map Expression.constValue?) bi.payload v n
        = some (c, B) → mval ≠ 0 → (c * env v).val < B := by
  intro n
  induction n with
  | zero => intro h; simp [scanScaled] at h
  | succ i ih =>
    intro h hmz
    unfold scanScaled at h
    cases he : bi.payload[i]? with
    | none => simp only [he] at h; exact ih h hmz
    | some e =>
      cases hc : scaledCoeff? e v with
      | none => simp only [he, hc] at h; exact ih h hmz
      | some c' =>
        cases hb : facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) i with
        | none => simp only [he, hc, hb] at h; exact ih h hmz
        | some b' =>
          simp only [he, hc, hb] at h
          split_ifs at h with hfilt
          swap
          · exact ih h hmz
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hcc, hbb⟩ := h
          rw [← hcc, ← hbb]
          -- the interaction is active at multiplicity `mval`, hence not violating
          have hmeval : (bi.eval env).multiplicity = mval :=
            bi.multiplicity.constValue?_sound mval hmc env
          have hv : bs.violatesConstraint (bi.eval env) = false := by
            apply hviol; rw [hmeval]; exact hmz
          -- the evaluated slot holds `e.eval env = c'·env v`
          have hget : (bi.eval env).payload[i]? = some (c' * env v) := by
            show (bi.payload.map (fun t => t.eval env))[i]? = some (c' * env v)
            rw [List.getElem?_map, he]
            simp only [Option.map_some, Option.some.injEq]
            exact scaledCoeff?_eval e v c' hc env
          have hb' : facts.slotBound (bi.eval env).busId (bi.eval env).multiplicity
              (bi.payload.map Expression.constValue?) i = some b' := by
            show facts.slotBound bi.busId (bi.eval env).multiplicity _ i = some b'
            rw [hmeval]; exact hb
          exact facts.slotBound_sound (bi.eval env)
            (bi.payload.map Expression.constValue?) i b' (c' * env v) hb'
            (matches_evalPattern bi.payload env) hv hget

/-- Scan a bus-interaction list for a scaled bound `(c, B)` on `v`. -/
def findScaledBound {bs : BusSemantics p} (facts : BusFacts p bs) (v : Variable) :
    List (BusInteraction (Expression p)) → Option (ZMod p × Nat)
  | [] => none
  | bi :: rest =>
    match bi.multiplicity.constValue? with
    | some mval =>
      if mval = 0 then findScaledBound facts v rest
      else match scanScaled facts bi.busId mval (bi.payload.map Expression.constValue?)
            bi.payload v bi.payload.length with
        | some r => some r
        | none => findScaledBound facts v rest
    | none => findScaledBound facts v rest

theorem findScaledBound_sound {bs : BusSemantics p} (facts : BusFacts p bs) (v : Variable)
    (bis : List (BusInteraction (Expression p))) (c : ZMod p) (B : Nat)
    (h : findScaledBound facts v bis = some (c, B)) (env : Variable → ZMod p)
    (hbus : ∀ bi ∈ bis, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (c * env v).val < B := by
  induction bis with
  | nil => simp [findScaledBound] at h
  | cons bi rest ih =>
    unfold findScaledBound at h
    cases hmc : bi.multiplicity.constValue? with
    | none => simp only [hmc] at h; exact ih h (fun bi' hbi' => hbus bi' (List.mem_cons_of_mem _ hbi'))
    | some mval =>
      simp only [hmc] at h
      split_ifs at h with hmz
      · exact ih h (fun bi' hbi' => hbus bi' (List.mem_cons_of_mem _ hbi'))
      · cases hs : scanScaled facts bi.busId mval (bi.payload.map Expression.constValue?)
            bi.payload v bi.payload.length with
        | none => simp only [hs] at h; exact ih h (fun bi' hbi' => hbus bi' (List.mem_cons_of_mem _ hbi'))
        | some r =>
          rw [hs] at h
          simp only [Option.some.injEq] at h; subst h
          exact scanScaled_sound facts bi v c B mval hmc env
            (hbus bi (List.mem_cons_self ..)) bi.payload.length hs hmz

/-- The joint-bound argument: a byte `v < B1` whose scaled copy `c·v < B2` with `c ≥ B2` and no
    wraparound (`c·(B1−1) < p`) forces `v = 0`. -/
theorem zero_of_bounds {p : ℕ} (v c : ZMod p) (B1 B2 : Nat)
    (hb1 : v.val < B1) (hb2 : (c * v).val < B2)
    (hc : B2 ≤ c.val) (hnw : c.val * (B1 - 1) < p) : v = 0 := by
  rw [← ZMod.val_eq_zero]
  by_contra hne
  have hv1 : 1 ≤ v.val := Nat.one_le_iff_ne_zero.mpr hne
  have hle : c.val * v.val ≤ c.val * (B1 - 1) := Nat.mul_le_mul_left _ (by omega)
  have hlt : c.val * v.val < p := lt_of_le_of_lt hle hnw
  have hval : (c * v).val = c.val * v.val := by rw [ZMod.val_mul, Nat.mod_eq_of_lt hlt]
  rw [hval] at hb2
  -- c.val * v.val ≥ c.val ≥ B2, contradicting < B2
  have : c.val ≤ c.val * v.val := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The two-term generalization of `zero_of_bounds`: a byte-slot value `k·v − k·w` (both `v`, `w`
    bounded by `B`) that is `< B2` with `k ≥ B2` (genuinely scaled) and no wraparound
    (`k·(B−1) ≤ p − B2`) forces `v = w`. The `k`-scaled difference of two bytes is either `0` (when
    `v = w`) or has field value `≥ B2` (a multiple of `k` on one side, `≥ p − k·(B−1) ≥ B2` on the
    other), so `< B2` pins it to `0`. This is exactly the SP1 `lbu; xor; sb` dead-byte OR operand
    `8323072·(b_low − higher)`: a byte, forcing `b_low = higher`. -/
theorem two_term_zero {p : ℕ} [NeZero p] (v w k : ZMod p) (B B2 : Nat)
    (hv : v.val < B) (hw : w.val < B) (hB2 : 1 ≤ B2)
    (hk : B2 ≤ k.val) (hnw : k.val * (B - 1) ≤ p - B2)
    (hs : (k * v - k * w).val < B2) : v = w := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hnwlt : k.val * (B - 1) < p := lt_of_le_of_lt hnw (by omega)
  have hmul : k * v - k * w = k * (v - w) := by ring
  rw [hmul] at hs
  rcases Nat.lt_or_ge v.val w.val with hlt | hle
  · -- v.val < w.val: `k·(v−w) = −(k·(w−v))` has value `≥ B2`, contradicting `hs`.
    exfalso
    have hd'val : (w - v).val = w.val - v.val := ZMod.val_sub (le_of_lt hlt)
    have hd'pos : 1 ≤ (w - v).val := by rw [hd'val]; omega
    have hkwv_val : (k * (w - v)).val = k.val * (w - v).val := by
      rw [ZMod.val_mul, Nat.mod_eq_of_lt (lt_of_le_of_lt
        (Nat.mul_le_mul_left _ (by rw [hd'val]; omega)) hnwlt)]
    have hkwv_ne : k * (w - v) ≠ 0 := by
      intro h0
      rw [h0, ZMod.val_zero] at hkwv_val
      have : k.val ≤ k.val * (w - v).val := Nat.le_mul_of_pos_right _ (by omega)
      omega
    haveI : NeZero (k * (w - v)) := ⟨hkwv_ne⟩
    have hneg : k * (v - w) = -(k * (w - v)) := by ring
    rw [hneg, ZMod.val_neg_of_ne_zero, hkwv_val] at hs
    have hle2 : k.val * (w - v).val ≤ p - B2 :=
      le_trans (Nat.mul_le_mul_left _ (by rw [hd'val]; omega)) hnw
    have hB2p : B2 ≤ p := le_of_lt (lt_of_le_of_lt hk (ZMod.val_lt k))
    -- `p − X < B2` (hs) but `X ≤ p − B2` (hle2) ⇒ `p − X ≥ B2`: contradiction (`X` opaque to omega).
    generalize hX : k.val * (w - v).val = X at hs hle2
    omega
  · -- v.val ≥ w.val: `d = v − w` is a nonneg byte, so `zero_of_bounds` applies.
    have hdval : (v - w).val = v.val - w.val := ZMod.val_sub hle
    have hdB : (v - w).val < B := by rw [hdval]; omega
    exact sub_eq_zero.mp (zero_of_bounds (v - w) k B B2 hdB hs hk hnwlt)

/-- `v` is provably `0`: bare-bounded by `B1` and scaled-bounded by `(c, B2)` over `cs`'s
    interactions, with `c ≥ B2` and the no-wrap `c·(B1−1) < p`. -/
def scaledZeroOk {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (v : Variable) : Bool :=
  match findVarBound bs facts cs.busInteractions v, findScaledBound facts v cs.busInteractions with
  | some B1, some (c, B2) =>
    decide (1 ≤ B1) && decide (B2 ≤ c.val) && decide (c.val * (B1 - 1) < p)
  | _, _ => false

theorem scaledZeroOk_sound {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (v : Variable) (h : scaledZeroOk facts cs v = true) (env : Variable → ZMod p)
    (hsat : cs.satisfies bs env) : env v = 0 := by
  unfold scaledZeroOk at h
  cases hb1 : findVarBound bs facts cs.busInteractions v with
  | none => rw [hb1] at h; simp at h
  | some B1 =>
    cases hb2 : findScaledBound facts v cs.busInteractions with
    | none => rw [hb1, hb2] at h; simp at h
    | some cB =>
      obtain ⟨c, B2⟩ := cB
      rw [hb1, hb2] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hB1, hcB2⟩, hnw⟩ := h
      have hbus : ∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
          bs.violatesConstraint (bi.eval env) = false := fun bi hbi => hsat.2 bi hbi
      exact zero_of_bounds (env v) c B1 B2
        (findVarBound_sound bs facts cs.busInteractions v B1 hb1 env hbus)
        (findScaledBound_sound facts v cs.busInteractions c B2 hb2 env hbus) hcB2 hnw

/-- The variable of a genuinely-scaled slot `c·v` (`c ≠ 0, 1`), else `none`. Restricts the candidate
    search to the few shift-trick operands, so the pass does not rescan every byte-bus variable. -/
def scaledVarOf? (e : Expression p) : Option Variable :=
  match linearize e with
  | some ⟨cst, [(w, c)]⟩ => if decide (cst = 0) && decide (c ≠ 1) && decide (c ≠ 0) then some w else none
  | _ => none

/-- Candidate variables: those that appear as a *scaled* term `c·v` in some interaction slot. -/
def scaledCandidates (cs : ConstraintSystem p) : List Variable :=
  (cs.busInteractions.flatMap (fun bi => bi.payload.filterMap scaledVarOf?)).eraseDups

/-- The seeds `v = 0` (as the expression `v`) for every provably-zero candidate. -/
def scaledZeroSeeds {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (Expression p) :=
  ((scaledCandidates cs).filter (fun v => scaledZeroOk facts cs v)).map Expression.var

theorem scaledZeroSeeds_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p) (env : Variable → ZMod p)
    (hsat : cs.satisfies bs env) : ∀ e ∈ scaledZeroSeeds facts cs, e.eval env = 0 := by
  intro e he
  unfold scaledZeroSeeds at he
  rw [List.mem_map] at he
  obtain ⟨v, hv, rfl⟩ := he
  have hok := (List.mem_filter.mp hv).2
  show env v = 0
  exact scaledZeroOk_sound facts cs v hok env hsat

/-! ## Two-term scaled slots (`k·v − k·w`)

The SP1 `lbu; xor; sb` dead-byte OR operands are byte slots holding `8323072·(b_low − higher)` — a
`k·v − k·w` form, not a single scaled variable. Its byte bound forces `v = w` (`two_term_zero`),
which `Gauss` uses to merge the two limbs; the emptied operand then reaches the constant `0` and the
result byte is dropped by `xorEqExtract`'s OR arm. -/

/-- `v − w` as an expression (`v + (−1)·w`). -/
def pairDiff (v w : Variable) : Expression p :=
  Expression.add (Expression.var v) (Expression.mul (Expression.const (-1)) (Expression.var w))

theorem pairDiff_eval (v w : Variable) (env : Variable → ZMod p) :
    (pairDiff v w).eval env = env v - env w := by
  simp only [pairDiff, Expression.eval]; ring

/-- If `L` is a two-term form `ca·a + cb·b` with `ca + cb = 0`, extract `(v, w, k)` with the
    smaller-`val` coefficient as `k`, oriented so `L = k·v − k·w`. -/
def twoTermParts (L : LinExpr p) : Option (Variable × Variable × ZMod p) :=
  if L.const = 0 then
    match L.terms with
    | [(a, ca), (b, cb)] =>
      if ca + cb = 0 then
        if ca.val ≤ cb.val then some (a, b, ca) else some (b, a, cb)
      else none
    | _ => none
  else none

theorem twoTermParts_eval (L : LinExpr p) (v w : Variable) (k : ZMod p)
    (h : twoTermParts L = some (v, w, k)) (env : Variable → ZMod p) :
    L.eval env = k * env v - k * env w := by
  obtain ⟨cst, terms⟩ := L
  unfold twoTermParts at h
  by_cases hconst : cst = 0
  · rw [if_pos hconst] at h
    rcases terms with _ | ⟨⟨a, ca⟩, _ | ⟨⟨b, cb⟩, _ | rest⟩⟩
    · simp at h
    · simp at h
    · -- terms = [(a, ca), (b, cb)]
      dsimp only at h
      by_cases hsum : ca + cb = 0
      · rw [if_pos hsum] at h
        by_cases hle : ca.val ≤ cb.val
        · rw [if_pos hle] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [LinExpr.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          linear_combination hconst + (env b) * hsum
        · rw [if_neg hle] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [LinExpr.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          linear_combination hconst + (env a) * hsum
      · rw [if_neg hsum] at h; simp at h
    · simp at h
  · rw [if_neg hconst] at h; simp at h

/-- A single slot's two-term seed: the emptied difference `v − w` when payload slot `i` linearizes to
    `k·v − k·w`, has a byte bound `B2`, and both variables are bounded so `two_term_zero` applies. -/
def pair2SeedAt {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (bi : BusInteraction (Expression p)) (mval : ZMod p) (i : Nat) : Option (Expression p) :=
  if 0 < p then
    match bi.payload[i]?, facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) i with
    | some e, some B2 =>
      match linearize e with
      | some L =>
        match twoTermParts L with
        | some (v, w, k) =>
          match findVarBound bs facts cs.busInteractions v,
                findVarBound bs facts cs.busInteractions w with
          | some Bv, some Bw =>
            if 1 ≤ B2 ∧ B2 ≤ k.val ∧ k.val * (max Bv Bw - 1) ≤ p - B2 then
              some (pairDiff v w)
            else none
          | _, _ => none
        | none => none
      | none => none
    | _, _ => none
  else none

theorem pair2SeedAt_sound {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (bi : BusInteraction (Expression p)) (mval : ZMod p) (i : Nat) (e : Expression p)
    (hmc : bi.multiplicity.constValue? = some mval) (hmz : mval ≠ 0)
    (h : pair2SeedAt facts cs bi mval i = some e) (env : Variable → ZMod p)
    (hsat : cs.satisfies bs env) (hbi : bi ∈ cs.busInteractions) : e.eval env = 0 := by
  have hbus : ∀ bi' ∈ cs.busInteractions, (bi'.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi'.eval env) = false := fun bi' hbi' => hsat.2 bi' hbi'
  unfold pair2SeedAt at h
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp at h
    · exact hp
  rw [if_pos hp0] at h
  haveI : NeZero p := ⟨by omega⟩
  cases hpe : bi.payload[i]? with
  | none => rw [hpe] at h; simp at h
  | some ei =>
    cases hsb : facts.slotBound bi.busId mval (bi.payload.map Expression.constValue?) i with
    | none => rw [hpe, hsb] at h; simp at h
    | some B2 =>
      rw [hpe, hsb] at h
      cases hL : linearize ei with
      | none => simp only [hL] at h; simp at h
      | some L =>
        cases htt : twoTermParts L with
        | none => simp only [hL, htt] at h; simp at h
        | some vwk =>
          obtain ⟨v, w, k⟩ := vwk
          cases hbv : findVarBound bs facts cs.busInteractions v with
          | none => simp only [hL, htt, hbv] at h; simp at h
          | some Bv =>
            cases hbw : findVarBound bs facts cs.busInteractions w with
            | none => simp only [hL, htt, hbv, hbw] at h; simp at h
            | some Bw =>
              simp only [hL, htt, hbv, hbw] at h
              split at h
              · rename_i hcond
                obtain ⟨hB2, hkB2, hnw⟩ := hcond
                simp only [Option.some.injEq] at h
                subst h
                -- the interaction is active, hence accepted
                have hmeval : (bi.eval env).multiplicity = mval :=
                  bi.multiplicity.constValue?_sound mval hmc env
                have hviol : bs.violatesConstraint (bi.eval env) = false := by
                  apply hbus bi hbi; rw [hmeval]; exact hmz
                -- the slot value `ei.eval env` is bounded by `B2`
                have hget : (bi.eval env).payload[i]? = some (ei.eval env) := by
                  show (bi.payload.map (fun t => t.eval env))[i]? = some (ei.eval env)
                  rw [List.getElem?_map, hpe]; rfl
                have hsb' : facts.slotBound (bi.eval env).busId (bi.eval env).multiplicity
                    (bi.payload.map Expression.constValue?) i = some B2 := by
                  show facts.slotBound bi.busId (bi.eval env).multiplicity _ i = some B2
                  rw [hmeval]; exact hsb
                have hbound : (ei.eval env).val < B2 :=
                  facts.slotBound_sound (bi.eval env) (bi.payload.map Expression.constValue?) i B2
                    (ei.eval env) hsb' (matches_evalPattern bi.payload env) hviol hget
                -- `ei.eval env = k·v − k·w`
                have heq : ei.eval env = k * env v - k * env w := by
                  rw [linearize_eval ei L hL env, twoTermParts_eval L v w k htt env]
                rw [heq] at hbound
                -- bounds on v, w
                have hvb : (env v).val < Bv :=
                  findVarBound_sound bs facts cs.busInteractions v Bv hbv env hbus
                have hwb : (env w).val < Bw :=
                  findVarBound_sound bs facts cs.busInteractions w Bw hbw env hbus
                have hvB : (env v).val < max Bv Bw := lt_of_lt_of_le hvb (le_max_left _ _)
                have hwB : (env w).val < max Bv Bw := lt_of_lt_of_le hwb (le_max_right _ _)
                have := two_term_zero (env v) (env w) k (max Bv Bw) B2 hvB hwB hB2 hkB2 hnw hbound
                rw [pairDiff_eval]; rw [this]; ring
              · exact absurd h (by simp)

/-- Every two-term seed over the whole system (one per forceable byte slot). -/
def pair2Seeds {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (Expression p) :=
  cs.busInteractions.flatMap (fun bi =>
    match bi.multiplicity.constValue? with
    | some mval => if mval = 0 then [] else
        (List.range bi.payload.length).filterMap (pair2SeedAt facts cs bi mval)
    | none => [])

theorem pair2Seeds_sound {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (env : Variable → ZMod p) (hsat : cs.satisfies bs env) :
    ∀ e ∈ pair2Seeds facts cs, e.eval env = 0 := by
  intro e he
  unfold pair2Seeds at he
  rw [List.mem_flatMap] at he
  obtain ⟨bi, hbi, he2⟩ := he
  cases hmc : bi.multiplicity.constValue? with
  | none => simp only [hmc] at he2; simp at he2
  | some mval =>
    simp only [hmc] at he2
    by_cases hmz : mval = 0
    · rw [if_pos hmz] at he2; simp at he2
    · rw [if_neg hmz] at he2
      rw [List.mem_filterMap] at he2
      obtain ⟨i, _, hseed⟩ := he2
      exact pair2SeedAt_sound facts cs bi mval i e hmc hmz hseed env hsat hbi

/-- Combined soundness of the single-variable and two-term seeds. -/
theorem allSeeds_sound {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (env : Variable → ZMod p) (hsat : cs.satisfies bs env) :
    ∀ e ∈ scaledZeroSeeds facts cs ++ pair2Seeds facts cs, e.eval env = 0 := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact scaledZeroSeeds_sound facts cs env hsat e h
  · exact pair2Seeds_sound facts cs env hsat e h

/-- The pass: add the entailed `v = 0` (single scaled variable) and `v − w = 0` (two-term scaled
    slot) for every candidate the byte bounds pin. -/
def scaledZeroPass : VerifiedPassW p := fun cs bs facts =>
  let seeds := scaledZeroSeeds facts cs ++ pair2Seeds facts cs
  let new := seeds.filter (fun e => e.vars.all (fun z => cs.vars.contains z))
  if new.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
  else
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
     cs.addConstraints_correct bs new
       (fun env _ hsat e he => allSeeds_sound facts cs env hsat e (List.mem_of_mem_filter he))
       (fun e he z hz => by
         have hp := (List.mem_filter.1 he).2
         simp only [List.all_eq_true] at hp
         exact List.contains_iff_mem.mp (hp z hz))⟩

end ScaledZero
