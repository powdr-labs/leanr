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

/-- The pass: add the entailed `v = 0` for every candidate the joint byte bounds pin to zero. -/
def scaledZeroPass : VerifiedPassW p := fun cs bs facts =>
  let seeds := scaledZeroSeeds facts cs
  let new := seeds.filter (fun e => e.vars.all (fun z => cs.vars.contains z))
  if new.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
  else
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
     cs.addConstraints_correct bs new
       (fun env _ hsat e he => scaledZeroSeeds_sound facts cs env hsat e (List.mem_of_mem_filter he))
       (fun e he z hz => by
         have hp := (List.mem_filter.1 he).2
         simp only [List.all_eq_true] at hp
         exact List.contains_iff_mem.mp (hp z hz))⟩

end ScaledZero
