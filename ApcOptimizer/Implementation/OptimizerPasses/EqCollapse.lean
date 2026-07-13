import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse

set_option autoImplicit false

/-! # Sum-of-squares byte no-wrap (crux lemma for the is-equal gadget collapse, C5-eq)

The is-equal gadget `Σᵢ (aᵢ − bᵢ)·dimᵢ = cmp` (with `aᵢ`, `bᵢ` byte-bounded and `dimᵢ` fresh
inverse-hint witnesses) collapses — powdr-style — to `(Σᵢ (aᵢ − bᵢ)²)·inv = cmp`, dropping the
`dimᵢ`. The completeness branch (`Σ (aᵢ−bᵢ)² = 0`) needs: **a sum of squares of byte-differences that
is zero (in the field) forces every difference to be zero** — sound because each `(aᵢ − bᵢ)²` has
value `< 256²`, so the sum can't wrap for a small number of limbs. This file proves that arithmetic
fact; the pass and its reencode correctness build on it. -/

namespace EqCollapse

variable {p : ℕ}

/-- The square of a difference of two byte-bounded field elements is the cast of a natural number
    `< 256²`. -/
theorem sq_diff_cast [NeZero p] (a b : ZMod p) (ha : a.val < 256) (hb : b.val < 256) :
    ∃ m : Nat, m < 65536 ∧ (a - b) ^ 2 = (m : ZMod p) := by
  by_cases h : b.val ≤ a.val
  · refine ⟨(a.val - b.val) * (a.val - b.val), ?_, ?_⟩
    · have hlt : a.val - b.val < 256 := by omega
      calc (a.val - b.val) * (a.val - b.val) < 256 * 256 :=
            Nat.mul_lt_mul_of_lt_of_le hlt (le_of_lt hlt) (by norm_num)
        _ = 65536 := by norm_num
    · have hd : ((a.val - b.val : Nat) : ZMod p) = a - b := by
        rw [Nat.cast_sub h, ZMod.natCast_rightInverse a, ZMod.natCast_rightInverse b]
      rw [Nat.cast_mul, hd]; ring
  · have h' : a.val ≤ b.val := le_of_lt (Nat.lt_of_not_le h)
    refine ⟨(b.val - a.val) * (b.val - a.val), ?_, ?_⟩
    · have hlt : b.val - a.val < 256 := by omega
      calc (b.val - a.val) * (b.val - a.val) < 256 * 256 :=
            Nat.mul_lt_mul_of_lt_of_le hlt (le_of_lt hlt) (by norm_num)
        _ = 65536 := by norm_num
    · have hd : ((b.val - a.val : Nat) : ZMod p) = b - a := by
        rw [Nat.cast_sub h', ZMod.natCast_rightInverse b, ZMod.natCast_rightInverse a]
      rw [Nat.cast_mul, hd]; ring

/-- Value of the square of a byte-difference is `< 256²`. -/
theorem sq_diff_val [NeZero p] (hp : 65536 ≤ p) (a b : ZMod p)
    (ha : a.val < 256) (hb : b.val < 256) :
    ((a - b) ^ 2).val < 65536 := by
  obtain ⟨m, hm, hmeq⟩ := sq_diff_cast a b ha hb
  rw [hmeq, ZMod.val_natCast_of_lt (lt_of_lt_of_le hm hp)]
  exact hm

/-- The square of a byte-difference is zero iff the two bytes are equal. -/
theorem sq_diff_zero_iff [Fact p.Prime] (a b : ZMod p) :
    (a - b) ^ 2 = 0 ↔ a = b := by
  rw [pow_eq_zero_iff (n := 2) (by norm_num), sub_eq_zero]

/-- **Sum-of-squares byte no-wrap.** If each `(aᵢ, bᵢ)` is byte-bounded and there are few enough
    limbs that the value-sum stays below `p`, then `Σᵢ (aᵢ − bᵢ)² = 0` (in the field) forces every
    `aᵢ = bᵢ`. -/
theorem sumSq_zero_all_eq [Fact p.Prime] (hp : 65536 ≤ p)
    (L : List (ZMod p × ZMod p))
    (hbound : ∀ ab ∈ L, ab.1.val < 256 ∧ ab.2.val < 256)
    (hfit : L.length * 65536 < p)
    (h0 : (L.map (fun ab => (ab.1 - ab.2) ^ 2)).sum = 0) :
    ∀ ab ∈ L, ab.1 = ab.2 := by
  haveI : NeZero p := ⟨by omega⟩
  set M := L.map (fun ab => (ab.1 - ab.2) ^ 2) with hM
  have hfitSum : (M.map (fun x => x.val)).sum < p := by
    have hbnd : ∀ x ∈ M, x.val ≤ 65536 := by
      intro x hx
      obtain ⟨ab, hab, rfl⟩ := List.mem_map.1 hx
      exact le_of_lt (sq_diff_val hp ab.1 ab.2 (hbound ab hab).1 (hbound ab hab).2)
    calc (M.map (fun x => x.val)).sum
        ≤ (M.map (fun x => x.val)).length • 65536 := by
          apply List.sum_le_card_nsmul
          intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          exact hbnd x hx
      _ = L.length * 65536 := by rw [List.length_map, hM, List.length_map, smul_eq_mul]
      _ < p := hfit
  have hall := sum_zero_all_zero (by omega) M hfitSum h0
  intro ab hab
  have hz : (ab.1 - ab.2) ^ 2 = 0 := hall _ (List.mem_map.2 ⟨ab, hab, rfl⟩)
  exact (sq_diff_zero_iff ab.1 ab.2).1 hz

/-- Per-element form: field elements whose squares each have value `< 256²` and whose squares sum
    (in the field) to zero are all zero. -/
theorem sumSq_zero_all_zero' [Fact p.Prime] (hp : 65536 ≤ p) (L : List (ZMod p))
    (hbnd : ∀ d ∈ L, ((d ^ 2).val < 65536)) (hfit : L.length * 65536 < p)
    (h0 : (L.map (fun d => d ^ 2)).sum = 0) : ∀ d ∈ L, d = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  have hfitSum : ((L.map (fun d => d ^ 2)).map (fun x => x.val)).sum < p := by
    calc ((L.map (fun d => d ^ 2)).map (fun x => x.val)).sum
        ≤ ((L.map (fun d => d ^ 2)).map (fun x => x.val)).length • 65536 := by
          apply List.sum_le_card_nsmul
          intro y hy
          obtain ⟨sq, hsq, rfl⟩ := List.mem_map.1 hy
          obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hsq
          exact le_of_lt (hbnd d hd)
      _ = L.length * 65536 := by rw [List.length_map, List.length_map, smul_eq_mul]
      _ < p := hfit
  have hall := sum_zero_all_zero (by omega) (L.map (fun d => d ^ 2)) hfitSum h0
  intro d hd
  have : d ^ 2 = 0 := hall _ (List.mem_map.2 ⟨d, hd, rfl⟩)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-! ## Non-uniform marker reassignment and the sum-of-squares collapse identity -/

/-- `Σᵢ diffᵢ²` as an expression. -/
def sumSqExpr (diffs : List (Expression p)) : Expression p :=
  sumExpr (diffs.map (fun d => Expression.mul d d))

theorem sumSqExpr_eval (diffs : List (Expression p)) (env : Variable → ZMod p) :
    (sumSqExpr diffs).eval env = (diffs.map (fun d => (d.eval env) ^ 2)).sum := by
  rw [sumSqExpr, sumExpr_eval, List.map_map]
  congr 1
  apply List.map_congr_left
  intro d _; simp [Expression.eval, sq]

theorem sumSqExpr_vars {diffs : List (Expression p)} {x : Variable}
    (hx : x ∈ (sumSqExpr diffs).vars) : ∃ d ∈ diffs, x ∈ d.vars := by
  obtain ⟨c, hc, hxc⟩ := sumExpr_vars hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  simp only [Expression.vars, List.mem_append] at hxc
  exact ⟨d, hd, hxc.elim id id⟩

/-- Set each variable listed in the association list `assoc` to its paired value (outer pairs win),
    leaving the rest at `env`. -/
def setMarkers : List (Variable × ZMod p) → (Variable → ZMod p) → (Variable → ZMod p)
  | [], env => env
  | (d, w) :: rest, env => Function.update (setMarkers rest env) d w

/-- Value at a variable not among the association keys is unchanged. -/
theorem setMarkers_not_key (assoc : List (Variable × ZMod p)) (env : Variable → ZMod p)
    (x : Variable) (hx : x ∉ assoc.map Prod.fst) : setMarkers assoc env x = env x := by
  induction assoc with
  | nil => rfl
  | cons dw rest ih =>
    obtain ⟨d, w⟩ := dw
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    show Function.update (setMarkers rest env) d w x = env x
    rw [Function.update_of_ne hx.1, ih hx.2]

/-- An expression free of every association key is unaffected by `setMarkers`. -/
theorem setMarkers_free (assoc : List (Variable × ZMod p)) (env : Variable → ZMod p)
    (e : Expression p) (h : ∀ v ∈ assoc.map Prod.fst, v ∉ e.vars) :
    e.eval (setMarkers assoc env) = e.eval env :=
  Expression.eval_congr e _ _ (fun x hx =>
    setMarkers_not_key assoc env x (fun hk => h x hk hx))

/-- Value at a listed key (keys distinct): the paired value. -/
theorem setMarkers_key (assoc : List (Variable × ZMod p)) (env : Variable → ZMod p)
    (hnodup : (assoc.map Prod.fst).Nodup) (d : Variable) (w : ZMod p) (hmem : (d, w) ∈ assoc) :
    setMarkers assoc env d = w := by
  induction assoc with
  | nil => simp at hmem
  | cons dw rest ih =>
    obtain ⟨d', w'⟩ := dw
    simp only [List.map_cons, List.nodup_cons] at hnodup
    show Function.update (setMarkers rest env) d' w' d = w
    rcases List.mem_cons.1 hmem with h | h
    · rw [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [Function.update_self]
    · have hdmem : d ∈ rest.map Prod.fst := List.mem_map.2 ⟨(d, w), h, rfl⟩
      have hdd' : d ≠ d' := fun heq => hnodup.1 (heq ▸ hdmem)
      rw [Function.update_of_ne hdd']; exact ih hnodup.2 h

/-- `foldr (+) 0` of a mapped list is the sum of the map. -/
theorem foldr_add_eq_sum {α : Type} (f : α → ZMod p) (l : List α) :
    l.foldr (fun a acc => f a + acc) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

/-- Positional zip membership: `(c, d) ∈ diffs.zip D` gives `(d, f c) ∈ D.zip (diffs.map f)`. -/
theorem zip_pair_mem {α β γ : Type} (f : α → γ) (diffs : List α) (D : List β)
    (c : α) (d : β) (h : (c, d) ∈ diffs.zip D) : (d, f c) ∈ D.zip (diffs.map f) := by
  induction diffs generalizing D with
  | nil => simp at h
  | cons a as ih =>
    cases D with
    | nil => simp at h
    | cons b bs =>
      rw [List.zip_cons_cons, List.mem_cons] at h
      rw [List.map_cons, List.zip_cons_cons, List.mem_cons]
      rcases h with h | h
      · rw [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
      · exact Or.inr (ih bs h)

/-- Foldr-sum of the peel terms under the non-uniform reassignment `dimᵢ := diffᵢ·w`. -/
theorem foldr_setMarkers_sq (diffs : List (Expression p)) (D : List Variable)
    (env : Variable → ZMod p) (w : ZMod p)
    (hlen : diffs.length = D.length) (hnodup : D.Nodup)
    (hDdiffs : ∀ d ∈ D, ∀ df ∈ diffs, d ∉ df.vars) :
    ((diffs.zip D).foldr (fun cd acc =>
        cd.1.eval (setMarkers (D.zip (diffs.map (fun df => df.eval env * w))) env)
          * setMarkers (D.zip (diffs.map (fun df => df.eval env * w))) env cd.2 + acc) 0)
      = (diffs.map (fun df => (df.eval env) ^ 2)).sum * w := by
  set assoc := D.zip (diffs.map (fun df => df.eval env * w)) with hassoc
  have hkeys : assoc.map Prod.fst = D := by
    rw [hassoc, List.map_fst_zip]; rw [List.length_map]; omega
  have hnd : (assoc.map Prod.fst).Nodup := by rw [hkeys]; exact hnodup
  rw [foldr_add_eq_sum]
  -- each zip term equals `(cd.1.eval env)² · w`
  have hterm : (diffs.zip D).map
      (fun cd => cd.1.eval (setMarkers assoc env) * setMarkers assoc env cd.2)
      = (diffs.zip D).map (fun cd => (cd.1.eval env) ^ 2 * w) := by
    apply List.map_congr_left
    intro cd hcd
    obtain ⟨c, d⟩ := cd
    have hc : c ∈ diffs := (List.of_mem_zip hcd).1
    have hd : d ∈ D := (List.of_mem_zip hcd).2
    have hce : c.eval (setMarkers assoc env) = c.eval env :=
      setMarkers_free assoc env c (by rw [hkeys]; exact fun d' hd' => hDdiffs d' hd' c hc)
    have hde : setMarkers assoc env d = c.eval env * w :=
      setMarkers_key assoc env hnd d _ (by rw [hassoc]; exact zip_pair_mem _ diffs D c d hcd)
    simp only [hce, hde]; ring
  rw [hterm]
  -- sum over the zip depends only on the (full) `diffs`
  rw [show (diffs.zip D).map (fun cd => (cd.1.eval env) ^ 2 * w)
        = diffs.map (fun df => (df.eval env) ^ 2 * w) by
        rw [show (fun cd : Expression p × Variable => (cd.1.eval env) ^ 2 * w)
              = (fun df : Expression p => (df.eval env) ^ 2 * w) ∘ Prod.fst from rfl,
          ← List.map_map, List.map_fst_zip (by omega)]]
  rw [List.sum_map_mul_right]

/-- The soundness reconstruction: set each marker `dimᵢ := (diffᵢ.eval env)·(env inv)`. -/
def reconEnv (diffs : List (Expression p)) (D : List Variable) (inv : Variable)
    (env : Variable → ZMod p) : Variable → ZMod p :=
  setMarkers (D.zip (diffs.map (fun df => df.eval env * env inv))) env

/-- **The sum-of-squares collapse is a verified pass.** Replacing the target constraint
    `E = Σᵢ diffᵢ·dimᵢ + rest` by `E' = (Σᵢ diffᵢ²)·inv + rest` and dropping the once-occurring
    witnesses `D = [dimᵢ]` (with `inv = QuotientOrZero(−rest, Σ diffᵢ²)` a fresh derived column) is
    `PassCorrect`. Mirrors `HintCollapse.collapse_correct`, but the soundness reconstruction is the
    **non-uniform** `dimᵢ := diffᵢ·inv` (via `reconEnv`), so `Σ diffᵢ·(diffᵢ·inv) = (Σdiffᵢ²)·inv`
    recovers `E`. The `denom = 0` completeness branch is discharged by `hbyte`. -/
theorem collapseSq_correct [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (E rest : Expression p) (diffs : List (Expression p)) (D : List Variable) (inv : Variable)
    (hE : E ∈ cs.algebraicConstraints)
    (hpeel : peel D E = (diffs, rest))
    (hlen : diffs.length = D.length) (hnodup : D.Nodup)
    (hbyte : ∀ env, cs.satisfies bs env → (sumSqExpr diffs).eval env = 0 → rest.eval env = 0)
    (hinv_fresh : inv ∉ cs.vars) (hinv_id : inv.powdrId? = none)
    (hDonce : ∀ d ∈ D, ∀ c ∈ cs.algebraicConstraints, d ∈ c.vars → c = E)
    (hDbus : ∀ d ∈ D, ∀ bi ∈ cs.busInteractions,
      d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars)
    (hDdiffs : ∀ d ∈ D, ∀ df ∈ diffs, d ∉ df.vars) (hDrest : ∀ d ∈ D, d ∉ rest.vars)
    (hden_free : inv ∉ (sumSqExpr diffs).vars) (hrest_free : inv ∉ rest.vars)
    (hden_sub : ∀ x ∈ (sumSqExpr diffs).vars, x ∈ cs.vars)
    (hrest_sub : ∀ x ∈ rest.vars, x ∈ cs.vars)
    (hden_pow : ∀ x ∈ (sumSqExpr diffs).vars, x.powdrId?.isSome)
    (hrest_pow : ∀ x ∈ rest.vars, x.powdrId?.isSome) :
    PassCorrect cs
      { algebraicConstraints :=
          cs.algebraicConstraints.map (fun c => if c = E then
            (Expression.add (Expression.mul (sumSqExpr diffs) (Expression.var inv)) rest) else c),
        busInteractions := cs.busInteractions }
      [(inv, ComputationMethod.quotientOrZero (Expression.mul (Expression.const (-1)) rest)
          (sumSqExpr diffs))]
      bs := by
  set denom : Expression p := sumSqExpr diffs with hdenomdef
  set E' : Expression p := Expression.add (Expression.mul denom (Expression.var inv)) rest with hE'
  set method : ComputationMethod p :=
    ComputationMethod.quotientOrZero (Expression.mul (Expression.const (-1)) rest) denom with hmeth
  set f : Expression p → Expression p := (fun c => if c = E then E' else c) with hf
  set out : ConstraintSystem p :=
    { algebraicConstraints := cs.algebraicConstraints.map f, busInteractions := cs.busInteractions }
    with hout
  have hE'eval : ∀ env : Variable → ZMod p,
      E'.eval env = denom.eval env * env inv + rest.eval env := fun env => rfl
  -- keys of the reconstruction association are exactly `D`.
  have hkeys : ∀ env : Variable → ZMod p,
      (D.zip (diffs.map (fun df => df.eval env * env inv))).map Prod.fst = D := by
    intro env; rw [List.map_fst_zip]; rw [List.length_map]; omega
  -- frame: an expression free of `D` is unaffected by the reconstruction.
  have hframe : ∀ (env : Variable → ZMod p) (c : Expression p), (∀ d ∈ D, d ∉ c.vars) →
      c.eval (reconEnv diffs D inv env) = c.eval env := by
    intro env c hc
    exact setMarkers_free _ env c (by rw [hkeys env]; exact hc)
  -- the collapse identity: `E` at the reconstruction is `denom·inv + rest`.
  have hEeq : ∀ env : Variable → ZMod p,
      E.eval (reconEnv diffs D inv env) = denom.eval env * env inv + rest.eval env := by
    intro env
    unfold reconEnv
    rw [peel_eval D E, hpeel]
    simp only
    rw [foldr_setMarkers_sq diffs D env (env inv) hlen hnodup hDdiffs,
      setMarkers_free _ env rest (by rw [hkeys env]; exact hDrest),
      hdenomdef, sumSqExpr_eval]
  have hmemOut : ∀ c' ∈ out.algebraicConstraints, c' = E' ∨ c' ∈ cs.algebraicConstraints := by
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    by_cases h : c = E
    · exact Or.inl (by simp [hf, h])
    · exact Or.inr (by simpa [hf, h] using hc)
  have hE'mem : E' ∈ out.algebraicConstraints := List.mem_map.2 ⟨E, hE, by simp [hf]⟩
  -- every bus of `cs` is `D`-free: the reconstruction leaves its evaluation unchanged.
  have hbe : ∀ (env : Variable → ZMod p) (bi : BusInteraction (Expression p)),
      bi ∈ cs.busInteractions → bi.eval (reconEnv diffs D inv env) = bi.eval env := by
    intro env bi hbi
    have hbifree : ∀ d ∈ D, d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars :=
      fun d hd => hDbus d hd bi hbi
    unfold BusInteraction.eval
    congr 1
    · exact hframe _ _ (fun d hd => (hbifree d hd).1)
    · exact List.map_congr_left (fun e he => hframe _ _ (fun d hd => (hbifree d hd).2 e he))
  -- `out.satisfies env` ⇒ `cs` is satisfied at the reconstructed environment.
  have hcssat : ∀ env, out.satisfies bs env → cs.satisfies bs (reconEnv diffs D inv env) := by
    intro env hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · by_cases h : c = E
      · subst h
        rw [hEeq env]
        have hz : E'.eval env = 0 := hsat.1 E' hE'mem
        rw [hE'eval] at hz; exact hz
      · have hcvarsfree : ∀ d ∈ D, d ∉ c.vars := fun d hd hdc => h (hDonce d hd c hc hdc)
        rw [hframe env c hcvarsfree]
        have hfc : f c = c := by simp [hf, h]
        have hc0 := hsat.1 (f c) (List.mem_map.2 ⟨c, hc, rfl⟩)
        rwa [hfc] at hc0
    · rw [hbe env bi hbi]; exact hsat.2 bi hbi
  have hsound : out.implies cs bs := by
    intro env hsat
    refine ⟨reconEnv diffs D inv env, hcssat env hsat, ?_⟩
    have hse : cs.sideEffects bs (reconEnv diffs D inv env) = out.sideEffects bs env := by
      show (cs.busInteractions.filter _).map _ = (cs.busInteractions.filter _).map _
      exact List.map_congr_left (fun bi hbi => by rw [hbe env bi (List.mem_of_mem_filter hbi)])
    rw [hse]; exact BusState.equiv_refl _
  have hout_vars : ∀ v ∈ out.vars, v = inv ∨ v ∈ cs.vars := by
    intro v hv
    rcases ConstraintSystem.mem_vars.1 hv with ⟨c', hc', hvc⟩ | ⟨bi, hbi, hbiv⟩
    · rcases hmemOut c' hc' with rfl | hcs
      · rw [hE'] at hvc
        simp only [Expression.vars, List.mem_append, List.mem_singleton] at hvc
        rcases hvc with (hd | hi) | hr
        · exact Or.inr (hden_sub v hd)
        · exact Or.inl hi
        · exact Or.inr (hrest_sub v hr)
      · exact Or.inr (ConstraintSystem.mem_vars_of_constraint hcs hvc)
    · exact Or.inr (ConstraintSystem.mem_vars.2 (Or.inr ⟨bi, hbi, hbiv⟩))
  have hagreeC : ∀ (env : Variable → ZMod p) (x : Variable), x ∈ cs.vars →
      Function.update env inv (method.eval env) x = env x := by
    intro env x hx
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hinv_fresh hx
  refine ⟨hsound, ?_, ?_, ?_⟩
  · intro hcsInv env hsatOut bi hbiOut
    show (bi.eval env).multiplicity ≠ 0 → bs.breaksInvariant (bi.eval env) = false
    rw [← hbe env bi hbiOut]
    exact hcsInv (reconEnv diffs D inv env) (hcssat env hsatOut) bi hbiOut
  · intro v hvout hvpow
    rcases hout_vars v hvout with rfl | hcs
    · rw [hinv_id] at hvpow; exact absurd hvpow (by simp)
    · exact hcs
  · intro env hadm hsat
    set envC := Function.update env inv (method.eval env) with hCdef
    have hbeC : ∀ bi ∈ cs.busInteractions, bi.eval envC = bi.eval env := by
      intro bi hbi
      unfold BusInteraction.eval
      congr 1
      · exact Expression.eval_congr _ _ _ (fun x hx =>
          hagreeC env x (ConstraintSystem.mem_vars_of_mult hbi hx))
      · exact List.map_congr_left (fun e he => Expression.eval_congr _ _ _ (fun x hx =>
          hagreeC env x (ConstraintSystem.mem_vars_of_payload hbi he hx)))
    refine ⟨envC, ⟨fun c' hc' => ?_, fun bi hbi => ?_⟩, ?_, ?_, ?_, ?_⟩
    · rcases hmemOut c' hc' with rfl | hcs
      · rw [hE'eval]
        have hdenC : denom.eval envC = denom.eval env :=
          Expression.eval_congr _ _ _ (fun x hx => hagreeC env x (hden_sub x hx))
        have hrestC : rest.eval envC = rest.eval env :=
          Expression.eval_congr _ _ _ (fun x hx => hagreeC env x (hrest_sub x hx))
        rw [hdenC, hrestC, hCdef, Function.update_self, hmeth]
        by_cases hd0 : denom.eval env = 0
        · simp only [ComputationMethod.eval, hd0, if_true, mul_zero, zero_add]
          exact hbyte env hsat (by rw [hdenomdef] at hd0 ⊢; exact hd0)
        · simp only [ComputationMethod.eval, hd0, if_false, Expression.eval]
          rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]; ring
      · have hce : c'.eval envC = c'.eval env :=
          Expression.eval_congr _ _ _ (fun x hx =>
            hagreeC env x (ConstraintSystem.mem_vars_of_constraint hcs hx))
        rw [hce]; exact hsat.1 c' hcs
    · rw [hbeC bi hbi]; exact hsat.2 bi hbi
    · have hmapeq : (cs.busInteractions.map (fun bi => bi.eval envC))
          = (cs.busInteractions.map (fun bi => bi.eval env)) :=
        List.map_congr_left (fun bi hbi => hbeC bi hbi)
      show bs.admissible ((cs.busInteractions.map (fun bi => bi.eval envC)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
      rw [hmapeq]; exact hadm
    · have hse : cs.sideEffects bs env = out.sideEffects bs envC := by
        show (cs.busInteractions.filter _).map _ = (cs.busInteractions.filter _).map _
        exact List.map_congr_left (fun bi hbi => by rw [hbeC bi (List.mem_of_mem_filter hbi)])
      rw [hse]; exact BusState.equiv_refl _
    · intro v hvpow
      exact Function.update_of_ne
        (fun h => by rw [h, hinv_id] at hvpow; exact absurd hvpow (by simp)) _ _
    · intro inputVars hpowIn dsIn hrec v hvout hvnone
      by_cases hveq : v = inv
      · subst hveq
        have hmethfree : ∀ x ∈ method.vars, x ≠ v := by
          intro x hx
          rw [hmeth] at hx
          simp only [ComputationMethod.vars, Expression.vars, List.nil_append, List.mem_append] at hx
          rcases hx with hr | hd
          · exact fun h => hrest_free (h ▸ hr)
          · exact fun h => hden_free (h ▸ hd)
        refine ⟨method, ?_, ?_, ?_, ?_⟩
        · rw [Derivations.methodFor_append]; simp [Derivations.methodFor]
        · intro x hx
          rw [hmeth] at hx
          simp only [ComputationMethod.vars, Expression.vars, List.nil_append, List.mem_append] at hx
          rcases hx with hr | hd
          · exact hrest_pow x hr
          · exact hden_pow x hd
        · intro x hx
          rw [hmeth] at hx
          simp only [ComputationMethod.vars, Expression.vars, List.nil_append, List.mem_append] at hx
          rcases hx with hr | hd
          · exact hpowIn x (hrest_sub x hr) (hrest_pow x hr)
          · exact hpowIn x (hden_sub x hd) (hden_pow x hd)
        · rw [hCdef, Function.update_self]
          refine ComputationMethod.eval_congr method envC env (fun x hx => ?_)
          rw [hCdef]; exact Function.update_of_ne (hmethfree x hx) _ _
      · have hvcs : v ∈ cs.vars := (hout_vars v hvout).resolve_left hveq
        obtain ⟨cm, hmf, hcmpow, hcmin, hcmev⟩ := hrec v hvcs hvnone
        refine ⟨cm, ?_, hcmpow, hcmin, ?_⟩
        · rw [Derivations.methodFor_append]
          simp only [Derivations.methodFor, Option.orElse]
          rw [if_neg (fun h => hveq h.symm)]
          simpa using hmf
        · rw [hCdef, Function.update_of_ne hveq, ← hcmev]
          refine ComputationMethod.eval_congr cm envC env (fun x hx => ?_)
          have hxpow : x.powdrId?.isSome := hcmpow x hx
          have hxne : x ≠ inv := fun h => by rw [h, hinv_id] at hxpow; exact absurd hxpow (by simp)
          rw [hCdef]; exact Function.update_of_ne hxne _ _

/-! ## Recognizer: is-equal gadget coefficients as byte-differences -/

/-- A coefficient that is a difference of two variables `a − b` (the `peel`/`fold` shape of an
    is-equal gadget's `(aᵢ − bᵢ)·dimᵢ` term); returns `(a, b)`. -/
def diffVars : Expression p → Option (Variable × Variable)
  | .add (.var a) (.mul (.const c) (.var b)) => if c = -1 then some (a, b) else none
  | .add (.mul (.const c) (.var b)) (.var a) => if c = -1 then some (a, b) else none
  | _ => none

theorem diffVars_sound {c : Expression p} {a b : Variable} (h : diffVars c = some (a, b)) :
    (∀ env, c.eval env = env a - env b) ∧ (∀ x ∈ c.vars, x = a ∨ x = b) := by
  unfold diffVars at h
  split at h
  · split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; subst hc
    refine ⟨fun env => by simp only [Expression.eval]; ring, fun x hx => ?_⟩
    simp only [Expression.vars, List.mem_append, List.mem_singleton,
      List.nil_append] at hx
    tauto
  · split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; subst hc
    refine ⟨fun env => by simp only [Expression.eval]; ring, fun x hx => ?_⟩
    simp only [Expression.vars, List.mem_append, List.mem_singleton,
      List.nil_append] at hx
    tauto
  · exact absurd h (by simp)

/-- Each coefficient's `fold` is a byte-difference `a − b` (both `≤ 256` per the bounds map), is
    `D`-free, and reads only input columns. -/
def diffsByteOK (B : Std.HashMap Variable Nat) (D : List Variable) :
    List (Expression p) → Bool
  | [] => true
  | c :: cs =>
    (match diffVars c.fold with
     | some (a, b) =>
        (match B[a]? with | some ba => decide (ba ≤ 256) | none => false) &&
        (match B[b]? with | some bb => decide (bb ≤ 256) | none => false)
     | none => false) &&
    D.all (fun d => decide (d ∉ c.vars)) &&
    c.vars.all (fun x => x.powdrId?.isSome) &&
    diffsByteOK B D cs

theorem diffsByteOK_sound (B : Std.HashMap Variable Nat) (D : List Variable) :
    ∀ (coeffs : List (Expression p)), diffsByteOK B D coeffs = true →
      ∀ c ∈ coeffs, ∃ a b : Variable,
        (∀ env, c.eval env = env a - env b) ∧ (∀ d ∈ D, d ∉ c.vars) ∧
        (∀ x ∈ c.vars, x.powdrId?.isSome = true) ∧
        (∃ ba, B[a]? = some ba ∧ ba ≤ 256) ∧ (∃ bb, B[b]? = some bb ∧ bb ≤ 256) := by
  intro coeffs
  induction coeffs with
  | nil => intro _ c hc; simp at hc
  | cons c0 cs ih =>
      intro h c hc
      simp only [diffsByteOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hdv, hDf⟩, hpow⟩, hrec⟩ := h
      rcases List.mem_cons.1 hc with rfl | hcs
      · cases hdva : diffVars c.fold with
        | none => rw [hdva] at hdv; simp at hdv
        | some ab =>
            obtain ⟨a, b⟩ := ab
            simp only [hdva, Bool.and_eq_true] at hdv
            obtain ⟨hba, hbb⟩ := hdv
            have hfold := diffVars_sound hdva
            refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
            · intro env; rw [← Expression.fold_eval c env]; exact hfold.1 env
            · intro d hd; exact of_decide_eq_true (List.all_eq_true.1 hDf d hd)
            · intro x hx; exact List.all_eq_true.1 hpow x hx
            · revert hba; cases hb : B[a]? with
              | none => intro hba; simp at hba
              | some ba => intro hba; exact ⟨ba, rfl, of_decide_eq_true hba⟩
            · revert hbb; cases hb : B[b]? with
              | none => intro hbb; simp at hbb
              | some bb => intro hbb; exact ⟨bb, rfl, of_decide_eq_true hbb⟩
      · exact ih hrec c hcs

/-! ## The pass -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Core collapse on an *opaque* peel result `(co, rst)` — abstracting the peeled lists as
    parameters keeps `peel`/`D` out of `whnf` (they never get expanded by `omega`/`simp`). -/
def collapseCore [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bm : BoundsMap p cs bs) (E : Expression p) (hE : E ∈ cs.algebraicConstraints)
    (D : List Variable) (inv : Variable) (hnodup : D.Nodup) (hinv_id : inv.powdrId? = none)
    (hEvarsub : ∀ x ∈ E.vars, x ∈ cs.vars)
    (hDonce : ∀ d ∈ D, ∀ c ∈ cs.algebraicConstraints, d ∈ c.vars → c = E)
    (hDbus : ∀ d ∈ D, ∀ bi ∈ cs.busInteractions,
      d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars)
    (co : List (Expression p)) (rst : Expression p)
    (hpe : peel D E = (co, rst)) (hlen : co.length = D.length)
    (hcoEsub : ∀ c ∈ co, ∀ x ∈ c.vars, x ∈ E.vars)
    (hrstEsub : ∀ x ∈ rst.vars, x ∈ E.vars) : Option (PassResult cs bs) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hco : (peel D E).1 = co := congrArg Prod.fst hpe
  have hrs : (peel D E).2 = rst := congrArg Prod.snd hpe
  by_cases hchk : (decide (2 ≤ D.length) && (diffsByteOK Bm.map D co &&
      (decide (∀ d ∈ D, d ∉ rst.vars) &&
      (decide (∀ x ∈ rst.vars, x.powdrId?.isSome = true) &&
      (decide (inv ∉ cs.vars) && decide (co.length * 65536 < p)))))) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨h2len, hbyteOK, hrfree, hrpow, hinvfresh, hfit⟩ := hchk
    have hp256 : 65536 ≤ p := by omega
    have hcfree : ∀ c ∈ co, ∀ d ∈ D, d ∉ c.vars := by
      intro c hc d hd
      obtain ⟨a, b, _, hDf, _, _, _⟩ := diffsByteOK_sound Bm.map D co hbyteOK c hc
      exact hDf d hd
    have hbyte : ∀ env, cs.satisfies bs env → (sumSqExpr co).eval env = 0 → rst.eval env = 0 := by
      intro env hsat hsq0
      have hE0 : E.eval env = 0 := hsat.1 E hE
      have hbnd : ∀ c ∈ co, (((c.eval env) ^ 2).val < 65536) := by
        intro c hc
        obtain ⟨a, b, heval, _, _, ⟨ba, hba, hba256⟩, ⟨bb, hbb, hbb256⟩⟩ :=
          diffsByteOK_sound Bm.map D co hbyteOK c hc
        have hla := Bm.sound env (fun bi hbi => hsat.2 bi hbi) a ba hba
        have hlb := Bm.sound env (fun bi hbi => hsat.2 bi hbi) b bb hbb
        rw [heval env]
        exact sq_diff_val hp256 (env a) (env b) (by omega) (by omega)
      have hsum' : ((co.map (fun c => c.eval env)).map (fun d => d ^ 2)).sum = 0 := by
        rw [List.map_map,
          show ((fun d : ZMod p => d ^ 2) ∘ fun c : Expression p => c.eval env)
            = (fun c : Expression p => (c.eval env) ^ 2) from rfl,
          ← sumSqExpr_eval]
        exact hsq0
      have hbnd' : ∀ d ∈ co.map (fun c => c.eval env), ((d ^ 2).val < 65536) := by
        intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd; exact hbnd c hc
      have hfit' : (co.map (fun c => c.eval env)).length * 65536 < p := by
        rw [List.length_map]; exact hfit
      have hallz : ∀ c ∈ co, c.eval env = 0 := by
        have hL : ∀ d ∈ co.map (fun c => c.eval env), d = 0 :=
          sumSq_zero_all_zero' hp256 _ hbnd' hfit' hsum'
        intro c hc
        exact hL (c.eval env) (List.mem_map_of_mem hc)
      have hfz' : (co.zip D).foldr (fun cd acc => cd.1.eval env * env cd.2 + acc) 0 = 0 :=
        foldr_zero (co.zip D) env (fun cd hcd => hallz cd.1 (List.of_mem_zip hcd).1)
      have hpev : E.eval env
          = (co.zip D).foldr (fun cd acc => cd.1.eval env * env cd.2 + acc) 0 + rst.eval env := by
        have h := peel_eval D E env
        rw [hco, hrs] at h; exact h
      rw [hpev, hfz', zero_add] at hE0
      exact hE0
    have hden_free : inv ∉ (sumSqExpr co).vars := by
      intro hx; obtain ⟨c, hc, hxc⟩ := sumSqExpr_vars hx
      exact hinvfresh (hEvarsub inv (hcoEsub c hc inv hxc))
    have hrest_free : inv ∉ rst.vars := fun hx => hinvfresh (hEvarsub inv (hrstEsub inv hx))
    have hden_sub : ∀ x ∈ (sumSqExpr co).vars, x ∈ cs.vars := by
      intro x hx; obtain ⟨c, hc, hxc⟩ := sumSqExpr_vars hx
      exact hEvarsub x (hcoEsub c hc x hxc)
    have hrest_sub : ∀ x ∈ rst.vars, x ∈ cs.vars := fun x hx => hEvarsub x (hrstEsub x hx)
    have hden_pow : ∀ x ∈ (sumSqExpr co).vars, x.powdrId?.isSome = true := by
      intro x hx; obtain ⟨c, hc, hxc⟩ := sumSqExpr_vars hx
      obtain ⟨a, b, _, _, hpow, _, _⟩ := diffsByteOK_sound Bm.map D co hbyteOK c hc
      exact hpow x hxc
    exact some ⟨_, _, collapseSq_correct cs bs E rst co D inv hE hpe hlen
      hnodup hbyte hinvfresh hinv_id hDonce hDbus (fun d hd df hdf => hcfree df hdf d hd) hrfree
      hden_free hrest_free hden_sub hrest_sub hden_pow hrpow⟩
  · exact none

/-- Try to collapse the is-equal gadget with target constraint `E`: derive the witnesses `D`
    (once-in-`E`, non-bus) and hand the peeled coefficients to `collapseCore` as opaque data. -/
def tryOneEq [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bm : BoundsMap p cs bs) (busVars : Std.HashSet Variable)
    (E : Expression p) (hE : E ∈ cs.algebraicConstraints) : Option (PassResult cs bs) := by
  classical
  set D := E.vars.dedup.filter (fun v =>
    !busVars.contains v && occursOnlyInTarget cs E v) with hD
  have hnodup : D.Nodup := by rw [hD]; exact (List.nodup_dedup _).filter _
  have hEvarsub : ∀ x ∈ E.vars, x ∈ cs.vars := fun x hx =>
    ConstraintSystem.mem_vars_of_constraint hE hx
  have hDcert : ∀ d ∈ D, occursOnlyInTarget cs E d = true := by
    intro d hd
    have h := (List.mem_filter.1 (hD ▸ hd)).2
    simp only [Bool.and_eq_true] at h
    exact h.2
  exact collapseCore cs bs Bm E hE D ⟨"eqinv#" ++ (D.headD ⟨"_", none⟩).name, none⟩ hnodup rfl
    hEvarsub (fun d hd => occursOnlyInTarget_constr (hDcert d hd))
    (fun d hd => occursOnlyInTarget_bus (hDcert d hd))
    (peel D E).1 (peel D E).2 rfl (peel_length D E)
    (fun c hc x hx => peel_fst_vars D E c hc x hx)
    (fun x hx => peel_snd_vars D E x hx)

/-- Scan a constraint sublist for the first collapsible is-equal target. -/
def tryListEq [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bm : BoundsMap p cs bs) (busVars : Std.HashSet Variable) :
    (L : List (Expression p)) → (∀ E ∈ L, E ∈ cs.algebraicConstraints) → Option (PassResult cs bs)
  | [], _ => none
  | E :: rest, hmem =>
    match tryOneEq cs bs Bm busVars E (hmem E (List.mem_cons_self ..)) with
    | some r => some r
    | none => tryListEq cs bs Bm busVars rest (fun E' h => hmem E' (List.mem_cons_of_mem _ h))

/-- The is-equal collapse pass: replace the first byte-difference reciprocal-witness gadget
    `Σ (aᵢ−bᵢ)·dimᵢ + t` by the sum-of-squares form `(Σ (aᵢ−bᵢ)²)·inv + t` with a single derived
    inverse witness, dropping the `n−1` markers. Needs prime `p`; identity otherwise, and identity
    with `BusFacts.trivial` (no byte bounds ⇒ `diffsByteOK` fails). -/
def eqCollapsePass : VerifiedPassW p := fun cs bs facts =>
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    let Bm : BoundsMap p cs bs := BoundsMap.build facts
    let busVars : Std.HashSet Variable := cs.busInteractions.foldl (init := ∅) fun s bi =>
      bi.payload.foldl (fun s e => e.vars.foldl (·.insert ·) s)
        (bi.multiplicity.vars.foldl (·.insert ·) s)
    (tryListEq cs bs Bm busVars cs.algebraicConstraints (fun _ h => h)).getD
      ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

end EqCollapse
