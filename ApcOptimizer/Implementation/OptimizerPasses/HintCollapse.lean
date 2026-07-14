import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus

set_option autoImplicit false

/-! # Collapsing a multi-limb reciprocal-witness group to one hint (finishes powdr's `seqz`/`seq`)

A comparison gadget carries several fresh inverse-hint witnesses `dimᵢ` in one *bilinear*
constraint `Σᵢ coeffᵢ·dimᵢ + t = 0`, where the `dimᵢ` occur **only** here (pure witnesses) and each
`coeffᵢ` is byte-bounded. powdr keeps a **single** inverse hint. This pass performs that collapse.
Both the collapse *and* its correctness are captured once by `collapse_correct`, which replaces the
target `E` by `denom·inv + t` for a supplied denominator `denom`, a fresh derived witness
`inv = QuotientOrZero(−t, denom)`, and a reassignment `reasg env w` sending each `dimᵢ` to its share
of `w` so that `E` collapses to `denom·w + t`. Two instances share it:

* **Plain sum** (`is-zero`/`seqz`, `tryOne`): each `coeffᵢ` is a **single** byte-bounded variable
  `aᵢ` (via `BusFacts.slotBound`); `denom = Σᵢ aᵢ`, `reasg` sets every `dimᵢ := w`. Completeness's
  `denom = 0` branch closes because byte-bounded (non-negative) coefficients summing to `0` are all
  `0` — but this fails once coefficients can be negative.
* **Sum of squares** (`is-equal`, `tryOneSq`): each `coeffᵢ` is a byte-bounded **difference**
  `aᵢ − bᵢ`, so `Σ(aᵢ − bᵢ)` may vanish without every difference vanishing. Mirroring powdr, the
  denominator is instead `denom = Σᵢ (aᵢ − bᵢ)²` and `reasg` sets `dimᵢ := (aᵢ − bᵢ)·w`, so
  `Σ(aᵢ − bᵢ)·dimᵢ = (Σ(aᵢ − bᵢ)²)·w`. A zero sum of squares forces every difference to `0`
  (each square is `< 256²`, so the field sum cannot wrap and — `p` prime — each square, hence each
  difference, is `0`); the target constraint then pins `t = 0`.

In both cases `t` and the coefficients read only input (powdr-ID) columns and no bus is touched, so
side effects and `admissible` are unchanged. With `BusFacts.trivial` (no `slotBound`) neither
fires. -/

variable {p : ℕ}

/-! ## Splitting off the linear part in one variable -/

/-- Split `E` as `coeff · d + rest` in the single variable `d`. The eval identity below holds
    **unconditionally**; when `d` occurs at most once the returned `coeff`/`rest` are `d`-free
    (checked at the call site via `d ∉ ·.vars`). -/
def extractLinear (d : Variable) : Expression p → Expression p × Expression p
  | .const c => (.const 0, .const c)
  | .var x => if x = d then (.const 1, .const 0) else (.const 0, .var x)
  | .add e1 e2 =>
      let (c1, r1) := extractLinear d e1
      let (c2, r2) := extractLinear d e2
      (.add c1 c2, .add r1 r2)
  | .mul e1 e2 =>
      if d ∈ e1.vars then
        let (c1, r1) := extractLinear d e1
        (.mul c1 e2, .mul r1 e2)
      else
        let (c2, r2) := extractLinear d e2
        (.mul e1 c2, .mul e1 r2)

theorem extractLinear_eval (d : Variable) (E : Expression p) (env : Variable → ZMod p) :
    E.eval env = (extractLinear d E).1.eval env * env d + (extractLinear d E).2.eval env := by
  induction E with
  | const c => simp [extractLinear, Expression.eval]
  | var x =>
      by_cases h : x = d <;> simp [extractLinear, h, Expression.eval]
  | add e1 e2 ih1 ih2 =>
      simp only [extractLinear, Expression.eval]
      rw [ih1, ih2]; ring
  | mul e1 e2 ih1 ih2 =>
      simp only [extractLinear]
      split
      · simp only [Expression.eval]; rw [ih1]; ring
      · simp only [Expression.eval]; rw [ih2]; ring

/-- Peel every variable of `ds` off `E` in turn, returning the list of coefficients (one per `ds`
    entry) and the final remainder. The eval identity chains `extractLinear_eval`. -/
def peel : List Variable → Expression p → List (Expression p) × Expression p
  | [], E => ([], E)
  | d :: ds, E =>
      let (c, r) := extractLinear d E
      let (cs, rest) := peel ds r
      (c :: cs, rest)

theorem peel_eval (ds : List Variable) (E : Expression p) (env : Variable → ZMod p) :
    E.eval env
      = ((peel ds E).1.zip ds).foldr (fun cd acc => cd.1.eval env * env cd.2 + acc) 0
        + (peel ds E).2.eval env := by
  induction ds generalizing E with
  | nil => simp [peel]
  | cons d ds ih =>
      simp only [peel]
      rw [extractLinear_eval d E env, ih (extractLinear d E).2]
      simp only [List.zip_cons_cons, List.foldr_cons]
      ring

/-! ## A byte-bounded field sum that is zero forces every summand to zero -/

/-- If a list of field elements each has `.val < p` and their `.val`s sum to `< p`, the field sum's
    `.val` equals the natural-number sum (no wraparound). -/
theorem sum_val_eq (hp : 0 < p) :
    ∀ (L : List (ZMod p)), (L.map (fun x => x.val)).sum < p →
      L.sum.val = (L.map (fun x => x.val)).sum
  | [], _ => by simp
  | x :: rest, hfit => by
      haveI : NeZero p := ⟨hp.ne'⟩
      simp only [List.map_cons, List.sum_cons] at hfit ⊢
      have hrest : (rest.map (fun x => x.val)).sum < p := by omega
      have ih := sum_val_eq hp rest hrest
      have hadd : (x + rest.sum).val = x.val + rest.sum.val :=
        ZMod.val_add_of_lt (by rw [ih]; omega)
      rw [hadd, ih]

/-- Byte-bounded field elements summing (in the field) to `0`, with the value-sum below `p`, are all
    `0`. Used for the `Σ aᵢ = 0` completeness branch. -/
theorem sum_zero_all_zero (hp : 0 < p) (L : List (ZMod p))
    (hfit : (L.map (fun x => x.val)).sum < p) (h0 : L.sum = 0) :
    ∀ x ∈ L, x = 0 := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hval : (L.map (fun x => x.val)).sum = 0 := by
    have := sum_val_eq hp L hfit
    rw [h0] at this; simpa using this.symm
  intro x hx
  have hxval : x.val = 0 := by
    have : x.val ≤ (L.map (fun y => y.val)).sum :=
      List.single_le_sum (by intro _ _; exact Nat.zero_le _) _ (List.mem_map.2 ⟨x, hx, rfl⟩)
    omega
  exact (ZMod.val_eq_zero x).1 hxval

/-! ## Sum of expressions and the reassignment frame -/

/-- The expression `Σ l`. -/
def sumExpr (l : List (Expression p)) : Expression p := l.foldr Expression.add (Expression.const 0)

theorem sumExpr_eval (l : List (Expression p)) (env : Variable → ZMod p) :
    (sumExpr l).eval env = (l.map (fun c => c.eval env)).sum := by
  induction l with
  | nil => simp [sumExpr, Expression.eval]
  | cons c cs ih =>
      simp only [sumExpr, List.foldr_cons] at *
      simp only [Expression.eval, List.map_cons, List.sum_cons, ih]

theorem sumExpr_vars {l : List (Expression p)} {x : Variable}
    (hx : x ∈ (sumExpr l).vars) : ∃ c ∈ l, x ∈ c.vars := by
  induction l with
  | nil => simp [sumExpr, Expression.vars] at hx
  | cons c cs ih =>
      simp only [sumExpr, List.foldr_cons, Expression.vars, List.mem_append] at hx
      rcases hx with h | h
      · exact ⟨c, List.mem_cons_self .., h⟩
      · obtain ⟨c', hc', hx'⟩ := ih h
        exact ⟨c', List.mem_cons_of_mem _ hc', hx'⟩

/-- Reassign every variable of `D` to `w`, leaving the rest at `env`. -/
def reassign (D : List Variable) (w : ZMod p) (env : Variable → ZMod p) : Variable → ZMod p :=
  fun v => if v ∈ D then w else env v

/-- An expression free of every `D` variable is unaffected by reassigning `D`. -/
theorem eval_reassign_free (c : Expression p) (D : List Variable) (w : ZMod p)
    (env : Variable → ZMod p) (h : ∀ d ∈ D, d ∉ c.vars) :
    c.eval (reassign D w env) = c.eval env :=
  Expression.eval_congr c _ _ (fun x hx => by
    show (if x ∈ D then w else env x) = env x
    rw [if_neg (fun hxD => h x hxD hx)])

/-! ## `peel` structure: length, variable containment, and the collapse identity -/

theorem peel_length (D : List Variable) (E : Expression p) : (peel D E).1.length = D.length := by
  induction D generalizing E with
  | nil => simp [peel]
  | cons d ds ih => simp only [peel, List.length_cons]; rw [ih]

theorem extractLinear_vars (d : Variable) (E : Expression p) :
    (∀ x ∈ (extractLinear d E).1.vars, x ∈ E.vars) ∧
      (∀ x ∈ (extractLinear d E).2.vars, x ∈ E.vars) := by
  induction E with
  | const c => simp [extractLinear, Expression.vars]
  | var x => by_cases h : x = d <;> simp [extractLinear, h, Expression.vars]
  | add e1 e2 ih1 ih2 =>
      simp only [extractLinear, Expression.vars, List.mem_append]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> rcases hx with h | h
      · exact Or.inl (ih1.1 x h)
      · exact Or.inr (ih2.1 x h)
      · exact Or.inl (ih1.2 x h)
      · exact Or.inr (ih2.2 x h)
  | mul e1 e2 ih1 ih2 =>
      simp only [extractLinear]
      split <;> simp only [Expression.vars, List.mem_append] <;>
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> rcases hx with h | h
      · exact Or.inl (ih1.1 x h)
      · exact Or.inr h
      · exact Or.inl (ih1.2 x h)
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr (ih2.1 x h)
      · exact Or.inl h
      · exact Or.inr (ih2.2 x h)

theorem peel_snd_vars (D : List Variable) (E : Expression p) :
    ∀ x ∈ (peel D E).2.vars, x ∈ E.vars := by
  induction D generalizing E with
  | nil => simp [peel]
  | cons d ds ih =>
      intro x hx
      simp only [peel] at hx
      exact (extractLinear_vars d E).2 x (ih (extractLinear d E).2 x hx)

theorem peel_fst_vars (D : List Variable) (E : Expression p) :
    ∀ c ∈ (peel D E).1, ∀ x ∈ c.vars, x ∈ E.vars := by
  induction D generalizing E with
  | nil => simp [peel]
  | cons d ds ih =>
      intro c hc x hx
      simp only [peel, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact (extractLinear_vars d E).1 x hx
      · exact (extractLinear_vars d E).2 x (ih (extractLinear d E).2 c hc x hx)

/-- The `foldr` produced by `peel_eval`, evaluated at a `D`-reassignment, collapses to the coefficient
    sum times the common value (each coefficient is `D`-free, each second component is in `D`). -/
theorem foldr_reassign (pairs : List (Expression p × Variable)) (D : List Variable)
    (env : Variable → ZMod p) (w : ZMod p)
    (hmem : ∀ cd ∈ pairs, cd.2 ∈ D)
    (hfree : ∀ cd ∈ pairs, ∀ d ∈ D, d ∉ cd.1.vars) :
    pairs.foldr (fun cd acc => cd.1.eval (reassign D w env) * (reassign D w env) cd.2 + acc) 0
      = (pairs.map (fun cd => cd.1.eval env)).sum * w := by
  induction pairs with
  | nil => simp
  | cons cd rest ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      rw [ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
            (fun x hx => hfree x (List.mem_cons_of_mem _ hx))]
      have h1 : (reassign D w env) cd.2 = w := by
        show (if cd.2 ∈ D then w else env cd.2) = w
        rw [if_pos (hmem cd (List.mem_cons_self ..))]
      have h2 : cd.1.eval (reassign D w env) = cd.1.eval env :=
        eval_reassign_free cd.1 D w env (fun d hd => hfree cd (List.mem_cons_self ..) d hd)
      rw [h1, h2]; ring

/-- The collapse identity (`hEeq` for `collapse_correct`): setting every `D` variable to a common
    `w` turns `E` into `(Σ coeffs)·w + rest`, where `(coeffs, rest) = peel D E`. -/
theorem peel_reassign_eval (D : List Variable) (E : Expression p)
    (hcfree : ∀ c ∈ (peel D E).1, ∀ d ∈ D, d ∉ c.vars)
    (hrfree : ∀ d ∈ D, d ∉ (peel D E).2.vars)
    (env : Variable → ZMod p) (w : ZMod p) :
    E.eval (reassign D w env)
      = (sumExpr (peel D E).1).eval env * w + (peel D E).2.eval env := by
  have hz : ((peel D E).1.zip D).map (fun cd => cd.1.eval env)
      = (peel D E).1.map (fun c => c.eval env) := by
    have hlen : (peel D E).1.length ≤ D.length := by rw [peel_length]
    conv_rhs => rw [← List.map_fst_zip hlen, List.map_map]
    rfl
  rw [peel_eval D E (reassign D w env), eval_reassign_free _ D w env hrfree,
      foldr_reassign ((peel D E).1.zip D) D env w
        (fun cd hcd => (List.of_mem_zip hcd).2)
        (fun cd hcd d hd => hcfree cd.1 (List.of_mem_zip hcd).1 d hd),
      sumExpr_eval, hz]

/-- `foldr` of `peel_eval` vanishes when every coefficient evaluates to `0`. -/
theorem foldr_zero (pairs : List (Expression p × Variable)) (env : Variable → ZMod p)
    (h0 : ∀ cd ∈ pairs, cd.1.eval env = 0) :
    pairs.foldr (fun cd acc => cd.1.eval env * env cd.2 + acc) 0 = 0 := by
  induction pairs with
  | nil => simp
  | cons cd rest ih =>
      simp only [List.foldr_cons]
      rw [h0 cd (List.mem_cons_self ..), ih (fun x hx => h0 x (List.mem_cons_of_mem _ hx))]
      ring

/-! ## The core collapse, as an algebraic `PassCorrect` (peel-free; the pass discharges the facts) -/

/-- Replacing the target constraint `E` by `E' = denom·inv + rest` (with `inv` a fresh derived
    witness `= QuotientOrZero(−rest, denom)`) and dropping the once-occurring witnesses `D` is a
    verified pass. The two structural facts the pass supplies:
    `hEeq` — collapsing every `dᵢ` to a common value `w` turns `E` into `denom·w + rest`
    (the reciprocal-witness shape); and `hbyte` — when `denom` vanishes so does `rest` (byte-bounded
    coefficients summing to zero are all zero). Everything else is framing (freshness, the witnesses
    occurring only in `E`, and the new expressions reading only input columns). -/
theorem collapse_correct [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (E denom rest : Expression p) (D : List Variable) (inv : Variable)
    (reasg : (Variable → ZMod p) → ZMod p → (Variable → ZMod p))
    (hE : E ∈ cs.algebraicConstraints)
    (hagree : ∀ (env : Variable → ZMod p) (w : ZMod p) (v : Variable),
      v ∉ D → reasg env w v = env v)
    (hEeq : ∀ (env : Variable → ZMod p) (w : ZMod p),
      E.eval (reasg env w) = denom.eval env * w + rest.eval env)
    (hbyte : ∀ env, cs.satisfies bs env → denom.eval env = 0 → rest.eval env = 0)
    (hinv_fresh : inv ∉ cs.vars) (hinv_id : inv.powdrId? = none)
    (hDonce : ∀ d ∈ D, ∀ c ∈ cs.algebraicConstraints, d ∈ c.vars → c = E)
    (hDbus : ∀ d ∈ D, ∀ bi ∈ cs.busInteractions,
      d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars)
    (hden_free : inv ∉ denom.vars ∧ (∀ d ∈ D, d ∉ denom.vars))
    (hrest_free : inv ∉ rest.vars ∧ (∀ d ∈ D, d ∉ rest.vars))
    (hden_sub : ∀ x ∈ denom.vars, x ∈ cs.vars) (hrest_sub : ∀ x ∈ rest.vars, x ∈ cs.vars)
    (hden_pow : ∀ x ∈ denom.vars, x.powdrId?.isSome)
    (hrest_pow : ∀ x ∈ rest.vars, x.powdrId?.isSome) :
    PassCorrect cs
      { algebraicConstraints :=
          cs.algebraicConstraints.map (fun c => if c = E then
            (Expression.add (Expression.mul denom (Expression.var inv)) rest) else c),
        busInteractions := cs.busInteractions }
      [(inv, ComputationMethod.quotientOrZero (Expression.mul (Expression.const (-1)) rest) denom)]
      bs := by
  set E' : Expression p := Expression.add (Expression.mul denom (Expression.var inv)) rest with hE'
  set method : ComputationMethod p :=
    ComputationMethod.quotientOrZero (Expression.mul (Expression.const (-1)) rest) denom with hmeth
  set f : Expression p → Expression p := (fun c => if c = E then E' else c) with hf
  set out : ConstraintSystem p :=
    { algebraicConstraints := cs.algebraicConstraints.map f, busInteractions := cs.busInteractions }
    with hout
  -- `E'` evaluates as `denom·(env inv) + rest`.
  have hE'eval : ∀ env : Variable → ZMod p,
      E'.eval env = denom.eval env * env inv + rest.eval env := fun env => rfl
  -- A constraint of `out` is `E'` (if it was `E`) or an unchanged constraint of `cs`.
  have hmemOut : ∀ c' ∈ out.algebraicConstraints, c' = E' ∨ c' ∈ cs.algebraicConstraints := by
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    by_cases h : c = E
    · exact Or.inl (by simp [hf, h])
    · exact Or.inr (by simpa [hf, h] using hc)
  -- `E'` is a constraint of `out` (it is `f E`).
  have hE'mem : E' ∈ out.algebraicConstraints :=
    List.mem_map.2 ⟨E, hE, by simp [hf]⟩
  -- Frame: variables of `cs` other than the witnesses `D` are unaffected by reassigning `D`.
  have hframe_ne : ∀ (c : Expression p), (∀ d ∈ D, d ∉ c.vars) →
      ∀ (w : ZMod p) (env : Variable → ZMod p), c.eval (reasg env w) = c.eval env := by
    intro c hc w env
    refine Expression.eval_congr c _ _ (fun x hx => ?_)
    exact hagree env w x (fun hxD => hc x hxD hx)
  -- Every bus of `cs` (= `out`) is `D`-free: reassigning `D` leaves its evaluation unchanged.
  have hbe : ∀ (env : Variable → ZMod p) (bi : BusInteraction (Expression p)),
      bi ∈ cs.busInteractions → bi.eval (reasg env (env inv)) = bi.eval env := by
    intro env bi hbi
    have hbifree : ∀ d ∈ D, d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars :=
      fun d hd => hDbus d hd bi hbi
    unfold BusInteraction.eval
    congr 1
    · exact hframe_ne _ (fun d hd => (hbifree d hd).1) _ _
    · exact List.map_congr_left (fun e he => hframe_ne _ (fun d hd => (hbifree d hd).2 e he) _ _)
  -- `out.satisfies env` ⇒ `cs` is satisfied at the witness-collapsed environment.
  have hcssat : ∀ env, out.satisfies bs env → cs.satisfies bs (reasg env (env inv)) := by
    intro env hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · by_cases h : c = E
      · subst h
        rw [hEeq env (env inv)]
        have hz : E'.eval env = 0 := hsat.1 E' hE'mem
        rw [hE'eval] at hz; exact hz
      · have hcvarsfree : ∀ d ∈ D, d ∉ c.vars := fun d hd hdc => h (hDonce d hd c hc hdc)
        rw [hframe_ne c hcvarsfree]
        have hfc : f c = c := by simp [hf, h]
        have hc0 := hsat.1 (f c) (List.mem_map.2 ⟨c, hc, rfl⟩)
        rwa [hfc] at hc0
    · rw [hbe env bi hbi]; exact hsat.2 bi hbi
  -- soundness
  have hsound : out.implies cs bs := by
    intro env hsat
    refine ⟨reasg env (env inv), hcssat env hsat, ?_⟩
    have hse : cs.sideEffects bs (reasg env (env inv)) = out.sideEffects bs env := by
      show (cs.busInteractions.filter _).map _ = (cs.busInteractions.filter _).map _
      exact List.map_congr_left (fun bi hbi => by rw [hbe env bi (List.mem_of_mem_filter hbi)])
    rw [hse]; exact BusState.equiv_refl _
  -- `out`'s variables are `cs`'s (dropping the witnesses) plus possibly `inv`.
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
  -- envC agrees with env off `inv`, and `inv ∉ cs.vars`.
  have hagreeC : ∀ (env : Variable → ZMod p) (x : Variable), x ∈ cs.vars →
      Function.update env inv (method.eval env) x = env x := by
    intro env x hx
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hinv_fresh hx
  refine ⟨hsound, ?_, ?_, ?_⟩
  · -- invariant preservation
    intro hcsInv env hsatOut bi hbiOut
    show (bi.eval env).multiplicity ≠ 0 → bs.breaksInvariant (bi.eval env) = false
    rw [← hbe env bi hbiOut]
    exact hcsInv (reasg env (env inv)) (hcssat env hsatOut) bi hbiOut
  · -- no new powdr-ID column
    intro v hvout hvpow
    rcases hout_vars v hvout with rfl | hcs
    · rw [hinv_id] at hvpow; exact absurd hvpow (by simp)
    · exact hcs
  · -- completeness
    intro env hadm hsat
    set envC := Function.update env inv (method.eval env) with hCdef
    -- `bi.eval envC = bi.eval env` (inv ∉ any bus).
    have hbeC : ∀ bi ∈ cs.busInteractions, bi.eval envC = bi.eval env := by
      intro bi hbi
      unfold BusInteraction.eval
      congr 1
      · exact Expression.eval_congr _ _ _ (fun x hx =>
          hagreeC env x (ConstraintSystem.mem_vars_of_mult hbi hx))
      · exact List.map_congr_left (fun e he => Expression.eval_congr _ _ _ (fun x hx =>
          hagreeC env x (ConstraintSystem.mem_vars_of_payload hbi he hx)))
    refine ⟨envC, ⟨fun c' hc' => ?_, fun bi hbi => ?_⟩, ?_, ?_, ?_, ?_⟩
    · -- output constraints hold at envC
      rcases hmemOut c' hc' with rfl | hcs
      · -- c' = E'
        rw [hE'eval]
        have hdenC : denom.eval envC = denom.eval env :=
          Expression.eval_congr _ _ _ (fun x hx => hagreeC env x (hden_sub x hx))
        have hrestC : rest.eval envC = rest.eval env :=
          Expression.eval_congr _ _ _ (fun x hx => hagreeC env x (hrest_sub x hx))
        rw [hdenC, hrestC, hCdef, Function.update_self, hmeth]
        by_cases hd0 : denom.eval env = 0
        · simp only [ComputationMethod.eval, hd0, if_true, mul_zero, zero_add]
          exact hbyte env hsat hd0
        · simp only [ComputationMethod.eval, hd0, if_false, Expression.eval]
          rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
          ring
      · have hce : c'.eval envC = c'.eval env :=
          Expression.eval_congr _ _ _ (fun x hx =>
            hagreeC env x (ConstraintSystem.mem_vars_of_constraint hcs hx))
        rw [hce]; exact hsat.1 c' hcs
    · rw [hbeC bi hbi]; exact hsat.2 bi hbi
    · -- admissible preserved: out shares cs's buses and envC agrees with env there
      have hmapeq : (cs.busInteractions.map (fun bi => bi.eval envC))
          = (cs.busInteractions.map (fun bi => bi.eval env)) :=
        List.map_congr_left (fun bi hbi => hbeC bi hbi)
      show bs.admissible ((cs.busInteractions.map (fun bi => bi.eval envC)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
      rw [hmapeq]; exact hadm
    · -- side effects equivalent
      have hse : cs.sideEffects bs env = out.sideEffects bs envC := by
        show (cs.busInteractions.filter _).map _ = (cs.busInteractions.filter _).map _
        exact List.map_congr_left (fun bi hbi => by rw [hbeC bi (List.mem_of_mem_filter hbi)])
      rw [hse]; exact BusState.equiv_refl _
    · -- input columns preserved
      intro v hvpow
      exact Function.update_of_ne (fun h => by rw [h, hinv_id] at hvpow; exact absurd hvpow (by simp)) _ _
    · -- reconstruction of derived columns
      intro inputVars hpowIn dsIn hrec v hvout hvnone
      by_cases hveq : v = inv
      · subst hveq
        have hmethfree : ∀ x ∈ method.vars, x ≠ v := by
          intro x hx
          rw [hmeth] at hx
          simp only [ComputationMethod.vars, Expression.vars, List.nil_append, List.mem_append] at hx
          rcases hx with hr | hd
          · exact fun h => hrest_free.1 (h ▸ hr)
          · exact fun h => hden_free.1 (h ▸ hd)
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

/-! ## Weighted (sum-of-squares) collapse for difference coefficients

For the is-*equal* gadget `Σᵢ (aᵢ − bᵢ)·mᵢ + rest = 0` (`mᵢ` pure witnesses, `aᵢ,bᵢ`
byte-bounded), the plain coefficient sum `Σ(aᵢ − bᵢ)` can vanish without every difference vanishing
(the differences cancel), so `collapse_correct`'s plain-sum completeness branch fails. The fix —
mirroring powdr's `is-equal` witness — is the **sum of squares** `Σᵢ (aᵢ − bᵢ)²`, which is `0` iff
every difference is `0`: each square is a non-negative integer `< 256²`, so the field sum does not
wrap and a zero sum forces each square, hence each difference, to `0`. Soundness sets each marker
`mᵢ := (aᵢ − bᵢ)·inv`, so `Σ(aᵢ − bᵢ)·mᵢ = (Σ(aᵢ − bᵢ)²)·inv`; this is the reassignment `assocReassign`
supplies to `collapse_correct`. -/

/-- Set each witness `cd.2` (paired with its coefficient `cd.1`) to `cd.1.eval env * w`, leaving
    every other variable at `env`. The per-witness weight is the coefficient's own value, so the
    collapse identity produces a *sum-of-squares* denominator rather than a plain coefficient sum. -/
def assocReassign (P : List (Expression p × Variable)) (env : Variable → ZMod p) (w : ZMod p) :
    Variable → ZMod p :=
  fun v => match P.find? (fun cd => cd.2 == v) with
    | some cd => cd.1.eval env * w
    | none => env v

/-- Off the witnesses, `assocReassign` is `env`. -/
theorem assocReassign_agree (P : List (Expression p × Variable)) (env : Variable → ZMod p)
    (w : ZMod p) (v : Variable) (hv : v ∉ P.map (·.2)) : assocReassign P env w v = env v := by
  have hnone : P.find? (fun cd => cd.2 == v) = none := by
    rw [List.find?_eq_none]
    intro cd hcd hbeq
    exact hv (List.mem_map.2 ⟨cd, hcd, of_decide_eq_true hbeq⟩)
  simp only [assocReassign, hnone]

/-- On a witness list with distinct keys, `find?` on a member's key returns that member. -/
theorem find?_snd_of_nodup (P : List (Expression p × Variable))
    (hnd : (P.map (·.2)).Nodup) (cd : Expression p × Variable) (hmem : cd ∈ P) :
    P.find? (fun x => x.2 == cd.2) = some cd := by
  induction P with
  | nil => simp at hmem
  | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hmem with rfl | htl
      · rw [List.find?_cons_of_pos (by simp)]
      · have hne : hd.2 ≠ cd.2 := fun h => hnd.1 (h ▸ List.mem_map.2 ⟨cd, htl, rfl⟩)
        rw [List.find?_cons_of_neg (by simp [hne])]
        exact ih hnd.2 htl

/-- The witness value under `assocReassign` is exactly `coeff · w` (distinct keys). -/
theorem assocReassign_key (P : List (Expression p × Variable)) (hnd : (P.map (·.2)).Nodup)
    (env : Variable → ZMod p) (w : ZMod p) (cd : Expression p × Variable) (hmem : cd ∈ P) :
    assocReassign P env w cd.2 = cd.1.eval env * w := by
  simp only [assocReassign, find?_snd_of_nodup P hnd cd hmem]

/-- The `peel` `foldr`, evaluated at a reassignment `σ` sending each key to `coeff · w` and fixing
    the (witness-free) coefficients, collapses to the *sum of squared* coefficient values times the
    common `w`. `σ` is kept abstract (as in `foldr_reassign`) so the induction does not disturb it. -/
theorem foldr_sqReassign (P : List (Expression p × Variable)) (σ env : Variable → ZMod p)
    (w : ZMod p) (hval : ∀ cd ∈ P, σ cd.2 = cd.1.eval env * w)
    (hfree : ∀ cd ∈ P, cd.1.eval σ = cd.1.eval env) :
    P.foldr (fun cd acc => cd.1.eval σ * σ cd.2 + acc) 0
      = (P.map (fun cd => cd.1.eval env * cd.1.eval env)).sum * w := by
  induction P with
  | nil => simp
  | cons cd rest ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      rw [hval cd (List.mem_cons_self ..), hfree cd (List.mem_cons_self ..),
          ih (fun x hx => hval x (List.mem_cons_of_mem _ hx))
             (fun x hx => hfree x (List.mem_cons_of_mem _ hx))]
      ring

/-! ## A byte-bounded square value bound and the sum-of-squares collapse identity -/

/-- The value of a squared difference of two byte-bounded field elements is `< 256²`. -/
theorem sq_diff_val_lt [NeZero p] (hp : 65536 ≤ p) (x y : ZMod p)
    (hx : x.val < 256) (hy : y.val < 256) : ((x - y) * (x - y)).val < 65536 := by
  rcases Nat.lt_or_ge x.val y.val with hlt | hge
  · -- x < y: x - y = -↑(y.val - x.val), squares to the same value
    have hd : x - y = -((y.val - x.val : ℕ) : ZMod p) := by
      have hcast : ((y.val - x.val : ℕ) : ZMod p) = y - x := by
        rw [Nat.cast_sub (le_of_lt hlt), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [hcast]; ring
    have hb : y.val - x.val ≤ 255 := by omega
    have hsq : (y.val - x.val) * (y.val - x.val) ≤ 255 * 255 := Nat.mul_le_mul hb hb
    rw [hd, neg_mul_neg, ← Nat.cast_mul, ZMod.val_natCast_of_lt (by omega)]; omega
  · -- x ≥ y: x - y = ↑(x.val - y.val)
    have hd : x - y = ((x.val - y.val : ℕ) : ZMod p) := by
      rw [Nat.cast_sub hge, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hb : x.val - y.val ≤ 255 := by omega
    have hsq : (x.val - y.val) * (x.val - y.val) ≤ 255 * 255 := Nat.mul_le_mul hb hb
    rw [hd, ← Nat.cast_mul, ZMod.val_natCast_of_lt (by omega)]; omega

/-! ## Detection: find a collapsible reciprocal-witness group and discharge the facts -/

/-- A witness variable `d` occurs (in the whole system) only in the target constraint `E`.
    Decided with the allocation-free `Expression.mentions` (early-exit tree walk) rather than
    `d ∉ ·.vars`, which would materialize every expression's variable list once per `(E, d)`
    pair — this check runs inside the per-constraint candidate scan. -/
def occursOnlyInTarget (cs : ConstraintSystem p) (E : Expression p) (d : Variable) : Bool :=
  (cs.algebraicConstraints.all (fun c => decide (c = E) || !(c.mentions d))) &&
  (cs.busInteractions.all (fun bi =>
    !(bi.multiplicity.mentions d) && bi.payload.all (fun e => !(e.mentions d))))

theorem occursOnlyInTarget_constr {cs : ConstraintSystem p} {E : Expression p} {d : Variable}
    (h : occursOnlyInTarget cs E d = true) : ∀ c ∈ cs.algebraicConstraints, d ∈ c.vars → c = E := by
  intro c hc hdc
  simp only [occursOnlyInTarget, Bool.and_eq_true, List.all_eq_true] at h
  have hc' := h.1 c hc
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc'
  rcases hc' with h1 | h2
  · exact h1
  · exact absurd hdc (mentions_false_not_mem_vars d c h2)

theorem occursOnlyInTarget_bus {cs : ConstraintSystem p} {E : Expression p} {d : Variable}
    (h : occursOnlyInTarget cs E d = true) : ∀ bi ∈ cs.busInteractions,
      d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars := by
  intro bi hbi
  simp only [occursOnlyInTarget, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hm, hp⟩ := h.2 bi hbi
  exact ⟨mentions_false_not_mem_vars d bi.multiplicity hm,
    fun e he => mentions_false_not_mem_vars d e (hp e he)⟩

/-- The single variable a coefficient reduces to: a bare `var a`, or `a·1` / `1·a` (the shape `peel`
    produces from a `aᵢ·dimᵢ` term). Returns `none` for anything else. -/
def coeffVar : Expression p → Option Variable
  | .var a => some a
  | .mul (.var a) (.const c) => if c = 1 then some a else none
  | .mul (.const c) (.var a) => if c = 1 then some a else none
  | _ => none

theorem coeffVar_sound {c : Expression p} {a : Variable} (h : coeffVar c = some a) :
    (∀ env, c.eval env = env a) ∧ (∀ x ∈ c.vars, x = a) := by
  unfold coeffVar at h
  split at h
  · rename_i a'; simp only [Option.some.injEq] at h; subst h
    exact ⟨fun _ => rfl, fun x hx => by simpa [Expression.vars] using hx⟩
  · rename_i a' c'; split_ifs at h with hc1; simp only [Option.some.injEq] at h; subst h; subst hc1
    exact ⟨fun env => by simp [Expression.eval], fun x hx => by simpa [Expression.vars] using hx⟩
  · rename_i c' a'; split_ifs at h with hc1; simp only [Option.some.injEq] at h; subst h; subst hc1
    exact ⟨fun env => by simp [Expression.eval], fun x hx => by simpa [Expression.vars] using hx⟩
  · exact absurd h (by simp)

/-- Each coefficient's `fold` reduces to a single variable with a `≤ 256` value bound; the raw
    coefficient is `D`-free and reads only powdr-ID columns. (`peel` leaves each coefficient as a
    zero-cluttered sum `Σⱼ aⱼ·0 + aᵢ·1` that `fold` cleans to `aᵢ`; it is already `D`-free because
    the other witnesses land in the remainder, not the coefficient.) -/
def coeffsByteOK (B : Std.HashMap Variable Nat) (D : List Variable) :
    List (Expression p) → Bool
  | [] => true
  | c :: cs =>
    (match coeffVar c.fold with
     | some a => (match B[a]? with | some b => decide (b ≤ 256) | none => false)
     | none => false) &&
    D.all (fun d => decide (d ∉ c.vars)) &&
    c.vars.all (fun x => x.powdrId?.isSome) &&
    coeffsByteOK B D cs

theorem coeffsByteOK_sound (B : Std.HashMap Variable Nat) (D : List Variable) :
    ∀ (coeffs : List (Expression p)), coeffsByteOK B D coeffs = true →
      ∀ c ∈ coeffs, ∃ a : Variable, (∀ env, c.eval env = env a) ∧ (∀ d ∈ D, d ∉ c.vars) ∧
        (∀ x ∈ c.vars, x.powdrId?.isSome = true) ∧ ∃ b, B[a]? = some b ∧ b ≤ 256 := by
  intro coeffs
  induction coeffs with
  | nil => intro _ c hc; simp at hc
  | cons c0 cs ih =>
      intro h c hc
      simp only [coeffsByteOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hcv, hDf⟩, hpow⟩, hrec⟩ := h
      rcases List.mem_cons.1 hc with rfl | hcs
      · cases hcva : coeffVar c.fold with
        | none => rw [hcva] at hcv; simp at hcv
        | some a =>
            simp only [hcva] at hcv
            refine ⟨a, ?_, ?_, ?_, ?_⟩
            · intro env
              rw [← Expression.fold_eval c env]; exact (coeffVar_sound hcva).1 env
            · intro d hd; exact of_decide_eq_true (List.all_eq_true.1 hDf d hd)
            · intro x hx; exact List.all_eq_true.1 hpow x hx
            · revert hcv
              cases hb : B[a]? with
              | none => intro hcv; simp at hcv
              | some b => intro hcv; exact ⟨b, rfl, of_decide_eq_true hcv⟩
      · exact ih hrec c hcs

/-! ## Sum-of-squares collapse detection: difference coefficients (is-equal gadget) -/

/-- Recognize a `fold`-normalized difference `a - b` of two variables, as
    `add (var a) (mul (const (-1)) (var b))`. Returns the two variables, or `none`. -/
def diffVarsOf : Expression p → Option (Variable × Variable)
  | .add (.var a) (.mul (.const c) (.var b)) => if c = -1 then some (a, b) else none
  | _ => none

theorem diffVarsOf_sound {c : Expression p} {a b : Variable} (h : diffVarsOf c = some (a, b)) :
    (∀ env, c.eval env = env a - env b) ∧ (∀ x ∈ c.vars, x = a ∨ x = b) := by
  unfold diffVarsOf at h
  split at h
  · rename_i a' c' b'
    split_ifs at h with hc1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; subst hc1
    refine ⟨fun env => by simp [Expression.eval, sub_eq_add_neg], fun x hx => ?_⟩
    simp only [Expression.vars, List.nil_append, List.mem_append, List.mem_singleton] at hx
    exact hx
  · exact absurd h (by simp)

/-- Each coefficient is a `fold`-recognized difference of two `≤ 256`-bounded variables, is
    witness-free, and reads only powdr-ID columns. Mirrors `coeffsByteOK` for the difference shape. -/
def sqCoeffsOK (B : Std.HashMap Variable Nat) (D : List Variable) :
    List (Expression p) → Bool
  | [] => true
  | c :: cs =>
    (match diffVarsOf c.fold with
     | some (a, b) =>
         (match B[a]? with | some ba => decide (ba ≤ 256) | none => false) &&
         (match B[b]? with | some bb => decide (bb ≤ 256) | none => false)
     | none => false) &&
    D.all (fun d => decide (d ∉ c.vars)) &&
    c.vars.all (fun x => x.powdrId?.isSome) &&
    sqCoeffsOK B D cs

theorem sqCoeffsOK_sound (B : Std.HashMap Variable Nat) (D : List Variable) :
    ∀ (coeffs : List (Expression p)), sqCoeffsOK B D coeffs = true →
      ∀ c ∈ coeffs, ∃ a b : Variable, (∀ env, c.eval env = env a - env b) ∧
        (∀ d ∈ D, d ∉ c.vars) ∧ (∀ x ∈ c.vars, x.powdrId?.isSome = true) ∧
        (∃ ba, B[a]? = some ba ∧ ba ≤ 256) ∧ (∃ bb, B[b]? = some bb ∧ bb ≤ 256) := by
  intro coeffs
  induction coeffs with
  | nil => intro _ c hc; simp at hc
  | cons c0 cs ih =>
      intro h c hc
      simp only [sqCoeffsOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hdv, hDf⟩, hpow⟩, hrec⟩ := h
      rcases List.mem_cons.1 hc with rfl | hcs
      · cases hdva : diffVarsOf c.fold with
        | none => rw [hdva] at hdv; simp at hdv
        | some ab =>
            obtain ⟨a, b⟩ := ab
            simp only [hdva, Bool.and_eq_true] at hdv
            obtain ⟨hba, hbb⟩ := hdv
            refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
            · intro env; rw [← Expression.fold_eval c env]; exact (diffVarsOf_sound hdva).1 env
            · intro d hd; exact of_decide_eq_true (List.all_eq_true.1 hDf d hd)
            · intro x hx; exact List.all_eq_true.1 hpow x hx
            · revert hba; cases hb : B[a]? with
              | none => intro hba; simp at hba
              | some ba => intro hba; exact ⟨ba, rfl, of_decide_eq_true hba⟩
            · revert hbb; cases hb : B[b]? with
              | none => intro hbb; simp at hbb
              | some bb => intro hbb; exact ⟨bb, rfl, of_decide_eq_true hbb⟩
      · exact ih hrec c hcs

/-- The sum-of-squares collapse identity (`hEeq` for `collapse_correct` with `reasg = assocReassign`):
    setting each witness `dᵢ` to `coeffᵢ · w` turns `E` into `(Σ coeffᵢ²)·w + rest`. -/
theorem peel_sqReassign_eval (D : List Variable) (E : Expression p) (hnd : D.Nodup)
    (hcfree : ∀ c ∈ (peel D E).1, ∀ d ∈ D, d ∉ c.vars)
    (hrfree : ∀ d ∈ D, d ∉ (peel D E).2.vars)
    (env : Variable → ZMod p) (w : ZMod p) :
    E.eval (assocReassign ((peel D E).1.zip D) env w)
      = (sumExpr ((peel D E).1.map (fun c => Expression.mul c c))).eval env * w
        + (peel D E).2.eval env := by
  set P := (peel D E).1.zip D with hP
  set σ := assocReassign P env w with hσ
  have hlen : (peel D E).1.length = D.length := peel_length D E
  have hmap2 : P.map (·.2) = D := by rw [hP]; exact List.map_snd_zip (by rw [hlen])
  have hmap1 : P.map (·.1) = (peel D E).1 := by rw [hP]; exact List.map_fst_zip (by rw [hlen])
  have hndP : (P.map (·.2)).Nodup := by rw [hmap2]; exact hnd
  have hrestσ : (peel D E).2.eval σ = (peel D E).2.eval env :=
    Expression.eval_congr _ _ _ (fun x hx => by
      rw [hσ]; exact assocReassign_agree P env w x
        (by rw [hmap2]; exact fun hxD => hrfree x hxD hx))
  have hcoσ : ∀ cd ∈ P, cd.1.eval σ = cd.1.eval env := by
    intro cd hcd
    have hc1 : cd.1 ∈ (peel D E).1 := by rw [← hmap1]; exact List.mem_map.2 ⟨cd, hcd, rfl⟩
    refine Expression.eval_congr _ _ _ (fun x hx => ?_)
    rw [hσ]
    exact assocReassign_agree P env w x (by rw [hmap2]; exact fun hxD => hcfree cd.1 hc1 x hxD hx)
  have hval : ∀ cd ∈ P, σ cd.2 = cd.1.eval env * w :=
    fun cd hcd => by rw [hσ]; exact assocReassign_key P hndP env w cd hcd
  rw [peel_eval D E σ, hrestσ, foldr_sqReassign P σ env w hval hcoσ]
  have hLHS : P.map (fun cd => cd.1.eval env * cd.1.eval env)
      = (peel D E).1.map (fun c => c.eval env * c.eval env) := by
    rw [← hmap1, List.map_map]; rfl
  have hRHS : (sumExpr ((peel D E).1.map (fun c => Expression.mul c c))).eval env
      = ((peel D E).1.map (fun c => c.eval env * c.eval env)).sum := by
    rw [sumExpr_eval, List.map_map]; rfl
  rw [hLHS, hRHS]

/-- The witnesses of `E`: variables that occur (in the whole system) only in `E`. This is the
    expensive part of a collapse attempt — a full-system `occursOnlyInTarget` scan per candidate —
    so the scanner computes it once per constraint and shares it across the plain / sum-of-squares
    attempts. Kept as its own definition (not an inline `filter`) so that the `rfl` proofs at the
    call sites are trivial rather than forcing the filter to reduce. -/
def witnessesOf (cs : ConstraintSystem p) (busVars : Std.HashSet Variable) (E : Expression p) :
    List Variable :=
  E.vars.dedup.filter (fun v => !busVars.contains v && occursOnlyInTarget cs E v)

/-- Attempt the plain-sum collapse with target constraint `E` and its precomputed witness set `D`:
    peel the coefficients and — if all checks pass — return the verified `PassResult`.

    Runtime shape (this runs once per constraint per pass invocation): the bounds map `Bm`, the
    bus-occurring variable set `busVars`, and the witness set `D` are built **once** per invocation /
    constraint and passed in. The certificate is one short-circuiting `&&` chain, so on the (vast
    majority of) constraints with `D.length < 2` nothing else is evaluated. -/
def tryOne [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bm : BoundsMap p cs bs) (busVars : Std.HashSet Variable)
    (E : Expression p) (hE : E ∈ cs.algebraicConstraints)
    (D : List Variable) (hD : D = witnessesOf cs busVars E) : Option (PassResult cs bs) := by
  classical
  set inv : Variable := ⟨"hcinv#" ++ (D.headD ⟨"_", none⟩).name, none⟩ with hinvdef
  by_cases hchk : (decide (2 ≤ D.length) && (coeffsByteOK Bm.map D (peel D E).1 &&
      (decide (∀ d ∈ D, d ∉ (peel D E).2.vars) &&
      (decide (∀ x ∈ (peel D E).2.vars, x.powdrId?.isSome = true) &&
      (decide (inv ∉ cs.vars) && decide ((peel D E).1.length * 256 ≤ p)))))) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨h2len, hbyteOK, hrfree, hrpow, hinvfresh, hfit⟩ := hchk
    have hEvarsub : ∀ x ∈ E.vars, x ∈ cs.vars := fun x hx =>
      ConstraintSystem.mem_vars_of_constraint hE hx
    have hcfree : ∀ c ∈ (peel D E).1, ∀ d ∈ D, d ∉ c.vars := by
      intro c hc d hd
      obtain ⟨a, _, hDf, _, _⟩ := coeffsByteOK_sound Bm.map D (peel D E).1 hbyteOK c hc
      exact hDf d hd
    have hEeq := peel_reassign_eval D E hcfree hrfree
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hbyte : ∀ env, cs.satisfies bs env → (sumExpr (peel D E).1).eval env = 0 →
        (peel D E).2.eval env = 0 := by
      intro env hsat hden0
      have hE0 : E.eval env = 0 := hsat.1 E hE
      have hbytes : ∀ c ∈ (peel D E).1, (c.eval env).val < 256 := by
        intro c hc
        obtain ⟨a, heval, _, _, b, hlk, hb256⟩ :=
          coeffsByteOK_sound Bm.map D (peel D E).1 hbyteOK c hc
        have hlt := Bm.sound env (fun bi hbi => hsat.2 bi hbi) a b hlk
        rw [heval env]; omega
      have hsum0 : ((peel D E).1.map (fun c => c.eval env)).sum = 0 := by
        rw [← sumExpr_eval]; exact hden0
      have hfit' : (((peel D E).1.map (fun c => c.eval env)).map (fun x => x.val)).sum < p := by
        have hle := List.sum_le_card_nsmul
          (((peel D E).1.map (fun c => c.eval env)).map (fun x => x.val)) 255 (by
            intro x hx
            simp only [List.mem_map] at hx
            obtain ⟨b, ⟨c, hc, rfl⟩, rfl⟩ := hx
            have := hbytes c hc; omega)
        simp only [List.length_map, smul_eq_mul] at hle
        have hlen : (peel D E).1.length = D.length := peel_length D E
        omega
      have hallz : ∀ c ∈ (peel D E).1, c.eval env = 0 := fun c hc =>
        sum_zero_all_zero hp0 _ hfit' hsum0 (c.eval env) (List.mem_map.2 ⟨c, hc, rfl⟩)
      have hfz := foldr_zero ((peel D E).1.zip D) env
        (fun cd hcd => hallz cd.1 (List.of_mem_zip hcd).1)
      rw [peel_eval D E env, hfz, zero_add] at hE0
      exact hE0
    have hDcert : ∀ d ∈ D, occursOnlyInTarget cs E d = true := by
      intro d hd
      rw [hD] at hd
      simp only [witnessesOf, List.mem_filter, Bool.and_eq_true] at hd
      exact hd.2.2
    have hDonce : ∀ d ∈ D, ∀ c ∈ cs.algebraicConstraints, d ∈ c.vars → c = E := fun d hd =>
      occursOnlyInTarget_constr (hDcert d hd)
    have hDbus : ∀ d ∈ D, ∀ bi ∈ cs.busInteractions,
        d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars := fun d hd =>
      occursOnlyInTarget_bus (hDcert d hd)
    have hden_free : inv ∉ (sumExpr (peel D E).1).vars ∧ ∀ d ∈ D, d ∉ (sumExpr (peel D E).1).vars := by
      refine ⟨fun hx => ?_, fun d hd hx => ?_⟩
      · obtain ⟨c, hc, hxc⟩ := sumExpr_vars hx
        exact hinvfresh (hEvarsub inv (peel_fst_vars D E c hc inv hxc))
      · obtain ⟨c, hc, hxc⟩ := sumExpr_vars hx; exact hcfree c hc d hd hxc
    have hrest_free : inv ∉ (peel D E).2.vars ∧ ∀ d ∈ D, d ∉ (peel D E).2.vars :=
      ⟨fun hx => hinvfresh (hEvarsub inv (peel_snd_vars D E inv hx)), hrfree⟩
    have hden_sub : ∀ x ∈ (sumExpr (peel D E).1).vars, x ∈ cs.vars := by
      intro x hx; obtain ⟨c, hc, hxc⟩ := sumExpr_vars hx
      exact hEvarsub x (peel_fst_vars D E c hc x hxc)
    have hrest_sub : ∀ x ∈ (peel D E).2.vars, x ∈ cs.vars := fun x hx =>
      hEvarsub x (peel_snd_vars D E x hx)
    have hden_pow : ∀ x ∈ (sumExpr (peel D E).1).vars, x.powdrId?.isSome = true := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := sumExpr_vars hx
      obtain ⟨a, _, _, hpow, _⟩ := coeffsByteOK_sound Bm.map D (peel D E).1 hbyteOK c hc
      exact hpow x hxc
    exact some ⟨_, _, collapse_correct cs bs E (sumExpr (peel D E).1) (peel D E).2 D inv
      (fun env w => reassign D w env) hE
      (fun env w v hv => by simp only [reassign]; rw [if_neg hv])
      hEeq hbyte hinvfresh rfl hDonce hDbus hden_free hrest_free hden_sub hrest_sub hden_pow hrpow⟩
  · exact none

/-- Attempt the sum-of-squares collapse (is-*equal* gadget): the witnesses `D` occur only in `E`,
    every peeled coefficient is a byte-bounded *difference* `aᵢ − bᵢ`, and the reciprocal-witness
    tail `rest` reads only input columns. The target `Σᵢ (aᵢ − bᵢ)·dᵢ + rest = 0` is replaced by
    `(Σᵢ (aᵢ − bᵢ)²)·inv + rest = 0` with the single derived hint `inv = QuotientOrZero(−rest, Σ …²)`,
    dropping every `dᵢ`. Completeness: a zero sum-of-squares forces every difference to `0` (each
    square is `< 256²`, so the field sum does not wrap). -/
def tryOneSq [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bm : BoundsMap p cs bs) (busVars : Std.HashSet Variable)
    (E : Expression p) (hE : E ∈ cs.algebraicConstraints)
    (D : List Variable) (hD : D = witnessesOf cs busVars E) : Option (PassResult cs bs) := by
  classical
  set inv : Variable := ⟨"hcsq#" ++ (D.headD ⟨"_", none⟩).name, none⟩ with hinvdef
  set denom : Expression p := sumExpr ((peel D E).1.map (fun c => Expression.mul c c)) with hden
  by_cases hchk : (decide (2 ≤ D.length) && (sqCoeffsOK Bm.map D (peel D E).1 &&
      (decide (∀ d ∈ D, d ∉ (peel D E).2.vars) &&
      (decide (∀ x ∈ (peel D E).2.vars, x.powdrId?.isSome = true) &&
      (decide (inv ∉ cs.vars) && decide ((peel D E).1.length * 65536 ≤ p)))))) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨h2len, hsqOK, hrfree, hrpow, hinvfresh, hfit⟩ := hchk
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hlen : (peel D E).1.length = D.length := peel_length D E
    have hnd : D.Nodup := by
      rw [hD]; unfold witnessesOf; exact (List.nodup_dedup E.vars).filter _
    have hEvarsub : ∀ x ∈ E.vars, x ∈ cs.vars := fun x hx =>
      ConstraintSystem.mem_vars_of_constraint hE hx
    have hcfree : ∀ c ∈ (peel D E).1, ∀ d ∈ D, d ∉ c.vars := by
      intro c hc d hd
      obtain ⟨a, b, _, hDf, _, _, _⟩ := sqCoeffsOK_sound Bm.map D (peel D E).1 hsqOK c hc
      exact hDf d hd
    have hEeq := peel_sqReassign_eval D E hnd hcfree hrfree
    -- Denominator = the sum of squared coefficient values.
    have hdeneval : ∀ env : Variable → ZMod p, denom.eval env
        = ((peel D E).1.map (fun c => c.eval env * c.eval env)).sum := by
      intro env; rw [hden, sumExpr_eval, List.map_map]; rfl
    -- A collapsed value of the denominator forces the reciprocal-witness tail to vanish.
    have hbyte : ∀ env, cs.satisfies bs env → denom.eval env = 0 → (peel D E).2.eval env = 0 := by
      intro env hsat hden0
      have hE0 : E.eval env = 0 := hsat.1 E hE
      have hbytes : ∀ c ∈ (peel D E).1, ((c.eval env) * (c.eval env)).val < 65536 := by
        intro c hc
        obtain ⟨a, b, heval, _, _, ⟨ba, hlka, hba⟩, ⟨bb, hlkb, hbb⟩⟩ :=
          sqCoeffsOK_sound Bm.map D (peel D E).1 hsqOK c hc
        have hlta := Bm.sound env (fun bi hbi => hsat.2 bi hbi) a ba hlka
        have hltb := Bm.sound env (fun bi hbi => hsat.2 bi hbi) b bb hlkb
        haveI : NeZero p := ⟨hp0.ne'⟩
        rw [heval env]
        exact sq_diff_val_lt (by omega) (env a) (env b) (by omega) (by omega)
      have hsum0 : ((peel D E).1.map (fun c => c.eval env * c.eval env)).sum = 0 := by
        rw [← hdeneval env]; exact hden0
      have hfit' : (((peel D E).1.map (fun c => c.eval env * c.eval env)).map
          (fun x => x.val)).sum < p := by
        have hle := List.sum_le_card_nsmul
          (((peel D E).1.map (fun c => c.eval env * c.eval env)).map (fun x => x.val)) 65535 (by
            intro x hx
            simp only [List.mem_map] at hx
            obtain ⟨s, ⟨c, hc, rfl⟩, rfl⟩ := hx
            have := hbytes c hc; omega)
        simp only [List.length_map, smul_eq_mul] at hle
        omega
      have hallz : ∀ c ∈ (peel D E).1, c.eval env * c.eval env = 0 := fun c hc =>
        sum_zero_all_zero hp0 _ hfit' hsum0 (c.eval env * c.eval env) (List.mem_map.2 ⟨c, hc, rfl⟩)
      have hallz0 : ∀ c ∈ (peel D E).1, c.eval env = 0 := fun c hc =>
        mul_self_eq_zero.1 (hallz c hc)
      have hfz := foldr_zero ((peel D E).1.zip D) env
        (fun cd hcd => hallz0 cd.1 (List.of_mem_zip hcd).1)
      rw [peel_eval D E env, hfz, zero_add] at hE0
      exact hE0
    have hDcert : ∀ d ∈ D, occursOnlyInTarget cs E d = true := by
      intro d hd
      rw [hD] at hd
      simp only [witnessesOf, List.mem_filter, Bool.and_eq_true] at hd
      exact hd.2.2
    have hDonce : ∀ d ∈ D, ∀ c ∈ cs.algebraicConstraints, d ∈ c.vars → c = E := fun d hd =>
      occursOnlyInTarget_constr (hDcert d hd)
    have hDbus : ∀ d ∈ D, ∀ bi ∈ cs.busInteractions,
        d ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, d ∉ e.vars := fun d hd =>
      occursOnlyInTarget_bus (hDcert d hd)
    have hdenvars : ∀ x ∈ denom.vars, ∃ c ∈ (peel D E).1, x ∈ c.vars := by
      intro x hx
      rw [hden] at hx
      obtain ⟨e, he, hxe⟩ := sumExpr_vars hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      simp only [Expression.vars, List.mem_append, or_self] at hxe
      exact ⟨c, hc, hxe⟩
    have hden_free : inv ∉ denom.vars ∧ ∀ d ∈ D, d ∉ denom.vars := by
      refine ⟨fun hx => ?_, fun d hd hx => ?_⟩
      · obtain ⟨c, hc, hxc⟩ := hdenvars inv hx
        exact hinvfresh (hEvarsub inv (peel_fst_vars D E c hc inv hxc))
      · obtain ⟨c, hc, hxc⟩ := hdenvars d hx; exact hcfree c hc d hd hxc
    have hrest_free : inv ∉ (peel D E).2.vars ∧ ∀ d ∈ D, d ∉ (peel D E).2.vars :=
      ⟨fun hx => hinvfresh (hEvarsub inv (peel_snd_vars D E inv hx)), hrfree⟩
    have hden_sub : ∀ x ∈ denom.vars, x ∈ cs.vars := by
      intro x hx; obtain ⟨c, hc, hxc⟩ := hdenvars x hx
      exact hEvarsub x (peel_fst_vars D E c hc x hxc)
    have hrest_sub : ∀ x ∈ (peel D E).2.vars, x ∈ cs.vars := fun x hx =>
      hEvarsub x (peel_snd_vars D E x hx)
    have hden_pow : ∀ x ∈ denom.vars, x.powdrId?.isSome = true := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hdenvars x hx
      obtain ⟨a, b, _, _, hpow, _, _⟩ := sqCoeffsOK_sound Bm.map D (peel D E).1 hsqOK c hc
      exact hpow x hxc
    have hmap2 : ((peel D E).1.zip D).map (·.2) = D := List.map_snd_zip (by rw [hlen])
    exact some ⟨_, _, collapse_correct cs bs E denom (peel D E).2 D inv
      (fun env w => assocReassign ((peel D E).1.zip D) env w) hE
      (fun env w v hv => assocReassign_agree _ env w v (by rw [hmap2]; exact hv))
      hEeq hbyte hinvfresh rfl hDonce hDbus hden_free hrest_free hden_sub hrest_sub hden_pow hrpow⟩
  · exact none

/-- Scan a constraint sublist for the first collapsible target, trying both the plain-sum
    (`is-zero`/`seqz`) and the sum-of-squares (`is-equal`) shape on each constraint.

    The once-in-`E` witness set `D` is the expensive part — a full-system `occursOnlyInTarget`
    scan per candidate witness — so it is computed **once** per constraint here and shared by both
    `tryOne` and `tryOneSq` (rather than re-derived by a second whole-list pass). When `D.length < 2`
    both attempts short-circuit immediately, so the marginal cost of also offering the sum-of-squares
    shape is only the cheap coefficient re-check on the rare candidate constraints. -/
def tryList [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bm : BoundsMap p cs bs) (busVars : Std.HashSet Variable) :
    (L : List (Expression p)) → (∀ E ∈ L, E ∈ cs.algebraicConstraints) → Option (PassResult cs bs)
  | [], _ => none
  | E :: rest, hmem =>
    let hE := hmem E (List.mem_cons_self ..)
    let D := witnessesOf cs busVars E
    match tryOne cs bs Bm busVars E hE D rfl with
    | some r => some r
    | none =>
      match tryOneSq cs bs Bm busVars E hE D rfl with
      | some r => some r
      | none => tryList cs bs Bm busVars rest (fun E' h => hmem E' (List.mem_cons_of_mem _ h))

/-- The hint-collapse pass: replace the first bilinear reciprocal-witness constraint by a single
    derived inverse hint (needs prime `p` for the field inverse; identity otherwise, and identity
    with `BusFacts.trivial` since no coefficient is byte-bounded). A single `tryList` scan tries both
    collapse shapes per constraint — the plain-sum (single byte-bounded coefficients, `is-zero`/`seqz`)
    and the sum-of-squares (byte-bounded *difference* coefficients, `is-equal`) — sharing the
    per-constraint witness-set computation. The bounds map and the set of bus-occurring variables are
    built once here, not once per scanned constraint. -/
def hintCollapsePass : VerifiedPassW p := fun cs bs facts =>
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    let Bm : BoundsMap p cs bs := BoundsMap.build facts
    let busVars : Std.HashSet Variable := cs.busInteractions.foldl (init := ∅) fun s bi =>
      bi.payload.foldl (fun s e => e.vars.foldl (·.insert ·) s)
        (bi.multiplicity.vars.foldl (·.insert ·) s)
    (tryList cs bs Bm busVars cs.algebraicConstraints (fun _ h => h)).getD
      ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

