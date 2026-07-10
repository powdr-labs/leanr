import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Flag unification across duplicate scaled range checks

After the two-root unification (`RootPairUnify.lean`) both the surviving and the eliminated
memory access range-check the **same** low limb `x`, each through its own scaled slot
`k·x + R` (`k` constant, `R` the access's flag polynomial times `−k`): the slot value `u`
satisfies `x = k⁻¹·u + W` with `W = −k⁻¹·R` the flag-polynomial value. Two such checks on the
same `x` force `W_X.val = W_Y.val` — both are the residue of `x.val` under `m = k⁻¹.val`
(`residue_uniq`), given the slot bounds and per-point `W < m` — and the flag encoding is
injective on its (tiny, provable) domain box, so the *individual flag variables* of the two
accesses are provably equal. The entailed equalities feed the same `Solved`/`substF` machinery
as the limb unification; once substituted, the two checks become syntactically identical and
`dedupPass` collects the copy.

Nothing here is memory-specific: the pass unifies variables pinned by any two scaled
range-check slots of the same carrier variable whose offset parts agree pointwise on their
finite domains. Prime `p` only (finite flag domains come from booleanity roots), re-checked at
runtime. -/

variable {p : ℕ}

/-- Two summands below `M` that complete the same integer against multiples of `M` are equal. -/
theorem residue_uniq (M A B w1 w2 : Nat) (h : M * A + w1 = M * B + w2)
    (h1 : w1 < M) (h2 : w2 < M) : w1 = w2 := by
  have e1 : (M * A + w1) % M = w1 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h1
  have e2 : (M * B + w2) % M = w2 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h2
  rw [← e1, h, e2]

/-! ## The pair certificate -/

/-- Decidable certificate that interactions `biX`, `biY` are scaled range checks of the same
    carrier `x` whose offset parts pin `vy` (in `biY`'s flags) to `vx` (in `biX`'s flags):
    both slots decompose as `k·x + R` with the same unit `k`, the slot values are fact-bounded,
    every joint flag point keeps both offsets below `m = k⁻¹` (so the integer residue argument
    applies), and every joint point with equal offset values has `vy = vx`. Re-checked inside
    the adoption proof. -/
def fuCheck (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (Expression p))
    (biX biY : BusInteraction (Expression p)) (x vx vy : Variable) : Bool :=
  match biX.multiplicity.constValue?, biY.multiplicity.constValue? with
  | some mx, some my =>
    !(decide (mx = 0)) && !(decide (my = 0)) &&
    (match biX.payload[0]?, biY.payload[0]? with
     | some OX, some OY =>
       (match facts.slotBound biX.busId mx (biX.payload.map Expression.constValue?) 0,
              facts.slotBound biY.busId my (biY.payload.map Expression.constValue?) 0 with
        | some bX, some bY =>
          (match OX.splitAt x, OY.splitAt x with
           | some (k, RX), some (k2, RY) =>
             decide (k2 = k) && decide (k * k⁻¹ = 1) &&
             decide (vx ∈ RX.vars) && decide (vy ∈ RY.vars) && !(decide (vy = vx)) &&
             decide (vx ∈ biX.payload.flatMap Expression.vars) &&
             decide (k⁻¹.val * (bX - 1) + (k⁻¹.val - 1) < p) &&
             decide (k⁻¹.val * (bY - 1) + (k⁻¹.val - 1) < p) &&
             (let jointVars := (RX.vars ++ RY.vars).eraseDups
              let doms := jointVars.filterMap (fun v =>
                (findDomainAlg domCs v).map (fun d => (v, d)))
              decide (doms.map Prod.fst = jointVars) &&
              decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
              (assignments doms).all (fun pt =>
                decide (((-k⁻¹) * RX.eval (envOf pt)).val < k⁻¹.val) &&
                decide (((-k⁻¹) * RY.eval (envOf pt)).val < k⁻¹.val) &&
                (!(decide (((-k⁻¹) * RX.eval (envOf pt)).val
                    = ((-k⁻¹) * RY.eval (envOf pt)).val))
                  || decide (envOf pt vy = envOf pt vx))))
           | _, _ => false)
        | _, _ => false)
     | _, _ => false)
  | _, _ => false

/-- Extract the `varsIn` membership from a passed certificate. -/
theorem fuCheck_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (biX biY : BusInteraction (Expression p))
    (x vx vy : Variable) (h : fuCheck bs facts domCs biX biY x vx vy = true) :
    vx ∈ biX.payload.flatMap Expression.vars := by
  unfold fuCheck at h
  cases hmx : biX.multiplicity.constValue? with
  | none => rw [hmx] at h; simp at h
  | some mx =>
    cases hmy : biY.multiplicity.constValue? with
    | none => rw [hmx, hmy] at h; simp at h
    | some my =>
      rw [hmx, hmy] at h
      cases hOX : biX.payload[0]? with
      | none => simp [hOX] at h
      | some OX =>
        cases hOY : biY.payload[0]? with
        | none => simp [hOX, hOY] at h
        | some OY =>
          simp only [hOX, hOY] at h
          cases hbX : facts.slotBound biX.busId mx (biX.payload.map Expression.constValue?) 0 with
          | none => simp [hbX] at h
          | some bX =>
            cases hbY : facts.slotBound biY.busId my
                (biY.payload.map Expression.constValue?) 0 with
            | none => simp [hbX, hbY] at h
            | some bY =>
              simp only [hbX, hbY] at h
              cases hsX : OX.splitAt x with
              | none => simp [hsX] at h
              | some kRX =>
                obtain ⟨k, RX⟩ := kRX
                cases hsY : OY.splitAt x with
                | none => simp [hsX, hsY] at h
                | some kRY =>
                  obtain ⟨k2, RY⟩ := kRY
                  simp only [hsX, hsY, Bool.and_eq_true, decide_eq_true_eq] at h
                  exact h.2.1.1.1.2

theorem fuCheck_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (biX biY : BusInteraction (Expression p))
    (x vx vy : Variable) (h : fuCheck bs facts domCs biX biY x vx vy = true)
    (env : Variable → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval env = 0)
    (hobX : (biX.eval env).multiplicity ≠ 0 → bs.violatesConstraint (biX.eval env) = false)
    (hobY : (biY.eval env).multiplicity ≠ 0 → bs.violatesConstraint (biY.eval env) = false) :
    env vy = env vx := by
  unfold fuCheck at h
  cases hmx : biX.multiplicity.constValue? with
  | none => rw [hmx] at h; simp at h
  | some mx =>
    cases hmy : biY.multiplicity.constValue? with
    | none => rw [hmx, hmy] at h; simp at h
    | some my =>
      rw [hmx, hmy] at h
      cases hOX : biX.payload[0]? with
      | none => simp [hOX] at h
      | some OX =>
        cases hOY : biY.payload[0]? with
        | none => simp [hOX, hOY] at h
        | some OY =>
          simp only [hOX, hOY] at h
          cases hbX : facts.slotBound biX.busId mx (biX.payload.map Expression.constValue?) 0 with
          | none => simp [hbX] at h
          | some bX =>
            cases hbY : facts.slotBound biY.busId my
                (biY.payload.map Expression.constValue?) 0 with
            | none => simp [hbX, hbY] at h
            | some bY =>
              simp only [hbX, hbY] at h
              cases hsX : OX.splitAt x with
              | none => simp [hsX] at h
              | some kRX =>
                obtain ⟨k, RX⟩ := kRX
                cases hsY : OY.splitAt x with
                | none => simp [hsX, hsY] at h
                | some kRY =>
                  obtain ⟨k2, RY⟩ := kRY
                  simp only [hsX, hsY, Bool.and_eq_true, Bool.not_eq_true',
                    decide_eq_true_eq, decide_eq_false_iff_not] at h
                  obtain ⟨⟨hmx0, hmy0⟩,
                    ⟨⟨⟨⟨⟨⟨⟨⟨hk2, hunit⟩, hvxR⟩, hvyR⟩, _hvyne⟩, _hvxpay⟩, hwrapX⟩, hwrapY⟩,
                      ⟨⟨hcover, _hcap⟩, hpts⟩⟩⟩ := h
                  -- acceptance and slot-value bounds
                  have hmXe : (biX.eval env).multiplicity = mx :=
                    biX.multiplicity.constValue?_sound mx hmx env
                  have hmYe : (biY.eval env).multiplicity = my :=
                    biY.multiplicity.constValue?_sound my hmy env
                  have hviolX : bs.violatesConstraint (biX.eval env) = false :=
                    hobX (by rw [hmXe]; exact hmx0)
                  have hviolY : bs.violatesConstraint (biY.eval env) = false :=
                    hobY (by rw [hmYe]; exact hmy0)
                  have hgetX : (biX.eval env).payload[0]? = some (OX.eval env) := by
                    show (biX.payload.map (fun e => e.eval env))[0]? = _
                    rw [List.getElem?_map, hOX]; rfl
                  have hgetY : (biY.eval env).payload[0]? = some (OY.eval env) := by
                    show (biY.payload.map (fun e => e.eval env))[0]? = _
                    rw [List.getElem?_map, hOY]; rfl
                  have hbXv : (OX.eval env).val < bX :=
                    facts.slotBound_sound (biX.eval env)
                      (biX.payload.map Expression.constValue?) 0 bX (OX.eval env)
                      (by rw [(rfl : (biX.eval env).busId = biX.busId), hmXe]; exact hbX)
                      (matches_evalPattern biX.payload env) hviolX hgetX
                  have hbYv : (OY.eval env).val < bY :=
                    facts.slotBound_sound (biY.eval env)
                      (biY.payload.map Expression.constValue?) 0 bY (OY.eval env)
                      (by rw [(rfl : (biY.eval env).busId = biY.busId), hmYe]; exact hbY)
                      (matches_evalPattern biY.payload env) hviolY hgetY
                  -- field decomposition `x = m·u + W`, both sides
                  set m := k⁻¹ with hm
                  have hOXe : OX.eval env = k * env x + RX.eval env :=
                    Expression.splitAt_eval x OX k RX hsX env
                  have hOYe : OY.eval env = k * env x + RY.eval env := by
                    have h0 := Expression.splitAt_eval x OY k2 RY hsY env
                    rw [hk2] at h0; exact h0
                  have hxX : env x = m * OX.eval env + (-m) * RX.eval env := by
                    have h1 : m * OX.eval env = m * k * env x + m * RX.eval env := by
                      rw [hOXe]; ring
                    rw [mul_comm m k, hunit, one_mul] at h1
                    linear_combination -h1
                  have hxY : env x = m * OY.eval env + (-m) * RY.eval env := by
                    have h1 : m * OY.eval env = m * k * env x + m * RY.eval env := by
                      rw [hOYe]; ring
                    rw [mul_comm m k, hunit, one_mul] at h1
                    linear_combination -h1
                  -- the environment restricted to the joint flag box is an enumerated point
                  have hmemdoms : ∀ vd ∈ (RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
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
                  have hpt := mem_assignments ((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                    (findDomainAlg domCs v).map (fun d => (v, d)))) env hmemdoms
                  have hagree : ∀ v, v ∈ (RX.vars ++ RY.vars).eraseDups →
                      envOf (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                        (findDomainAlg domCs v).map (fun d => (v, d)))).map
                          (fun vd => (vd.1, env vd.1))) v = env v := by
                    intro v hv
                    refine envOf_map _ env v ?_
                    rw [show (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                      (findDomainAlg domCs v).map (fun d => (v, d)))).map Prod.fst)
                      = (RX.vars ++ RY.vars).eraseDups from hcover]
                    exact hv
                  have hRXagree : RX.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                      (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                        (fun vd => (vd.1, env vd.1)))) = RX.eval env :=
                    Expression.eval_congr RX _ env (fun v hv =>
                      hagree v (List.mem_eraseDups.2 (List.mem_append_left _ hv)))
                  have hRYagree : RY.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                      (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                        (fun vd => (vd.1, env vd.1)))) = RY.eval env :=
                    Expression.eval_congr RY _ env (fun v hv =>
                      hagree v (List.mem_eraseDups.2 (List.mem_append_right _ hv)))
                  -- the per-point conditions, at the environment's own point
                  have hptc := List.all_eq_true.mp hpts _ hpt
                  rw [Bool.and_eq_true, Bool.and_eq_true] at hptc
                  have hWXlt : ((-m) * RX.eval env).val < m.val := by
                    rw [← hRXagree]; exact of_decide_eq_true hptc.1.1
                  have hWYlt : ((-m) * RY.eval env).val < m.val := by
                    rw [← hRYagree]; exact of_decide_eq_true hptc.1.2
                  -- integer decomposition of `x.val` through both checks
                  have hbX1 : (OX.eval env).val ≤ bX - 1 := by omega
                  have hbY1 : (OY.eval env).val ≤ bY - 1 := by omega
                  have hle1 : m.val * (OX.eval env).val ≤ m.val * (bX - 1) :=
                    Nat.mul_le_mul_left _ hbX1
                  have hle2 : m.val * (OY.eval env).val ≤ m.val * (bY - 1) :=
                    Nat.mul_le_mul_left _ hbY1
                  have hMuX : (m * OX.eval env).val = m.val * (OX.eval env).val :=
                    ZMod.val_mul_of_lt (by omega)
                  have hMuY : (m * OY.eval env).val = m.val * (OY.eval env).val :=
                    ZMod.val_mul_of_lt (by omega)
                  have hsumX : (m * OX.eval env).val + ((-m) * RX.eval env).val < p := by
                    rw [hMuX]; omega
                  have hsumY : (m * OY.eval env).val + ((-m) * RY.eval env).val < p := by
                    rw [hMuY]; omega
                  have hvalX : (env x).val
                      = m.val * (OX.eval env).val + ((-m) * RX.eval env).val := by
                    rw [hxX, ZMod.val_add_of_lt hsumX, hMuX]
                  have hvalY : (env x).val
                      = m.val * (OY.eval env).val + ((-m) * RY.eval env).val := by
                    rw [hxY, ZMod.val_add_of_lt hsumY, hMuY]
                  have hres : ((-m) * RX.eval env).val = ((-m) * RY.eval env).val :=
                    residue_uniq m.val (OX.eval env).val (OY.eval env).val _ _
                      (hvalX.symm.trans hvalY) hWXlt hWYlt
                  -- resolve the point disjunction and pull the equality back to `env`
                  have hor := hptc.2
                  rw [Bool.or_eq_true] at hor
                  rcases hor with hL | hR
                  · rw [Bool.not_eq_true'] at hL
                    have hXpt := hres
                    rw [← hRXagree, ← hRYagree] at hXpt
                    exact absurd hXpt (of_decide_eq_false hL)
                  · rw [← hagree vy (List.mem_eraseDups.2 (List.mem_append_right _ hvyR)),
                        ← hagree vx (List.mem_eraseDups.2 (List.mem_append_left _ hvxR))]
                    exact of_decide_eq_true hR

/-! ## The scan loop and the pass -/

/-- A previously seen scaled-check candidate: the interaction (with membership), its carrier
    variable, and the matching key `(busId, second-slot constant, k, carrier)`. -/
structure FUSeen (p : ℕ) (cs : ConstraintSystem p) where
  bi : BusInteraction (Expression p)
  mem : bi ∈ cs.busInteractions
  x : Variable
  key : Nat × Option (ZMod p) × ZMod p × Variable

/-- Scaled-check candidates of one interaction: carrier variables of the first payload slot
    with a constant-coefficient decomposition and a *nonempty* offset part (raw checks have
    nothing to unify). -/
def fuCandidates (bi : BusInteraction (Expression p)) :
    List (Variable × (Nat × Option (ZMod p) × ZMod p × Variable)) :=
  match bi.payload[0]? with
  | none => []
  | some O =>
    O.vars.eraseDups.filterMap (fun x =>
      match O.splitAt x with
      | some (k, R) =>
        if R.vars.isEmpty then none
        else some (x, (bi.busId, (bi.payload[1]?).bind Expression.constValue?, k, x))
      | none => none)

/-- Flag-target combinations for a matched pair: variables of the two offset parts. -/
def fuTargets (biX biY : BusInteraction (Expression p)) (x : Variable) :
    List (Variable × Variable) :=
  match biX.payload[0]?, biY.payload[0]? with
  | some OX, some OY =>
    match OX.splitAt x, OY.splitAt x with
    | some (_, RX), some (_, RY) =>
      RY.vars.eraseDups.flatMap (fun vy => RX.vars.eraseDups.map (fun vx => (vy, vx)))
    | _, _ => []
  | _, _ => []

/-- Scan the interactions: for each scaled-check candidate, look for an earlier twin with the
    same key and adopt every flag pair the certificate confirms. The certificate is re-checked
    inside the adoption proof, so the scan itself carries no obligations. -/
def fuLoop [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) →
    List (FUSeen p cs) → Solved p cs bs → Solved p cs bs
  | [], _, _, σ => σ
  | c :: rest, hmem, seen, σ =>
    have hc : c ∈ cs.busInteractions := hmem c (List.mem_cons_self ..)
    let hrest := fun c' h' => hmem c' (List.mem_cons_of_mem _ h')
    let cands := fuCandidates c
    match cands.findSome? (fun xk =>
        seen.findSome? (fun e => if e.key == xk.2 then some (e, xk.1) else none)) with
    | some ex =>
        let pairs := (fuTargets ex.1.bi c ex.2).filterMap (fun t =>
          if fuCheck bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1
          then some (t.1, Expression.var t.2) else none)
        have hpairs : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env := by
          intro env hsat yt hyt
          obtain ⟨t, _ht, hif⟩ := List.mem_filterMap.1 hyt
          by_cases hck : fuCheck bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 = true
          · rw [if_pos hck] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            show env t.1 = env t.2
            exact fuCheck_sound bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 hck env
              (fun c' hc' => hsat.1 c' hc')
              (fun hmult => hsat.2 ex.1.bi ex.1.mem hmult)
              (fun hmult => hsat.2 c hc hmult)
          · rw [if_neg hck] at hif
            exact absurd hif (by simp)
        have hpairsV : ∀ yt ∈ pairs, ∀ z ∈ yt.2.vars, z ∈ cs.vars := by
          intro yt hyt z hz
          obtain ⟨t, _ht, hif⟩ := List.mem_filterMap.1 hyt
          by_cases hck : fuCheck bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 = true
          · rw [if_pos hck] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            obtain rfl : z = t.2 := by simpa [Expression.vars] using hz
            obtain ⟨e', he', hv'⟩ := List.mem_flatMap.1
              (fuCheck_vars bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 hck)
            exact ConstraintSystem.mem_vars_of_payload ex.1.mem he' hv'
          · rw [if_neg hck] at hif
            exact absurd hif (by simp)
        fuLoop cs bs facts rest hrest
          (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩) ++ seen)
          (σ.insertAll pairs hpairs hpairsV)
    | none =>
        fuLoop cs bs facts rest hrest
          (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩) ++ seen) σ

/-- Flag unification across duplicate scaled range checks. Prime `p` only (re-checked at
    runtime). Runs after `rootPairUnifyPass` — the carrier limbs must already be shared — and
    before `dedupPass`, which collects the checks this pass makes syntactically identical. -/
def flagUnifyPass : VerifiedPassW p := fun cs bs facts =>
  if hp : (decide p.Prime) = true then
    haveI : Fact p.Prime := ⟨of_decide_eq_true hp⟩
    let σ := fuLoop cs bs facts cs.busInteractions (fun _ h => h) [] Solved.empty
    if σ.map.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs.substF σ.fn, [],
      cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)
        (fun y t hyt => σ.varsIn y t hyt)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
