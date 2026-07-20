import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.RootPairUnify

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

/-- Pair-level certificate data: everything independent of the target flag pair. `pts` pairs
    each enumerated joint flag point with whether the two offset values coincide there. -/
structure FuData (p : ℕ) where
  rxVars : List Variable
  ryVars : List Variable
  payXVars : List Variable
  pts : List (List (Variable × ZMod p) × Bool)

/-- The pair-level half of the certificate: slot decompositions, fact bounds, no-wrap checks,
    domain cover, and the per-point offset bounds — computed **once per matched pair** (the
    field inversion in particular is hoisted; it used to run dozens of times per target). -/
def fuPairData? (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (Expression p))
    (biX biY : BusInteraction (Expression p)) (x : Variable) : Option (FuData p) :=
  match biX.multiplicity.constValue?, biY.multiplicity.constValue? with
  | some mx, some my =>
    if mx = 0 then none else if my = 0 then none else
    (match biX.payload[0]?, biY.payload[0]? with
     | some OX, some OY =>
       (match facts.slotBound biX.busId mx (biX.payload.map Expression.constValue?) 0,
              facts.slotBound biY.busId my (biY.payload.map Expression.constValue?) 0 with
        | some bX, some bY =>
          (match OX.splitAt x, OY.splitAt x with
           | some (k, RX), some (k2, RY) =>
             let m := k⁻¹
             if k2 = k ∧ k * m = 1 ∧
                 m.val * (bX - 1) + (m.val - 1) < p ∧
                 m.val * (bY - 1) + (m.val - 1) < p then
               let jointVars := (RX.vars ++ RY.vars).eraseDups
               let doms := jointVars.filterMap (fun v =>
                 (findDomainAlg domCs v).map (fun d => (v, d)))
               if doms.map Prod.fst = jointVars ∧
                   (doms.map (fun vd => vd.2.length)).prod ≤ 32 then
                 let pts0 := assignments doms
                 if pts0.all (fun pt =>
                     decide (((-m) * RX.eval (envOf pt)).val < m.val) &&
                     decide (((-m) * RY.eval (envOf pt)).val < m.val)) then
                   some { rxVars := RX.vars, ryVars := RY.vars,
                          payXVars := biX.payload.flatMap Expression.vars,
                          pts := pts0.map (fun pt =>
                            (pt, decide (((-m) * RX.eval (envOf pt)).val
                              = ((-m) * RY.eval (envOf pt)).val))) }
                 else none
               else none
             else none
           | _, _ => none)
        | _, _ => none)
     | _, _ => none)
  | _, _ => none

/-- The per-target half: memberships, disequality, and pointwise flag agreement wherever the
    offsets coincide. -/
def fuCheckWith (d : FuData p) (vx vy : Variable) : Bool :=
  decide (vx ∈ d.rxVars) && decide (vy ∈ d.ryVars) && !(decide (vy = vx)) &&
  decide (vx ∈ d.payXVars) &&
  d.pts.all (fun ptb => !ptb.2 || decide (envOf ptb.1 vy = envOf ptb.1 vx))

/-- Decidable certificate that interactions `biX`, `biY` are scaled range checks of the same
    carrier `x` whose offset parts pin `vy` (in `biY`'s flags) to `vx` (in `biX`'s flags).
    Defined through `fuPairData?`/`fuCheckWith` so the scan can share the pair-level work
    across targets with a *definitionally* identical value. Re-checked inside the adoption
    proof. -/
def fuCheck (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (Expression p))
    (biX biY : BusInteraction (Expression p)) (x vx vy : Variable) : Bool :=
  match fuPairData? bs facts domCs biX biY x with
  | some d => fuCheckWith d vx vy
  | none => false

/-- Extract the `varsIn` membership from a passed certificate. -/
theorem fuCheck_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (biX biY : BusInteraction (Expression p))
    (x vx vy : Variable) (h : fuCheck bs facts domCs biX biY x vx vy = true) :
    vx ∈ biX.payload.flatMap Expression.vars := by
  unfold fuCheck at h
  cases hd : fuPairData? bs facts domCs biX biY x with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    -- the data's payload-vars field is the payload's variable list, by construction
    have hpay : d.payXVars = biX.payload.flatMap Expression.vars := by
      unfold fuPairData? at hd
      cases hmx : biX.multiplicity.constValue? with
      | none => rw [hmx] at hd; simp at hd
      | some mx =>
        cases hmy : biY.multiplicity.constValue? with
        | none => rw [hmx, hmy] at hd; simp at hd
        | some my =>
          simp only [hmx, hmy] at hd
          split_ifs at hd
          cases hOX : biX.payload[0]? with
          | none => simp [hOX] at hd
          | some OX =>
            cases hOY : biY.payload[0]? with
            | none => simp [hOX, hOY] at hd
            | some OY =>
              simp only [hOX, hOY] at hd
              cases hbX : facts.slotBound biX.busId mx
                  (biX.payload.map Expression.constValue?) 0 with
              | none => simp [hbX] at hd
              | some bX =>
                cases hbY : facts.slotBound biY.busId my
                    (biY.payload.map Expression.constValue?) 0 with
                | none => simp [hbX, hbY] at hd
                | some bY =>
                  simp only [hbX, hbY] at hd
                  cases hsX : OX.splitAt x with
                  | none => simp [hsX] at hd
                  | some kRX =>
                    obtain ⟨k, RX⟩ := kRX
                    cases hsY : OY.splitAt x with
                    | none => simp [hsX, hsY] at hd
                    | some kRY =>
                      obtain ⟨k2, RY⟩ := kRY
                      simp only [hsX, hsY] at hd
                      split_ifs at hd
                      simp only [Option.some.injEq] at hd
                      rw [← hd]
    unfold fuCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact hpay ▸ h.1.2

theorem fuCheck_sound [Fact p.Prime] (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (Expression p)) (biX biY : BusInteraction (Expression p))
    (x vx vy : Variable) (h : fuCheck bs facts domCs biX biY x vx vy = true)
    (env : Variable → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval env = 0)
    (hobX : (biX.eval env).multiplicity ≠ 0 → bs.violatesConstraint (biX.eval env) = false)
    (hobY : (biY.eval env).multiplicity ≠ 0 → bs.violatesConstraint (biY.eval env) = false) :
    env vy = env vx := by
  unfold fuCheck at h
  cases hd : fuPairData? bs facts domCs biX biY x with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    unfold fuCheckWith at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hvxR', hvyR'⟩, _hne⟩, _hpay'⟩, hcw⟩ := h
    unfold fuPairData? at hd
    cases hmx : biX.multiplicity.constValue? with
    | none => rw [hmx] at hd; simp at hd
    | some mx =>
      cases hmy : biY.multiplicity.constValue? with
      | none => rw [hmx, hmy] at hd; simp at hd
      | some my =>
        simp only [hmx, hmy] at hd
        split_ifs at hd with hmx0 hmy0
        cases hOX : biX.payload[0]? with
        | none => simp [hOX] at hd
        | some OX =>
          cases hOY : biY.payload[0]? with
          | none => simp [hOX, hOY] at hd
          | some OY =>
            simp only [hOX, hOY] at hd
            cases hbX : facts.slotBound biX.busId mx
                (biX.payload.map Expression.constValue?) 0 with
            | none => simp [hbX] at hd
            | some bX =>
              cases hbY : facts.slotBound biY.busId my
                  (biY.payload.map Expression.constValue?) 0 with
              | none => simp [hbX, hbY] at hd
              | some bY =>
                simp only [hbX, hbY] at hd
                cases hsX : OX.splitAt x with
                | none => simp [hsX] at hd
                | some kRX =>
                  obtain ⟨k, RX⟩ := kRX
                  cases hsY : OY.splitAt x with
                  | none => simp [hsX, hsY] at hd
                  | some kRY =>
                    obtain ⟨k2, RY⟩ := kRY
                    simp only [hsX, hsY] at hd
                    split_ifs at hd with hconds hcov hall
                    obtain ⟨hk2, hunit, hwrapX, hwrapY⟩ := hconds
                    obtain ⟨hcover, _hcap⟩ := hcov
                    simp only [Option.some.injEq] at hd
                    subst hd
                    simp only at hvxR' hvyR' hcw
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
                      | some dm =>
                        rw [hfd] at hvd'
                        simp only [Option.map_some, Option.some.injEq] at hvd'
                        obtain rfl := hvd'.symm
                        exact findDomainAlg_sound domCs v dm hfd env hdom
                    have hpt := mem_assignments ((RX.vars ++ RY.vars).eraseDups.filterMap
                      (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))) env hmemdoms
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
                    -- pair-level point bounds, at the environment's own point
                    have hpair := List.all_eq_true.mp hall _ hpt
                    rw [Bool.and_eq_true] at hpair
                    have hWXlt : ((-m) * RX.eval env).val < m.val := by
                      rw [← hRXagree]; exact of_decide_eq_true hpair.1
                    have hWYlt : ((-m) * RY.eval env).val < m.val := by
                      rw [← hRYagree]; exact of_decide_eq_true hpair.2
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
                    -- the combo condition at the environment's point
                    have hmempts : (((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1)),
                        decide (((-m) * RX.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val
                          = ((-m) * RY.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val))
                        ∈ (assignments ((RX.vars ++ RY.vars).eraseDups.filterMap (fun v =>
                          (findDomainAlg domCs v).map (fun d => (v, d))))).map
                            (fun pt => (pt, decide (((-m) * RX.eval (envOf pt)).val
                              = ((-m) * RY.eval (envOf pt)).val))) :=
                      List.mem_map.2 ⟨_, hpt, rfl⟩
                    have horb := List.all_eq_true.mp hcw _ hmempts
                    have hb : decide (((-m) * RX.eval (envOf (((RX.vars
                        ++ RY.vars).eraseDups.filterMap (fun v =>
                          (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val
                        = ((-m) * RY.eval (envOf (((RX.vars ++ RY.vars).eraseDups.filterMap
                          (fun v => (findDomainAlg domCs v).map (fun d => (v, d)))).map
                            (fun vd => (vd.1, env vd.1))))).val) = true :=
                      decide_eq_true (by rw [hRXagree, hRYagree]; exact hres)
                    simp only [hb, Bool.not_true, Bool.false_or, decide_eq_true_eq] at horb
                    rw [← hagree vy (List.mem_eraseDups.2 (List.mem_append_right _ hvyR')),
                        ← hagree vx (List.mem_eraseDups.2 (List.mem_append_left _ hvxR'))]
                    exact horb

/-! ## The scan loop and the pass -/

/-- A previously seen scaled-check candidate: the interaction (with membership), its carrier
    variable, and the matching key `(busId, second-slot constant, k, carrier)`. -/
structure FUSeen (p : ℕ) (cs : ConstraintSystem p) where
  bi : BusInteraction (Expression p)
  mem : bi ∈ cs.busInteractions
  x : Variable
  key : Nat × Option (ZMod p) × ZMod p × Variable

/-- Hash of an `FUSeen` match key, used to bucket the `seen` accumulator of `fuLoop`/`fxLoop`. It
    reads only fields the `key == key'` test compares, so equal keys share a bucket (a match is
    never hidden); unequal keys that collide are separated by the retained exact `e.key == xk.2`
    check inside the scan. -/
def fuKeyHash (key : Nat × Option (ZMod p) × ZMod p × Variable) : UInt64 :=
  mixHash (hash key.1) (mixHash (hash (key.2.1.map ZMod.val))
    (mixHash (hash key.2.2.1.val) (hash key.2.2.2)))

/-- Prepend seen-entries into their key-hash buckets. `foldr` keeps each bucket in the same order
    as the old flat `es ++ seen` list, so the bucketed scan returns the identical earliest twin —
    output unchanged, per-candidate scan now over one bucket instead of the whole history. -/
def fuInsertAll {cs : ConstraintSystem p} (m : Std.HashMap UInt64 (List (FUSeen p cs)))
    (es : List (FUSeen p cs)) : Std.HashMap UInt64 (List (FUSeen p cs)) :=
  es.foldr (fun e acc => acc.insert (fuKeyHash e.key) (e :: acc.getD (fuKeyHash e.key) [])) m

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
    Std.HashMap UInt64 (List (FUSeen p cs)) → Solved p cs bs → Solved p cs bs
  | [], _, _, σ => σ
  | c :: rest, hmem, seen, σ =>
    have hc : c ∈ cs.busInteractions := hmem c (List.mem_cons_self ..)
    let hrest := fun c' h' => hmem c' (List.mem_cons_of_mem _ h')
    let cands := fuCandidates c
    match cands.findSome? (fun xk =>
        (seen.getD (fuKeyHash xk.2) []).findSome? (fun e => if e.key == xk.2 then some (e, xk.1) else none)) with
    | some ex =>
        -- pair-level work once per match; per-target checks share it (definitionally the
        -- same value as `fuCheck` — see its definition)
        match hdata : fuPairData? bs facts cs.algebraicConstraints ex.1.bi c ex.2 with
        | none =>
            fuLoop cs bs facts rest hrest
              (fuInsertAll seen (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩))) σ
        | some d =>
        let pairs := (fuTargets ex.1.bi c ex.2).filterMap (fun t =>
          if fuCheckWith d t.2 t.1
          then some (t.1, Expression.var t.2) else none)
        have hpairs : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env := by
          intro env hsat yt hyt
          obtain ⟨t, _ht, hif⟩ := List.mem_filterMap.1 hyt
          by_cases hck : fuCheckWith d t.2 t.1 = true
          · rw [if_pos hck] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            show env t.1 = env t.2
            have hfc : fuCheck bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 = true := by
              unfold fuCheck; rw [hdata]; exact hck
            exact fuCheck_sound bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 hfc env
              (fun c' hc' => hsat.1 c' hc')
              (fun hmult => hsat.2 ex.1.bi ex.1.mem hmult)
              (fun hmult => hsat.2 c hc hmult)
          · rw [if_neg hck] at hif
            exact absurd hif (by simp)
        have hpairsV : ∀ yt ∈ pairs, ∀ z ∈ yt.2.vars, z ∈ cs.vars := by
          intro yt hyt z hz
          obtain ⟨t, _ht, hif⟩ := List.mem_filterMap.1 hyt
          by_cases hck : fuCheckWith d t.2 t.1 = true
          · rw [if_pos hck] at hif
            simp only [Option.some.injEq] at hif
            subst hif
            obtain rfl : z = t.2 := by simpa [Expression.vars] using hz
            have hfc : fuCheck bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 = true := by
              unfold fuCheck; rw [hdata]; exact hck
            obtain ⟨e', he', hv'⟩ := List.mem_flatMap.1
              (fuCheck_vars bs facts cs.algebraicConstraints ex.1.bi c ex.2 t.2 t.1 hfc)
            exact ConstraintSystem.mem_vars_of_payload ex.1.mem he' hv'
          · rw [if_neg hck] at hif
            exact absurd hif (by simp)
        fuLoop cs bs facts rest hrest
          (fuInsertAll seen (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩)))
          (σ.insertAll pairs hpairs hpairsV)
    | none =>
        fuLoop cs bs facts rest hrest
          (fuInsertAll seen (cands.map (fun xk => ⟨c, hc, xk.1, xk.2⟩))) σ

/-- Flag unification across duplicate scaled range checks. Prime `p` only (re-checked at
    runtime). Runs after `rootPairUnifyPass` — the carrier limbs must already be shared — and
    before `dedupPass`, which collects the checks this pass makes syntactically identical. -/
def flagUnifyPass (pw : PrimeWitness p) : VerifiedPassW p := fun cs bs facts =>
  if hpB : pw.isPrime = true then
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    let σ := fuLoop cs bs facts cs.busInteractions (fun _ h => h) ∅ Solved.empty
    if σ.map.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs.substF σ.fn, [],
      cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)
        (fun y t hyt => σ.varsIn y t hyt)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
