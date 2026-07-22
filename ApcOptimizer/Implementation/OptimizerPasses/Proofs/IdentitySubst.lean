import ApcOptimizer.Implementation.OptimizerPasses.IdentitySubst
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch

set_option autoImplicit false

/-! # Dense late identity-result substitution: correctness and wiring

`DensePassCorrect` for `denseIdentitySubstF` (`IdentitySubst.lean`), a single batch
`DenseConstraintSystem.substF` riding on `substF_denseCorrect` (`Proofs/DomainBatch.lean`): every
mapped pair is forced by its interaction's acceptance and every resolved operand occurs in `d`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `ZMod.val` is injective in nonzero characteristic. -/
private theorem val_inj [NeZero p] {a b : ZMod p} (h : a.val = b.val) : a = b :=
  (ZMod.natCast_rightInverse a).symm.trans ((congrArg _ h).trans (ZMod.natCast_rightInverse b))

/-! ## Structure of a recognised identity pair -/

theorem denseAsVar_spec (e : DenseExpr p) (v : VarId) (h : denseAsVar e = some v) :
    e = DenseExpr.var v := by
  cases e with
  | var v' => simp only [denseAsVar, Option.some.injEq] at h; subst h; rfl
  | const c => simp [denseAsVar] at h
  | add a b => simp [denseAsVar] at h
  | mul a b => simp [denseAsVar] at h

theorem denseOrIdentityOperand_spec (o1 o2 : DenseExpr p) (v : VarId)
    (h : denseOrIdentityOperand o1 o2 = some v) :
    (o1 = DenseExpr.var v ∧ o2 = DenseExpr.const 0)
      ∨ (o2 = DenseExpr.var v ∧ o1 = DenseExpr.const 0) := by
  unfold denseOrIdentityOperand at h
  split_ifs at h with ho2 ho1
  · exact Or.inl ⟨denseAsVar_spec o1 v h, ho2⟩
  · exact Or.inr ⟨denseAsVar_spec o2 v h, ho1⟩

theorem denseIdentityPairAt_spec {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (rv o1v : VarId)
    (h : denseIdentityPairAt facts bi = some (rv, o1v)) :
    ∃ (spec : ByteXorSpec p) (oop : ZMod p) (o1 o2 : DenseExpr p),
      facts.byteXorSpec bi.busId = some spec ∧ bi.multiplicity = DenseExpr.const 1 ∧
      spec.orOp = some oop ∧
      spec.decode bi.payload = some (DenseExpr.const oop, o1, o2, DenseExpr.var rv) ∧
      denseOrIdentityOperand o1 o2 = some o1v := by
  unfold denseIdentityPairAt at h
  split at h
  · rename_i spec hspec
    split at h
    · rename_i oop hoop
      split at h
      · rename_i op o1 o2 r hdec
        cases r with
        | var rv' =>
          split_ifs at h with hcond
          obtain ⟨hmc, hop⟩ := hcond
          cases hoo : denseOrIdentityOperand o1 o2 with
          | none => rw [hoo] at h; simp at h
          | some o1v' =>
            rw [hoo] at h
            simp only [] at h
            split_ifs at h with hne
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨spec, oop, o1, o2, hspec, hmc, hoop, hop ▸ hdec, hoo⟩
        | const _ => exact absurd h (by simp)
        | add _ _ => exact absurd h (by simp)
        | mul _ _ => exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A recognised identity pair is forced by acceptance: `denv rv = denv o1v`. -/
theorem denseIdentityPairAt_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (rv o1v : VarId)
    (h : denseIdentityPairAt facts bi = some (rv, o1v)) (denv : VarId → ZMod p)
    (hviol : bs.violatesConstraint (denseBIEval bi denv) = false) : denv rv = denv o1v := by
  obtain ⟨spec, oop, o1, o2, hspec, _, hoop, hdec, hoo⟩ :=
    denseIdentityPairAt_spec facts bi rv o1v h
  have hdecEv : spec.decode (denseBIEval bi denv).payload
      = some (oop, o1.eval denv, o2.eval denv, denv rv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]; rfl
  obtain ⟨horc, _⟩ := facts.byteBoolSound bi.busId spec hspec (denseBIEval bi denv).payload
    oop (o1.eval denv) (o2.eval denv) (denv rv) (denseBIEval bi denv).multiplicity hdecEv
  haveI := spec.pNeZero
  obtain ⟨_, _, hrval⟩ := (horc oop hoop rfl).mp hviol
  rcases denseOrIdentityOperand_spec o1 o2 o1v hoo with ⟨ho1, ho2⟩ | ⟨ho2, ho1⟩
  · have ho1e : o1.eval denv = denv o1v := by rw [ho1]; rfl
    have ho2e : o2.eval denv = 0 := by rw [ho2]; rfl
    rw [ho1e, ho2e, ZMod.val_zero] at hrval
    exact val_inj (by rw [hrval]; simp)
  · have ho1e : o1.eval denv = 0 := by rw [ho1]; rfl
    have ho2e : o2.eval denv = denv o1v := by rw [ho2]; rfl
    rw [ho1e, ho2e, ZMod.val_zero] at hrval
    exact val_inj (by rw [hrval]; simp)

/-! ## First-wins map membership and chain resolution -/

theorem denseFirstWins_mem : ∀ (pairs : List (VarId × VarId))
    (m : Std.HashMap VarId VarId) (y v : VarId),
    (denseFirstWins pairs m)[y]? = some v → m[y]? = some v ∨ (y, v) ∈ pairs := by
  intro pairs
  induction pairs with
  | nil => intro m y v h; exact Or.inl h
  | cons pr rest ih =>
    intro m y v h
    rcases ih _ y v h with hm | hr
    · by_cases hc : m.contains pr.1
      · rw [if_pos hc] at hm
        exact Or.inl hm
      · rw [if_neg hc, Std.HashMap.getElem?_insert] at hm
        by_cases hy : (pr.1 == y) = true
        · rw [if_pos hy] at hm
          simp only [Option.some.injEq] at hm
          have h1 : pr.1 = y := by simpa using hy
          exact Or.inr (List.mem_cons.2 (Or.inl (by rw [← h1, ← hm])))
        · rw [if_neg hy] at hm
          exact Or.inl hm
    · exact Or.inr (List.mem_cons_of_mem _ hr)

theorem denseResolveGo_sound (m : Std.HashMap VarId VarId) (denv : VarId → ZMod p)
    (hm : ∀ a b, m[a]? = some b → denv a = denv b) :
    ∀ (fuel : Nat) (v : VarId), denv (denseResolveGo m fuel v) = denv v := by
  intro fuel
  induction fuel with
  | zero => intro v; rfl
  | succ fuel ih =>
    intro v
    rw [denseResolveGo]
    cases hv : m[v]? with
    | some w => rw [ih w, hm v w hv]
    | none => rfl

theorem denseResolveGo_prop (m : Std.HashMap VarId VarId) (P : VarId → Prop)
    (hm : ∀ (a b : VarId), m[a]? = some b → P b) :
    ∀ (fuel : Nat) (v : VarId), P v → P (denseResolveGo m fuel v) := by
  intro fuel
  induction fuel with
  | zero => intro v hv; exact hv
  | succ fuel ih =>
    intro v hv
    rw [denseResolveGo]
    cases hmv : m[v]? with
    | some w => exact ih w (hm v w hmv)
    | none => exact hv

/-! ## Every stored pair is a recognised OR identity; its operand occurs in `d` -/

theorem denseIdentityMap_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (y v : VarId) (h : (denseIdentityMap facts d)[y]? = some v) :
    ∃ (bi : BusInteraction (DenseExpr p)),
      bi ∈ d.busInteractions ∧ denseIdentityPairAt facts bi = some (y, v) := by
  rcases denseFirstWins_mem _ _ y v h with hm | hpair
  · rw [Std.HashMap.getElem?_empty] at hm
    exact absurd hm (by simp)
  · obtain ⟨bi, hbi, hpairAt⟩ := List.mem_filterMap.1 hpair
    exact ⟨bi, hbi, hpairAt⟩

/-- A recognised pair's operand is a variable of the system (it sits in the interaction's
    payload). -/
theorem denseIdentityMap_operand_occ {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (y v : VarId) (h : (denseIdentityMap facts d)[y]? = some v) :
    v ∈ d.occ := by
  obtain ⟨bi, hbi, hpair⟩ := denseIdentityMap_mem facts d y v h
  obtain ⟨spec, oop, o1, o2, hspec, _, _, hdec, hoo⟩ := denseIdentityPairAt_spec facts bi y v hpair
  obtain ⟨ho1m, ho2m, _⟩ := spec.decode_mem _ _ _ _ _ hdec
  have hpv : ∀ (e : DenseExpr p), e ∈ bi.payload → v ∈ e.vars → v ∈ d.occ := fun e hem hve =>
    DenseConstraintSystem.mem_occ_of_bi hbi (by
      simp only [denseBIVars, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨e, hem, hve⟩)
  rcases denseOrIdentityOperand_spec o1 o2 v hoo with ⟨ho1, _⟩ | ⟨ho2, _⟩
  · exact hpv o1 (ho1 ▸ ho1m) (by rw [ho1]; simp [DenseExpr.vars])
  · exact hpv o2 (ho2 ▸ ho2m) (by rw [ho2]; simp [DenseExpr.vars])

/-! ## The pass -/

/-- Every mapped pair is forced by any satisfying assignment: `denv a = denv b` when
    `(denseIdentityMap facts d)[a]? = some b`. -/
theorem denseIdentityMap_forced {bs : BusSemantics p} (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (h1ne : (1 : ZMod p) ≠ 0) (denv : VarId → ZMod p)
    (hsat : d.satisfies bs denv) :
    ∀ a b, (denseIdentityMap facts d)[a]? = some b → denv a = denv b := by
  intro a b hab
  obtain ⟨bi, hbi, hpair⟩ := denseIdentityMap_mem facts d a b hab
  have hviol : bs.violatesConstraint (denseBIEval bi denv) = false := by
    refine hsat.2 bi hbi ?_
    obtain ⟨_, _, _, _, _, hmc, _, _, _⟩ := denseIdentityPairAt_spec facts bi a b hpair
    show (bi.multiplicity.eval denv) ≠ 0
    rw [hmc]; simpa using h1ne
  exact denseIdentityPairAt_sound facts bi a b hpair denv hviol

theorem denseIdentitySubstF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseIdentitySubstF bs facts d) [] bs := by
  unfold denseIdentitySubstF
  split
  · exact DensePassCorrect.refl reg.isInput d bs
  · split
    · rename_i h1ne
      refine DenseConstraintSystem.substF_denseCorrect d
        (denseIdentityFm (denseIdentityMap facts d) (denseIdentityMap facts d).size) bs reg.isInput
        ?_ ?_
      · -- each stored pair's resolved target composes the forced equalities along the chain
        intro denv hsat j t hf
        have hm := denseIdentityMap_forced facts d h1ne denv hsat
        simp only [denseIdentityFm, Option.map_eq_some_iff] at hf
        obtain ⟨w, hw, rfl⟩ := hf
        show denv j = denv (denseResolveGo (denseIdentityMap facts d) _ w)
        rw [denseResolveGo_sound (denseIdentityMap facts d) denv hm]
        exact hm j w hw
      · -- every resolved operand occurs in `d`
        intro j t hf z hz
        simp only [denseIdentityFm, Option.map_eq_some_iff] at hf
        obtain ⟨w, hw, rfl⟩ := hf
        simp only [DenseExpr.vars, List.mem_singleton] at hz
        subst hz
        exact denseResolveGo_prop (denseIdentityMap facts d) (· ∈ d.occ)
          (fun a b hab => denseIdentityMap_operand_occ facts d a b hab) _ w
          (denseIdentityMap_operand_occ facts d j w hw)
    · exact DensePassCorrect.refl reg.isInput d bs

theorem denseIdentitySubstF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseIdentitySubstF bs facts d).CoveredBy reg := by
  unfold denseIdentitySubstF
  split
  · exact hcov
  · split
    · refine DenseConstraintSystem.substF_covered hcov ?_
      intro i _ t hf z hz
      simp only [denseIdentityFm, Option.map_eq_some_iff] at hf
      obtain ⟨w, hw, rfl⟩ := hf
      simp only [DenseExpr.vars, List.mem_singleton] at hz
      subst hz
      exact DenseConstraintSystem.occ_valid hcov _
        (denseResolveGo_prop (denseIdentityMap facts d) (· ∈ d.occ)
          (fun a b hab => denseIdentityMap_operand_occ facts d a b hab) _ w
          (denseIdentityMap_operand_occ facts d i w hw))
    · exact hcov

/-- **The dense `identitySubst` step.** A single batch substitution of the OR-identity
    `result ↦ operand` map, connected to the audited spec via `DensePassCorrect.lift` (through
    `of`). -/
def denseIdentitySubstStep : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (fun bs facts d => denseIdentitySubstF bs facts d) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseIdentitySubstF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseIdentitySubstF_correct reg bs facts d)

/-- Run the dense identity substitution to a fixpoint so operand→operand chains collapse. -/
def denseIdentitySubstPass : DenseVerifiedPassW p :=
  denseIterateToFixpoint denseIdentitySubstStep

end ApcOptimizer.Dense
