import ApcOptimizer.Implementation.OptimizerPasses.XorEqExtract
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify

set_option autoImplicit false

/-! # Dense XOR/OR/AND constant-operand equality extraction: correctness and wiring

`DensePassCorrect` proof for `XorEqExtract.lean` via `DensePassCorrect.denseAddConstraints`,
lifted through `DenseVerifiedPassW.of`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `ZMod.val` is injective (nonzero characteristic). -/
private theorem val_inj [NeZero p] (a b : ZMod p) (h : a.val = b.val) : a = b :=
  (ZMod.natCast_rightInverse a).symm.trans ((congrArg _ h).trans (ZMod.natCast_rightInverse b))

/-- `(255 − a).val = 255 − a.val` for a byte `a` in a field with `256 ≤ p` (no wraparound). -/
private theorem sub255_val (hp : 256 ≤ p) (a : ZMod p) (ha : a.val < 256) :
    (255 - a).val = 255 - a.val := by
  haveI : NeZero p := ⟨by omega⟩
  have hcast255 : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  have hle : a.val ≤ 255 := Nat.le_of_lt_succ (by omega)
  have ha' : a = ((a.val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse a).symm
  calc (255 - a).val
      = ((255 : ZMod p) - ((a.val : ℕ) : ZMod p)).val := by rw [← ha']
    _ = (((255 - a.val : ℕ) : ZMod p)).val := by rw [Nat.cast_sub hle, hcast255]
    _ = 255 - a.val := ZMod.val_natCast_of_lt (by omega)

theorem denseComplExpr_eval (e : DenseExpr p) (denv : VarId → ZMod p) :
    (denseComplExpr e).eval denv = 255 - e.eval denv := by
  simp only [denseComplExpr, DenseExpr.eval]; ring

theorem denseOpIs_iff {o : Option (ZMod p)} {op : DenseExpr p} :
    denseOpIs o op = true ↔ ∃ v, o = some v ∧ op = DenseExpr.const v := by
  unfold denseOpIs
  cases o with
  | none => simp
  | some v => simp

/-! ## XOR half -/

theorem denseXorEq?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseXorEq? bs facts bi = some c) :
    ∃ (spec : ByteXorSpec p) (o1 o2 r : DenseExpr p),
      facts.byteXorSpec bi.busId = some spec ∧ bi.multiplicity = DenseExpr.const 1 ∧
      spec.decode bi.payload = some (DenseExpr.const spec.xorOp, o1, o2, r) ∧
        ((o1 = DenseExpr.const 0 ∧ c = denseEqExpr r o2)
          ∨ (o2 = DenseExpr.const 0 ∧ c = denseEqExpr r o1)
          ∨ (256 ≤ p ∧ spec.bound = 256 ∧ o1 = DenseExpr.const 255
              ∧ c = denseEqExpr r (denseComplExpr o2))
          ∨ (256 ≤ p ∧ spec.bound = 256 ∧ o2 = DenseExpr.const 255
              ∧ c = denseEqExpr r (denseComplExpr o1))) := by
  grind [denseXorEq?]

theorem denseXorEq?_eval (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (denv : VarId → ZMod p)
    (h1ne : (1 : ZMod p) ≠ 0) (h : denseXorEq? bs facts bi = some c) (hbi : bi ∈ d.busInteractions)
    (hsat : d.satisfies bs denv) : c.eval denv = 0 := by
  obtain ⟨spec, o1, o2, r, hspec, hmult, hdec, hcase⟩ := denseXorEq?_spec bs facts bi c h
  have hviol : bs.violatesConstraint (denseBIEval bi denv) = false := by
    refine hsat.2 bi hbi ?_
    show (bi.multiplicity.eval denv) ≠ 0
    rw [hmult]; simpa using h1ne
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
  have hdecEv : spec.decode (denseBIEval bi denv).payload
      = some (spec.xorOp, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]; rfl
  obtain ⟨ho1b, ho2b, hrval⟩ :=
    ((hsound (denseBIEval bi denv).payload spec.xorOp (o1.eval denv) (o2.eval denv) (r.eval denv)
      (denseBIEval bi denv).multiplicity hdecEv).1 rfl).mp hviol
  haveI := spec.pNeZero
  rcases hcase with ⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨hp, hbnd, hz, rfl⟩ | ⟨hp, hbnd, hz, rfl⟩
  · rw [denseEqExpr_eval]
    have hzero : (o1.eval denv) = 0 := by rw [hz]; rfl
    rw [hzero, ZMod.val_zero] at hrval
    rw [val_inj _ _ (hrval.trans (Nat.zero_xor _)), sub_self]
  · rw [denseEqExpr_eval]
    have hzero : (o2.eval denv) = 0 := by rw [hz]; rfl
    rw [hzero, ZMod.val_zero] at hrval
    rw [val_inj _ _ (hrval.trans (Nat.xor_zero _)), sub_self]
  · rw [denseEqExpr_eval, denseComplExpr_eval]
    have hcast255 : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
    have h255v : (255 : ZMod p).val = 255 := by
      rw [← hcast255, ZMod.val_natCast_of_lt (by omega)]
    have ho1 : (o1.eval denv) = 255 := by rw [hz]; rfl
    rw [ho1, h255v] at hrval
    have hx : (r.eval denv).val = 255 - (o2.eval denv).val := by
      rw [hrval, show Nat.xor 255 (o2.eval denv).val = Nat.xor (o2.eval denv).val 255
        from Nat.xor_comm _ _]
      exact nat_xor_255 _ (hbnd ▸ ho2b)
    rw [val_inj _ _ (hx.trans (sub255_val hp _ (hbnd ▸ ho2b)).symm), sub_self]
  · rw [denseEqExpr_eval, denseComplExpr_eval]
    have hcast255 : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
    have h255v : (255 : ZMod p).val = 255 := by
      rw [← hcast255, ZMod.val_natCast_of_lt (by omega)]
    have ho2 : (o2.eval denv) = 255 := by rw [hz]; rfl
    rw [ho2, h255v] at hrval
    have hx : (r.eval denv).val = 255 - (o1.eval denv).val := by
      rw [hrval]; exact nat_xor_255 _ (hbnd ▸ ho1b)
    rw [val_inj _ _ (hx.trans (sub255_val hp _ (hbnd ▸ ho1b)).symm), sub_self]

/-- Every variable of a recognised XOR equality occurs in `d`. -/
theorem denseXorEq?_vars (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseXorEq? bs facts bi = some c)
    (hbi : bi ∈ d.busInteractions) (z : VarId) (hz : z ∈ c.vars) : z ∈ d.occ := by
  obtain ⟨spec, o1, o2, r, _, _, hdec, hcase⟩ := denseXorEq?_spec bs facts bi c h
  obtain ⟨ho1m, ho2m, hrm⟩ := spec.decode_mem _ _ _ _ _ hdec
  have hpv : ∀ (e : DenseExpr p), e ∈ bi.payload → z ∈ e.vars → z ∈ d.occ := fun e hem hze =>
    DenseConstraintSystem.mem_occ_of_bi hbi (by
      simp only [denseBIVars, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨e, hem, hze⟩)
  rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    rcases List.mem_append.1 (by simpa only [denseEqExpr, denseComplExpr, DenseExpr.vars,
      List.append_assoc, List.nil_append] using hz) with h_r | h_o
  · exact hpv r hrm h_r
  · exact hpv o2 ho2m h_o
  · exact hpv r hrm h_r
  · exact hpv o1 ho1m h_o
  · exact hpv r hrm h_r
  · exact hpv o2 ho2m h_o
  · exact hpv r hrm h_r
  · exact hpv o1 ho1m h_o

/-! ## OR / AND half -/

theorem denseBoolEq?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseBoolEq? bs facts bi = some c) :
    ∃ (spec : ByteXorSpec p) (op o1 o2 r : DenseExpr p),
      facts.byteXorSpec bi.busId = some spec ∧ bi.multiplicity = DenseExpr.const 1 ∧
      spec.decode bi.payload = some (op, o1, o2, r) ∧
        ((∃ oop, spec.orOp = some oop ∧ op = DenseExpr.const oop ∧
            ((o1 = DenseExpr.const 0 ∧ c = denseEqExpr r o2)
              ∨ (o2 = DenseExpr.const 0 ∧ c = denseEqExpr r o1)))
          ∨ (∃ aop, spec.andOp = some aop ∧ op = DenseExpr.const aop ∧
              ((o1 = DenseExpr.const 0 ∨ o2 = DenseExpr.const 0) ∧ c = r))) := by
  grind [denseBoolEq?, denseOpIs_iff]

theorem denseBoolEq?_eval (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (denv : VarId → ZMod p)
    (h1ne : (1 : ZMod p) ≠ 0) (h : denseBoolEq? bs facts bi = some c) (hbi : bi ∈ d.busInteractions)
    (hsat : d.satisfies bs denv) : c.eval denv = 0 := by
  obtain ⟨spec, op, o1, o2, r, hspec, hmult, hdec, hcase⟩ := denseBoolEq?_spec bs facts bi c h
  have hviol : bs.violatesConstraint (denseBIEval bi denv) = false := by
    refine hsat.2 bi hbi ?_
    show (bi.multiplicity.eval denv) ≠ 0
    rw [hmult]; simpa using h1ne
  have hdecEv : spec.decode (denseBIEval bi denv).payload
      = some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]; rfl
  obtain ⟨horc, handc⟩ := facts.byteBoolSound bi.busId spec hspec (denseBIEval bi denv).payload
    (op.eval denv) (o1.eval denv) (o2.eval denv) (r.eval denv) (denseBIEval bi denv).multiplicity
    hdecEv
  haveI := spec.pNeZero
  rcases hcase with ⟨oop, hspecOr, hopeq, hcc⟩ | ⟨aop, hspecAnd, hopeq, hcc⟩
  · have hopev : op.eval denv = oop := by rw [hopeq]; rfl
    obtain ⟨_, _, hrval⟩ := (horc oop hspecOr hopev).mp hviol
    rcases hcc with ⟨hz, rfl⟩ | ⟨hz, rfl⟩
    · rw [denseEqExpr_eval]
      have ho1z : (o1.eval denv) = 0 := by rw [hz]; rfl
      rw [ho1z, ZMod.val_zero] at hrval
      have heq : (r.eval denv).val = (o2.eval denv).val := by rw [hrval]; simp
      rw [val_inj _ _ heq, sub_self]
    · rw [denseEqExpr_eval]
      have ho2z : (o2.eval denv) = 0 := by rw [hz]; rfl
      rw [ho2z, ZMod.val_zero] at hrval
      have heq : (r.eval denv).val = (o1.eval denv).val := by rw [hrval]; simp
      rw [val_inj _ _ heq, sub_self]
  · have hopev : op.eval denv = aop := by rw [hopeq]; rfl
    obtain ⟨_, _, hrval⟩ := (handc aop hspecAnd hopev).mp hviol
    obtain ⟨hz, rfl⟩ := hcc
    refine (ZMod.val_eq_zero _).mp ?_
    rcases hz with hz | hz
    · have : (o1.eval denv) = 0 := by rw [hz]; rfl
      rw [this, ZMod.val_zero] at hrval; rw [hrval]; simp
    · have : (o2.eval denv) = 0 := by rw [hz]; rfl
      rw [this, ZMod.val_zero] at hrval; rw [hrval]; simp

/-- Every variable of a recognised OR/AND equality occurs in `d`. -/
theorem denseBoolEq?_vars (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p) (h : denseBoolEq? bs facts bi = some c)
    (hbi : bi ∈ d.busInteractions) (z : VarId) (hz : z ∈ c.vars) : z ∈ d.occ := by
  obtain ⟨spec, op, o1, o2, r, _, _, hdec, hcase⟩ := denseBoolEq?_spec bs facts bi c h
  obtain ⟨ho1m, ho2m, hrm⟩ := spec.decode_mem _ _ _ _ _ hdec
  have hpv : ∀ (e : DenseExpr p), e ∈ bi.payload → z ∈ e.vars → z ∈ d.occ := fun e hem hze =>
    DenseConstraintSystem.mem_occ_of_bi hbi (by
      simp only [denseBIVars, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨e, hem, hze⟩)
  rcases hcase with ⟨oop, _, _, hcc⟩ | ⟨aop, _, _, hcc⟩
  · rcases hcc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases List.mem_append.1 (by simpa only [denseEqExpr, DenseExpr.vars,
        List.append_assoc, List.nil_append] using hz) with h_r | h_o
    · exact hpv r hrm h_r
    · exact hpv o2 ho2m h_o
    · exact hpv r hrm h_r
    · exact hpv o1 ho1m h_o
  · obtain ⟨_, rfl⟩ := hcc
    exact hpv _ hrm hz

/-! ## The pass -/

/-- The appended list of entailed equalities; gated on `(1 : ZMod p) ≠ 0`. -/
def denseXorEqExtractNew (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  if (1 : ZMod p) ≠ 0 then
    d.busInteractions.filterMap (denseXorEq? bs facts)
      ++ d.busInteractions.filterMap (denseBoolEq? bs facts)
  else []

theorem denseXorEqExtractNew_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseXorEqExtractNew bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  grind [denseXorEqExtractNew, denseXorEq?_vars, denseBoolEq?_vars]

theorem denseXorEqExtractNew_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p)
    (hsat : d.satisfies bs denv) : ∀ c ∈ denseXorEqExtractNew bs facts d, c.eval denv = 0 := by
  grind [denseXorEqExtractNew, denseXorEq?_eval, denseBoolEq?_eval]

/-- The dense `xorEqExtract` pass: for a byte XOR/OR/AND interaction with a constant operand, adds
    the resulting equality on the result cell as a constraint — e.g. `0 XOR b = r` gives `r = b`,
    `255 XOR b = r` gives `r = 255 − b`. -/
def denseXorEqExtractPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofAddConstraints denseXorEqExtractNew denseXorEqExtractNew_vars
    (fun bs facts d denv _ hsat => denseXorEqExtractNew_sound bs facts d denv hsat)

end ApcOptimizer.Dense
