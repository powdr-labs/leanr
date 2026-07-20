import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.ZeroRegister

set_option autoImplicit false

/-! # Dense fixed-zero-register pinning (Task 3)

Dense, `VarId`-native port of `zeroRegisterPass`. The pass consumes the `zeroCell` real-trace fact:
for every active fixed-zero memory message it appends `data_i = 0` for the message's data limbs
(filtered to non-trivial, not-already-present equalities over existing columns).

It is **fact-consuming**, so it is built with the DigitFold direct-`DensePassResult` construction
(threading the unchanged `BusFacts`), not `ofTransform`. The per-interaction `cellZeroExprs`
recognizer is mirrored on `DenseExpr` (the fact fields are VM-neutral: bus ids, payload slot indices,
and field constants), and the filter predicate's parts — `normalize.fold.isConstZero`, the
`contains` membership, and the `vars ⊆ cs.vars` gate — each commute with decode (the last via the
covered-injectivity of `resolve`, using the dense occurrence list `d.occ` for `cs.vars`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Small list helper -/

/-- Filtering commutes with a decode-map when the predicates agree pointwise on the list. -/
theorem filter_map_decode {α β : Type _} (f : α → β) {q : β → Bool} {r : α → Bool}
    (l : List α) (h : ∀ a ∈ l, q (f a) = r a) : (l.filter r).map f = (l.map f).filter q := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr (fun a ha => (h a ha).symm)

/-! ## `collectZeroCells` computes a flat map -/

theorem collectZeroCells_fst (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    ∀ (pending : List (BusInteraction (Expression p)))
      (hmem : ∀ bi ∈ pending, bi ∈ cs.busInteractions),
      (collectZeroCells cs bs facts pending hmem).1 = pending.flatMap (cellZeroExprs bs facts) := by
  intro pending
  induction pending with
  | nil => intro _; rfl
  | cons bi rest ih =>
      intro hmem
      show cellZeroExprs bs facts bi ++ (collectZeroCells cs bs facts rest _).1 = _
      rw [ih (fun b hb => hmem b (List.mem_cons_of_mem _ hb)), List.flatMap_cons]

/-! ## Dense per-interaction fixed-zero data limbs -/

/-- Dense `cellZeroExprs` (see `cellZeroExprs`). -/
def denseCellZeroExprs (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  match facts.zeroCell bi.busId with
  | none => []
  | some (addrReq, dataSlots) =>
    match bi.multiplicity.constValue? with
    | none => []
    | some c =>
      if decide (c ≠ 0) &&
          addrReq.all (fun ar => decide (bi.payload[ar.1]? = some (DenseExpr.const ar.2))) then
        dataSlots.map (fun slot => (bi.payload[slot]?).getD (DenseExpr.const 0))
      else []

theorem denseCellZeroExprs_decode (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    cellZeroExprs bs facts (reg.decodeBI bi)
      = (denseCellZeroExprs bs facts bi).map reg.decodeExpr := by
  unfold cellZeroExprs denseCellZeroExprs
  rw [show (reg.decodeBI bi).busId = bi.busId from rfl]
  cases facts.zeroCell bi.busId with
  | none => rfl
  | some adrs =>
      obtain ⟨addrReq, dataSlots⟩ := adrs
      dsimp only
      rw [show (reg.decodeBI bi).multiplicity = reg.decodeExpr bi.multiplicity from rfl,
        reg.decodeExpr_constValue?]
      cases bi.multiplicity.constValue? with
      | none => rfl
      | some c =>
          dsimp only
          have haddr : (fun ar : Nat × ZMod p =>
                decide ((reg.decodeBI bi).payload[ar.1]? = some (Expression.const ar.2)))
              = (fun ar => decide (bi.payload[ar.1]? = some (DenseExpr.const ar.2))) := by
            funext ar
            refine decide_eq_decide.mpr ?_
            show (bi.payload.map reg.decodeExpr)[ar.1]? = some (Expression.const ar.2) ↔ _
            rw [List.getElem?_map]
            cases bi.payload[ar.1]? with
            | none => simp
            | some e => simp only [Option.map_some, Option.some.injEq, reg.decodeExpr_eq_const]
          rw [haddr]
          by_cases hcond : decide (c ≠ 0) &&
              addrReq.all (fun ar => decide (bi.payload[ar.1]? = some (DenseExpr.const ar.2)))
          · rw [if_pos hcond, if_pos hcond, List.map_map]
            refine List.map_congr_left (fun slot _ => ?_)
            show ((reg.decodeBI bi).payload[slot]?).getD (Expression.const 0)
              = reg.decodeExpr ((bi.payload[slot]?).getD (DenseExpr.const 0))
            show ((bi.payload.map reg.decodeExpr)[slot]?).getD (Expression.const 0) = _
            rw [List.getElem?_map]
            cases bi.payload[slot]? with
            | none => rfl
            | some e => rfl
          · rw [if_neg hcond, if_neg hcond]; rfl

/-- Elements of the dense fixed-zero limbs of a covered interaction are covered. -/
theorem denseCellZeroExprs_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    {bi : BusInteraction (DenseExpr p)} (hbi : denseBICovered reg bi) :
    ∀ c ∈ denseCellZeroExprs bs facts bi, c.CoveredBy reg := by
  intro c hc
  unfold denseCellZeroExprs at hc
  cases hz : facts.zeroCell bi.busId with
  | none => rw [hz] at hc; simp at hc
  | some adrs =>
      obtain ⟨addrReq, dataSlots⟩ := adrs
      rw [hz] at hc
      cases hm : bi.multiplicity.constValue? with
      | none => rw [hm] at hc; simp at hc
      | some cval =>
          rw [hm] at hc
          dsimp only at hc
          split_ifs at hc with hcond
          · obtain ⟨slot, _, rfl⟩ := List.mem_map.1 hc
            cases hpsl : bi.payload[slot]? with
            | none => exact DenseExpr.coveredBy_const reg (0 : ZMod p)
            | some e =>
                rw [Option.getD_some]
                exact hbi.2 e (List.mem_of_getElem? hpsl)
          · simp at hc

/-! ## The dense filter predicate and its correspondence -/

/-- Dense fixed-zero filter predicate (see the filter inside `zeroRegisterPass`). -/
def denseZeroPred (d : DenseConstraintSystem p) (c : DenseExpr p) : Bool :=
  !c.normalize.fold.isConstZero && !d.algebraicConstraints.contains c
    && c.vars.all (fun z => decide (z ∈ d.occ))

/-- Spec fixed-zero filter predicate (the inline predicate of `zeroRegisterPass`). -/
def specZeroPred (cs : ConstraintSystem p) (c : Expression p) : Bool :=
  !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c
    && c.vars.all (fun z => decide (z ∈ cs.vars))

/-- `contains` under a decode-map commutes on covered lists (via covered-injectivity). -/
theorem contains_map_decode (reg : VarRegistry) {l : List (DenseExpr p)}
    (hl : ∀ e ∈ l, e.CoveredBy reg) {c : DenseExpr p} (hc : c.CoveredBy reg) :
    (l.map reg.decodeExpr).contains (reg.decodeExpr c) = l.contains c := by
  by_cases hm : c ∈ l
  · rw [List.contains_iff_mem.mpr hm, List.contains_iff_mem.mpr (List.mem_map.2 ⟨c, hm, rfl⟩)]
  · have hnm : reg.decodeExpr c ∉ l.map reg.decodeExpr := by
      intro hcon
      obtain ⟨e, he, heq⟩ := List.mem_map.1 hcon
      exact hm (reg.decodeExpr_inj (hl e he) hc heq ▸ he)
    have h1 : l.contains c = false := by
      cases hcc : l.contains c with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hcc) hm
    have h2 : (l.map reg.decodeExpr).contains (reg.decodeExpr c) = false := by
      cases hcc : (l.map reg.decodeExpr).contains (reg.decodeExpr c) with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hcc) hnm
    rw [h1, h2]

/-- `(reg.decodeCS d).vars` is the dense occurrence list resolved elementwise. -/
theorem VarRegistry.decodeCS_vars (reg : VarRegistry) (d : DenseConstraintSystem p) :
    (reg.decodeCS d).vars = d.occ.map reg.resolve := reg.decodeCS_occ d

/-- The membership gate `z ∈ cs.vars` commutes with decode on valid ids. -/
theorem occ_mem_decode (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    {z : VarId} (hz : reg.Valid z) :
    decide (reg.resolve z ∈ (reg.decodeCS d).vars) = decide (z ∈ d.occ) := by
  refine decide_eq_decide.mpr ?_
  rw [reg.decodeCS_vars d]
  constructor
  · intro h
    obtain ⟨w, hw, hwz⟩ := List.mem_map.1 h
    rw [reg.resolve_inj (DenseConstraintSystem.occ_valid hcov w hw) hz hwz] at hw
    exact hw
  · intro h; exact List.mem_map.2 ⟨z, h, rfl⟩

/-- The filter predicates agree pointwise, after decode, on covered expressions. -/
theorem specZeroPred_decode (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    {c : DenseExpr p} (hc : c.CoveredBy reg) :
    specZeroPred (reg.decodeCS d) (reg.decodeExpr c) = denseZeroPred d c := by
  unfold specZeroPred denseZeroPred
  have hA : (reg.decodeExpr c).normalize.fold.isConstZero = c.normalize.fold.isConstZero := by
    rw [← reg.decodeExpr_normalize c hc, ← reg.decodeExpr_fold, reg.decodeExpr_isConstZero]
  have hB : (reg.decodeCS d).algebraicConstraints.contains (reg.decodeExpr c)
      = d.algebraicConstraints.contains c :=
    contains_map_decode reg (fun e he => hcov.1 e he) hc
  have hC : (reg.decodeExpr c).vars.all (fun z => decide (z ∈ (reg.decodeCS d).vars))
      = c.vars.all (fun z => decide (z ∈ d.occ)) := by
    rw [reg.decodeExpr_vars, List.all_map]
    refine list_all_congr (fun z hz => ?_)
    exact occ_mem_decode reg d hcov (hc z hz)
  rw [hA, hB, hC]

/-! ## The dense transform and pass -/

/-- The dense fixed-zero pinning transform. Appends the filtered fixed-zero data limbs (identity when
    there are none), mirroring `zeroRegisterPass`. -/
def denseZeroRegisterF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  let new := (d.busInteractions.flatMap (denseCellZeroExprs bs facts)).filter (denseZeroPred d)
  if new.isEmpty then d
  else { d with algebraicConstraints := d.algebraicConstraints ++ new }

/-- The spec pass output, in flat-map/filter form (the `collectZeroCells` subtype unpacked). -/
theorem zeroRegisterPass_out (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    (zeroRegisterPass cs bs facts).out
      = (if ((cs.busInteractions.flatMap (cellZeroExprs bs facts)).filter (specZeroPred cs)).isEmpty
         then cs
         else { cs with algebraicConstraints := cs.algebraicConstraints
            ++ (cs.busInteractions.flatMap (cellZeroExprs bs facts)).filter (specZeroPred cs) }) := by
  have hproof := (collectZeroCells cs bs facts cs.busInteractions (fun _ h => h)).2
  rw [collectZeroCells_fst cs bs facts cs.busInteractions (fun _ h => h)] at hproof
  have hczeq : collectZeroCells cs bs facts cs.busInteractions (fun _ h => h)
      = ⟨cs.busInteractions.flatMap (cellZeroExprs bs facts), hproof⟩ :=
    Subtype.ext (collectZeroCells_fst cs bs facts cs.busInteractions (fun _ h => h))
  unfold zeroRegisterPass
  rw [hczeq]
  dsimp only
  rw [apply_ite PassResult.out]
  rfl

/-- The dense output covers its registry. -/
theorem denseZeroRegisterF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseZeroRegisterF bs facts d).CoveredBy reg := by
  have hnew : ∀ c ∈ (d.busInteractions.flatMap (denseCellZeroExprs bs facts)).filter (denseZeroPred d),
      c.CoveredBy reg := by
    intro c hc
    obtain ⟨bi, hbi, hcbi⟩ := List.mem_flatMap.1 (List.mem_of_mem_filter hc)
    exact denseCellZeroExprs_covered reg bs facts (hcov.2 bi hbi) c hcbi
  unfold denseZeroRegisterF
  by_cases he : ((d.busInteractions.flatMap (denseCellZeroExprs bs facts)).filter
      (denseZeroPred d)).isEmpty
  · rw [if_pos he]; exact hcov
  · rw [if_neg he]
    refine ⟨fun e hemem => ?_, fun bi hbimem => hcov.2 bi hbimem⟩
    rcases List.mem_append.1 hemem with h | h
    · exact hcov.1 e h
    · exact hnew e h

/-- The dense fixed-zero-register pass. Fact-consuming; inherits `zeroRegisterPass`'s `PassCorrect`
    through the decode-commutation of its transform. -/
def denseZeroRegisterPass : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := denseZeroRegisterF bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := denseZeroRegisterF_covered reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := by
      show PassCorrect (reg.decodeCS d) (reg.decodeCS (denseZeroRegisterF bs facts d))
        (reg.decodeDerivs ([] : DenseDerivations p)) bs
      have hnew : ((d.busInteractions.flatMap (denseCellZeroExprs bs facts)).filter
              (denseZeroPred d)).map reg.decodeExpr
          = ((reg.decodeCS d).busInteractions.flatMap (cellZeroExprs bs facts)).filter
              (specZeroPred (reg.decodeCS d)) := by
        have hcovE : ∀ c ∈ d.busInteractions.flatMap (denseCellZeroExprs bs facts),
            c.CoveredBy reg := by
          intro c hc
          obtain ⟨bi, hbi, hcbi⟩ := List.mem_flatMap.1 hc
          exact denseCellZeroExprs_covered reg bs facts (hcov.2 bi hbi) c hcbi
        rw [filter_map_decode reg.decodeExpr _
              (fun c hc => specZeroPred_decode reg d hcov (hcovE c hc))]
        congr 1
        show ((d.busInteractions.flatMap (denseCellZeroExprs bs facts)).map reg.decodeExpr) = _
        rw [List.map_flatMap]
        show (d.busInteractions.flatMap
            (fun bi => (denseCellZeroExprs bs facts bi).map reg.decodeExpr)) = _
        rw [show (reg.decodeCS d).busInteractions = d.busInteractions.map reg.decodeBI from rfl,
          List.flatMap_map]
        exact List.flatMap_congr (fun bi _ => (denseCellZeroExprs_decode reg bs facts bi).symm)
      have hlen : ((d.busInteractions.flatMap (denseCellZeroExprs bs facts)).filter
              (denseZeroPred d)).isEmpty
          = (((reg.decodeCS d).busInteractions.flatMap (cellZeroExprs bs facts)).filter
              (specZeroPred (reg.decodeCS d))).isEmpty := by
        rw [← hnew, List.isEmpty_map]
      have hout : reg.decodeCS (denseZeroRegisterF bs facts d)
          = (zeroRegisterPass (reg.decodeCS d) bs facts).out := by
        rw [zeroRegisterPass_out]
        unfold denseZeroRegisterF
        by_cases he : ((d.busInteractions.flatMap (denseCellZeroExprs bs facts)).filter
            (denseZeroPred d)).isEmpty
        · rw [if_pos he, if_pos (hlen ▸ he)]
        · rw [if_neg he, if_neg (hlen ▸ he), reg.decodeCS_append_constraints d, hnew]
      rw [show reg.decodeDerivs ([] : DenseDerivations p) = [] from rfl, hout]
      have hderiv : (zeroRegisterPass (reg.decodeCS d) bs facts).derivs = [] := by
        unfold zeroRegisterPass
        rcases collectZeroCells (reg.decodeCS d) bs facts (reg.decodeCS d).busInteractions
          (fun _ h => h) with ⟨exprs, hexprs⟩
        dsimp only
        split <;> rfl
      have hc := (zeroRegisterPass (reg.decodeCS d) bs facts).correct
      rw [hderiv] at hc
      exact hc }

end ApcOptimizer.Dense
