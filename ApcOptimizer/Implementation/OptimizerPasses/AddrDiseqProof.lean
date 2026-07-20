import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Bridge
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.AddrDiseq

set_option autoImplicit false

/-! # Native soundness for the dense address-disequality certificate library (Task 3, chunk M1)

The proof layer for `Dense/AddrDiseq.lean`. This module is a **library**: it exposes no pass, only the
value-level soundness lemmas the upcoming dense `busUnify` native proof (chunk M2) — and later
`busPairCancel` — consume to discharge their `DensePassCorrect` without re-proving representation
correspondence per certificate.

## Proof strategy

Each dense certificate is proved sound **at the value level** over dense environments `VarId → ZMod p`
(`DenseExpr.eval`/`denseBIEval`), by **reusing the audited spec `_sound` lemmas** after decoding the
arguments and environment through the registry:

* the dense environment `denv` is extended to a spec environment `reg.extendEnv denv (fun _ => 0)`
  (`Dense/Bridge.lean`);
* the dense arguments (lin forms, expressions, bus interactions) are decoded through the registry;
* the spec lemma (`addrAffineNeq_sound`, `addrNonzeroNeq_sound`, `constDiffNZ_sound`,
  `twoRootOf?_sound`, `ptrBranchesOf_eval`, `diffSumOver_eval_zero`, …) is applied to the decoded data;
* the conclusion is transported back to the dense side with `decodeLin_eval`/`decodeExpr_eval` and the
  covered-var congruence.

This is the established fact-consuming template (`Dense/DomainBatchNativeProof.lean` applies BusFacts
soundness at the value level the same way) and is *not* the forbidden landing tactic: it reuses spec
*lemmas* at the value level, never a reference *pass*'s `PassCorrect`.

The one certificate whose spec `_sound` lemma consumes a proof-carrying `TwoRootMap`
(`addrTwoRootNeq_sound`) is handled through a **lookup-wise soundness invariant**
`DenseTwoRootMap.Sound` (the dense mirror of `TwoRootMap.sound`, proved by induction along
`build`/`addAll`/`addVars`/`insertEntry`): the map-iteration glue (`ptrReductions`/`exprTwoRootNeq`)
is re-established over the dense map while the field-membership algebra (`twoRootOf?_sound`,
`ptrBranchesOf_eval`, `constDiffNZ_sound`) is reused from spec. No whole-`HashMap` decode-equality is
used.

`denseTwoRootOf?_decode` (the decode-commutation of `denseTwoRootOf?`) is flagged for reuse by the
later dense `rootPairUnify` port (chunk S1). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Environment/decode bridges: dense eval under `denv` = spec eval of the decode under the
    extended env -/

/-- A dense linear form's value under `denv` equals its decode's value under the extended env
    (all term ids valid). -/
theorem eval_decodeLin_extendEnv (reg : VarRegistry) (l : DenseLinExpr p)
    (hv : ∀ i ∈ l.terms.map Prod.fst, reg.Valid i) (denv : VarId → ZMod p) (E : Variable → ZMod p) :
    (reg.decodeLin l).eval (reg.extendEnv denv E) = l.eval denv := by
  have hmap : (l.terms.map (fun t : VarId × ZMod p => t.2 * reg.extendEnv denv E (reg.resolve t.1)))
            = (l.terms.map (fun t => t.2 * denv t.1)) :=
    List.map_congr_left (fun t ht => by
      rw [reg.extendEnv_resolve denv E (hv t.1 (List.mem_map.2 ⟨t, ht, rfl⟩))])
  rw [reg.decodeLin_eval l (reg.extendEnv denv E)]
  simp only [DenseLinExpr.eval]
  rw [hmap]

/-- A dense expression's value under `denv`, resolved into the extended env. -/
private theorem denseExpr_eval_resolve (reg : VarRegistry) (e : DenseExpr p) (hc : e.CoveredBy reg)
    (denv : VarId → ZMod p) (E : Variable → ZMod p) :
    e.eval (fun i => reg.extendEnv denv E (reg.resolve i)) = e.eval denv := by
  induction e with
  | const n => rfl
  | var i => exact reg.extendEnv_resolve denv E (hc i (by simp [DenseExpr.vars]))
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      simp only [DenseExpr.eval, iha ha, ihb hb]
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      simp only [DenseExpr.eval, iha ha, ihb hb]

/-- A dense expression's value under `denv` equals its decode's value under the extended env
    (covered). -/
theorem eval_decodeExpr_extendEnv (reg : VarRegistry) (e : DenseExpr p) (hc : e.CoveredBy reg)
    (denv : VarId → ZMod p) (E : Variable → ZMod p) :
    (reg.decodeExpr e).eval (reg.extendEnv denv E) = e.eval denv := by
  rw [reg.decodeExpr_eval e (reg.extendEnv denv E)]; exact denseExpr_eval_resolve reg e hc denv E

/-- A `VarId` occurring in a covered dense bus interaction is valid. -/
theorem denseBICovered_valid (reg : VarRegistry) (bi : BusInteraction (DenseExpr p))
    (hc : denseBICovered reg bi) {i : VarId} (hi : i ∈ denseBIVars bi) : reg.Valid i := by
  simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hi
  rcases hi with hm | ⟨e, he, hie⟩
  · exact hc.1 i hm
  · exact hc.2 e he i hie

/-- A dense bus interaction's evaluation under `denv` equals its decode's evaluation under the
    extended env (covered). -/
theorem denseBIEval_extendEnv (reg : VarRegistry) (bi : BusInteraction (DenseExpr p))
    (hc : denseBICovered reg bi) (denv : VarId → ZMod p) (E : Variable → ZMod p) :
    (reg.decodeBI bi).eval (reg.extendEnv denv E) = denseBIEval bi denv := by
  rw [reg.decodeBI_eval bi (reg.extendEnv denv E)]
  exact denseBIEval_congr bi _ _
    (fun i hi => reg.extendEnv_resolve denv E (denseBICovered_valid reg bi hc hi))

/-! ## Decode-commutation of the simple (map-free) certificate helpers -/

/-- **`constDiffNZ` decodes** (validity-gated). -/
theorem VarRegistry.denseConstDiffNZ_decode (reg : VarRegistry) (a b : DenseLinExpr p)
    (ha : ∀ i ∈ a.terms.map Prod.fst, reg.Valid i) (hb : ∀ i ∈ b.terms.map Prod.fst, reg.Valid i) :
    denseConstDiffNZ a b = constDiffNZ (reg.decodeLin a) (reg.decodeLin b) := by
  have hv : ∀ i ∈ (a.add (b.scale (-1))).terms.map Prod.fst, reg.Valid i := by
    intro i hi
    simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hi
    rcases hi with h | h
    · exact ha i h
    · rw [DenseLinExpr.scale_terms_fst] at h; exact hb i h
  have hdecode : reg.decodeLin ((a.add (b.scale (-1))).norm)
      = ((reg.decodeLin a).add ((reg.decodeLin b).scale (-1))).norm := by
    rw [reg.decodeLin_norm _ hv, reg.decodeLin_add, reg.decodeLin_scale]
  simp only [denseConstDiffNZ, constDiffNZ]
  rw [show ((reg.decodeLin a).add ((reg.decodeLin b).scale (-1))).norm
        = reg.decodeLin ((a.add (b.scale (-1))).norm) from hdecode.symm,
     reg.decodeLin_terms_isEmpty, reg.decodeLin_const]

/-- **`isZeroLin` decodes** (validity-gated). -/
theorem VarRegistry.denseIsZeroLin_decode (reg : VarRegistry) (l : DenseLinExpr p)
    (hv : ∀ i ∈ l.terms.map Prod.fst, reg.Valid i) :
    denseIsZeroLin l = isZeroLin (reg.decodeLin l) := by
  simp only [denseIsZeroLin, isZeroLin]
  rw [show (reg.decodeLin l).norm = reg.decodeLin l.norm from (reg.decodeLin_norm l hv).symm,
     reg.decodeLin_terms_isEmpty, reg.decodeLin_const]

/-- `constDiffNZ` soundness, transported to the dense side. -/
theorem denseConstDiffNZ_sound (reg : VarRegistry) (a b : DenseLinExpr p)
    (ha : ∀ i ∈ a.terms.map Prod.fst, reg.Valid i) (hb : ∀ i ∈ b.terms.map Prod.fst, reg.Valid i)
    (h : denseConstDiffNZ a b = true) (denv : VarId → ZMod p) : a.eval denv ≠ b.eval denv := by
  rw [reg.denseConstDiffNZ_decode a b ha hb] at h
  have hs := constDiffNZ_sound (reg.decodeLin a) (reg.decodeLin b) h (reg.extendEnv denv (fun _ => 0))
  rwa [eval_decodeLin_extendEnv reg a ha, eval_decodeLin_extendEnv reg b hb] at hs

/-! ## Address-slot glue: a per-slot value disequality forces an address disequality (dense) -/

/-- If some declared address slot of `S` and `bi` evaluates differently under `denv`, the addresses
    differ. Dense mirror of the `addr_eq_slot` contrapositive. -/
theorem denseAddr_slot_neq (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p))
    (denv : VarId → ZMod p) {slot : Nat} (hslot : slot ∈ shape.addressFields)
    {e e' : DenseExpr p} (hSe : S.payload[slot]? = some e) (hbe : bi.payload[slot]? = some e')
    (hne : e.eval denv ≠ e'.eval denv) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  intro heq
  obtain ⟨j, hj⟩ : ∃ j, shape.addressFields[j]? = some slot := List.getElem?_of_mem hslot
  have e1 : (shape.address (denseBIEval S denv))[j]? = some ((denseBIEval S denv).payload[slot]?) := by
    simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
  have e2 : (shape.address (denseBIEval bi denv))[j]? = some ((denseBIEval bi denv).payload[slot]?) := by
    simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
  rw [heq, e2] at e1
  have key : (denseBIEval S denv).payload[slot]? = (denseBIEval bi denv).payload[slot]? :=
    (Option.some.inj e1).symm
  have keyS : (denseBIEval S denv).payload[slot]? = some (e.eval denv) := by
    show (S.payload.map (fun e => e.eval denv))[slot]? = some (e.eval denv)
    rw [List.getElem?_map, hSe]; rfl
  have keyB : (denseBIEval bi denv).payload[slot]? = some (e'.eval denv) := by
    show (bi.payload.map (fun e => e.eval denv))[slot]? = some (e'.eval denv)
    rw [List.getElem?_map, hbe]; rfl
  rw [keyS, keyB] at key
  exact hne (Option.some.inj key)

/-! ## The affine (same-base) certificate: reuse `addrAffineNeq_sound` via decode -/

/-- **`denseAddrAffineNeq` is sound.** Some address slot linearizes to two affine forms differing by a
    nonzero constant, so the addresses differ. Reuses `addrAffineNeq_sound`. -/
theorem denseAddrAffineNeq_sound (reg : VarRegistry) (shape : MemoryBusShape)
    (S bi : BusInteraction (DenseExpr p)) (hS : denseBICovered reg S) (hbi : denseBICovered reg bi)
    (h : denseAddrAffineNeq shape S bi = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  have hspec : addrAffineNeq shape (reg.decodeBI S) (reg.decodeBI bi) = true := by
    obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
    refine List.any_eq_true.2 ⟨slot, hslot, ?_⟩
    cases hSp : S.payload[slot]? with
    | none => simp [hSp] at hcond
    | some e =>
      cases hbp : bi.payload[slot]? with
      | none => simp [hSp, hbp] at hcond
      | some e' =>
        simp only [hSp, hbp] at hcond
        have hSp' : (reg.decodeBI S).payload[slot]? = some (reg.decodeExpr e) := by
          show (S.payload.map reg.decodeExpr)[slot]? = _; rw [List.getElem?_map, hSp]; rfl
        have hbp' : (reg.decodeBI bi).payload[slot]? = some (reg.decodeExpr e') := by
          show (bi.payload.map reg.decodeExpr)[slot]? = _; rw [List.getElem?_map, hbp]; rfl
        simp only [hSp', hbp']
        cases hLe : denseLinearize e with
        | none => simp [hLe] at hcond
        | some L =>
          cases hLe' : denseLinearize e' with
          | none => simp [hLe, hLe'] at hcond
          | some L' =>
            simp only [hLe, hLe'] at hcond
            have hecov : e.CoveredBy reg := hS.2 e (List.mem_of_getElem? hSp)
            have he'cov : e'.CoveredBy reg := hbi.2 e' (List.mem_of_getElem? hbp)
            have hLval : ∀ i ∈ L.terms.map Prod.fst, reg.Valid i :=
              reg.denseLinearize_covered_terms hecov hLe
            have hL'val : ∀ i ∈ L'.terms.map Prod.fst, reg.Valid i :=
              reg.denseLinearize_covered_terms he'cov hLe'
            have hLinS : linearize (reg.decodeExpr e) = some (reg.decodeLin L) := by
              rw [← reg.denseLinearize_decode e, hLe]; rfl
            have hLinS' : linearize (reg.decodeExpr e') = some (reg.decodeLin L') := by
              rw [← reg.denseLinearize_decode e', hLe']; rfl
            simp only [hLinS, hLinS']
            rw [← reg.denseConstDiffNZ_decode L L' hLval hL'val]
            exact hcond
  have hsound := addrAffineNeq_sound shape (reg.decodeBI S) (reg.decodeBI bi) hspec
    (reg.extendEnv denv (fun _ => 0))
  rwa [denseBIEval_extendEnv reg S hS denv (fun _ => 0),
     denseBIEval_extendEnv reg bi hbi denv (fun _ => 0)] at hsound

/-! ## The reciprocal-nonzero certificate

`DenseNonzeroWits` mirrors `NonzeroWits` (a *list*), so the correspondence is a clean list decode; the
spec `NonzeroWits.build (decoded)` supplies a genuine proof-carrying witness structure, and
`addrNonzeroNeq_sound` is reused via decode. -/

/-- **`reciprocalWitsProd` decodes.** No validity needed (`linearize` never compares variables). -/
theorem VarRegistry.denseReciprocalWitsProd_decode (reg : VarRegistry) (a b r : DenseExpr p) :
    (denseReciprocalWitsProd a b r).map reg.decodeLin
      = reciprocalWitsProd (reg.decodeExpr a) (reg.decodeExpr b) (reg.decodeExpr r) := by
  unfold denseReciprocalWitsProd reciprocalWitsProd
  rw [← reg.denseLinearize_decode r]
  cases hLr : denseLinearize r with
  | none => simp
  | some lr =>
      simp only [Option.map_some, reg.decodeLin_terms_isEmpty, reg.decodeLin_const]
      split_ifs with hc
      · rw [List.map_append, ← reg.denseLinearize_decode a, ← reg.denseLinearize_decode b]
        congr 1
        · cases denseLinearize a <;> simp
        · cases denseLinearize b <;> simp
      · simp

/-- **`reciprocalWits?` decodes.** -/
theorem VarRegistry.denseReciprocalWits?_decode (reg : VarRegistry) (c : DenseExpr p) :
    (denseReciprocalWits? c).map reg.decodeLin = reciprocalWits? (reg.decodeExpr c) := by
  cases c with
  | const n => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
  | var i => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
  | mul a b => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
  | add e1 e2 =>
      cases e1 with
      | mul a b =>
          simp only [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
          exact reg.denseReciprocalWitsProd_decode a b e2
      | const n =>
          cases e2 with
          | mul a b =>
              simp only [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
              exact reg.denseReciprocalWitsProd_decode a b (.const n)
          | const m => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
          | var i => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
          | add x y => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
      | var i =>
          cases e2 with
          | mul a b =>
              simp only [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
              exact reg.denseReciprocalWitsProd_decode a b (.var i)
          | const m => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
          | var j => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
          | add x y => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
      | add x y =>
          cases e2 with
          | mul a b =>
              simp only [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
              exact reg.denseReciprocalWitsProd_decode a b (.add x y)
          | const m => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
          | var j => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]
          | add u w => simp [denseReciprocalWits?, reciprocalWits?, VarRegistry.decodeExpr]

/-- Every term id of a reciprocal witness of a covered constraint is valid. -/
theorem VarRegistry.denseReciprocalWitsProd_valid (reg : VarRegistry) {a b r : DenseExpr p}
    (ha : a.CoveredBy reg) (hb : b.CoveredBy reg) {g : DenseLinExpr p}
    (hg : g ∈ denseReciprocalWitsProd a b r) : ∀ i ∈ g.terms.map Prod.fst, reg.Valid i := by
  unfold denseReciprocalWitsProd at hg
  cases hr : denseLinearize r with
  | none => simp only [hr] at hg; exact absurd hg (by simp)
  | some lr =>
      simp only [hr] at hg
      split_ifs at hg with hcond
      · rw [List.mem_append] at hg
        rcases hg with hla | hlb
        · cases hla' : denseLinearize a with
          | none => simp only [hla'] at hla; exact absurd hla (by simp)
          | some la =>
              simp only [hla', List.mem_singleton] at hla; subst hla
              exact reg.denseLinearize_covered_terms ha hla'
        · cases hlb' : denseLinearize b with
          | none => simp only [hlb'] at hlb; exact absurd hlb (by simp)
          | some lb =>
              simp only [hlb', List.mem_singleton] at hlb; subst hlb
              exact reg.denseLinearize_covered_terms hb hlb'
      · exact absurd hg (by simp)

/-- Every term id of a reciprocal witness of a covered constraint is valid. -/
theorem VarRegistry.denseReciprocalWits?_valid (reg : VarRegistry) {c : DenseExpr p}
    (hc : c.CoveredBy reg) {g : DenseLinExpr p} (hg : g ∈ denseReciprocalWits? c) :
    ∀ i ∈ g.terms.map Prod.fst, reg.Valid i := by
  cases c with
  | const n => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
  | var i => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
  | mul a b => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
  | add e1 e2 =>
      obtain ⟨he1, he2⟩ := DenseExpr.coveredBy_add.mp hc
      cases e1 with
      | mul a b =>
          obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp he1
          simp only [denseReciprocalWits?] at hg
          exact reg.denseReciprocalWitsProd_valid ha hb hg
      | const n =>
          cases e2 with
          | mul a b =>
              obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp he2
              simp only [denseReciprocalWits?] at hg
              exact reg.denseReciprocalWitsProd_valid ha hb hg
          | const m => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
          | var i => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
          | add x y => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
      | var i =>
          cases e2 with
          | mul a b =>
              obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp he2
              simp only [denseReciprocalWits?] at hg
              exact reg.denseReciprocalWitsProd_valid ha hb hg
          | const m => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
          | var j => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
          | add x y => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
      | add x y =>
          cases e2 with
          | mul a b =>
              obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp he2
              simp only [denseReciprocalWits?] at hg
              exact reg.denseReciprocalWitsProd_valid ha hb hg
          | const m => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
          | var j => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim
          | add u w => simp only [denseReciprocalWits?] at hg; exact (List.not_mem_nil hg).elim

/-- **`diffSumOver` decodes.** No validity needed. -/
theorem VarRegistry.denseDiffSumOver_decode (reg : VarRegistry) (S m : BusInteraction (DenseExpr p)) :
    ∀ fields : List Nat, (denseDiffSumOver S m fields).map reg.decodeLin
      = diffSumOver (reg.decodeBI S) (reg.decodeBI m) fields := by
  intro fields
  induction fields with
  | nil => rfl
  | cons f fs ih =>
      simp only [denseDiffSumOver, diffSumOver]
      cases hacc : denseDiffSumOver S m fs with
      | none =>
          have hs : diffSumOver (reg.decodeBI S) (reg.decodeBI m) fs = none := by
            rw [← ih, hacc]; rfl
          rw [hs]; simp
      | some acc =>
          have hs : diffSumOver (reg.decodeBI S) (reg.decodeBI m) fs = some (reg.decodeLin acc) := by
            rw [← ih, hacc]; rfl
          rw [hs]
          have hSp : (reg.decodeBI S).payload[f]? = (S.payload[f]?).map reg.decodeExpr := by
            show (S.payload.map reg.decodeExpr)[f]? = _; rw [List.getElem?_map]
          have hmp : (reg.decodeBI m).payload[f]? = (m.payload[f]?).map reg.decodeExpr := by
            show (m.payload.map reg.decodeExpr)[f]? = _; rw [List.getElem?_map]
          rw [hSp, hmp]
          cases hSf : S.payload[f]? with
          | none => simp
          | some eS =>
            cases hmf : m.payload[f]? with
            | none => simp
            | some eM =>
              simp only [Option.map_some]
              have hkS := reg.denseLinearize_decode eS
              have hkM := reg.denseLinearize_decode eM
              cases hlS : denseLinearize eS with
              | none => rw [hlS] at hkS; simp only [Option.map_none] at hkS; rw [← hkS]; simp
              | some lS =>
                cases hlM : denseLinearize eM with
                | none => rw [hlM] at hkM; simp only [Option.map_none] at hkM; rw [← hkM]; simp
                | some lM =>
                  rw [hlS] at hkS; rw [hlM] at hkM
                  simp only [Option.map_some] at hkS hkM
                  rw [← hkS, ← hkM]
                  simp only [Option.map_some]
                  rw [reg.decodeLin_add, reg.decodeLin_add, reg.decodeLin_scale]

/-- Every term id of `denseDiffSumOver` over covered payloads is valid. -/
theorem VarRegistry.denseDiffSumOver_valid (reg : VarRegistry) (S m : BusInteraction (DenseExpr p))
    (hS : denseBICovered reg S) (hm : denseBICovered reg m) :
    ∀ (fields : List Nat) (D : DenseLinExpr p), denseDiffSumOver S m fields = some D →
      ∀ i ∈ D.terms.map Prod.fst, reg.Valid i := by
  intro fields
  induction fields with
  | nil => intro D h; simp only [denseDiffSumOver, Option.some.injEq] at h; subst h; simp
  | cons f fs ih =>
      intro D h
      simp only [denseDiffSumOver] at h
      cases hacc : denseDiffSumOver S m fs with
      | none => simp only [hacc] at h; exact absurd h (by simp)
      | some acc =>
          cases hSf : S.payload[f]? with
          | none => simp only [hacc, hSf] at h; exact absurd h (by simp)
          | some eS =>
            cases hmf : m.payload[f]? with
            | none => simp only [hacc, hSf, hmf] at h; exact absurd h (by simp)
            | some eM =>
              cases hlS : denseLinearize eS with
              | none => simp only [hacc, hSf, hmf, hlS] at h; exact absurd h (by simp)
              | some lS =>
                cases hlM : denseLinearize eM with
                | none => simp only [hacc, hSf, hmf, hlS, hlM] at h; exact absurd h (by simp)
                | some lM =>
                    simp only [hacc, hSf, hmf, hlS, hlM, Option.some.injEq] at h
                    subst h
                    have hSval : ∀ i ∈ lS.terms.map Prod.fst, reg.Valid i :=
                      reg.denseLinearize_covered_terms (hS.2 eS (List.mem_of_getElem? hSf)) hlS
                    have hMval : ∀ i ∈ lM.terms.map Prod.fst, reg.Valid i :=
                      reg.denseLinearize_covered_terms (hm.2 eM (List.mem_of_getElem? hmf)) hlM
                    have hAccval : ∀ i ∈ acc.terms.map Prod.fst, reg.Valid i := ih acc hacc
                    intro i hi
                    simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hi
                    rcases hi with (h | h) | h
                    · exact hMval i h
                    · rw [DenseLinExpr.scale_terms_fst] at h; exact hSval i h
                    · exact hAccval i h

/-! ## The two-root map: the lookup-wise soundness invariant -/

/-- The dense mirror of `TwoRootMap.sound`: every successful lookup is prime-gated, unit-coefficient,
    and witnessed by an actual constraint's `denseTwoRootOf?` decomposition. Purely dense; the decode
    to the spec `twoRootOf?` entry is supplied at use by `denseTwoRootOf?_decode`. -/
def DenseTwoRootMap.Sound (dcs : List (DenseExpr p)) (T : DenseTwoRootMap p) : Prop :=
  ∀ v k A δ, T.map[v]? = some (k, A, δ) →
    Nat.Prime p ∧ k * k⁻¹ = 1 ∧ ∃ c ∈ dcs, denseTwoRootOf? c v = some (k, A, δ)

theorem DenseTwoRootMap.empty_sound (dcs : List (DenseExpr p)) :
    (DenseTwoRootMap.empty : DenseTwoRootMap p).Sound dcs := by
  intro v k A δ h
  simp only [DenseTwoRootMap.empty, Std.HashMap.getElem?_empty] at h
  exact absurd h (by simp)

theorem DenseTwoRootMap.Sound.insertEntry {dcs : List (DenseExpr p)} {T : DenseTwoRootMap p}
    (hT : T.Sound dcs) {v : VarId} {k : ZMod p} {A : DenseLinExpr p} {δ : ZMod p}
    (hnew : Nat.Prime p ∧ k * k⁻¹ = 1 ∧ ∃ c ∈ dcs, denseTwoRootOf? c v = some (k, A, δ)) :
    (T.insertEntry v k A δ).Sound dcs := by
  intro w k' A' δ' hw
  simp only [DenseTwoRootMap.insertEntry, Std.HashMap.getElem?_insert] at hw
  by_cases hvw : (v == w) = true
  · rw [if_pos hvw] at hw
    have heq : (k, A, δ) = (k', A', δ') := by simpa using hw
    have hvw' : v = w := by simpa using hvw
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    subst hvw'
    exact hnew
  · rw [if_neg hvw] at hw
    exact hT w k' A' δ' hw

theorem DenseTwoRootMap.Sound.addVars {dcs : List (DenseExpr p)} (hp : Nat.Prime p) {c : DenseExpr p}
    (hc : c ∈ dcs) : ∀ (T : DenseTwoRootMap p) (vs : List VarId), T.Sound dcs →
      (DenseTwoRootMap.addVars c T vs).Sound dcs := by
  intro T vs
  induction vs generalizing T with
  | nil => intro hT; exact hT
  | cons v rest ih =>
      intro hT
      rw [DenseTwoRootMap.addVars]
      cases htr : denseTwoRootOf? c v with
      | none => exact ih T hT
      | some kAδ =>
          obtain ⟨k, A, δ⟩ := kAδ
          dsimp only
          by_cases hu : k * k⁻¹ = 1
          · rw [if_pos hu]; exact ih _ (hT.insertEntry ⟨hp, hu, c, hc, htr⟩)
          · rw [if_neg hu]; exact ih T hT

theorem DenseTwoRootMap.Sound.addAll {dcs : List (DenseExpr p)} (hp : Nat.Prime p) :
    ∀ (T : DenseTwoRootMap p) (pending : List (DenseExpr p)), (∀ c ∈ pending, c ∈ dcs) →
      T.Sound dcs → (DenseTwoRootMap.addAll T pending).Sound dcs := by
  intro T pending
  induction pending generalizing T with
  | nil => intro _ hT; exact hT
  | cons c rest ih =>
      intro hmem hT
      rw [DenseTwoRootMap.addAll]
      exact ih _ (fun c' h => hmem c' (List.mem_cons_of_mem _ h))
        (DenseTwoRootMap.Sound.addVars hp (hmem c (List.mem_cons_self ..)) T _ hT)

/-- **The built two-root map is sound.** Dense mirror of `TwoRootMap.build`'s soundness. -/
theorem DenseTwoRootMap.build_sound (dcs : List (DenseExpr p)) :
    (DenseTwoRootMap.build dcs).Sound dcs := by
  rw [DenseTwoRootMap.build]
  by_cases hp : Nat.Prime p
  · rw [if_pos hp]
    exact DenseTwoRootMap.Sound.addAll hp DenseTwoRootMap.empty dcs (fun _ h => h)
      (DenseTwoRootMap.empty_sound dcs)
  · rw [if_neg hp]; exact DenseTwoRootMap.empty_sound dcs

/-! ## Decode-commutation of `denseTwoRootOf?` (flagged for chunk S1 reuse) -/

/-- The `A` component of a recognized `denseTwoRootOf?` of a covered constraint has valid term ids. -/
theorem VarRegistry.denseTwoRootOf?_A_valid (reg : VarRegistry) {c : DenseExpr p} {x : VarId}
    {k : ZMod p} {A : DenseLinExpr p} {δ : ZMod p} (hc : c.CoveredBy reg)
    (h : denseTwoRootOf? c x = some (k, A, δ)) : ∀ i ∈ A.terms.map Prod.fst, reg.Valid i := by
  cases c with
  | const n => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | var i => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | add a b => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | mul f1 f2 =>
      obtain ⟨hf1, _⟩ := DenseExpr.coveredBy_mul.mp hc
      simp only [denseTwoRootOf?] at h
      cases hl1 : denseLinearize f1 with
      | none => simp only [hl1] at h; exact absurd h (by simp)
      | some l1 =>
        cases hl2 : denseLinearize f2 with
        | none => simp only [hl1, hl2] at h; exact absurd h (by simp)
        | some l2 =>
          simp only [hl1, hl2] at h
          split_ifs at h with hcond
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, hA, _⟩ := h
            subst hA
            intro i hi
            have hl1val : ∀ i ∈ l1.terms.map Prod.fst, reg.Valid i :=
              reg.denseLinearize_covered_terms hf1 hl1
            apply hl1val i
            have h2 := (l1.others x).norm_terms_fst i hi
            simp only [DenseLinExpr.others, List.mem_map] at h2 ⊢
            obtain ⟨t, ht, rfl⟩ := h2
            exact ⟨t, List.mem_of_mem_filter ht, rfl⟩

/-- **`denseTwoRootOf?` decodes** (forward; covered constraint, valid variable). Reused by the dense
    `rootPairUnify` port (chunk S1). -/
theorem VarRegistry.denseTwoRootOf?_decode (reg : VarRegistry) (c : DenseExpr p) (x : VarId)
    {k : ZMod p} {A : DenseLinExpr p} {δ : ZMod p} (hc : c.CoveredBy reg) (hx : reg.Valid x)
    (h : denseTwoRootOf? c x = some (k, A, δ)) :
    twoRootOf? (reg.decodeExpr c) (reg.resolve x) = some (k, reg.decodeLin A, δ) := by
  cases c with
  | const n => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | var i => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | add a b => simp only [denseTwoRootOf?] at h; exact absurd h (by simp)
  | mul f1 f2 =>
      obtain ⟨hf1, hf2⟩ := DenseExpr.coveredBy_mul.mp hc
      simp only [denseTwoRootOf?] at h
      cases hl1 : denseLinearize f1 with
      | none => simp only [hl1] at h; exact absurd h (by simp)
      | some l1 =>
        cases hl2 : denseLinearize f2 with
        | none => simp only [hl1, hl2] at h; exact absurd h (by simp)
        | some l2 =>
          simp only [hl1, hl2] at h
          split_ifs at h with hcond
          · obtain ⟨hk0, hcoeff, hterms⟩ := hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hkeq, hAeq, hδeq⟩ := h
            have hl1val : ∀ i ∈ l1.terms.map Prod.fst, reg.Valid i :=
              reg.denseLinearize_covered_terms hf1 hl1
            have hl2val : ∀ i ∈ l2.terms.map Prod.fst, reg.Valid i :=
              reg.denseLinearize_covered_terms hf2 hl2
            have ho1val : ∀ i ∈ (l1.others x).terms.map Prod.fst, reg.Valid i := by
              intro i hi; apply hl1val i; simp only [DenseLinExpr.others, List.mem_map] at hi ⊢
              obtain ⟨t, ht, rfl⟩ := hi; exact ⟨t, List.mem_of_mem_filter ht, rfl⟩
            have ho2val : ∀ i ∈ (l2.others x).terms.map Prod.fst, reg.Valid i := by
              intro i hi; apply hl2val i; simp only [DenseLinExpr.others, List.mem_map] at hi ⊢
              obtain ⟨t, ht, rfl⟩ := hi; exact ⟨t, List.mem_of_mem_filter ht, rfl⟩
            have hL1 : linearize (reg.decodeExpr f1) = some (reg.decodeLin l1) := by
              rw [← reg.denseLinearize_decode f1, hl1]; rfl
            have hL2 : linearize (reg.decodeExpr f2) = some (reg.decodeLin l2) := by
              rw [← reg.denseLinearize_decode f2, hl2]; rfl
            have hc1 : (reg.decodeLin l1).coeff (reg.resolve x) = l1.coeff x :=
              reg.decodeLin_coeff l1 hx hl1val
            have hc2 : (reg.decodeLin l2).coeff (reg.resolve x) = l2.coeff x :=
              reg.decodeLin_coeff l2 hx hl2val
            have hAdec : ((reg.decodeLin l1).others (reg.resolve x)).norm
                = reg.decodeLin ((l1.others x).norm) := by
              rw [← reg.decodeLin_others l1 hx hl1val, reg.decodeLin_norm (l1.others x) ho1val]
            have hA2dec : ((reg.decodeLin l2).others (reg.resolve x)).norm
                = reg.decodeLin ((l2.others x).norm) := by
              rw [← reg.decodeLin_others l2 hx hl2val, reg.decodeLin_norm (l2.others x) ho2val]
            show twoRootOf? (Expression.mul (reg.decodeExpr f1) (reg.decodeExpr f2)) (reg.resolve x)
              = _
            rw [twoRootOf?]
            simp only [hL1, hL2]
            have hcondS : (reg.decodeLin l1).coeff (reg.resolve x) ≠ 0
                ∧ (reg.decodeLin l2).coeff (reg.resolve x) = (reg.decodeLin l1).coeff (reg.resolve x)
                ∧ (((reg.decodeLin l2).others (reg.resolve x)).norm).terms
                  = (((reg.decodeLin l1).others (reg.resolve x)).norm).terms := by
              refine ⟨?_, ?_, ?_⟩
              · rw [hc1]; exact hk0
              · rw [hc1, hc2]; exact hcoeff
              · rw [hAdec, hA2dec]; simp only [VarRegistry.decodeLin]; rw [hterms]
            rw [if_pos hcondS, hc1, hAdec]
            simp only [Option.some.injEq, Prod.mk.injEq]
            refine ⟨hkeq, ?_, ?_⟩
            · rw [hAeq]
            · rw [hA2dec, reg.decodeLin_const, reg.decodeLin_const]; exact hδeq

/-! ## Decode-commutation of `densePtrBranchesOf` -/

/-- `densePtrBranchesOf` decodes (validity-gated through `decodeLin_norm`). -/
theorem VarRegistry.densePtrBranchesOf_decode (reg : VarRegistry) (k : ZMod p) (A : DenseLinExpr p)
    (δ cx : ZMod p) (rest : DenseLinExpr p) (hA : ∀ i ∈ A.terms.map Prod.fst, reg.Valid i)
    (hrest : ∀ i ∈ rest.terms.map Prod.fst, reg.Valid i) :
    reg.decodeLin (densePtrBranchesOf k A δ cx rest).1
        = (ptrBranchesOf k (reg.decodeLin A) δ cx (reg.decodeLin rest)).1
    ∧ reg.decodeLin (densePtrBranchesOf k A δ cx rest).2
        = (ptrBranchesOf k (reg.decodeLin A) δ cx (reg.decodeLin rest)).2 := by
  have hscale : ∀ i ∈ (A.scale (-(k⁻¹))).terms.map Prod.fst, reg.Valid i := by
    intro i hi; rw [DenseLinExpr.scale_terms_fst] at hi; exact hA i hi
  have hv1 : ∀ i ∈ (rest.add ((A.scale (-(k⁻¹))).scale cx)).terms.map Prod.fst, reg.Valid i := by
    intro i hi; simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hi
    rcases hi with h | h
    · exact hrest i h
    · rw [DenseLinExpr.scale_terms_fst] at h; exact hscale i h
  have hv2 : ∀ i ∈ (rest.add (((A.scale (-(k⁻¹))).add ⟨-(k⁻¹ * δ), []⟩).scale cx)).terms.map Prod.fst,
      reg.Valid i := by
    intro i hi
    simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hi
    rcases hi with h | h
    · exact hrest i h
    · rw [DenseLinExpr.scale_terms_fst] at h
      simp only [List.map_append, List.mem_append] at h
      rcases h with h | h
      · exact hscale i h
      · simp at h
  refine ⟨?_, ?_⟩
  · simp only [densePtrBranchesOf, ptrBranchesOf]
    rw [reg.decodeLin_norm _ hv1, reg.decodeLin_add, reg.decodeLin_scale, reg.decodeLin_scale]
  · simp only [densePtrBranchesOf, ptrBranchesOf]
    rw [reg.decodeLin_norm _ hv2, reg.decodeLin_add, reg.decodeLin_scale, reg.decodeLin_add,
      reg.decodeLin_scale]
    rfl

/-- Both branch forms produced by `densePtrReductions` have valid term ids. -/
theorem VarRegistry.densePtrBranchesOf_terms_valid (reg : VarRegistry) (k : ZMod p)
    (A : DenseLinExpr p) (δ cx : ZMod p) (rest : DenseLinExpr p)
    (hA : ∀ i ∈ A.terms.map Prod.fst, reg.Valid i)
    (hrest : ∀ i ∈ rest.terms.map Prod.fst, reg.Valid i) :
    (∀ i ∈ (densePtrBranchesOf k A δ cx rest).1.terms.map Prod.fst, reg.Valid i)
    ∧ (∀ i ∈ (densePtrBranchesOf k A δ cx rest).2.terms.map Prod.fst, reg.Valid i) := by
  have hscale : ∀ i ∈ (A.scale (-(k⁻¹))).terms.map Prod.fst, reg.Valid i := by
    intro i hi; rw [DenseLinExpr.scale_terms_fst] at hi; exact hA i hi
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [densePtrBranchesOf] at hi
    have h2 := DenseLinExpr.norm_terms_fst _ i hi
    simp only [DenseLinExpr.add, List.map_append, List.mem_append] at h2
    rcases h2 with h | h
    · exact hrest i h
    · rw [DenseLinExpr.scale_terms_fst] at h; exact hscale i h
  · intro i hi
    simp only [densePtrBranchesOf] at hi
    have h2 := DenseLinExpr.norm_terms_fst _ i hi
    simp only [DenseLinExpr.add, List.map_append, List.mem_append] at h2
    rcases h2 with h | h
    · exact hrest i h
    · rw [DenseLinExpr.scale_terms_fst] at h
      simp only [List.map_append, List.mem_append] at h
      rcases h with h | h
      · exact hscale i h
      · simp at h

/-! ## `densePtrReductions` soundness (the map-consuming glue, re-derived over the dense map) -/

/-- Both branch forms of a `densePtrReductions` entry have valid term ids. -/
theorem densePtrReductions_valid (reg : VarRegistry) {dcs : List (DenseExpr p)}
    (T : DenseTwoRootMap p) (hT : T.Sound dcs) (hdcov : ∀ c ∈ dcs, c.CoveredBy reg)
    (E : DenseExpr p) (hE : E.CoveredBy reg) {b1 b2 : DenseLinExpr p}
    (hmem : (b1, b2) ∈ densePtrReductions T E) :
    (∀ i ∈ b1.terms.map Prod.fst, reg.Valid i) ∧ (∀ i ∈ b2.terms.map Prod.fst, reg.Valid i) := by
  unfold densePtrReductions at hmem
  cases hL : denseLinearize E with
  | none => rw [hL] at hmem; simp at hmem
  | some L =>
    rw [hL] at hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨v, hv, hmatch⟩ := hmem
    cases htm : T.map[v]? with
    | none => rw [htm] at hmatch; simp at hmatch
    | some kAδ =>
      obtain ⟨k, A, δ⟩ := kAδ
      rw [htm] at hmatch
      dsimp only at hmatch
      simp only [Option.some.injEq] at hmatch
      obtain ⟨_, _, c, hc, htr⟩ := hT v k A δ htm
      have hLval : ∀ i ∈ L.terms.map Prod.fst, reg.Valid i :=
        reg.denseLinearize_covered_terms hE hL
      have hAval : ∀ i ∈ A.terms.map Prod.fst, reg.Valid i :=
        reg.denseTwoRootOf?_A_valid (hdcov c hc) htr
      have hOval : ∀ i ∈ (L.others v).terms.map Prod.fst, reg.Valid i := by
        intro i hi; apply hLval i; simp only [DenseLinExpr.others, List.mem_map] at hi ⊢
        obtain ⟨t, ht, rfl⟩ := hi; exact ⟨t, List.mem_of_mem_filter ht, rfl⟩
      obtain ⟨hb1, hb2⟩ :=
        reg.densePtrBranchesOf_terms_valid k A δ (L.coeff v) (L.others v) hAval hOval
      have hb1eq : b1 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).1 :=
        (congrArg Prod.fst hmatch).symm
      have hb2eq : b2 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).2 :=
        (congrArg Prod.snd hmatch).symm
      exact ⟨hb1eq ▸ hb1, hb2eq ▸ hb2⟩

/-- **`densePtrReductions` is sound** (value-level, over the dense map): every reduction pair of a
    covered expression brackets `E`'s value under any dense environment satisfying the constraints.
    Mirrors `ptrReductions_sound`, reusing `twoRootOf?_sound`/`ptrBranchesOf_eval` after decode. -/
theorem densePtrReductions_sound (reg : VarRegistry) {dcs : List (DenseExpr p)}
    (T : DenseTwoRootMap p) (hT : T.Sound dcs) (hdcov : ∀ c ∈ dcs, c.CoveredBy reg)
    (E : DenseExpr p) (hE : E.CoveredBy reg) (b1 b2 : DenseLinExpr p)
    (hmem : (b1, b2) ∈ densePtrReductions T E) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    E.eval denv = b1.eval denv ∨ E.eval denv = b2.eval denv := by
  unfold densePtrReductions at hmem
  cases hL : denseLinearize E with
  | none => rw [hL] at hmem; simp at hmem
  | some L =>
    rw [hL] at hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨v, hv, hmatch⟩ := hmem
    cases htm : T.map[v]? with
    | none => rw [htm] at hmatch; simp at hmatch
    | some kAδ =>
      obtain ⟨k, A, δ⟩ := kAδ
      rw [htm] at hmatch
      dsimp only at hmatch
      simp only [Option.some.injEq] at hmatch
      obtain ⟨hp, hunit, c, hc, htr⟩ := hT v k A δ htm
      haveI : Fact p.Prime := ⟨hp⟩
      have hLval : ∀ i ∈ L.terms.map Prod.fst, reg.Valid i :=
        reg.denseLinearize_covered_terms hE hL
      have hvvalid : reg.Valid v := hLval v (List.mem_eraseDups.mp hv)
      have hccov := hdcov c hc
      have hAval : ∀ i ∈ A.terms.map Prod.fst, reg.Valid i :=
        reg.denseTwoRootOf?_A_valid hccov htr
      have hOval : ∀ i ∈ (L.others v).terms.map Prod.fst, reg.Valid i := by
        intro i hi; apply hLval i; simp only [DenseLinExpr.others, List.mem_map] at hi ⊢
        obtain ⟨t, ht, rfl⟩ := hi; exact ⟨t, List.mem_of_mem_filter ht, rfl⟩
      set env := reg.extendEnv denv (fun _ => 0) with henv
      have htr' : twoRootOf? (reg.decodeExpr c) (reg.resolve v) = some (k, reg.decodeLin A, δ) :=
        reg.denseTwoRootOf?_decode c v hccov hvvalid htr
      have hcz : (reg.decodeExpr c).eval env = 0 := by
        rw [eval_decodeExpr_extendEnv reg c hccov denv (fun _ => 0)]; exact hcon c hc
      have hroot := twoRootOf?_sound (reg.decodeExpr c) (reg.resolve v) k (reg.decodeLin A) δ htr'
        hunit env hcz
      have hLinE : linearize (reg.decodeExpr E) = some (reg.decodeLin L) := by
        rw [← reg.denseLinearize_decode E, hL]; rfl
      have hEL : (reg.decodeExpr E).eval env = (reg.decodeLin L).eval env :=
        linearize_eval _ _ hLinE env
      have hsplit : (reg.decodeLin L).eval env
          = (reg.decodeLin L).coeff (reg.resolve v) * env (reg.resolve v)
            + ((reg.decodeLin L).others (reg.resolve v)).eval env :=
        (reg.decodeLin L).eval_split (reg.resolve v) env
      have hcoeff : (reg.decodeLin L).coeff (reg.resolve v) = L.coeff v :=
        reg.decodeLin_coeff L hvvalid hLval
      have hothers : (reg.decodeLin L).others (reg.resolve v) = reg.decodeLin (L.others v) :=
        (reg.decodeLin_others L hvvalid hLval).symm
      obtain ⟨hbr1, hbr2⟩ :=
        reg.densePtrBranchesOf_decode k A δ (L.coeff v) (L.others v) hAval hOval
      have hb1eq : b1 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).1 :=
        (congrArg Prod.fst hmatch).symm
      have hb2eq : b2 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).2 :=
        (congrArg Prod.snd hmatch).symm
      obtain ⟨hb1val, hb2val⟩ :=
        reg.densePtrBranchesOf_terms_valid k A δ (L.coeff v) (L.others v) hAval hOval
      have hEbridge : E.eval denv = (reg.decodeExpr E).eval env :=
        (eval_decodeExpr_extendEnv reg E hE denv (fun _ => 0)).symm
      obtain ⟨he1, he2⟩ := ptrBranchesOf_eval k (reg.decodeLin A) δ
        ((reg.decodeLin L).coeff (reg.resolve v)) ((reg.decodeLin L).others (reg.resolve v)) env
      rcases hroot with hr | hr
      · left
        have hdb1 : reg.decodeLin b1 = (ptrBranchesOf k (reg.decodeLin A) δ
            ((reg.decodeLin L).coeff (reg.resolve v)) ((reg.decodeLin L).others (reg.resolve v))).1 := by
          rw [hb1eq, hbr1, ← hcoeff, hothers]
        have hb1bridge : b1.eval denv = (reg.decodeLin b1).eval env :=
          (eval_decodeLin_extendEnv reg b1 (by rw [hb1eq]; exact hb1val) denv (fun _ => 0)).symm
        rw [hEbridge, hEL, hsplit, hr, hb1bridge, hdb1, he1]; ring
      · right
        have hdb2 : reg.decodeLin b2 = (ptrBranchesOf k (reg.decodeLin A) δ
            ((reg.decodeLin L).coeff (reg.resolve v)) ((reg.decodeLin L).others (reg.resolve v))).2 := by
          rw [hb2eq, hbr2, ← hcoeff, hothers]
        have hb2bridge : b2.eval denv = (reg.decodeLin b2).eval env :=
          (eval_decodeLin_extendEnv reg b2 (by rw [hb2eq]; exact hb2val) denv (fun _ => 0)).symm
        rw [hEbridge, hEL, hsplit, hr, hb2bridge, hdb2, he2]; ring

/-- **`denseExprTwoRootNeq` is sound.** Mirrors `exprTwoRootNeq_sound`. -/
theorem denseExprTwoRootNeq_sound (reg : VarRegistry) {dcs : List (DenseExpr p)}
    (T : DenseTwoRootMap p) (hT : T.Sound dcs) (hdcov : ∀ c ∈ dcs, c.CoveredBy reg)
    (e e' : DenseExpr p) (he : e.CoveredBy reg) (he' : e'.CoveredBy reg)
    (h : denseExprTwoRootNeq T e e' = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) : e.eval denv ≠ e'.eval denv := by
  unfold denseExprTwoRootNeq at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨a1, a2⟩, hred, hinner⟩ := h
  rw [List.any_eq_true] at hinner
  obtain ⟨⟨b1, b2⟩, hred', hchk⟩ := hinner
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨h11, h12⟩, h21⟩, h22⟩ := hchk
  have hev := densePtrReductions_sound reg T hT hdcov e he a1 a2 hred denv hcon
  have hev' := densePtrReductions_sound reg T hT hdcov e' he' b1 b2 hred' denv hcon
  obtain ⟨ha1, ha2⟩ := densePtrReductions_valid reg T hT hdcov e he hred
  obtain ⟨hb1, hb2⟩ := densePtrReductions_valid reg T hT hdcov e' he' hred'
  rcases hev with ha | ha <;> rcases hev' with hb | hb <;> rw [ha, hb]
  · exact denseConstDiffNZ_sound reg a1 b1 ha1 hb1 h11 denv
  · exact denseConstDiffNZ_sound reg a1 b2 ha1 hb2 h12 denv
  · exact denseConstDiffNZ_sound reg a2 b1 ha2 hb1 h21 denv
  · exact denseConstDiffNZ_sound reg a2 b2 ha2 hb2 h22 denv

/-- **`denseAddrTwoRootNeq` is sound.** Some address slot's two interactions provably differ, so the
    addresses differ. Consumes the lookup-wise `DenseTwoRootMap.Sound` invariant. -/
theorem denseAddrTwoRootNeq_sound (reg : VarRegistry) (shape : MemoryBusShape)
    {dcs : List (DenseExpr p)} (T : DenseTwoRootMap p) (hT : T.Sound dcs)
    (hdcov : ∀ c ∈ dcs, c.CoveredBy reg) (S bi : BusInteraction (DenseExpr p))
    (hS : denseBICovered reg S) (hbi : denseBICovered reg bi)
    (h : denseAddrTwoRootNeq shape T S bi = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  unfold denseAddrTwoRootNeq at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : bi.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at hcond
      have hecov : e.CoveredBy reg := hS.2 e (List.mem_of_getElem? hSp)
      have he'cov : e'.CoveredBy reg := hbi.2 e' (List.mem_of_getElem? hbp)
      have hne := denseExprTwoRootNeq_sound reg T hT hdcov e e' hecov he'cov hcond denv hcon
      exact denseAddr_slot_neq shape S bi denv hslot hSp hbp hne

/-! ## The reciprocal-nonzero certificate soundness -/

/-- **`denseAddrNonzeroNeq` is sound.** Reuses `addrNonzeroNeq_sound` with the spec witness structure
    `NonzeroWits.build (decoded constraints)` and the decode of `denseDiffSumOver`/`denseIsZeroLin`. -/
theorem denseAddrNonzeroNeq_sound (reg : VarRegistry) (shape : MemoryBusShape)
    (dcs : List (DenseExpr p)) (hdcov : ∀ c ∈ dcs, c.CoveredBy reg)
    (S m : BusInteraction (DenseExpr p)) (hS : denseBICovered reg S) (hm : denseBICovered reg m)
    (h : denseAddrNonzeroNeq shape (DenseNonzeroWits.build dcs) S m = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval m denv) := by
  set nwSpec : NonzeroWits p (dcs.map reg.decodeExpr) := NonzeroWits.build (dcs.map reg.decodeExpr)
    with hnwSpec
  have hwits : nwSpec.wits = (DenseNonzeroWits.build dcs).wits.map reg.decodeLin := by
    show (dcs.map reg.decodeExpr).flatMap reciprocalWits?
      = (dcs.flatMap denseReciprocalWits?).map reg.decodeLin
    rw [List.map_flatMap, List.flatMap_map]
    exact (flatMap_congr_mem dcs (fun c _ => reg.denseReciprocalWits?_decode c)).symm
  have hspec : addrNonzeroNeq shape nwSpec (reg.decodeBI S) (reg.decodeBI m) = true := by
    unfold denseAddrNonzeroNeq at h
    rw [List.any_eq_true] at h
    obtain ⟨T, hT, hcond⟩ := h
    unfold addrNonzeroNeq
    rw [List.any_eq_true]
    refine ⟨T, hT, ?_⟩
    cases hD : denseDiffSumOver S m T with
    | none => rw [hD] at hcond; simp at hcond
    | some D =>
      rw [hD] at hcond
      have hDspec : diffSumOver (reg.decodeBI S) (reg.decodeBI m) T = some (reg.decodeLin D) := by
        rw [← reg.denseDiffSumOver_decode S m T, hD]; rfl
      rw [hDspec]
      rw [List.any_eq_true] at hcond ⊢
      obtain ⟨g, hg, hgz⟩ := hcond
      have hDval : ∀ i ∈ D.terms.map Prod.fst, reg.Valid i :=
        reg.denseDiffSumOver_valid S m hS hm T D hD
      have hgval : ∀ i ∈ g.terms.map Prod.fst, reg.Valid i := by
        have hgm : g ∈ dcs.flatMap denseReciprocalWits? := hg
        rw [List.mem_flatMap] at hgm
        obtain ⟨c, hc, hgc⟩ := hgm
        exact reg.denseReciprocalWits?_valid (hdcov c hc) hgc
      refine ⟨reg.decodeLin g, ?_, ?_⟩
      · rw [hwits]; exact List.mem_map_of_mem hg
      · have hv1 : ∀ i ∈ (D.add (g.scale (-1))).terms.map Prod.fst, reg.Valid i := by
          intro i hi; simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hi
          rcases hi with h | h
          · exact hDval i h
          · rw [DenseLinExpr.scale_terms_fst] at h; exact hgval i h
        have hv2 : ∀ i ∈ (D.add g).terms.map Prod.fst, reg.Valid i := by
          intro i hi; simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hi
          rcases hi with h | h
          · exact hDval i h
          · exact hgval i h
        have e1 : denseIsZeroLin (D.add (g.scale (-1)))
            = isZeroLin ((reg.decodeLin D).add ((reg.decodeLin g).scale (-1))) := by
          rw [reg.denseIsZeroLin_decode _ hv1, reg.decodeLin_add, reg.decodeLin_scale]
        have e2 : denseIsZeroLin (D.add g) = isZeroLin ((reg.decodeLin D).add (reg.decodeLin g)) := by
          rw [reg.denseIsZeroLin_decode _ hv2, reg.decodeLin_add]
        rw [← e1, ← e2]; exact hgz
  have hconS : ∀ c ∈ dcs.map reg.decodeExpr, c.eval (reg.extendEnv denv (fun _ => 0)) = 0 := by
    intro c hc; obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    rw [eval_decodeExpr_extendEnv reg c0 (hdcov c0 hc0)]; exact hcon c0 hc0
  have hsound := addrNonzeroNeq_sound shape nwSpec (reg.decodeBI S) (reg.decodeBI m) hspec
    (reg.extendEnv denv (fun _ => 0)) hconS
  rwa [denseBIEval_extendEnv reg S hS denv (fun _ => 0),
     denseBIEval_extendEnv reg m hm denv (fun _ => 0)] at hsound

end ApcOptimizer.Dense
