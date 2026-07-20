import ApcOptimizer.Implementation.OptimizerPasses.Pass

set_option autoImplicit false

/-! # Encode of computation methods / derivations, and the generic spec adapter (Task 3)

`encodeCM`/`encodeDerivs` complete the encode side (they register fresh variables introduced by a
pass, e.g. `Reencode`'s derived booleans), with the same extension / coverage / round-trip
correspondence as the expression encoders.

`DenseVerifiedPassW.ofSpec` wraps any existing spec `VerifiedPassW` as a dense pass by
decode → run → re-encode. It is **development scaffolding only** — it round-trips through the spec
representation, so it wins no runtime and must not survive into the finished, adapter-free pipeline
(the task forbids per-pass decode/re-encode there). Its purpose is to stand up the whole dense
pipeline, correct and byte-identical by construction (`decode ∘ ofSpec = spec pass`), so that each
true dense pass can then replace one `ofSpec` in isolation, verified against the same
`DensePassResult` interface. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Constraint-system coverage monotonicity and list-of-bus coverage -/

theorem DenseConstraintSystem.CoveredBy.mono {r r' : VarRegistry} (h : r.Extends r')
    {d : DenseConstraintSystem p} (hc : d.CoveredBy r) : d.CoveredBy r' := by
  obtain ⟨hac, hbi⟩ := hc
  refine ⟨fun e he => (hac e he).mono h, fun bi hbimem => ?_⟩
  obtain ⟨hm, hp⟩ := hbi bi hbimem
  exact ⟨hm.mono h, fun e he => (hp e he).mono h⟩

theorem denseBICovered_mono {r r' : VarRegistry} (h : r.Extends r')
    {bi : BusInteraction (DenseExpr p)} (hc : denseBICovered r bi) : denseBICovered r' bi :=
  ⟨hc.1.mono h, fun e he => (hc.2 e he).mono h⟩

theorem VarRegistry.encodeBIs_covered (r : VarRegistry)
    (bis : List (BusInteraction (Expression p))) :
    ∀ bi ∈ (r.encodeBIs bis).2, denseBICovered (r.encodeBIs bis).1 bi := by
  induction bis generalizing r with
  | nil => intro bi hbi; simp [VarRegistry.encodeBIs] at hbi
  | cons b rest ih =>
      rw [VarRegistry.encodeBIs_cons]
      intro bi hbi
      rcases List.mem_cons.mp hbi with heq | hmem
      · subst heq
        exact denseBICovered_mono ((r.encodeBI b).1.encodeBIs_extends rest) (r.encodeBI_covered b)
      · exact ih (r.encodeBI b).1 bi hmem

theorem VarRegistry.encodeCS_extends (r : VarRegistry) (cs : ConstraintSystem p) :
    r.Extends (r.encodeCS cs).1 := by
  rw [VarRegistry.encodeCS_fst]
  exact (r.encodeExprs_extends cs.algebraicConstraints).trans
    ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs_extends cs.busInteractions)

theorem VarRegistry.encodeCS_covered (r : VarRegistry) (cs : ConstraintSystem p) :
    (r.encodeCS cs).2.CoveredBy (r.encodeCS cs).1 := by
  rw [VarRegistry.encodeCS_fst]
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · rw [VarRegistry.encodeCS_acs] at he
    exact (r.encodeExprs_covered cs.algebraicConstraints e he).mono
      ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs_extends cs.busInteractions)
  · rw [VarRegistry.encodeCS_bis] at hbi
    exact (r.encodeExprs cs.algebraicConstraints).1.encodeBIs_covered cs.busInteractions bi hbi

/-! ## Encoding computation methods and derivations -/

/-- Encode a spec computation method, threading the registry through its sub-expressions/methods. -/
def VarRegistry.encodeCM (r : VarRegistry) :
    ComputationMethod p → VarRegistry × DenseComputationMethod p
  | .const c => (r, .const c)
  | .quotientOrZero num den =>
      let (r1, n) := r.encodeExpr num
      let (r2, d) := r1.encodeExpr den
      (r2, .quotientOrZero n d)
  | .ifEqZero cond thenM elseM =>
      let (r1, c) := r.encodeExpr cond
      let (r2, t) := r1.encodeCM thenM
      let (r3, e) := r2.encodeCM elseM
      (r3, .ifEqZero c t e)

/-- Encode a spec derivation list: register each key variable, then encode its method. -/
def VarRegistry.encodeDerivs (r : VarRegistry) : Derivations p → VarRegistry × DenseDerivations p
  | [] => (r, [])
  | (x, cm) :: rest =>
      let (r1, i) := r.register x
      let (r2, dcm) := r1.encodeCM cm
      let (r3, rest') := r2.encodeDerivs rest
      (r3, (i, dcm) :: rest')

theorem VarRegistry.encodeDerivs_cons (r : VarRegistry) (x : Variable) (cm : ComputationMethod p)
    (rest : Derivations p) :
    r.encodeDerivs ((x, cm) :: rest) =
      ((((r.register x).1.encodeCM cm).1.encodeDerivs rest).1,
        ((r.register x).2, ((r.register x).1.encodeCM cm).2)
          :: (((r.register x).1.encodeCM cm).1.encodeDerivs rest).2) := rfl

/-! ## encodeCM: extension, coverage, round trip -/

theorem VarRegistry.encodeCM_extends (r : VarRegistry) (cm : ComputationMethod p) :
    r.Extends (r.encodeCM cm).1 := by
  induction cm generalizing r with
  | const c => exact VarRegistry.Extends.refl r
  | quotientOrZero num den =>
      exact (r.encodeExpr_extends num).trans ((r.encodeExpr num).1.encodeExpr_extends den)
  | ifEqZero cond thenM elseM iht ihe =>
      exact ((r.encodeExpr_extends cond).trans (iht (r.encodeExpr cond).1)).trans
        (ihe ((r.encodeExpr cond).1.encodeCM thenM).1)

theorem VarRegistry.encodeCM_covered (r : VarRegistry) (cm : ComputationMethod p) :
    (r.encodeCM cm).2.CoveredBy (r.encodeCM cm).1 := by
  induction cm generalizing r with
  | const c => exact True.intro
  | quotientOrZero num den =>
      exact ⟨(r.encodeExpr_covered num).mono ((r.encodeExpr num).1.encodeExpr_extends den),
        (r.encodeExpr num).1.encodeExpr_covered den⟩
  | ifEqZero cond thenM elseM iht ihe =>
      refine ⟨?_, ?_, ?_⟩
      · exact (r.encodeExpr_covered cond).mono
          (((r.encodeExpr cond).1.encodeCM_extends thenM).trans
            (((r.encodeExpr cond).1.encodeCM thenM).1.encodeCM_extends elseM))
      · exact (iht (r.encodeExpr cond).1).mono
          (((r.encodeExpr cond).1.encodeCM thenM).1.encodeCM_extends elseM)
      · exact ihe ((r.encodeExpr cond).1.encodeCM thenM).1

theorem VarRegistry.decodeCM_encodeCM (r : VarRegistry) (cm : ComputationMethod p) :
    (r.encodeCM cm).1.decodeCM (r.encodeCM cm).2 = cm := by
  induction cm generalizing r with
  | const c => rfl
  | quotientOrZero num den =>
      show ((r.encodeExpr num).1.encodeExpr den).1.decodeCM
        (.quotientOrZero (r.encodeExpr num).2 ((r.encodeExpr num).1.encodeExpr den).2) = _
      rw [VarRegistry.decodeCM]
      congr 1
      · rw [((r.encodeExpr num).1.encodeExpr_extends den).decodeExpr_eq (r.encodeExpr_covered num)]
        exact r.decodeExpr_encodeExpr num
      · exact (r.encodeExpr num).1.decodeExpr_encodeExpr den
  | ifEqZero cond thenM elseM iht ihe =>
      show (((r.encodeExpr cond).1.encodeCM thenM).1.encodeCM elseM).1.decodeCM
        (.ifEqZero (r.encodeExpr cond).2 ((r.encodeExpr cond).1.encodeCM thenM).2
          (((r.encodeExpr cond).1.encodeCM thenM).1.encodeCM elseM).2) = _
      rw [VarRegistry.decodeCM]
      have hext13 : (r.encodeExpr cond).1.Extends
          (((r.encodeExpr cond).1.encodeCM thenM).1.encodeCM elseM).1 :=
        ((r.encodeExpr cond).1.encodeCM_extends thenM).trans
          (((r.encodeExpr cond).1.encodeCM thenM).1.encodeCM_extends elseM)
      congr 1
      · rw [hext13.decodeExpr_eq (r.encodeExpr_covered cond)]
        exact r.decodeExpr_encodeExpr cond
      · rw [(((r.encodeExpr cond).1.encodeCM thenM).1.encodeCM_extends elseM).decodeCM_eq
            ((r.encodeExpr cond).1.encodeCM_covered thenM)]
        exact iht (r.encodeExpr cond).1
      · exact ihe ((r.encodeExpr cond).1.encodeCM thenM).1

/-! ## encodeDerivs: extension, coverage, round trip -/

theorem VarRegistry.encodeDerivs_extends (r : VarRegistry) (ds : Derivations p) :
    r.Extends (r.encodeDerivs ds).1 := by
  induction ds generalizing r with
  | nil => exact VarRegistry.Extends.refl r
  | cons hd rest ih =>
      obtain ⟨x, cm⟩ := hd
      rw [VarRegistry.encodeDerivs_cons]
      exact ((r.register_extends x).trans ((r.register x).1.encodeCM_extends cm)).trans
        (ih ((r.register x).1.encodeCM cm).1)

theorem VarRegistry.encodeDerivs_covered (r : VarRegistry) (ds : Derivations p) :
    (r.encodeDerivs ds).2.CoveredBy (r.encodeDerivs ds).1 := by
  induction ds generalizing r with
  | nil => intro x hx; simp [VarRegistry.encodeDerivs] at hx
  | cons hd rest ih =>
      obtain ⟨x, cm⟩ := hd
      rw [VarRegistry.encodeDerivs_cons]
      intro y hy
      rcases List.mem_cons.mp hy with heq | hmem
      · subst heq
        refine ⟨?_, ?_⟩
        · exact (((r.register x).1.encodeCM cm).1.encodeDerivs_extends rest).valid
            (((r.register x).1.encodeCM_extends cm).valid (r.register_valid x))
        · exact ((r.register x).1.encodeCM_covered cm).mono
            (((r.register x).1.encodeCM cm).1.encodeDerivs_extends rest)
      · exact ih ((r.register x).1.encodeCM cm).1 y hmem

theorem VarRegistry.decodeDerivs_encodeDerivs (r : VarRegistry) (ds : Derivations p) :
    (r.encodeDerivs ds).1.decodeDerivs (r.encodeDerivs ds).2 = ds := by
  induction ds generalizing r with
  | nil => rfl
  | cons hd rest ih =>
      obtain ⟨x, cm⟩ := hd
      rw [VarRegistry.encodeDerivs_cons]
      simp only [VarRegistry.decodeDerivs, List.map_cons]
      congr 1
      · -- (resolve r3 i, decodeCM r3 dcm) = (x, cm)
        refine Prod.ext ?_ ?_
        · -- resolve r3 (register x).2 = x
          rw [(((r.register x).1.encodeCM cm).1.encodeDerivs_extends rest).resolve_eq
              (((r.register x).1.encodeCM_extends cm).valid (r.register_valid x)),
            ((r.register x).1.encodeCM_extends cm).resolve_eq (r.register_valid x)]
          exact r.register_resolve x
        · -- decodeCM r3 dcm = cm
          rw [(((r.register x).1.encodeCM cm).1.encodeDerivs_extends rest).decodeCM_eq
              ((r.register x).1.encodeCM_covered cm)]
          exact (r.register x).1.decodeCM_encodeCM cm
      · exact ih ((r.register x).1.encodeCM cm).1

/-! ## The generic spec adapter (development scaffolding) -/

/-- Wrap a spec `VerifiedPassW` as a dense pass by decode → run → re-encode. Correct and
    byte-identical by construction, but runtime-neutral (round-trips through the spec form); only
    for incremental development, never in the finished pipeline. -/
def DenseVerifiedPassW.ofSpec (f : VerifiedPassW p) : DenseVerifiedPassW p :=
  fun reg d _ bs facts =>
    let r := f (reg.decodeCS d) bs facts
    let e1 := reg.encodeCS r.out
    let e2 := e1.1.encodeDerivs r.derivs
    { reg' := e2.1
      out := e1.2
      derivs := e2.2
      ext := (reg.encodeCS_extends r.out).trans (e1.1.encodeDerivs_extends r.derivs)
      covered := (reg.encodeCS_covered r.out).mono (e1.1.encodeDerivs_extends r.derivs)
      dcovered := e1.1.encodeDerivs_covered r.derivs
      correct := by
        have hout : e2.1.decodeCS e1.2 = r.out := by
          rw [(e1.1.encodeDerivs_extends r.derivs).decodeCS_eq (reg.encodeCS_covered r.out)]
          exact reg.decodeCS_encodeCS r.out
        have hderivs : e2.1.decodeDerivs e2.2 = r.derivs := e1.1.decodeDerivs_encodeDerivs r.derivs
        rw [hout, hderivs]
        exact r.correct }

/-- `ofSpec`'s output (`.out`), as a `rfl` projection. -/
theorem DenseVerifiedPassW.ofSpec_out (f : VerifiedPassW p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    (ofSpec f reg d hcov bs facts).out = (reg.encodeCS (f (reg.decodeCS d) bs facts).out).2 := rfl

/-- `ofSpec`'s resulting registry (`.reg'`), as a `rfl` projection. -/
theorem DenseVerifiedPassW.ofSpec_reg (f : VerifiedPassW p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    (ofSpec f reg d hcov bs facts).reg'
      = ((reg.encodeCS (f (reg.decodeCS d) bs facts).out).1.encodeDerivs
          (f (reg.decodeCS d) bs facts).derivs).1 := rfl

/-- The decoded output of `ofSpec f` is exactly the spec pass's output (byte-identical). -/
theorem DenseVerifiedPassW.ofSpec_out_decode (f : VerifiedPassW p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    (ofSpec f reg d hcov bs facts).reg'.decodeCS (ofSpec f reg d hcov bs facts).out
      = (f (reg.decodeCS d) bs facts).out := by
  rw [ofSpec_out, ofSpec_reg,
    ((reg.encodeCS (f (reg.decodeCS d) bs facts).out).1.encodeDerivs_extends
      (f (reg.decodeCS d) bs facts).derivs).decodeCS_eq (reg.encodeCS_covered _)]
  exact reg.decodeCS_encodeCS _

/-- If the spec pass respects the degree bound, so does its `ofSpec` wrapper. -/
theorem DenseVerifiedPassW.ofSpec_respectsDeg {b : DegreeBound} {f : VerifiedPassW p}
    (h : RespectsDeg b f) : DenseRespectsDeg b (ofSpec f) := by
  intro reg d hcov bs facts hin
  rw [ofSpec_out_decode]
  exact h (reg.decodeCS d) bs facts hin

end ApcOptimizer.Dense
