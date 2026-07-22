import ApcOptimizer.Implementation.OptimizerPasses.Pass

set_option autoImplicit false

/-! # Constraint-system coverage monotonicity

A covered dense constraint system stays covered under registry extension, and the encode of a spec
system is covered by the registry it produces (`encodeCS_covered`, used at the pipeline entry). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

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

theorem VarRegistry.encodeCS_covered (r : VarRegistry) (cs : ConstraintSystem p) :
    (r.encodeCS cs).2.CoveredBy (r.encodeCS cs).1 := by
  rw [VarRegistry.encodeCS_fst]
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · rw [VarRegistry.encodeCS_acs] at he
    exact (r.encodeExprs_covered cs.algebraicConstraints e he).mono
      ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs_extends cs.busInteractions)
  · rw [VarRegistry.encodeCS_bis] at hbi
    exact (r.encodeExprs cs.algebraicConstraints).1.encodeBIs_covered cs.busInteractions bi hbi

end ApcOptimizer.Dense
