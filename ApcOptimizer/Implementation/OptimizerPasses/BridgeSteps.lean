import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Certified-step loop combinators

`DenseNativeStep` carries a certified step's invariants with its value; `trans`/`drain` compose
per-step certificates into one, closed into a pass by `DenseVerifiedPassW.ofDenseStep`.

The `isInput`-composition fact baked in: registering a `powdrId? = none` `Variable` leaves
`VarRegistry.isInput` pointwise unchanged, so a pass minting only derived variables preserves
`isInput` exactly and certificates compose at literally the same function. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `DenseNativeStep`: a certified step, invariants travelling with the value -/

structure DenseNativeStep (p : ℕ) (bs : BusSemantics p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) where
  /-- The (possibly extended) output registry. -/
  reg' : VarRegistry
  out : DenseConstraintSystem p
  /-- The dense derivations minted by this step. -/
  dd : DenseDerivations p
  /-- The registry only grows. -/
  ext : reg.Extends reg'
  /-- Minting only derived (`powdrId? = none`) columns preserves `isInput` pointwise. -/
  hii : reg'.isInput = reg.isInput
  cov : out.CoveredBy reg'
  dcov : dd.CoveredBy reg'
  /-- Correctness at the output registry's `isInput`. -/
  correct : DensePassCorrect reg'.isInput d out dd bs

/-- Reflexivity / identity step: same registry and system, no new derivations. -/
def DenseNativeStep.refl (bs : BusSemantics p) {reg : VarRegistry} {d : DenseConstraintSystem p}
    (hcov : d.CoveredBy reg) : DenseNativeStep p bs reg d where
  reg' := reg
  out := d
  dd := []
  ext := VarRegistry.Extends.refl reg
  hii := rfl
  cov := hcov
  dcov := by intro x hx; simp at hx
  correct := DensePassCorrect.refl reg.isInput d bs

/-- Non-extending step: keep the registry, change the system to `out`, no new derivations; the
    caller supplies `hcov`/`hcorrect`. -/
def DenseNativeStep.ofSame (bs : BusSemantics p) {reg : VarRegistry} {d out : DenseConstraintSystem p}
    (hcov : out.CoveredBy reg) (hcorrect : DensePassCorrect reg.isInput d out [] bs) :
    DenseNativeStep p bs reg d where
  reg' := reg
  out := out
  dd := []
  ext := VarRegistry.Extends.refl reg
  hii := rfl
  cov := hcov
  dcov := by intro x hx; simp at hx
  correct := hcorrect

/-- Sequential composition of two certified steps (`s2` from `s1`'s output), concatenating
    derivations (`s1.dd ++ s2.dd`); `s1`'s certificate is transported forward by `rw [s2.hii]`. -/
def DenseNativeStep.trans {bs : BusSemantics p} {reg : VarRegistry} {d : DenseConstraintSystem p}
    (s1 : DenseNativeStep p bs reg d) (s2 : DenseNativeStep p bs s1.reg' s1.out) :
    DenseNativeStep p bs reg d where
  reg' := s2.reg'
  out := s2.out
  dd := s1.dd ++ s2.dd
  ext := s1.ext.trans s2.ext
  hii := s2.hii.trans s1.hii
  cov := s2.cov
  dcov := DenseDerivations.coveredBy_append (DenseDerivations.CoveredBy.mono s2.ext s1.dcov) s2.dcov
  correct := by
    have h1 : DensePassCorrect s2.reg'.isInput d s1.out s1.dd bs := by
      rw [s2.hii]; exact s1.correct
    exact h1.andThen s2.correct

/-! ## Fold and drain combinators

Both fold per-step certificates into one `DenseNativeStep` via `trans`, threading an opaque state
`σ` and the running coverage. -/

/-- Drain: iterate `step` (reporting `none` at the fixpoint) up to `fuel` times, composing the
    per-step certificates into one certified step and returning the final `σ`. -/
def DenseNativeStep.drain {σ : Type} (bs : BusSemantics p)
    (step : σ → (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
      Option (σ × DenseNativeStep p bs reg d)) :
    Nat → σ → (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
      σ × DenseNativeStep p bs reg d
  | 0, s, _reg, _d, hcov => (s, DenseNativeStep.refl bs hcov)
  | fuel + 1, s, reg, d, hcov =>
    match step s reg d hcov with
    | none => (s, DenseNativeStep.refl bs hcov)
    | some r1 =>
      let r2 := DenseNativeStep.drain bs step fuel r1.1 r1.2.reg' r1.2.out r1.2.cov
      (r2.1, r1.2.trans r2.2)

/-! ## Glue into `DensePassResult` / the pass builders

`toDensePassResult` closes a certified step into a `DensePassResult`; `ofDenseStep` wires it into a
`DenseVerifiedPassW`. -/

/-- Close a certified step into a `DensePassResult` (`correct` via `DensePassCorrect.lift`). -/
def DenseNativeStep.toDensePassResult {bs : BusSemantics p} {reg : VarRegistry}
    {d : DenseConstraintSystem p} (s : DenseNativeStep p bs reg d) (hcov : d.CoveredBy reg) :
    DensePassResult reg d bs where
  reg' := s.reg'
  out := s.out
  derivs := s.dd
  ext := s.ext
  covered := s.cov
  dcovered := s.dcov
  correct := by
    have hcovd' : d.CoveredBy s.reg' := denseCS_coveredBy_mono s.ext hcov
    have hlift := DensePassCorrect.lift hcovd' s.cov s.dcov s.correct
    rwa [s.ext.decodeCS_eq hcov] at hlift

/-- Build a `DenseVerifiedPassW` from a per-invocation certified-step builder. -/
def DenseVerifiedPassW.ofDenseStep
    (build : (reg : VarRegistry) → (bs : BusSemantics p) → (facts : BusFacts p bs) →
      (d : DenseConstraintSystem p) → d.CoveredBy reg → DenseNativeStep p bs reg d) :
    DenseVerifiedPassW p :=
  fun reg d hcov bs facts => (build reg bs facts d hcov).toDensePassResult hcov

end ApcOptimizer.Dense
