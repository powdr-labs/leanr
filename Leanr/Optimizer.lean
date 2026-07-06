import Leanr.Spec

set_option autoImplicit false

variable {p : ℕ} [Fact p.Prime]

-- None of the proofs below need `p` to be prime; they are purely structural.
omit [Fact p.Prime]

/-- The identity optimizer: it returns the constraint system unchanged.
    This is the trivial optimizer that does nothing, serving as a baseline. -/
def identityOptimizer (cs : ConstraintSystem p) (_ : BusSemantics p) : ConstraintSystem p :=
  cs

/-- `≈` on `BusState` is reflexive: every message trivially has the same net
    multiplicity in a state as in itself. -/
theorem BusState.equiv_refl (s : BusState p) : s ≈ s :=
  fun _ => rfl

/-- Any constraint system implies itself: the same satisfying assignment works
    and its side effects are (reflexively) equal. -/
theorem ConstraintSystem.implies_refl (cs : ConstraintSystem p) (busSemantics : BusSemantics p) :
    cs.implies cs busSemantics :=
  fun env hsat => ⟨env, hsat, BusState.equiv_refl _⟩

/-- Any constraint system admissibly-implies itself: the same admissible assignment works. -/
theorem ConstraintSystem.impliesAdmissible_refl (cs : ConstraintSystem p)
    (busSemantics : BusSemantics p) : cs.impliesAdmissible cs busSemantics :=
  fun env hadm hsat => ⟨env, hsat, hadm, BusState.equiv_refl _⟩

/-- Any constraint system refines itself (sound + admissible-complete, both reflexively). -/
theorem ConstraintSystem.refines_refl (cs : ConstraintSystem p) (busSemantics : BusSemantics p) :
    cs.refines cs busSemantics :=
  ⟨cs.implies_refl busSemantics, cs.impliesAdmissible_refl busSemantics⟩

/-- The identity optimizer maintains correctness: it returns the system unchanged, so it
    `refines` the input, preserves invariants, and (leaving every expression as-is) never
    changes any degree — hence trivially respects the degree bound. -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) identityOptimizer :=
  ⟨fun cs busSemantics => ⟨cs.refines_refl busSemantics, id⟩,
   fun _ _ h => h⟩
