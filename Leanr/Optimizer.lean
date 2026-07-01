import Leanr.Spec

set_option autoImplicit false

variable {p : ℕ} [Fact p.Prime]

-- None of the proofs below need `p` to be prime; they are purely structural.
omit [Fact p.Prime]

/-- The circuit optimizer. Currently the identity: it returns the constraint system
    unchanged. This is the starting point for an optimizer that actually shrinks the
    circuit while preserving correctness. -/
def optimizer (cs : ConstraintSystem p) (_ : BusSemantics p) : ConstraintSystem p :=
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

/-- Any constraint system is equivalent to itself. -/
theorem ConstraintSystem.equivalentTo_refl (cs : ConstraintSystem p) (busSemantics : BusSemantics p) :
    cs.equivalentTo cs busSemantics :=
  ⟨cs.implies_refl busSemantics, cs.implies_refl busSemantics⟩

/-- The optimizer maintains correctness. -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) optimizer :=
  fun cs busSemantics =>
    ⟨cs.equivalentTo_refl busSemantics, id⟩
