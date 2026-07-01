import Leanr.Spec

set_option autoImplicit false

variable {p : ℕ} [Fact p.Prime]

-- None of the proofs below need `p` to be prime; they are purely structural.
omit [Fact p.Prime]

/-! ## Equivalence is an equivalence relation

Reflexivity, symmetry and transitivity for the spec's equivalence notions (`≈` on `BusState`,
`ConstraintSystem.implies`, `ConstraintSystem.equivalentTo`). This is the reusable glue that lets
us compose many small, individually-proven optimization passes into one optimizer — chaining
`equivalentTo` facts with `equivalentTo_trans` — instead of ever re-proving a growing monolith. -/

/-- `≈` on `BusState` is reflexive: every message trivially has the same net multiplicity in a
    state as in itself. -/
theorem BusState.equiv_refl (s : BusState p) : s ≈ s :=
  fun _ => rfl

/-- `≈` on `BusState` is symmetric. -/
theorem BusState.equiv_symm {s t : BusState p} (h : s ≈ t) : t ≈ s :=
  fun message => (h message).symm

/-- `≈` on `BusState` is transitive. -/
theorem BusState.equiv_trans {s t u : BusState p} (h1 : s ≈ t) (h2 : t ≈ u) : s ≈ u :=
  fun message => (h1 message).trans (h2 message)

/-- Any constraint system implies itself: the same satisfying assignment works and its side
    effects are (reflexively) equal. -/
theorem ConstraintSystem.implies_refl (cs : ConstraintSystem p) (busSemantics : BusSemantics p) :
    cs.implies cs busSemantics :=
  fun env hsat => ⟨env, hsat, BusState.equiv_refl _⟩

/-- `implies` is transitive: chain the witness assignments and the side-effect equalities. -/
theorem ConstraintSystem.implies_trans {a b c : ConstraintSystem p} {busSemantics : BusSemantics p}
    (h1 : a.implies b busSemantics) (h2 : b.implies c busSemantics) : a.implies c busSemantics :=
  fun env hsat =>
    let ⟨env', hb, hab⟩ := h1 env hsat
    let ⟨env'', hc, hbc⟩ := h2 env' hb
    ⟨env'', hc, BusState.equiv_trans hab hbc⟩

/-- Any constraint system is equivalent to itself. -/
theorem ConstraintSystem.equivalentTo_refl (cs : ConstraintSystem p) (busSemantics : BusSemantics p) :
    cs.equivalentTo cs busSemantics :=
  ⟨cs.implies_refl busSemantics, cs.implies_refl busSemantics⟩

/-- `equivalentTo` is symmetric. -/
theorem ConstraintSystem.equivalentTo_symm {a b : ConstraintSystem p} {busSemantics : BusSemantics p}
    (h : a.equivalentTo b busSemantics) : b.equivalentTo a busSemantics :=
  ⟨h.2, h.1⟩

/-- `equivalentTo` is transitive. -/
theorem ConstraintSystem.equivalentTo_trans {a b c : ConstraintSystem p} {busSemantics : BusSemantics p}
    (h1 : a.equivalentTo b busSemantics) (h2 : b.equivalentTo c busSemantics) :
    a.equivalentTo c busSemantics :=
  ⟨ConstraintSystem.implies_trans h1.1 h2.1, ConstraintSystem.implies_trans h2.2 h1.2⟩

/-! ## Verified passes

A single optimization step, packaged with its correctness proof. `VerifiedPass` is a function
that, given a constraint system and bus semantics, returns a new constraint system **together
with a proof** that it (a) is equivalent to the input and (b) preserves invariants. Because the
proof is part of the return value, there is no separate theorem to weaken: a pass simply cannot
be written down without discharging its obligations.

Passes compose with `VerifiedPass.andThen` (run one, then the next), which threads the two proofs
through `equivalentTo_trans` and the composition of invariant-preservation. The whole optimizer is
then one `VerifiedPass` (`pipeline`), and `optimizer_maintainsCorrectness` is a projection of its
carried proof.

**To add an optimization:** write a `VerifiedPass` for it (returning the transformed system and a
proof of `PassCorrect`), then insert it into `pipeline` with `.andThen`. Prove `PassCorrect` for
your transformation; do not touch anything above this line or in `Spec.lean`. -/

/-- The per-pass correctness obligation: `out` is equivalent to the input `cs`, and if `cs`
    guarantees the system's invariants then so does `out`. This is exactly the two-part contract
    of `optimizerMaintainsCorrectness`, stated for a single step. -/
def PassCorrect (cs out : ConstraintSystem p) (busSemantics : BusSemantics p) : Prop :=
  out.equivalentTo cs busSemantics ∧
    (cs.guaranteesInvariants busSemantics → out.guaranteesInvariants busSemantics)

/-- A proof-carrying optimization pass: maps a constraint system to a new one, bundled with a
    proof that the step is correct (`PassCorrect`). -/
abbrev VerifiedPass (p : ℕ) :=
  (cs : ConstraintSystem p) → (busSemantics : BusSemantics p) →
    { out : ConstraintSystem p // PassCorrect cs out busSemantics }

/-- The identity pass: returns the system unchanged, correct by reflexivity. -/
def VerifiedPass.id : VerifiedPass p :=
  fun cs busSemantics => ⟨cs, cs.equivalentTo_refl busSemantics, _root_.id⟩

/-- Sequential composition: run `f`, then run `g` on its output. The result is correct by
    transitivity of `equivalentTo` and composition of the invariant-preservation implications. -/
def VerifiedPass.andThen (f g : VerifiedPass p) : VerifiedPass p :=
  fun cs busSemantics =>
    let r1 := f cs busSemantics
    let r2 := g r1.val busSemantics
    ⟨r2.val,
     ConstraintSystem.equivalentTo_trans r2.property.1 r1.property.1,
     fun h => r2.property.2 (r1.property.2 h)⟩

/-! ## The optimizer -/

/-- The optimization pipeline: the sequence of verified passes that make up the optimizer.
    Currently just the identity (no passes yet). Extend it by composing passes with `.andThen`,
    e.g. `somePass.andThen anotherPass`. -/
def pipeline : VerifiedPass p :=
  VerifiedPass.id

/-- The circuit optimizer: run the pipeline and project out the resulting constraint system.
    The signature is fixed (`ConstraintSystem p → BusSemantics p → ConstraintSystem p`) so the
    size/effectiveness tooling and the snapshot test can use it directly; correctness travels
    separately via `pipeline`'s carried proof (`optimizer_maintainsCorrectness`). -/
def optimizer (cs : ConstraintSystem p) (busSemantics : BusSemantics p) : ConstraintSystem p :=
  (pipeline cs busSemantics).val

/-- The optimizer maintains correctness. This is just the proof carried by `pipeline`. -/
theorem optimizer_maintainsCorrectness :
    optimizerMaintainsCorrectness (p := p) optimizer :=
  fun cs busSemantics => (pipeline cs busSemantics).property
