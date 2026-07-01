import Leanr.Spec

set_option autoImplicit false

variable {p : ℕ}

/-! # Optimizer scaffolding

The reusable framework for building the circuit optimizer out of small, individually-proven
optimization *passes*. Nothing here is specific to a particular optimization; concrete passes
live in `Leanr/OptimizerPasses/`, and the pipeline that assembles them into the public
`optimizer` lives in `Leanr/Optimizer.lean`.

This module provides:

* the equivalence-relation glue for the spec's notions (`≈` on `BusState`,
  `ConstraintSystem.implies`, `ConstraintSystem.equivalentTo`) — reflexivity, symmetry,
  transitivity — which is what lets passes *compose* without re-proving a growing monolith;
* `PassCorrect`, the per-step correctness obligation;
* `VerifiedPass`, a pass bundled with its own `PassCorrect` proof (so a pass cannot be written
  without discharging its obligations), and `VerifiedPass.andThen`/`VerifiedPass.id` to compose
  and seed pipelines.

These proofs are purely structural; none of them need `p` to be prime. -/

/-! ## Equivalence is an equivalence relation -/

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
through `equivalentTo_trans` and the composition of invariant-preservation.

**To add an optimization:** create a `VerifiedPass` for it in a new file under
`Leanr/OptimizerPasses/`, then `.andThen` it into `pipeline` in `Leanr/Optimizer.lean`. Prove
`PassCorrect` for your transformation; do not change `Spec.lean` or the glue above. -/

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

/-- Iterate a pass `n` times. Used to run local, one-step passes (e.g. "substitute one variable")
    to a fixpoint: each application is a `VerifiedPass`, so the composite is correct by construction.
    A pass that finds nothing to do returns its input unchanged, so extra iterations are harmless. -/
def VerifiedPass.iterate (f : VerifiedPass p) : Nat → VerifiedPass p
  | 0 => VerifiedPass.id
  | n + 1 => (f.iterate n).andThen f
