import Leanr.Implementation.OptimizerPasses.Basic
import Leanr.Implementation.BusFacts
import Leanr.Utils.Size
import Mathlib.Data.Prod.Lex

set_option autoImplicit false

/-! # Fact-aware verified passes

A `VerifiedPassW` is a `VerifiedPass` that may additionally consult proven `BusFacts` about the
bus semantics it is given (see `Leanr/Implementation/BusFacts.lean`). The correctness obligation is unchanged —
`PassCorrect` against the *semantics* — the facts only widen what a pass can decide, never what
it may claim: with `BusFacts.trivial` every fact-aware pass degrades to fact-free behavior. -/

variable {p : ℕ}

/-- A proof-carrying pass that may consult proven facts about the bus semantics. -/
abbrev VerifiedPassW (p : ℕ) :=
  (cs : ConstraintSystem p) → (dsIn : Derivations p) → (bs : BusSemantics p) →
    (facts : BusFacts p bs) → PassResult cs dsIn bs

/-- Any fact-free pass is a fact-aware pass that ignores the facts. -/
def VerifiedPass.withFacts (f : VerifiedPass p) : VerifiedPassW p :=
  fun cs ds bs _ => f cs ds bs

/-- Sequential composition (same proof shape as `VerifiedPass.andThen`): derivations are threaded. -/
def VerifiedPassW.andThen (f g : VerifiedPassW p) : VerifiedPassW p :=
  fun cs ds bs facts =>
    let r1 := f cs ds bs facts
    let r2 := g r1.out r1.derivs bs facts
    ⟨r2.out, r2.derivs, r1.correct.andThen r2.correct⟩

/-- Iterate a fact-aware pass `n` times. -/
def VerifiedPassW.iterate (f : VerifiedPassW p) : Nat → VerifiedPassW p
  | 0 => fun cs ds bs _ => ⟨cs, ds, PassCorrect.refl cs ds bs⟩
  | n + 1 => (f.iterate n).andThen f

deriving instance DecidableEq for Expression
deriving instance DecidableEq for BusInteraction
deriving instance DecidableEq for ConstraintSystem

/-! ## Iterating to a fixpoint without a fuel bound

Structural recursion on a fuel counter would need an explicit iteration budget. We drop the
budget entirely by recursing on a *well-founded measure* instead: the lexicographic size key
`(#distinct variables, #bus interactions, #algebraic constraints)`, with variables most
significant — exactly the optimizer's effectiveness priority. Each cleanup cycle either strictly
lowers this key (so we recurse) or does not (so we stop, keeping the pre-cycle system). The
recursion is guarded by precisely the strict-decrease it needs, so `decreasing_by` is immediate and
no `iters` parameter is required. As a bonus the loop is size-monotone by construction: its output
never has a larger key than its input (`iterateToFixpoint_monotone`). Derivations accumulate across
the kept steps exactly as in `andThen`.

The distinct-variable count uses a `HashSet` (not `ConstraintSystem.size`'s `dedup`, which is
quadratic) so the per-cycle measure stays cheap on large circuits. -/

/-- Number of distinct variables, computed with a `HashSet` (linear, unlike the audited
    `ConstraintSystem.size`, which uses `List.dedup`). Same value; used only for the loop measure. -/
def ConstraintSystem.varCount (cs : ConstraintSystem p) : Nat :=
  ((cs.algebraicConstraints.flatMap Expression.vars ++
      cs.busInteractions.flatMap BusInteraction.vars).foldl
        (init := (∅ : Std.HashSet Variable)) (·.insert ·)).size

/-- The lexicographic size key `(#distinct vars, #bus interactions, #constraints)` — variables most
    significant, matching the effectiveness priority. Well-founded under `<`, so it can serve as a
    termination measure; decreasing it is exactly "the circuit got strictly smaller". -/
def ConstraintSystem.sizeKey (cs : ConstraintSystem p) : Nat ×ₗ Nat ×ₗ Nat :=
  toLex (cs.varCount, toLex (cs.busInteractions.length, cs.algebraicConstraints.length))

/-- Iterate a fact-aware pass to a fixpoint, with **no** iteration budget: apply `f`; if the result
    is strictly smaller (lexicographically in `sizeKey`), recurse from it; otherwise stop and return
    the input unchanged. Terminates because every recursive step strictly decreases the well-founded
    `sizeKey`. Correct by construction (each kept step is `PassCorrect`, derivations concatenating;
    stopping returns the input, correct by reflexivity). -/
def iterateToFixpoint (f : VerifiedPassW p) (cs : ConstraintSystem p) (dsIn : Derivations p)
    (bs : BusSemantics p) (facts : BusFacts p bs) : PassResult cs dsIn bs :=
  let r := f cs dsIn bs facts
  if _h : r.out.sizeKey < cs.sizeKey then
    let r2 := iterateToFixpoint f r.out r.derivs bs facts
    ⟨r2.out, r2.derivs, r.correct.andThen r2.correct⟩
  else
    ⟨cs, dsIn, PassCorrect.refl cs dsIn bs⟩
  termination_by cs.sizeKey
  decreasing_by exact _h

/-! ## Degree guarding

`optimizerRespectsDegreeBound` is enforced compositionally with **zero** per-pass proof burden:
every pass is wrapped in a checked guard that falls back to its (unchanged) input if the
output would exceed the semantics' degree bound. `RespectsDeg` then propagates through
composition and iteration. -/

/-- A pass never pushes a within-bound system past the semantics' degree bound. -/
def RespectsDeg (f : VerifiedPassW p) : Prop :=
  ∀ (cs : ConstraintSystem p) (dsIn : Derivations p) (bs : BusSemantics p) (facts : BusFacts p bs),
    cs.withinDegree bs.degreeBound → (f cs dsIn bs facts).out.withinDegree bs.degreeBound

/-- Wrap a pass with a degree guard: if the output would exceed the bound, keep the input. -/
def VerifiedPassW.guardDegree (f : VerifiedPassW p) : VerifiedPassW p :=
  fun cs ds bs facts =>
    let r := f cs ds bs facts
    if r.out.withinDegreeB bs.degreeBound then r
    else ⟨cs, ds, PassCorrect.refl cs ds bs⟩

theorem VerifiedPassW.guardDegree_respectsDeg (f : VerifiedPassW p) :
    RespectsDeg f.guardDegree := by
  intro cs ds bs facts h
  by_cases hok : (f cs ds bs facts).out.withinDegreeB bs.degreeBound = true
  · simp only [VerifiedPassW.guardDegree, hok, if_true]
    exact (ConstraintSystem.withinDegreeB_iff _ _).1 hok
  · simp only [VerifiedPassW.guardDegree, hok]
    exact h

theorem VerifiedPassW.andThen_respectsDeg {f g : VerifiedPassW p}
    (hf : RespectsDeg f) (hg : RespectsDeg g) : RespectsDeg (f.andThen g) := by
  intro cs ds bs facts h
  exact hg _ _ bs facts (hf cs ds bs facts h)

theorem VerifiedPassW.iterate_respectsDeg {f : VerifiedPassW p} (hf : RespectsDeg f) :
    ∀ n, RespectsDeg (f.iterate n)
  | 0 => fun _ _ _ _ h => h
  | n + 1 => VerifiedPassW.andThen_respectsDeg (iterate_respectsDeg hf n) hf

/-- The `sizeKey` order on constraint systems is well-founded (it is the inverse image of `<` on
    the lexicographic `Nat ×ₗ Nat ×ₗ Nat`, which is well-founded). Used to prove properties of
    `iterateToFixpoint` by strong induction on the measure it recurses on. -/
theorem sizeKey_wf : WellFounded (fun a b : ConstraintSystem p => a.sizeKey < b.sizeKey) :=
  InvImage.wf ConstraintSystem.sizeKey wellFounded_lt

/-- `iterateToFixpoint` preserves the degree bound: every kept step is `f` (which respects the
    bound) and the stopping case returns the unchanged input. Proved by strong induction on the
    `sizeKey` measure the loop recurses on. -/
theorem iterateToFixpoint_respectsDeg {f : VerifiedPassW p} (hf : RespectsDeg f) :
    RespectsDeg (iterateToFixpoint f) := by
  intro cs
  induction cs using sizeKey_wf.induction with
  | _ cs ih =>
    intro dsIn bs facts hcs
    rw [iterateToFixpoint]
    split
    · rename_i h
      exact ih _ h _ bs facts (hf cs dsIn bs facts hcs)
    · exact hcs

/-- **The cleanup loop can only improve the circuit.** `iterateToFixpoint f`'s output never has a
    larger lexicographic `sizeKey` (distinct vars, then bus interactions, then constraints) than its
    input: every recursive step strictly lowers the key, and the stopping case returns the input. -/
theorem iterateToFixpoint_monotone {f : VerifiedPassW p}
    (cs : ConstraintSystem p) (dsIn : Derivations p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    (iterateToFixpoint f cs dsIn bs facts).out.sizeKey ≤ cs.sizeKey := by
  induction cs using sizeKey_wf.induction generalizing dsIn with
  | _ cs ih =>
    rw [iterateToFixpoint]
    split
    · rename_i h
      exact le_trans (ih _ h _) (le_of_lt h)
    · exact le_refl _
