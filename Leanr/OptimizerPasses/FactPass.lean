import Leanr.OptimizerPasses.Basic
import Leanr.BusFacts

set_option autoImplicit false

/-! # Fact-aware verified passes

A `VerifiedPassW` is a `VerifiedPass` that may additionally consult proven `BusFacts` about the
bus semantics it is given (see `Leanr/BusFacts.lean`). The correctness obligation is unchanged —
`PassCorrect` against the *semantics* — the facts only widen what a pass can decide, never what
it may claim: with `BusFacts.trivial` every fact-aware pass degrades to fact-free behavior. -/

variable {p : ℕ}

/-- A proof-carrying pass that may consult proven facts about the bus semantics. -/
abbrev VerifiedPassW (p : ℕ) :=
  (cs : ConstraintSystem p) → (bs : BusSemantics p) → (facts : BusFacts p bs) →
    { out : ConstraintSystem p // PassCorrect cs out bs }

/-- Any fact-free pass is a fact-aware pass that ignores the facts. -/
def VerifiedPass.withFacts (f : VerifiedPass p) : VerifiedPassW p :=
  fun cs bs _ => f cs bs

/-- Sequential composition (same proof shape as `VerifiedPass.andThen`). -/
def VerifiedPassW.andThen (f g : VerifiedPassW p) : VerifiedPassW p :=
  fun cs bs facts =>
    let r1 := f cs bs facts
    let r2 := g r1.val bs facts
    ⟨r2.val,
     ConstraintSystem.equivalentTo_trans r2.property.1 r1.property.1,
     fun h => r2.property.2 (r1.property.2 h)⟩

/-- Iterate a fact-aware pass `n` times. -/
def VerifiedPassW.iterate (f : VerifiedPassW p) : Nat → VerifiedPassW p
  | 0 => fun cs bs _ => ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
  | n + 1 => (f.iterate n).andThen f

deriving instance DecidableEq for Expression
deriving instance DecidableEq for BusInteraction
deriving instance DecidableEq for ConstraintSystem

/-- Iterate a fact-aware pass at most `n` times, stopping as soon as a whole application is a
    (structural) no-op — from then on every further application would be too, so the result is
    the same as `iterate n`'s but without paying for the remaining cycles. Makes a generous
    iteration budget free for inputs that converge early. -/
def VerifiedPassW.iterateStable (f : VerifiedPassW p) : Nat → VerifiedPassW p
  | 0 => fun cs bs _ => ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
  | n + 1 => fun cs bs facts =>
      let r := f cs bs facts
      if r.val = cs then r
      else
        let r2 := (f.iterateStable n) r.val bs facts
        ⟨r2.val,
         ConstraintSystem.equivalentTo_trans r2.property.1 r.property.1,
         fun h => r2.property.2 (r.property.2 h)⟩

/-! ## Degree guarding

`optimizerRespectsDegree` is enforced compositionally with **zero** per-pass proof burden:
every pass is wrapped in a checked guard that falls back to its (unchanged) input if the
output would exceed the semantics' degree bound. `RespectsDeg` then propagates through
composition and iteration. -/

/-- A pass never pushes a within-bound system past the semantics' degree bound. -/
def RespectsDeg (f : VerifiedPassW p) : Prop :=
  ∀ (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs),
    cs.withinDegree bs.degreeBound → (f cs bs facts).val.withinDegree bs.degreeBound

/-- Wrap a pass with a degree guard: if the output would exceed the bound, keep the input. -/
def VerifiedPassW.guardDegree (f : VerifiedPassW p) : VerifiedPassW p :=
  fun cs bs facts =>
    let r := f cs bs facts
    if r.val.withinDegreeB bs.degreeBound then r
    else ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩

theorem VerifiedPassW.guardDegree_respectsDeg (f : VerifiedPassW p) :
    RespectsDeg f.guardDegree := by
  intro cs bs facts h
  by_cases hok : (f cs bs facts).val.withinDegreeB bs.degreeBound = true
  · simp only [VerifiedPassW.guardDegree, hok, if_true]
    exact (ConstraintSystem.withinDegreeB_iff _ _).1 hok
  · simp only [VerifiedPassW.guardDegree, hok, if_false]
    exact h

theorem VerifiedPassW.andThen_respectsDeg {f g : VerifiedPassW p}
    (hf : RespectsDeg f) (hg : RespectsDeg g) : RespectsDeg (f.andThen g) := by
  intro cs bs facts h
  exact hg _ bs facts (hf cs bs facts h)

theorem VerifiedPassW.iterate_respectsDeg {f : VerifiedPassW p} (hf : RespectsDeg f) :
    ∀ n, RespectsDeg (f.iterate n)
  | 0 => fun _ _ _ h => h
  | n + 1 => VerifiedPassW.andThen_respectsDeg (iterate_respectsDeg hf n) hf

theorem VerifiedPassW.iterateStable_respectsDeg {f : VerifiedPassW p} (hf : RespectsDeg f) :
    ∀ n, RespectsDeg (f.iterateStable n) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ h => h
  | succ n ih =>
    intro cs bs facts h
    by_cases heq : (f cs bs facts).val = cs
    · simp only [VerifiedPassW.iterateStable, heq, if_true]
      exact h
    · simp only [VerifiedPassW.iterateStable, heq, if_false]
      exact ih _ bs facts (hf cs bs facts h)
