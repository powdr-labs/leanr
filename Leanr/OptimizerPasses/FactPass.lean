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
