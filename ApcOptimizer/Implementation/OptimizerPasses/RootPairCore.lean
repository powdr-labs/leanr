import ApcOptimizer.Spec
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Two-root field core

Representation-independent (`ZMod p`-value only) core of the two-root bounded-integer argument.
Both the dense two-root soundness (`Dense/AddrDiseqProof.lean`, `Dense/RootPairUnifyProof.lean`) and
the reference `OldVariableBased/RootPairUnify.lean` consume these lemmas; they mention no
`Variable`/`Expression`/`VarId` representation, only field values and integer bounds. -/

variable {p : ℕ}

/-- Membership in the root pair: a satisfied two-root constraint puts `x` at one of the two
    roots, `g = k⁻¹·δ` apart. -/
theorem twoRoot_mem [Fact p.Prime] (k a δ x : ZMod p) (hunit : k * k⁻¹ = 1)
    (h : (a + k * x) * (a + δ + k * x) = 0) :
    x = -(k⁻¹ * a) ∨ x = -(k⁻¹ * a) - k⁻¹ * δ := by
  rcases mul_eq_zero.1 h with h0 | h0
  · left; linear_combination k⁻¹ * h0 - x * hunit
  · right; linear_combination k⁻¹ * h0 - x * hunit

/-- Two values in the same root pair, both bounded below the root gap (and its complement),
    are equal: their field difference is `0` or `±g`, and `±g` is out of integer reach. -/
theorem rootPair_eq [Fact p.Prime] (r g x y : ZMod p)
    (hx : x = r ∨ x = r - g) (hy : y = r ∨ y = r - g)
    (B : Nat) (hxB : x.val < B) (hyB : y.val < B)
    (h1 : B ≤ g.val) (h2 : B ≤ p - g.val) : x = y := by
  have key : ∀ u v : ZMod p, u.val < B → v.val < B → u = v - g → False := by
    intro u v hu hv huv
    have hvg : v = u + g := by rw [huv]; ring
    have hval : v.val = (u.val + g.val) % p := by rw [hvg, ZMod.val_add]
    by_cases hlt : u.val + g.val < p
    · rw [Nat.mod_eq_of_lt hlt] at hval
      omega
    · -- `u.val ≥ p − g.val ≥ B` contradicts `u.val < B`
      have hgp : g.val < p := ZMod.val_lt g
      omega
  rcases hx with rfl | rfl
  · rcases hy with h | h
    · exact h.symm
    · exact (key y x hyB hxB h).elim
  · rcases hy with h | h
    · exact (key (r - g) r hxB (h ▸ hyB) rfl).elim
    · exact h.symm
