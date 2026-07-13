import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Bitwise-XOR constant-operand equality extraction (C4a + C4b)

powdr-exported memory/shift/keccak blocks keep, on the bitwise-lookup bus, a family of interactions
`[x, y, z, 1]` (op 1: `z = x ⊕ y`, with `x`,`y` bytes) in which **one operand is a constant byte**.
For the two constants that make the XOR *affine* in the other operand — `0` and `255` — the
interaction pins an intermediate byte to a linear form:

* **zero operand** linearizes to an *equality*: `[0, y, z, 1] ⟹ z = y` and `[x, 0, z, 1] ⟹ z = x`
  (C4a, `BusFacts.xorZeroEq`, from `Nat.zero_xor`/`Nat.xor_zero`);
* **255 operand** linearizes to the byte *complement*: `[255, y, z, 1] ⟹ z = 255 − y` and
  `[x, 255, z, 1] ⟹ z = 255 − x` (C4b, `BusFacts.xorComplEq`, from `n ⊕ 255 = 255 − n` for a byte
  `n`, sound only when `255` is a genuine byte, `256 ≤ p`).

These are the *only* two constants for which `x ⊕ c` is affine in `x`; every other constant makes
the XOR bit-dependent. Both pin an intermediate byte (loaded-data / effective-address / NOT-result
limb, the `b`/`a`/`c` families) to a linear form of another variable, but — being carried on the
**bus** — Gaussian elimination never uses them, so the intermediate limbs survive. powdr represents
everything with the canonical value; this pass closes that gap.

`xorEqExtractPass` recognizes these constant-operand XOR interactions and **adds the entailed
equality constraint** (`z − y`, `z − x`, `z − (255 − y)`, or `z − (255 − x)`), keeping the
interaction (which still imposes byte-ness). Placed in the cleanup cycle, the added equalities feed
same-cycle Gauss, which eliminates the intermediate variables and cascades — a variable win (and,
via the range/bitwise checks the eliminated variables no longer need, a bus win).

Each added equality is entailed by the interaction's acceptance (`xorZeroEq_sound` / `xorComplEq_sound`),
so the pass is a `ConstraintSystem.addConstraints_correct` — soundness drops the added constraints,
and adding constraints touches no interaction, so side effects and admissibility are unchanged.
Gated on `(1 : ZMod p) ≠ 0` (every prime field; identity on `ZMod 1`); the `255` cases fire only
where the VM's `xorComplEq` fact is available (`trivial` and small fields claim nothing). -/

namespace XorEqExtract

variable {p : ℕ}

/-- `z − e` as an expression (`z + (-1)·e`). -/
def subE (z e : Expression p) : Expression p := .add z (.mul (.const (-1)) e)

theorem subE_eval (z e : Expression p) (env : Variable → ZMod p) :
    (subE z e).eval env = z.eval env - e.eval env := by
  simp only [subE, Expression.eval]; ring

/-- `255 − e` as an expression (the byte complement of `e`). -/
def complE (e : Expression p) : Expression p := .add (.const 255) (.mul (.const (-1)) e)

theorem complE_eval (e : Expression p) (env : Variable → ZMod p) :
    (complE e).eval env = 255 - e.eval env := by
  simp only [complE, Expression.eval]; ring

/-- The entailed equality from a constant-operand bitwise-XOR interaction `[x, y, z, 1]`
    (multiplicity 1): `z − y` / `z − x` for a `0` operand (`xorZeroEq`), and
    `z − (255 − y)` / `z − (255 − x)` for a `255` operand (`xorComplEq`); `none` otherwise. -/
def xorEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match bi.payload with
  | [x, y, z, op] =>
    if bi.multiplicity = Expression.const 1 ∧ op = Expression.const 1 then
      if facts.xorZeroEq bi.busId = true ∧ x = Expression.const 0 then some (subE z y)
      else if facts.xorZeroEq bi.busId = true ∧ y = Expression.const 0 then some (subE z x)
      else if facts.xorComplEq bi.busId = true ∧ x = Expression.const 255 then
        some (subE z (complE y))
      else if facts.xorComplEq bi.busId = true ∧ y = Expression.const 255 then
        some (subE z (complE x))
      else none
    else none
  | _ => none

/-- Structure of a recognized interaction: multiplicity 1, payload `[x, y, z, 1]`, and one of the
    four constant-operand cases with the matching added constraint. -/
theorem xorEq?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : xorEq? bs facts bi = some c) :
    bi.multiplicity = Expression.const 1 ∧
      ∃ x y z, bi.payload = [x, y, z, Expression.const 1] ∧
        ((facts.xorZeroEq bi.busId = true ∧ x = Expression.const 0 ∧ c = subE z y)
          ∨ (facts.xorZeroEq bi.busId = true ∧ y = Expression.const 0 ∧ c = subE z x)
          ∨ (facts.xorComplEq bi.busId = true ∧ x = Expression.const 255 ∧ c = subE z (complE y))
          ∨ (facts.xorComplEq bi.busId = true ∧ y = Expression.const 255 ∧ c = subE z (complE x))) := by
  unfold xorEq? at h
  split at h
  · rename_i x y z op hpay
    split_ifs at h with hmo hA hB hC hD
    · obtain ⟨hm, hop⟩ := hmo; obtain ⟨hfact, hx0⟩ := hA
      rw [hop] at hpay
      exact ⟨hm, x, y, z, hpay, Or.inl ⟨hfact, hx0, by simpa using h.symm⟩⟩
    · obtain ⟨hm, hop⟩ := hmo; obtain ⟨hfact, hy0⟩ := hB
      rw [hop] at hpay
      exact ⟨hm, x, y, z, hpay, Or.inr (Or.inl ⟨hfact, hy0, by simpa using h.symm⟩)⟩
    · obtain ⟨hm, hop⟩ := hmo; obtain ⟨hfact, hx255⟩ := hC
      rw [hop] at hpay
      exact ⟨hm, x, y, z, hpay, Or.inr (Or.inr (Or.inl ⟨hfact, hx255, by simpa using h.symm⟩))⟩
    · obtain ⟨hm, hop⟩ := hmo; obtain ⟨hfact, hy255⟩ := hD
      rw [hop] at hpay
      exact ⟨hm, x, y, z, hpay, Or.inr (Or.inr (Or.inr ⟨hfact, hy255, by simpa using h.symm⟩))⟩
  · exact absurd h (by simp)

/-- Extract every constant-operand bitwise-XOR equality and add it as an algebraic constraint. -/
def xorEqExtractPass : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    let new := cs.busInteractions.filterMap (xorEq? bs facts)
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
      cs.addConstraints_correct bs new
        (by
          -- entailment: each added equality holds on every satisfying assignment
          intro env _ hsat c hc
          obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
          obtain ⟨hmult, x, y, z, hpay, hcase⟩ := xorEq?_spec bs facts bi c hbc
          have hev : bi.eval env =
              { busId := bi.busId, multiplicity := 1,
                payload := [x.eval env, y.eval env, z.eval env, 1] } := by
            unfold BusInteraction.eval; rw [hmult, hpay]; simp [Expression.eval]
          have hviol : bs.violatesConstraint (bi.eval env) = false :=
            hsat.2 bi hbi (by rw [hev]; exact h1ne)
          rcases hcase with ⟨hfact, hx0, rfl⟩ | ⟨hfact, hy0, rfl⟩ | ⟨hfact, hx255, rfl⟩
            | ⟨hfact, hy255, rfl⟩
          · rw [subE_eval]
            have he0 : bi.eval env = ⟨bi.busId, 1, [0, y.eval env, z.eval env, 1]⟩ := by
              rw [hev, hx0]; simp [Expression.eval]
            rw [(facts.xorZeroEq_sound bi.busId hfact).1 (y.eval env) (z.eval env)
              (he0 ▸ hviol), sub_self]
          · rw [subE_eval]
            have he0 : bi.eval env = ⟨bi.busId, 1, [x.eval env, 0, z.eval env, 1]⟩ := by
              rw [hev, hy0]; simp [Expression.eval]
            rw [(facts.xorZeroEq_sound bi.busId hfact).2 (x.eval env) (z.eval env)
              (he0 ▸ hviol), sub_self]
          · rw [subE_eval, complE_eval]
            have he0 : bi.eval env = ⟨bi.busId, 1, [255, y.eval env, z.eval env, 1]⟩ := by
              rw [hev, hx255]; simp [Expression.eval]
            rw [(facts.xorComplEq_sound bi.busId hfact).2 (y.eval env) (z.eval env)
              (he0 ▸ hviol), sub_self]
          · rw [subE_eval, complE_eval]
            have he0 : bi.eval env = ⟨bi.busId, 1, [x.eval env, 255, z.eval env, 1]⟩ := by
              rw [hev, hy255]; simp [Expression.eval]
            rw [(facts.xorComplEq_sound bi.busId hfact).1 (x.eval env) (z.eval env)
              (he0 ▸ hviol), sub_self])
        (by
          -- no new variables: each equality's variables come from the interaction's payload
          intro c hc zv hz
          obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
          obtain ⟨_, x, y, w, hpay, hcase⟩ := xorEq?_spec bs facts bi c hbc
          have mem_pay : ∀ e ∈ ([x, y, w] : List (Expression p)), e ∈ bi.payload := by
            intro e he; rw [hpay]; simp only [List.mem_cons] at he ⊢; tauto
          rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
          · rcases List.mem_append.1 (by simpa only [subE, complE, Expression.vars,
              List.append_assoc, List.nil_append] using hz) with hzw | hze
            · exact ConstraintSystem.mem_vars_of_payload hbi (mem_pay w (by simp)) hzw
            · exact ConstraintSystem.mem_vars_of_payload hbi (mem_pay _ (by simp)) hze)⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

end XorEqExtract
