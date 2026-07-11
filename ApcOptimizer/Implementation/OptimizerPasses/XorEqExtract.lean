import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Bitwise-XOR equality extraction (C4a)

powdr-exported memory/shift blocks keep, on the bitwise-lookup bus, a family of interactions
`[x, y, z, 1]` (op 1: `z = x ⊕ y`, with `x`,`y` bytes) in which **one operand is the constant 0**.
Then the XOR linearizes to an *equality*: `[0, y, z, 1] ⟹ z = y` and `[x, 0, z, 1] ⟹ z = x`. These
equalities pin an intermediate byte (loaded-data / effective-address limb, the `b`/`a`/`c` families)
to another variable, but — being carried on the **bus** — Gaussian elimination never uses them, so
the intermediate limbs survive. powdr represents everything with the canonical loaded value; this
pass closes that gap.

`xorEqExtractPass` recognizes these 0-operand XOR interactions and **adds the entailed equality
constraint** `z − y` (resp. `z − x`), keeping the interaction (which still imposes byte-ness). Placed
in the cleanup cycle, the added equalities feed same-cycle Gauss, which eliminates the intermediate
variables and cascades — a variable win (and, via the range/bitwise checks the eliminated variables
no longer need, a bus win).

The equality is entailed by the interaction's acceptance (`BusFacts.xorZeroEq`, proven for OpenVM's
bitwise lookup from `Nat.zero_xor`/`Nat.xor_zero`), so the pass is a `ConstraintSystem.addConstraints_correct`
— soundness drops the added constraints, and adding constraints touches no interaction, so side
effects and admissibility are unchanged. Gated on `(1 : ZMod p) ≠ 0` (every prime field; identity on
`ZMod 1`).

The 255-operand XOR cases (`[x, 255, z, 1] ⟹ z = 255 − x`) are the sibling pass C4b, which needs the
byte-complement identity and stacks on this one. -/

namespace XorEqExtract

variable {p : ℕ}

/-- `z − e` as an expression (`z + (-1)·e`). -/
def subE (z e : Expression p) : Expression p := .add z (.mul (.const (-1)) e)

theorem subE_eval (z e : Expression p) (env : Variable → ZMod p) :
    (subE z e).eval env = z.eval env - e.eval env := by
  simp only [subE, Expression.eval]; ring

/-- The entailed equality from a 0-operand bitwise-XOR interaction `[x, y, z, 1]` (multiplicity 1) on
    a `xorZeroEq` bus: `some (z − y)` when `x = 0`, `some (z − x)` when `y = 0`; `none` otherwise. -/
def xorEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match bi.payload with
  | [x, y, z, op] =>
    if facts.xorZeroEq bi.busId = true ∧ bi.multiplicity = Expression.const 1
        ∧ op = Expression.const 1 then
      if x = Expression.const 0 then some (subE z y)
      else if y = Expression.const 0 then some (subE z x)
      else none
    else none
  | _ => none

/-- Structure of a recognized interaction. -/
theorem xorEq?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : xorEq? bs facts bi = some c) :
    facts.xorZeroEq bi.busId = true ∧ bi.multiplicity = Expression.const 1 ∧
      ∃ x y z, bi.payload = [x, y, z, Expression.const 1] ∧
        ((x = Expression.const 0 ∧ c = subE z y) ∨ (y = Expression.const 0 ∧ c = subE z x)) := by
  unfold xorEq? at h
  split at h
  · rename_i x y z op hpay
    split_ifs at h with hcond hx hy
    · obtain ⟨hfact, hmult, hop⟩ := hcond
      subst hop
      exact ⟨hfact, hmult, x, y, z, hpay, Or.inl ⟨hx, by simpa using h.symm⟩⟩
    · obtain ⟨hfact, hmult, hop⟩ := hcond
      subst hop
      exact ⟨hfact, hmult, x, y, z, hpay, Or.inr ⟨hy, by simpa using h.symm⟩⟩
  · exact absurd h (by simp)

/-- Extract every 0-operand bitwise-XOR equality and add it as an algebraic constraint. -/
def xorEqExtractPass : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    let new := cs.busInteractions.filterMap (xorEq? bs facts)
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
      cs.addConstraints_correct bs new
        (by
          -- entailment: each added equality holds on every satisfying assignment
          intro env _ hsat c hc
          obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
          obtain ⟨hfact, hmult, x, y, z, hpay, hcase⟩ := xorEq?_spec bs facts bi c hbc
          have hev : bi.eval env =
              { busId := bi.busId, multiplicity := 1,
                payload := [x.eval env, y.eval env, z.eval env, 1] } := by
            unfold BusInteraction.eval; rw [hmult, hpay]; simp [Expression.eval]
          have hviol : bs.violatesConstraint (bi.eval env) = false :=
            hsat.2 bi hbi (by rw [hev]; exact h1ne)
          rcases hcase with ⟨hx0, rfl⟩ | ⟨hy0, rfl⟩
          · rw [subE_eval]
            have he0 : bi.eval env = ⟨bi.busId, 1, [0, y.eval env, z.eval env, 1]⟩ := by
              rw [hev, hx0]; simp [Expression.eval]
            rw [(facts.xorZeroEq_sound bi.busId hfact).1 (y.eval env) (z.eval env)
              (he0 ▸ hviol), sub_self]
          · rw [subE_eval]
            have he0 : bi.eval env = ⟨bi.busId, 1, [x.eval env, 0, z.eval env, 1]⟩ := by
              rw [hev, hy0]; simp [Expression.eval]
            rw [(facts.xorZeroEq_sound bi.busId hfact).2 (x.eval env) (z.eval env)
              (he0 ▸ hviol), sub_self])
        (by
          -- no new variables: each equality's variables come from the interaction's payload
          intro c hc zv hz
          obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
          obtain ⟨_, _, x, y, w, hpay, hcase⟩ := xorEq?_spec bs facts bi c hbc
          have mem_pay : ∀ e ∈ ([x, y, w] : List (Expression p)), e ∈ bi.payload := by
            intro e he; rw [hpay]; simp only [List.mem_cons] at he ⊢; tauto
          rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          · rcases List.mem_append.1 (by simpa only [subE, Expression.vars, List.append_assoc,
              List.nil_append, Expression.vars] using hz) with hzw | hze
            · exact ConstraintSystem.mem_vars_of_payload hbi (mem_pay w (by simp)) hzw
            · exact ConstraintSystem.mem_vars_of_payload hbi (mem_pay _ (by simp)) hze)⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

end XorEqExtract
