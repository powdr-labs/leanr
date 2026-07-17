import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Bitwise-XOR constant-operand equality extraction (C4a + C4b)

powdr-exported memory/shift/keccak blocks keep, on the bitwise-lookup bus, a family of interactions
`[x, y, z, 1]` (op 1: `z = x ⊕ y`, with `x`,`y` bytes) in which **one operand is a constant byte**.
For the two constants that make the XOR *affine* in the other operand — `0` and `255` — the
interaction pins an intermediate byte to a linear form:

* **zero operand** linearizes to an *equality*: `[0, y, z, 1] ⟹ z = y` and `[x, 0, z, 1] ⟹ z = x`
  (C4a, from `Nat.zero_xor`/`Nat.xor_zero`);
* **255 operand** linearizes to the byte *complement*: `[255, y, z, 1] ⟹ z = 255 − y` and
  `[x, 255, z, 1] ⟹ z = 255 − x` (C4b, from `n ⊕ 255 = 255 − n` for a byte
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

Each added equality is entailed by the interaction's acceptance (`BusFacts.byteXorSpec_sound`),
so the pass is a `ConstraintSystem.addConstraints_correct` — soundness drops the added constraints,
and adding constraints touches no interaction, so side effects and admissibility are unchanged.
Gated on `(1 : ZMod p) ≠ 0` (every prime field; identity on `ZMod 1`); the `255` cases fire only
where the VM's `byteXorSpec` reports byte bound `256` in a large enough field (`256 ≤ p`; `trivial`
and small fields claim nothing). -/

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

/-- The entailed equality from a constant-operand XOR interaction, recognized through the VM-neutral
    `byteXorSpec` (multiplicity 1, decoded op selector `= xorOp`). For decoded operands `(o₁, o₂)`
    and result `r`: `r − o₂` / `r − o₁` for a `0` operand, and — when the field is large enough
    (`256 ≤ p`) and the byte bound is `256` — `r − (255 − o₂)` / `r − (255 − o₁)` for a `255`
    operand; `none` otherwise. -/
def xorEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if bi.multiplicity = Expression.const 1 then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if op = Expression.const spec.xorOp then
          if o1 = Expression.const 0 then some (subE r o2)
          else if o2 = Expression.const 0 then some (subE r o1)
          else if 256 ≤ p ∧ spec.bound = 256 ∧ o1 = Expression.const 255 then
            some (subE r (complE o2))
          else if 256 ≤ p ∧ spec.bound = 256 ∧ o2 = Expression.const 255 then
            some (subE r (complE o1))
          else none
        else none
      | none => none
    else none

/-- Structure of a recognized interaction: a `byteXorSpec`, multiplicity 1, a payload decoding to
    `(xorOp, o₁, o₂, r)`, and one of the four constant-operand cases with the matching constraint. -/
theorem xorEq?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : xorEq? bs facts bi = some c) :
    ∃ (spec : ByteXorSpec p) (o1 o2 r : Expression p),
      facts.byteXorSpec bi.busId = some spec ∧ bi.multiplicity = Expression.const 1 ∧
      spec.decode bi.payload = some (Expression.const spec.xorOp, o1, o2, r) ∧
        ((o1 = Expression.const 0 ∧ c = subE r o2)
          ∨ (o2 = Expression.const 0 ∧ c = subE r o1)
          ∨ (256 ≤ p ∧ spec.bound = 256 ∧ o1 = Expression.const 255 ∧ c = subE r (complE o2))
          ∨ (256 ≤ p ∧ spec.bound = 256 ∧ o2 = Expression.const 255 ∧ c = subE r (complE o1))) := by
  unfold xorEq? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i hmult
      split at h
      · rename_i op o1 o2 r hdec
        split at h
        · rename_i hop
          refine ⟨spec, o1, o2, r, hspec, hmult, hop ▸ hdec, ?_⟩
          split_ifs at h with h1 h2 h3 h4
          · exact Or.inl ⟨h1, by simpa using h.symm⟩
          · exact Or.inr (Or.inl ⟨h2, by simpa using h.symm⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨h3.1, h3.2.1, h3.2.2, by simpa using h.symm⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h4.1, h4.2.1, h4.2.2, by simpa using h.symm⟩))
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- `ZMod.val` is injective (nonzero characteristic). -/
private theorem val_inj {p : ℕ} [NeZero p] (a b : ZMod p) (h : a.val = b.val) : a = b :=
  (ZMod.natCast_rightInverse a).symm.trans ((congrArg _ h).trans (ZMod.natCast_rightInverse b))

/-- `(255 − a).val = 255 − a.val` for a byte `a` in a field with `256 ≤ p` (no wraparound). -/
private theorem sub255_val {p : ℕ} (hp : 256 ≤ p) (a : ZMod p) (ha : a.val < 256) :
    (255 - a).val = 255 - a.val := by
  haveI : NeZero p := ⟨by omega⟩
  have hcast255 : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  have hle : a.val ≤ 255 := Nat.le_of_lt_succ (by omega)
  have ha' : a = ((a.val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse a).symm
  calc (255 - a).val
      = ((255 : ZMod p) - ((a.val : ℕ) : ZMod p)).val := by rw [← ha']
    _ = (((255 - a.val : ℕ) : ZMod p)).val := by rw [Nat.cast_sub hle, hcast255]
    _ = 255 - a.val := ZMod.val_natCast_of_lt (by omega)

/-- Extract every constant-operand XOR equality and add it as an algebraic constraint. -/
def xorEqExtractPass : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    let new := cs.busInteractions.filterMap (xorEq? bs facts)
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
      cs.addConstraints_correct bs new
        (by
          -- entailment: each added equality holds on every satisfying assignment
          intro env _ hsat c hc
          obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
          obtain ⟨spec, o1, o2, r, hspec, hmult, hdec, hcase⟩ := xorEq?_spec bs facts bi c hbc
          have hviol : bs.violatesConstraint (bi.eval env) = false := by
            refine hsat.2 bi hbi ?_
            show (bi.multiplicity.eval env) ≠ 0
            rw [hmult]; simpa using h1ne
          obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
          have hdecEv : spec.decode (bi.eval env).payload
              = some (spec.xorOp, o1.eval env, o2.eval env, r.eval env) := by
            show spec.decode (bi.payload.map (fun e => e.eval env)) = _
            rw [spec.decode_map, hdec]; rfl
          obtain ⟨ho1b, ho2b, hrval⟩ :=
            ((hsound (bi.eval env).payload spec.xorOp (o1.eval env) (o2.eval env) (r.eval env)
              (bi.eval env).multiplicity hdecEv).1 rfl).mp hviol
          haveI := spec.pNeZero
          rcases hcase with ⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨hp, hbnd, hz, rfl⟩ | ⟨hp, hbnd, hz, rfl⟩
          · rw [subE_eval]
            have hzero : (o1.eval env) = 0 := by rw [hz]; rfl
            rw [hzero, ZMod.val_zero] at hrval
            rw [val_inj _ _ (hrval.trans (Nat.zero_xor _)), sub_self]
          · rw [subE_eval]
            have hzero : (o2.eval env) = 0 := by rw [hz]; rfl
            rw [hzero, ZMod.val_zero] at hrval
            rw [val_inj _ _ (hrval.trans (Nat.xor_zero _)), sub_self]
          · rw [subE_eval, complE_eval]
            have hcast255 : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
            have h255v : (255 : ZMod p).val = 255 := by
              rw [← hcast255, ZMod.val_natCast_of_lt (by omega)]
            have ho1 : (o1.eval env) = 255 := by rw [hz]; rfl
            rw [ho1, h255v] at hrval
            have hx : (r.eval env).val = 255 - (o2.eval env).val := by
              rw [hrval, show Nat.xor 255 (o2.eval env).val = Nat.xor (o2.eval env).val 255
                from Nat.xor_comm _ _]
              exact nat_xor_255 _ (hbnd ▸ ho2b)
            rw [val_inj _ _ (hx.trans (sub255_val hp _ (hbnd ▸ ho2b)).symm), sub_self]
          · rw [subE_eval, complE_eval]
            have hcast255 : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
            have h255v : (255 : ZMod p).val = 255 := by
              rw [← hcast255, ZMod.val_natCast_of_lt (by omega)]
            have ho2 : (o2.eval env) = 255 := by rw [hz]; rfl
            rw [ho2, h255v] at hrval
            have hx : (r.eval env).val = 255 - (o1.eval env).val := by
              rw [hrval]; exact nat_xor_255 _ (hbnd ▸ ho1b)
            rw [val_inj _ _ (hx.trans (sub255_val hp _ (hbnd ▸ ho1b)).symm), sub_self])
        (by
          -- no new variables: each equality's variables come from the interaction's payload
          intro c hc zv hz
          obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
          obtain ⟨spec, o1, o2, r, _, _, hdec, hcase⟩ := xorEq?_spec bs facts bi c hbc
          obtain ⟨ho1m, ho2m, hrm⟩ := spec.decode_mem _ _ _ _ _ hdec
          rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
            rcases List.mem_append.1 (by simpa only [subE, complE, Expression.vars,
              List.append_assoc, List.nil_append] using hz) with h_r | h_o
          · exact ConstraintSystem.mem_vars_of_payload hbi hrm h_r
          · exact ConstraintSystem.mem_vars_of_payload hbi ho2m h_o
          · exact ConstraintSystem.mem_vars_of_payload hbi hrm h_r
          · exact ConstraintSystem.mem_vars_of_payload hbi ho1m h_o
          · exact ConstraintSystem.mem_vars_of_payload hbi hrm h_r
          · exact ConstraintSystem.mem_vars_of_payload hbi ho2m h_o
          · exact ConstraintSystem.mem_vars_of_payload hbi hrm h_r
          · exact ConstraintSystem.mem_vars_of_payload hbi ho1m h_o)⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

end XorEqExtract
