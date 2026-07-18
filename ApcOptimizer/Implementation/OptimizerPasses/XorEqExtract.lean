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

/-- The entailment of a single recognized XOR equality, factored out of the pass so the pass can
    combine it with the OR/AND extraction below. -/
theorem xorEq?_eval (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (bi : BusInteraction (Expression p)) (c : Expression p) (env : Variable → ZMod p)
    (h1ne : (1 : ZMod p) ≠ 0) (h : xorEq? bs facts bi = some c) (hbi : bi ∈ cs.busInteractions)
    (hsat : cs.satisfies bs env) : c.eval env = 0 := by
  obtain ⟨spec, o1, o2, r, hspec, hmult, hdec, hcase⟩ := xorEq?_spec bs facts bi c h
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
    rw [val_inj _ _ (hx.trans (sub255_val hp _ (hbnd ▸ ho1b)).symm), sub_self]

/-- The variables of a recognized XOR equality come from the interaction's payload. -/
theorem xorEq?_vars (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : xorEq? bs facts bi = some c)
    (hbi : bi ∈ cs.busInteractions) (zv : Variable) (hz : zv ∈ c.vars) : zv ∈ cs.vars := by
  obtain ⟨spec, o1, o2, r, _, _, hdec, hcase⟩ := xorEq?_spec bs facts bi c h
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
  · exact ConstraintSystem.mem_vars_of_payload hbi ho1m h_o

/-! ## OR / AND constant-operand extraction (generalizing the XOR case above)

The same closure holds for the two other affine-in-one-operand bitwise ops a byte bus may carry
(declared as `spec.orOp` / `spec.andOp`, see `BusFacts.byteBoolSound`): with a **zero** operand,
`x | 0 = x` pins the result to the other operand (`z = y` / `z = x`), and `x & 0 = 0` pins it to
the constant `0` (`z = 0`). SP1's byte bus has both ops (`orOp = 1`, `andOp = 0`); OpenVM's declares
neither, so this is a no-op there.

**Constant target only.** For OR the pin `z = y` is emitted only when the surviving operand `y` is
a *constant* — so Gauss substitutes `z` by a constant, never by a wider expression. (Emitting
`z = k·(u − v)` for the scaled dead-byte operands of `lbu; xor; sb` would *expand* the clean byte
`z` into a two-term affine and block memory cancellation — a regression. Those operands are driven
to the constant `0` by `scaledZero` first, and *then* recognized here.) AND's target is always the
constant `0`, so it is unconditional. -/

/-- A substitution target Gauss can inline without disturbing anything: a *constant*. Pinning
    `result` to a wider expression — even a bare variable — turned out to displace the intermediate
    byte apc's memory cancellation was keying on and to block downstream telescoping (measured
    regression on the SP1 k256 blocks), so only constant targets are taken. The scaled dead-byte
    operands `k·(u − v)` reach a constant `0` here only after `scaledZero` forces `u = v`. -/
def simpleTarget (e : Expression p) : Bool := e.constValue?.isSome

/-- Does `op` match the (optional) op-selector value `o`? -/
def opIs (o : Option (ZMod p)) (op : Expression p) : Bool :=
  match o with
  | some v => decide (op = Expression.const v)
  | none => false

theorem opIs_iff {o : Option (ZMod p)} {op : Expression p} :
    opIs o op = true ↔ ∃ v, o = some v ∧ op = Expression.const v := by
  unfold opIs
  cases o with
  | none => simp
  | some v => simp

/-- The entailed equality from a constant-**zero**-operand OR/AND interaction, emitted only when the
    result is pinned to a *constant*: `r − o₂` / `r − o₁` for OR with a constant surviving operand,
    and `r` (i.e. `r = 0`) for AND. -/
def boolEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if bi.multiplicity = Expression.const 1 then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if opIs spec.orOp op then
          if o1 = Expression.const 0 then
            (if simpleTarget o2 then some (subE r o2) else none)
          else if o2 = Expression.const 0 then
            (if simpleTarget o1 then some (subE r o1) else none)
          else none
        else if opIs spec.andOp op then
          if o1 = Expression.const 0 ∨ o2 = Expression.const 0 then some r
          else none
        else none
      | none => none
    else none

/-- Structure of a recognized OR/AND interaction. -/
theorem boolEq?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : boolEq? bs facts bi = some c) :
    ∃ (spec : ByteXorSpec p) (op o1 o2 r : Expression p),
      facts.byteXorSpec bi.busId = some spec ∧ bi.multiplicity = Expression.const 1 ∧
      spec.decode bi.payload = some (op, o1, o2, r) ∧
        ((∃ oop, spec.orOp = some oop ∧ op = Expression.const oop ∧
            ((o1 = Expression.const 0 ∧ c = subE r o2)
              ∨ (o2 = Expression.const 0 ∧ c = subE r o1)))
          ∨ (∃ aop, spec.andOp = some aop ∧ op = Expression.const aop ∧
              ((o1 = Expression.const 0 ∨ o2 = Expression.const 0) ∧ c = r))) := by
  unfold boolEq? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i hmult
      split at h
      · rename_i op o1 o2 r hdec
        refine ⟨spec, op, o1, o2, r, hspec, hmult, hdec, ?_⟩
        split at h
        · rename_i hor
          obtain ⟨oop, hoeq, hopeq⟩ := opIs_iff.1 hor
          refine Or.inl ⟨oop, hoeq, hopeq, ?_⟩
          split_ifs at h with h1 h2 h3 h4
          · exact Or.inl ⟨h1, by simpa using h.symm⟩
          · exact Or.inr ⟨h3, by simpa using h.symm⟩
        · split at h
          · rename_i hand
            obtain ⟨aop, haeq, hopeq⟩ := opIs_iff.1 hand
            refine Or.inr ⟨aop, haeq, hopeq, ?_⟩
            split_ifs at h with h1
            · exact ⟨h1, by simpa using h.symm⟩
          · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- The entailment of a single recognized OR/AND equality (through `BusFacts.byteBoolSound`). -/
theorem boolEq?_eval (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (bi : BusInteraction (Expression p)) (c : Expression p) (env : Variable → ZMod p)
    (h1ne : (1 : ZMod p) ≠ 0) (h : boolEq? bs facts bi = some c) (hbi : bi ∈ cs.busInteractions)
    (hsat : cs.satisfies bs env) : c.eval env = 0 := by
  obtain ⟨spec, op, o1, o2, r, hspec, hmult, hdec, hcase⟩ := boolEq?_spec bs facts bi c h
  have hviol : bs.violatesConstraint (bi.eval env) = false := by
    refine hsat.2 bi hbi ?_
    show (bi.multiplicity.eval env) ≠ 0
    rw [hmult]; simpa using h1ne
  have hdecEv : spec.decode (bi.eval env).payload
      = some (op.eval env, o1.eval env, o2.eval env, r.eval env) := by
    show spec.decode (bi.payload.map (fun e => e.eval env)) = _
    rw [spec.decode_map, hdec]; rfl
  obtain ⟨horc, handc⟩ := facts.byteBoolSound bi.busId spec hspec (bi.eval env).payload
    (op.eval env) (o1.eval env) (o2.eval env) (r.eval env) (bi.eval env).multiplicity hdecEv
  haveI := spec.pNeZero
  rcases hcase with ⟨oop, hspecOr, hopeq, hcc⟩ | ⟨aop, hspecAnd, hopeq, hcc⟩
  · have hopev : op.eval env = oop := by rw [hopeq]; rfl
    obtain ⟨_, _, hrval⟩ := (horc oop hspecOr hopev).mp hviol
    rcases hcc with ⟨hz, rfl⟩ | ⟨hz, rfl⟩
    · rw [subE_eval]
      have ho1z : (o1.eval env) = 0 := by rw [hz]; rfl
      rw [ho1z, ZMod.val_zero] at hrval
      have heq : (r.eval env).val = (o2.eval env).val := by rw [hrval]; simp
      rw [val_inj _ _ heq, sub_self]
    · rw [subE_eval]
      have ho2z : (o2.eval env) = 0 := by rw [hz]; rfl
      rw [ho2z, ZMod.val_zero] at hrval
      have heq : (r.eval env).val = (o1.eval env).val := by rw [hrval]; simp
      rw [val_inj _ _ heq, sub_self]
  · have hopev : op.eval env = aop := by rw [hopeq]; rfl
    obtain ⟨_, _, hrval⟩ := (handc aop hspecAnd hopev).mp hviol
    obtain ⟨hz, rfl⟩ := hcc
    refine (ZMod.val_eq_zero _).mp ?_
    rcases hz with hz | hz
    · have : (o1.eval env) = 0 := by rw [hz]; rfl
      rw [this, ZMod.val_zero] at hrval; rw [hrval]; simp
    · have : (o2.eval env) = 0 := by rw [hz]; rfl
      rw [this, ZMod.val_zero] at hrval; rw [hrval]; simp

/-- The variables of a recognized OR/AND equality come from the interaction's payload. -/
theorem boolEq?_vars (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (bi : BusInteraction (Expression p)) (c : Expression p) (h : boolEq? bs facts bi = some c)
    (hbi : bi ∈ cs.busInteractions) (zv : Variable) (hz : zv ∈ c.vars) : zv ∈ cs.vars := by
  obtain ⟨spec, op, o1, o2, r, _, _, hdec, hcase⟩ := boolEq?_spec bs facts bi c h
  obtain ⟨ho1m, ho2m, hrm⟩ := spec.decode_mem _ _ _ _ _ hdec
  rcases hcase with ⟨oop, _, _, hcc⟩ | ⟨aop, _, _, hcc⟩
  · rcases hcc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases List.mem_append.1 (by simpa only [subE, Expression.vars,
        List.append_assoc, List.nil_append] using hz) with h_r | h_o
    · exact ConstraintSystem.mem_vars_of_payload hbi hrm h_r
    · exact ConstraintSystem.mem_vars_of_payload hbi ho2m h_o
    · exact ConstraintSystem.mem_vars_of_payload hbi hrm h_r
    · exact ConstraintSystem.mem_vars_of_payload hbi ho1m h_o
  · obtain ⟨_, rfl⟩ := hcc
    exact ConstraintSystem.mem_vars_of_payload hbi hrm hz

/-- Extract every constant-operand XOR/OR/AND equality and add it as an algebraic constraint. The
    XOR half (`xorEq?`) and the OR/AND half (`boolEq?`) are independent recognizers; their outputs
    are concatenated and each is entailed by its interaction's acceptance. -/
def xorEqExtractPass : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    let new := cs.busInteractions.filterMap (xorEq? bs facts)
      ++ cs.busInteractions.filterMap (boolEq? bs facts)
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
      cs.addConstraints_correct bs new
        (by
          -- entailment: each added equality holds on every satisfying assignment
          intro env _ hsat c hc
          rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
            exact xorEq?_eval bs facts cs bi c env h1ne hbc hbi hsat
          · obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
            exact boolEq?_eval bs facts cs bi c env h1ne hbc hbi hsat)
        (by
          -- no new variables: each equality's variables come from the interaction's payload
          intro c hc zv hz
          rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
            exact xorEq?_vars bs facts cs bi c hbc hbi zv hz
          · obtain ⟨bi, hbi, hbc⟩ := List.mem_filterMap.1 hc
            exact boolEq?_vars bs facts cs bi c hbc hbi zv hz)⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

end XorEqExtract
