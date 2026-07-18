import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.XorEqExtract

set_option autoImplicit false

/-! # Late identity-result substitution

An OR interaction decoding to `(orOp, byte_var, 0, result)` — or the mirror `(orOp, 0, byte_var,
result)` — is `result = byte_var | 0 = byte_var`, so `result` is a redundant copy of the surviving
operand. powdr substitutes it away. Adding the equality `result = byte_var` in the *cleanup* cycle
(so Gauss eliminates it) is correct but regresses SP1's k256 blocks: the substitution changes the
byte-check expressions and the *coda* re-packing (`splitBytePair`/`bytePack`) and `reencode` then
materialise a swarm of fresh byte checks and variables. Doing it **late** — a single batch `substF`
after all packing has run — captures the variable win without any re-packing: the interactions are
only renamed, so bus and constraint counts are unchanged and the `result` variables simply disappear.

Soundness is `ConstraintSystem.substF_correct`: each mapped pair `result ↦ byte_var` is forced by the
interaction's acceptance through `BusFacts.byteBoolSound` (the OR relation with one operand fixed to
`0`, in either slot). No audited surface; `trivial`/OpenVM declare no `orOp`, so the map is empty and
this is a no-op there. Wrapped in `iterateToFixpoint` so operand→operand chains collapse over
iterations. -/

namespace IdentitySubst

variable {p : ℕ}

/-- `ZMod.val` is injective in nonzero characteristic. -/
private theorem val_inj {p : ℕ} [NeZero p] {a b : ZMod p} (h : a.val = b.val) : a = b :=
  (ZMod.natCast_rightInverse a).symm.trans ((congrArg _ h).trans (ZMod.natCast_rightInverse b))

/-- The variable of a bare-variable expression, else `none`. -/
def asVar (e : Expression p) : Option Variable :=
  match e with | .var v => some v | _ => none

theorem asVar_spec (e : Expression p) (v : Variable) (h : asVar e = some v) :
    e = Expression.var v := by
  cases e with
  | var v' => simp only [asVar, Option.some.injEq] at h; subst h; rfl
  | const c => simp [asVar] at h
  | add a b => simp [asVar] at h
  | mul a b => simp [asVar] at h

/-- The operand variable of an OR-identity `(op, o1, o2, r)`: the non-zero operand when the other is
    the constant `0` (so `r = o1 | o2` collapses to that operand). -/
def orIdentityOperand (o1 o2 : Expression p) : Option Variable :=
  if o2 = Expression.const 0 then asVar o1
  else if o1 = Expression.const 0 then asVar o2
  else none

theorem orIdentityOperand_spec (o1 o2 : Expression p) (v : Variable)
    (h : orIdentityOperand o1 o2 = some v) :
    (o1 = Expression.var v ∧ o2 = Expression.const 0)
      ∨ (o2 = Expression.var v ∧ o1 = Expression.const 0) := by
  unfold orIdentityOperand at h
  split_ifs at h with ho2 ho1
  · exact Or.inl ⟨asVar_spec o1 v h, ho2⟩
  · exact Or.inr ⟨asVar_spec o2 v h, ho1⟩

/-- The `(result, operand)` pair of an OR-identity interaction decoding to `(orOp, o1, o2, result)`
    where one operand is `0` and the surviving operand is a bare variable distinct from the result. -/
def identityPairAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Variable × Variable) :=
  match facts.byteXorSpec bi.busId with
  | some spec =>
    match spec.orOp with
    | some oop =>
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        match r with
        | .var rv =>
          if bi.multiplicity = Expression.const 1 ∧ op = Expression.const oop then
            match orIdentityOperand o1 o2 with
            | some o1v => if rv = o1v then none else some (rv, o1v)
            | none => none
          else none
        | _ => none
      | none => none
    | none => none
  | none => none

/-- Structure of a recognised identity pair. -/
theorem identityPairAt_spec {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (rv o1v : Variable)
    (h : identityPairAt facts bi = some (rv, o1v)) :
    ∃ (spec : ByteXorSpec p) (oop : ZMod p) (o1 o2 : Expression p),
      facts.byteXorSpec bi.busId = some spec ∧ bi.multiplicity = Expression.const 1 ∧
      spec.orOp = some oop ∧
      spec.decode bi.payload = some (Expression.const oop, o1, o2, Expression.var rv) ∧
      orIdentityOperand o1 o2 = some o1v := by
  unfold identityPairAt at h
  split at h
  · rename_i spec hspec
    split at h
    · rename_i oop hoop
      split at h
      · rename_i op o1 o2 r hdec
        cases r with
        | var rv' =>
          split_ifs at h with hcond
          obtain ⟨hmc, hop⟩ := hcond
          cases hoo : orIdentityOperand o1 o2 with
          | none => rw [hoo] at h; simp at h
          | some o1v' =>
            rw [hoo] at h
            simp only [] at h
            split_ifs at h with hne
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨spec, oop, o1, o2, hspec, hmc, hoop, hop ▸ hdec, hoo⟩
        | const _ => exact absurd h (by simp)
        | add _ _ => exact absurd h (by simp)
        | mul _ _ => exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A recognised identity pair is forced by acceptance: `env rv = env o1v`. -/
theorem identityPairAt_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (rv o1v : Variable)
    (h : identityPairAt facts bi = some (rv, o1v)) (env : Variable → ZMod p)
    (hviol : bs.violatesConstraint (bi.eval env) = false) : env rv = env o1v := by
  obtain ⟨spec, oop, o1, o2, hspec, hmc, hoop, hdec, hoo⟩ := identityPairAt_spec facts bi rv o1v h
  have hdecEv : spec.decode (bi.eval env).payload
      = some (oop, o1.eval env, o2.eval env, env rv) := by
    show spec.decode (bi.payload.map (fun e => e.eval env)) = _
    rw [spec.decode_map, hdec]; rfl
  obtain ⟨horc, _⟩ := facts.byteBoolSound bi.busId spec hspec (bi.eval env).payload
    oop (o1.eval env) (o2.eval env) (env rv) (bi.eval env).multiplicity hdecEv
  haveI := spec.pNeZero
  obtain ⟨_, _, hrval⟩ := (horc oop hoop rfl).mp hviol
  rcases orIdentityOperand_spec o1 o2 o1v hoo with ⟨ho1, ho2⟩ | ⟨ho2, ho1⟩
  · have ho1e : o1.eval env = env o1v := by rw [ho1]; rfl
    have ho2e : o2.eval env = 0 := by rw [ho2]; rfl
    rw [ho1e, ho2e, ZMod.val_zero] at hrval
    exact val_inj (by rw [hrval]; simp)
  · have ho1e : o1.eval env = 0 := by rw [ho1]; rfl
    have ho2e : o2.eval env = env o1v := by rw [ho2]; rfl
    rw [ho1e, ho2e, ZMod.val_zero] at hrval
    exact val_inj (by rw [hrval]; simp)

/-- Candidate operands for a result `y`: the operand of every recognised identity whose result is `y`. -/
def identityCandidates {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (y : Variable) : List (Expression p) :=
  cs.busInteractions.filterMap (fun bi =>
    match identityPairAt facts bi with
    | some (rv, o1v) => if rv = y then some (Expression.var o1v) else none
    | none => none)

/-- The identity map: `result ↦ operand` for every recognised OR identity (first per key). -/
def identityF {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    Variable → Option (Expression p) :=
  fun y => (identityCandidates facts cs y).head?

theorem identityF_mem {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (y : Variable) (t : Expression p) (h : identityF facts cs y = some t) :
    ∃ (o1v : Variable) (bi : BusInteraction (Expression p)), t = Expression.var o1v ∧
      bi ∈ cs.busInteractions ∧ identityPairAt facts bi = some (y, o1v) := by
  unfold identityF at h
  have hmem : t ∈ identityCandidates facts cs y := by
    cases hc : identityCandidates facts cs y with
    | nil => rw [hc] at h; simp at h
    | cons a l => rw [hc] at h; simp only [List.head?_cons, Option.some.injEq] at h; subst h; simp
  obtain ⟨bi, hbi, hmap⟩ := List.mem_filterMap.1 hmem
  cases hp : identityPairAt facts bi with
  | none => rw [hp] at hmap; simp at hmap
  | some pr =>
    obtain ⟨rv, o1v⟩ := pr
    rw [hp] at hmap
    dsimp only at hmap
    split_ifs at hmap with hrv
    simp only [Option.some.injEq] at hmap
    subst hmap; subst hrv
    exact ⟨o1v, bi, rfl, hbi, hp⟩

/-- The pass: batch-substitute every OR-identity result by its operand. -/
def identitySubstStep : VerifiedPassW p := fun cs bs facts =>
  if h1ne : (1 : ZMod p) ≠ 0 then
    ⟨cs.substF (identityF facts cs), [],
      cs.substF_correct (identityF facts cs) bs
        (by
          intro env hsat y t hf
          obtain ⟨o1v, bi, rfl, hbi, hpair⟩ := identityF_mem facts cs y t hf
          have hviol : bs.violatesConstraint (bi.eval env) = false := by
            refine hsat.2 bi hbi ?_
            obtain ⟨_, _, _, _, _, hmc, _, _, _⟩ := identityPairAt_spec facts bi y o1v hpair
            show (bi.multiplicity.eval env) ≠ 0
            rw [hmc]; simpa using h1ne
          show env y = (Expression.var o1v).eval env
          exact identityPairAt_sound facts bi y o1v hpair env hviol)
        (by
          intro y t hf z hz
          obtain ⟨o1v, bi, rfl, hbi, hpair⟩ := identityF_mem facts cs y t hf
          simp only [Expression.vars, List.mem_singleton] at hz
          rw [hz]
          obtain ⟨spec, oop, o1, o2, hspec, _, _, hdec, hoo⟩ :=
            identityPairAt_spec facts bi y o1v hpair
          obtain ⟨ho1m, ho2m, _⟩ := spec.decode_mem _ _ _ _ _ hdec
          rcases orIdentityOperand_spec o1 o2 o1v hoo with ⟨ho1, _⟩ | ⟨ho2, _⟩
          · exact ConstraintSystem.mem_vars_of_payload hbi (ho1 ▸ ho1m) (by simp [Expression.vars])
          · exact ConstraintSystem.mem_vars_of_payload hbi (ho2 ▸ ho2m) (by simp [Expression.vars]))⟩
  else
    ⟨cs, [], PassCorrect.refl cs bs⟩

/-- Run the identity substitution to a fixpoint so operand→operand chains collapse. -/
def identitySubstPass : VerifiedPassW p := iterateToFixpoint identitySubstStep

end IdentitySubst
