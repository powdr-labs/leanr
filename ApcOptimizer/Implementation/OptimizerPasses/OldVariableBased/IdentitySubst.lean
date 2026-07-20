import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.XorEqExtract

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

/-- All recognised `(result, operand)` identity pairs in the system, computed once. Hoisting this out
    of the per-variable lookup below keeps `substF` — which calls the map once per variable
    occurrence — from re-`filterMap`ping (and re-decoding) every bus interaction on each visit; the
    lookup becomes a linear scan of this (small) list instead. -/
def identityPairs {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (Variable × Variable) :=
  cs.busInteractions.filterMap (identityPairAt facts)

/-- First-wins key→value map of a pair list: the value stored for `y` is the first pair keyed `y`,
    exactly the `filterMap … |>.head?` semantics, at one hash lookup per query. -/
def firstWins : List (Variable × Variable) → Std.HashMap Variable Variable →
    Std.HashMap Variable Variable
  | [], m => m
  | pr :: rest, m => firstWins rest (if m.contains pr.1 then m else m.insert pr.1 pr.2)

theorem firstWins_mem : ∀ (pairs : List (Variable × Variable))
    (m : Std.HashMap Variable Variable) (y v : Variable),
    (firstWins pairs m)[y]? = some v → m[y]? = some v ∨ (y, v) ∈ pairs := by
  intro pairs
  induction pairs with
  | nil => intro m y v h; exact Or.inl h
  | cons pr rest ih =>
    intro m y v h
    rcases ih _ y v h with hm | hr
    · by_cases hc : m.contains pr.1
      · rw [if_pos hc] at hm
        exact Or.inl hm
      · rw [if_neg hc, Std.HashMap.getElem?_insert] at hm
        by_cases hy : (pr.1 == y) = true
        · rw [if_pos hy] at hm
          simp only [Option.some.injEq] at hm
          have h1 : pr.1 = y := by simpa using hy
          exact Or.inr (List.mem_cons.2 (Or.inl (by rw [← h1, ← hm])))
        · rw [if_neg hy] at hm
          exact Or.inl hm
    · exact Or.inr (List.mem_cons_of_mem _ hr)

/-- Resolve a mapped variable through operand→operand chains, fuel-bounded (a cycle burns fuel
    and stops harmlessly — the fixpoint wrapper then discards the no-op, exactly as it discarded
    the old one-link-per-iteration swaps). Compressing the chains lets one `substF` collapse a
    whole chain, so the fixpoint converges in ~2 iterations instead of one per link. -/
def resolveGo (m : Std.HashMap Variable Variable) : Nat → Variable → Variable
  | 0, v => v
  | fuel + 1, v =>
    match m[v]? with
    | some w => resolveGo m fuel w
    | none => v

theorem resolveGo_sound (m : Std.HashMap Variable Variable) (env : Variable → ZMod p)
    (hm : ∀ a b, m[a]? = some b → env a = env b) :
    ∀ (fuel : Nat) (v : Variable), env (resolveGo m fuel v) = env v := by
  intro fuel
  induction fuel with
  | zero => intro v; rfl
  | succ fuel ih =>
    intro v
    rw [resolveGo]
    cases hv : m[v]? with
    | some w => rw [ih w, hm v w hv]
    | none => rfl

theorem resolveGo_prop (m : Std.HashMap Variable Variable) (P : Variable → Prop)
    (hm : ∀ (a b : Variable), m[a]? = some b → P b) :
    ∀ (fuel : Nat) (v : Variable), P v → P (resolveGo m fuel v) := by
  intro fuel
  induction fuel with
  | zero => intro v hv; exact hv
  | succ fuel ih =>
    intro v hv
    rw [resolveGo]
    cases hmv : m[v]? with
    | some w => exact ih w (hm v w hmv)
    | none => exact hv

/-- The mapped pairs, with the operand side path-compressed. -/
def identityMap {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    Std.HashMap Variable Variable :=
  firstWins (identityPairs facts cs) ∅

/-- The identity substitution over a prebuilt map: `result ↦ operand` (first per key), the
    operand resolved through chains (`resolveGo`). The map is a **parameter**, computed once by
    the pass body — a def-local `let … ; fun y => …` is re-evaluated per query by arity
    expansion, which made the old form rebuild the pair list per variable occurrence (measured
    2.8 s on apc_030 for a 4-pair map). -/
def identityFm (m : Std.HashMap Variable Variable) (fuel : Nat) :
    Variable → Option (Expression p) :=
  fun y => m[y]?.map (fun w => Expression.var (resolveGo m fuel w))

/-- Every stored pair comes from a recognised OR identity of the system. -/
theorem identityMap_mem {bs : BusSemantics p} (facts : BusFacts p bs) (cs : ConstraintSystem p)
    (y v : Variable) (h : (identityMap facts cs)[y]? = some v) :
    ∃ (bi : BusInteraction (Expression p)),
      bi ∈ cs.busInteractions ∧ identityPairAt facts bi = some (y, v) := by
  rcases firstWins_mem _ _ y v h with hm | hpair
  · rw [Std.HashMap.getElem?_empty] at hm
    exact absurd hm (by simp)
  · obtain ⟨bi, hbi, hpairAt⟩ := List.mem_filterMap.1 hpair
    exact ⟨bi, hbi, hpairAt⟩

/-- A recognised pair's operand is a variable of the system (it sits in the interaction's
    payload). -/
theorem identityMap_operand_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (cs : ConstraintSystem p) (y v : Variable) (h : (identityMap facts cs)[y]? = some v) :
    v ∈ cs.vars := by
  obtain ⟨bi, hbi, hpair⟩ := identityMap_mem facts cs y v h
  obtain ⟨spec, oop, o1, o2, hspec, _, _, hdec, hoo⟩ := identityPairAt_spec facts bi y v hpair
  obtain ⟨ho1m, ho2m, _⟩ := spec.decode_mem _ _ _ _ _ hdec
  rcases orIdentityOperand_spec o1 o2 v hoo with ⟨ho1, _⟩ | ⟨ho2, _⟩
  · exact ConstraintSystem.mem_vars_of_payload hbi (ho1 ▸ ho1m) (by simp [Expression.vars])
  · exact ConstraintSystem.mem_vars_of_payload hbi (ho2 ▸ ho2m) (by simp [Expression.vars])

/-- The pass: batch-substitute every OR-identity result by its operand. When the system has no
    recognised identities — e.g. any OpenVM circuit, whose bitwise bus declares no `orOp` — the `[]`
    branch returns it unchanged, skipping the whole-system `substF` traversal (which would be a no-op
    but still walks every expression). This keeps the pass ~free wherever it finds nothing to do. -/
def identitySubstStep : VerifiedPassW p := fun cs bs facts =>
  match identityPairs facts cs with
  | [] => ⟨cs, [], PassCorrect.refl cs bs⟩
  | _ :: _ =>
    if h1ne : (1 : ZMod p) ≠ 0 then
      -- Bind the map (and its fuel) here, fully applied — see `identityFm` on why the map must
      -- not live behind the substitution closure's missing argument.
      let m := identityMap facts cs
      ⟨cs.substF (identityFm m m.size), [],
        cs.substF_correct (identityFm m m.size) bs
          (by
            intro env hsat y t hf
            -- each stored pair is forced by its interaction's acceptance …
            have hm : ∀ a b, (identityMap facts cs)[a]? = some b → env a = env b := by
              intro a b hab
              obtain ⟨bi, hbi, hpair⟩ := identityMap_mem facts cs a b hab
              have hviol : bs.violatesConstraint (bi.eval env) = false := by
                refine hsat.2 bi hbi ?_
                obtain ⟨_, _, _, _, _, hmc, _, _, _⟩ := identityPairAt_spec facts bi a b hpair
                show (bi.multiplicity.eval env) ≠ 0
                rw [hmc]; simpa using h1ne
              exact identityPairAt_sound facts bi a b hpair env hviol
            -- … and the resolved target composes those equalities along the chain
            simp only [identityFm, Option.map_eq_some_iff] at hf
            obtain ⟨w, hw, rfl⟩ := hf
            show env y = env (resolveGo (identityMap facts cs) (identityMap facts cs).size w)
            rw [resolveGo_sound (identityMap facts cs) env hm]
            exact hm y w hw)
          (by
            intro y t hf z hz
            simp only [identityFm, Option.map_eq_some_iff] at hf
            obtain ⟨w, hw, rfl⟩ := hf
            simp only [Expression.vars, List.mem_singleton] at hz
            rw [hz]
            exact resolveGo_prop (identityMap facts cs) (· ∈ cs.vars)
              (fun a b hab => identityMap_operand_mem facts cs a b hab) _ w
              (identityMap_operand_mem facts cs y w hw))⟩
    else
      ⟨cs, [], PassCorrect.refl cs bs⟩

/-- Run the identity substitution to a fixpoint so operand→operand chains collapse. -/
def identitySubstPass : VerifiedPassW p := iterateToFixpoint identitySubstStep

end IdentitySubst
