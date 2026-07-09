import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.TrivialConstraint
import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Memory send/receive unification

The consumer of the audited memory discipline (`ConstraintSystem.isIntended`,
`ApcOptimizer/Spec.lean`): on a declared last-write-wins bus, when the fragment contains exactly two
active sends to the same address with a *constant* timestamp gap, the discipline's in-window
consumption clause entails that some in-fragment receive carries the earlier send's exact tuple.
The pass identifies that receive by *refuting* every other candidate — a receive whose timestamp
differs from the send's by an expression that provably cannot be zero (a constant plus
fact-bounded negative terms, e.g. `-1 - rdec₀ - 2^17·rdec₁` with the `rdec` limbs range-checked)
— and then **adds the entailed slot-wise equality constraints** `receive[i] = send[i]`. The
existing affine/domain passes consume those equations and eliminate the receive's witness
variables (`writes_aux__prev_data__* = b__*`) and, through the timestamp equation, the
decomposition limbs. Adding entailed constraints keeps this pass's own proof obligation small
(`addConstraints_correct`); all elimination is done by machinery that is already proven.

Everything is checked (`checkMemMatch`): the candidate search is proof-free, and the checked
side conditions are exactly what the entailment proof consumes. The value arithmetic
(`boundedSumMax`) uses `ZMod.val` with explicit no-overflow conditions, so no primality is
needed here — the discipline clauses and the bus facts carry all the strength. -/

variable {p : ℕ}

/-! ## Adding entailed constraints -/

/-- Adding constraints that every **admissible** satisfying assignment already fulfills is
    `PassCorrect`. The entailment `H` may consume the memory discipline (`admissible`), since it
    is only needed for the completeness direction; soundness drops the added constraints, and the
    added constraints touch no bus interaction, so `admissible` and the side effects are unchanged. -/
theorem ConstraintSystem.addConstraints_vars_subset (cs : ConstraintSystem p)
    (new : List (Expression p)) (hnv : ∀ c ∈ new, ∀ z ∈ c.vars, z ∈ cs.vars) :
    ∀ z ∈ ({ cs with algebraicConstraints := cs.algebraicConstraints ++ new }).vars, z ∈ cs.vars := by
  intro z hz
  rw [ConstraintSystem.mem_vars] at hz
  rcases hz with ⟨c, hc, hzc⟩ | ⟨bi, hbi, hzbi⟩
  · rcases List.mem_append.1 hc with h | h
    · exact ConstraintSystem.mem_vars_of_constraint h hzc
    · exact hnv c h z hzc
  · rcases hzbi with hm | ⟨e, he, hze⟩
    · exact ConstraintSystem.mem_vars_of_mult hbi hm
    · exact ConstraintSystem.mem_vars_of_payload hbi he hze

theorem ConstraintSystem.addConstraints_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (new : List (Expression p))
    (H : ∀ env, cs.admissible bs env → cs.satisfies bs env → ∀ c ∈ new, c.eval env = 0)
    (hnv : ∀ c ∈ new, ∀ z ∈ c.vars, z ∈ cs.vars) :
    PassCorrect cs { cs with algebraicConstraints := cs.algebraicConstraints ++ new } [] bs := by
  -- soundness helper: the augmented system's satisfaction always implies the original's
  have hfwd : ∀ env,
      (ConstraintSystem.satisfies
        { cs with algebraicConstraints := cs.algebraicConstraints ++ new } bs env)
      → cs.satisfies bs env := by
    rintro env ⟨hc, hb⟩
    exact ⟨fun c hcm => hc c (List.mem_append_left _ hcm), hb⟩
  refine PassCorrect.ofEnvEq ?_ ?_ (cs.addConstraints_vars_subset new hnv) ?_
  · -- soundness
    intro env hsat
    exact ⟨env, hfwd env hsat, BusState.equiv_refl _⟩
  · -- invariant preservation
    intro hinv env hsat bi hbi
    exact hinv env (hfwd env hsat) bi hbi
  · -- completeness (uses the discipline to discharge the added constraints), witness `env`
    intro env hadm hsat
    obtain ⟨hc, hb⟩ := hsat
    refine ⟨⟨fun c hcm => ?_, hb⟩, hadm, BusState.equiv_refl _⟩
    rcases List.mem_append.1 hcm with h | h
    · exact hc c h
    · exact H env hadm ⟨hc, hb⟩ c h

/-! ## Small verified building blocks -/

/-- `e₂ - e₁` as an expression. -/
def eqExpr (e2 e1 : Expression p) : Expression p := .add e2 (.mul (.const (-1)) e1)

theorem eqExpr_eval (e2 e1 : Expression p) (env : Variable → ZMod p) :
    (eqExpr e2 e1).eval env = e2.eval env - e1.eval env := by
  show e2.eval env + (-1) * e1.eval env = _
  ring

/-- The constant difference `e₂ - e₁`, when the difference normalizes to a constant. -/
def constDiff (e1 e2 : Expression p) : Option (ZMod p) :=
  match linearize (eqExpr e2 e1) with
  | none => none
  | some l => if l.norm.terms = [] then some l.norm.const else none

theorem constDiff_sound (e1 e2 : Expression p) (k : ZMod p) (h : constDiff e1 e2 = some k)
    (env : Variable → ZMod p) : e2.eval env = e1.eval env + k := by
  unfold constDiff at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hl
    split_ifs at h with ht
    simp only [Option.some.injEq] at h
    subst h
    have h1 : (eqExpr e2 e1).eval env = l.eval env := linearize_eval _ l hl env
    rw [eqExpr_eval] at h1
    have h2 : l.norm.eval env = l.eval env := l.norm_eval env
    have h3 : l.norm.eval env = l.norm.const := by
      simp [LinExpr.eval, ht]
    linear_combination h1 - h2 + h3

/-- Both entries of equal evaluated payloads evaluate equally (with a default for
    out-of-range slots). -/
theorem payloadSlot_eval_eq (P Q : List (Expression p)) (env : Variable → ZMod p)
    (h : P.map (fun e => e.eval env) = Q.map (fun e => e.eval env)) (i : Nat) :
    ((P[i]?).getD (.const 0)).eval env = ((Q[i]?).getD (.const 0)).eval env := by
  have hi := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map] at hi
  cases hP : P[i]? <;> cases hQ : Q[i]? <;> rw [hP, hQ] at hi <;> simp_all

/-! ## A proof-carrying bounds map (memoized `findVarBound`)

The refutation certificates below need value bounds for witness variables. Deriving them via
`findVarBound` scans every bus interaction *per query*; the chain passes issue millions of
queries per cycle, so the bounds are precomputed once per pass invocation into a hash map
bundled with its soundness. -/

/-- Fact-derived value bounds for variables, each sound under the bus obligations. -/
structure BoundsMap (p : ℕ) (cs : ConstraintSystem p) (bs : BusSemantics p) where
  map : Std.HashMap Variable Nat
  sound : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
    ∀ x b, map[x]? = some b → (env x).val < b

namespace BoundsMap

variable {cs : ConstraintSystem p} {bs : BusSemantics p}

def empty : BoundsMap p cs bs where
  map := ∅
  sound := by
    intro _ _ x b h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)

/-- Insert a sound bound, keeping the smaller of two bounds for a variable. -/
def insertEntry (T : BoundsMap p cs bs) (x : Variable) (b : Nat)
    (h : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) → (env x).val < b) : BoundsMap p cs bs :=
  let keep : Bool := match T.map[x]? with
    | some b0 => decide (b < b0)
    | none => true
  if keep then
    { map := T.map.insert x b,
      sound := by
        intro env hbus y c hyc
        rw [Std.HashMap.getElem?_insert] at hyc
        by_cases hxy : (x == y) = true
        · rw [if_pos hxy] at hyc
          have hxy' : x = y := by simpa using hxy
          have hbc : b = c := by simpa using hyc
          subst hxy'; subst hbc
          exact h env hbus
        · rw [if_neg hxy] at hyc
          exact T.sound env hbus y c hyc }
  else T

/-- The raw-variable payload entries of an interaction. -/
private def rawVarsOf (bi : BusInteraction (Expression p)) : List Variable :=
  bi.payload.filterMap (fun e => match e with | .var x => some x | _ => none)

/-- Collect bounds from all interactions' fact-bounded raw payload slots. -/
def addAll (facts : BusFacts p bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) → BoundsMap p cs bs → BoundsMap p cs bs
  | [], _, T => T
  | bi :: rest, hmem, T =>
    let hbi := hmem bi (List.mem_cons_self ..)
    let hrest := fun bi' h => hmem bi' (List.mem_cons_of_mem _ h)
    let rec addVars (xs : List Variable) (T : BoundsMap p cs bs) : BoundsMap p cs bs :=
      match xs with
      | [] => T
      | x :: xs =>
        match hr : interactionBound bs facts bi x with
        | some b =>
            addVars xs (T.insertEntry x b
              (fun env hbus => interactionBound_sound bs facts bi x b hr env (hbus bi hbi)))
        | none => addVars xs T
    addAll facts rest hrest (addVars (rawVarsOf bi) T)

/-- Build the bounds map for a system (one pass over the interactions). -/
def build (facts : BusFacts p bs) : BoundsMap p cs bs :=
  addAll facts cs.busInteractions (fun _ h => h) empty

end BoundsMap

/-! ## The bounded-negative-terms refutation

Certifies that an affine form `c + Σ aᵢ·vᵢ` is never zero: each coefficient is treated as
`aᵢ = -posᵢ`, each `vᵢ` has a fact-derived value bound `Bᵢ`, and the maximal possible value of
`Σ posᵢ·vᵢ` stays strictly below `c.val` — so the sum can never equal `c`. -/

/-- Maximal value of `Σ (-aᵢ)·vᵢ` over the bounds, all-or-nothing. -/
def boundedSumMax (B : Std.HashMap Variable Nat) :
    List (Variable × ZMod p) → Option Nat
  | [] => some 0
  | (v, a) :: rest =>
    match B[v]?, boundedSumMax B rest with
    | some bound, some m =>
        if 1 ≤ bound then some ((-a).val * (bound - 1) + m) else none
    | _, _ => none

theorem boundedSum_val (B : Std.HashMap Variable Nat)
    (terms : List (Variable × ZMod p)) (M : Nat)
    (hM : boundedSumMax B terms = some M) (hMp : M < p) (env : Variable → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    ∃ s : ZMod p, (terms.map (fun t => t.2 * env t.1)).sum = -s ∧ s.val ≤ M := by
  induction terms generalizing M with
  | nil =>
      simp only [boundedSumMax, Option.some.injEq] at hM
      exact ⟨0, by simp, by simp [← hM]⟩
  | cons t rest ih =>
    obtain ⟨v, a⟩ := t
    rw [boundedSumMax] at hM
    split at hM
    case _ bound m hBd hm =>
        split_ifs at hM with hb1
        simp only [Option.some.injEq] at hM
        subst hM
        obtain ⟨s', hsum', hs'le⟩ := ih m hm (by omega)
        have hv : (env v).val < bound := hB v bound hBd
        have hhead : ((-a) * env v).val = (-a).val * (env v).val :=
          ZMod.val_mul_of_lt (by
            calc (-a).val * (env v).val ≤ (-a).val * (bound - 1) :=
                  Nat.mul_le_mul_left _ (by omega)
              _ < p := by omega)
        refine ⟨(-a) * env v + s', ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hsum']
          ring
        · have htotal : ((-a) * env v + s').val = ((-a) * env v).val + s'.val :=
            ZMod.val_add_of_lt (by
              rw [hhead]
              calc (-a).val * (env v).val + s'.val
                  ≤ (-a).val * (bound - 1) + m :=
                    Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hs'le
                _ < p := by omega)
          rw [htotal, hhead]
          exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hs'le
    case _ => exact absurd hM (by simp)

/-- The refutation core: a normalized affine form whose bounded-negative sum stays below the
    constant can never evaluate to zero. -/
theorem linNeverZero (B : Std.HashMap Variable Nat) (l : LinExpr p) (M : Nat)
    (hp : 0 < p) (hM : boundedSumMax B l.terms = some M)
    (hlt : M < l.const.val) (env : Variable → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    l.eval env ≠ 0 := by
  intro h0
  haveI : NeZero p := ⟨hp.ne'⟩
  have hMp : M < p := lt_trans hlt (ZMod.val_lt l.const)
  obtain ⟨s, hsum, hsle⟩ := boundedSum_val B l.terms M hM hMp env hB
  have hs : s = l.const := by
    rw [LinExpr.eval, hsum] at h0
    linear_combination -h0
  rw [hs] at hsle
  omega

/-! ## The checked match -/

/-- Constant multiplicity of an interaction. -/
def multConst (bi : BusInteraction (Expression p)) : Option (ZMod p) :=
  bi.multiplicity.constValue?

/-- Do the two sends carry equal constant address entries? -/
def addrConstsEq (shape : MemoryBusShape) (S S' : BusInteraction (Expression p)) : Bool :=
  shape.addressFields.all (fun slot =>
    match S.payload[slot]?, S'.payload[slot]? with
    | some e, some e' =>
      decide (e = e') ||
      (match e.constValue?, e'.constValue? with
       | some c, some c' => c = c'
       | _, _ => false)
    | _, _ => false)

theorem addrConstsEq_sound (shape : MemoryBusShape) (S S' : BusInteraction (Expression p))
    (h : addrConstsEq shape S S' = true) (env : Variable → ZMod p) :
    shape.address (S.eval env) = shape.address (S'.eval env) := by
  unfold MemoryBusShape.address
  apply List.map_congr_left
  intro slot hslot
  have hs := List.all_eq_true.mp h slot hslot
  show (S.payload.map (fun e : Expression p => e.eval env))[slot]?
    = (S'.payload.map (fun e : Expression p => e.eval env))[slot]?
  rw [List.getElem?_map, List.getElem?_map]
  split at hs
  · rename_i e e' hP hQ
    rcases (Bool.or_eq_true _ _).mp hs with hsyn | hs
    · have hee : e = e' := of_decide_eq_true hsyn
      rw [hP, hQ, hee]
    · split at hs
      · rename_i c c' he he'
        have hcc : c = c' := of_decide_eq_true hs
        rw [hP, hQ]
        simp only [Option.map_some]
        rw [e.constValue?_sound c he env, e'.constValue?_sound c' he' env, hcc]
      all_goals exact absurd hs (by simp)
  all_goals exact absurd hs (by simp)

/-- Is `bi` certainly not an active send (constant multiplicity ≠ 1)? -/
def notSend (bi : BusInteraction (Expression p)) : Bool :=
  match multConst bi with
  | some m => decide (m ≠ 1)
  | none => false

/-- The entailed conclusions: slot-wise equality of the receive's and the send's payloads,
    excluding the (constant, already-equal) address slots. -/
def memEqConstraints (shape : MemoryBusShape) (S Rt : BusInteraction (Expression p)) :
    List (Expression p) :=
  ((List.range S.payload.length).filter (fun i => decide (i ∉ shape.addressFields))).map
    (fun i => eqExpr ((Rt.payload[i]?).getD (.const 0)) ((S.payload[i]?).getD (.const 0)))

