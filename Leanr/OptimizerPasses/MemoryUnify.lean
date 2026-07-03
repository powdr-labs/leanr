import Leanr.OptimizerPasses.DomainProp
import Leanr.OptimizerPasses.TrivialConstraint

set_option autoImplicit false

/-! # Memory send/receive unification

The consumer of the audited memory discipline (`ConstraintSystem.memoryDiscipline`,
`Leanr/Spec.lean`): on a declared last-write-wins bus, when the fragment contains exactly two
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

/-- Adding constraints that every satisfying assignment already fulfills is `PassCorrect`. -/
theorem ConstraintSystem.addConstraints_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (new : List (Expression p))
    (H : ∀ env, cs.satisfies bs env → ∀ c ∈ new, c.eval env = 0) :
    PassCorrect cs { cs with algebraicConstraints := cs.algebraicConstraints ++ new } bs := by
  have hiff : ∀ env,
      (ConstraintSystem.satisfies
        { cs with algebraicConstraints := cs.algebraicConstraints ++ new } bs env)
      ↔ cs.satisfies bs env := by
    intro env
    constructor
    · rintro ⟨hc, hb, hd⟩
      exact ⟨fun c hcm => hc c (List.mem_append_left _ hcm), hb, hd⟩
    · intro hsat
      obtain ⟨hc, hb, hd⟩ := hsat
      refine ⟨fun c hcm => ?_, hb, hd⟩
      rcases List.mem_append.1 hcm with h | h
      · exact hc c h
      · exact H env ⟨hc, hb, hd⟩ c h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, BusState.equiv_refl _⟩
  · intro env hsat
    exact ⟨env, (hiff env).2 hsat, BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    exact hinv env ((hiff env).1 hsat) bi hbi

/-! ## Small verified building blocks -/

/-- The timestamp expression of an interaction, per a memory-bus shape. -/
def tsExprOf (shape : MemoryBusShape) (bi : BusInteraction (Expression p)) : Expression p :=
  (bi.payload[shape.tsField]?).getD (.const 0)

theorem tsVal_eval (shape : MemoryBusShape) (bi : BusInteraction (Expression p))
    (env : String → ZMod p) :
    shape.tsVal (bi.eval env) = ((tsExprOf shape bi).eval env).val := by
  unfold MemoryBusShape.tsVal tsExprOf
  show (((bi.payload.map (fun e : Expression p => e.eval env))[shape.tsField]?).getD 0).val = _
  rw [List.getElem?_map]
  cases bi.payload[shape.tsField]? with
  | none => rfl
  | some e => rfl

/-- `e₂ - e₁` as an expression. -/
def eqExpr (e2 e1 : Expression p) : Expression p := .add e2 (.mul (.const (-1)) e1)

theorem eqExpr_eval (e2 e1 : Expression p) (env : String → ZMod p) :
    (eqExpr e2 e1).eval env = e2.eval env - e1.eval env := by
  show e2.eval env + (-1) * e1.eval env = _
  ring

/-- The constant difference `e₂ - e₁`, when the difference normalizes to a constant. -/
def constDiff (e1 e2 : Expression p) : Option (ZMod p) :=
  match linearize (eqExpr e2 e1) with
  | none => none
  | some l => if l.norm.terms = [] then some l.norm.const else none

theorem constDiff_sound (e1 e2 : Expression p) (k : ZMod p) (h : constDiff e1 e2 = some k)
    (env : String → ZMod p) : e2.eval env = e1.eval env + k := by
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
theorem payloadSlot_eval_eq (P Q : List (Expression p)) (env : String → ZMod p)
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
  map : Std.HashMap String Nat
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
def insertEntry (T : BoundsMap p cs bs) (x : String) (b : Nat)
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
private def rawVarsOf (bi : BusInteraction (Expression p)) : List String :=
  bi.payload.filterMap (fun e => match e with | .var x => some x | _ => none)

/-- Collect bounds from all interactions' fact-bounded raw payload slots. -/
def addAll (facts : BusFacts p bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) → BoundsMap p cs bs → BoundsMap p cs bs
  | [], _, T => T
  | bi :: rest, hmem, T =>
    let hbi := hmem bi (List.mem_cons_self ..)
    let hrest := fun bi' h => hmem bi' (List.mem_cons_of_mem _ h)
    let rec addVars (xs : List String) (T : BoundsMap p cs bs) : BoundsMap p cs bs :=
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
def boundedSumMax (B : Std.HashMap String Nat) :
    List (String × ZMod p) → Option Nat
  | [] => some 0
  | (v, a) :: rest =>
    match B[v]?, boundedSumMax B rest with
    | some bound, some m =>
        if 1 ≤ bound then some ((-a).val * (bound - 1) + m) else none
    | _, _ => none

theorem boundedSum_val (B : Std.HashMap String Nat)
    (terms : List (String × ZMod p)) (M : Nat)
    (hM : boundedSumMax B terms = some M) (hMp : M < p) (env : String → ZMod p)
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
theorem linNeverZero (B : Std.HashMap String Nat) (l : LinExpr p) (M : Nat)
    (hp : 0 < p) (hM : boundedSumMax B l.terms = some M)
    (hlt : M < l.const.val) (env : String → ZMod p)
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

/-- Refute (decidably) that a receive's timestamp can equal the send's. -/
def tsRefuted (B : Std.HashMap String Nat) (shape : MemoryBusShape)
    (S r : BusInteraction (Expression p)) : Bool :=
  match linearize (eqExpr (tsExprOf shape r) (tsExprOf shape S)) with
  | none => false
  | some l =>
    match boundedSumMax B l.norm.terms with
    | some M => decide (M < l.norm.const.val)
    | none => false

theorem tsRefuted_sound (B : Std.HashMap String Nat) (shape : MemoryBusShape)
    (S r : BusInteraction (Expression p)) (hp : 0 < p)
    (h : tsRefuted B shape S r = true) (env : String → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    (tsExprOf shape r).eval env ≠ (tsExprOf shape S).eval env := by
  intro heq
  unfold tsRefuted at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hl
    split at h
    · rename_i M hM
      have hzero : l.norm.eval env = 0 := by
        rw [l.norm_eval, ← linearize_eval _ l hl, eqExpr_eval, heq]
        ring
      exact linNeverZero B l.norm M hp hM (of_decide_eq_true h) env hB hzero
    · exact absurd h (by simp)

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
    (h : addrConstsEq shape S S' = true) (env : String → ZMod p) :
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

/-- The timestamp-gap certificate between the two sends. -/
def sendGapOk (shape : MemoryBusShape) (S S' : BusInteraction (Expression p)) : Bool :=
  match constDiff (tsExprOf shape S) (tsExprOf shape S') with
  | some k => decide (0 < k.val) && decide (shape.tsBound + k.val ≤ p)
  | none => false

/-- Is `bi` certainly not an active send (constant multiplicity ≠ 1)? -/
def notSend (bi : BusInteraction (Expression p)) : Bool :=
  match multConst bi with
  | some m => decide (m ≠ 1)
  | none => false

/-- Is `bi` certainly not the matching receive: constant multiplicity ≠ -1, or its timestamp
    provably differs from the send's? -/
def notMatch (B : Std.HashMap String Nat) (shape : MemoryBusShape)
    (S bi : BusInteraction (Expression p)) : Bool :=
  (match multConst bi with
   | some m => decide (m ≠ -1)
   | none => false) || tsRefuted B shape S bi

/-- All checked side conditions for a memory match `(S, S', Rt)` on `busId`:
    `S`/`S'` the only two active sends (constant multiplicities), same constant address,
    constant timestamp gap within range; every other interaction is provably not the matching
    receive, so `Rt` is. -/
def checkMemMatch (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (busId : Nat) (shape : MemoryBusShape) (S S' Rt : BusInteraction (Expression p)) : Bool :=
  let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
  decide ((1 : ZMod p) ≠ 0) && decide ((2 : ZMod p) ≠ 0) &&
  decide (1 ≤ shape.tsBound) &&
  decide (S ∈ L) && decide (S' ∈ L) && decide (Rt ∈ L) &&
  decide (multConst S = some 1) && decide (multConst S' = some 1) &&
  decide (multConst Rt = some (-1)) &&
  addrConstsEq shape S S' &&
  sendGapOk shape S S' &&
  L.all (fun bi => decide (bi = S) || decide (bi = S') || notSend bi) &&
  L.all (fun bi => decide (bi = Rt) || notMatch B shape S bi)

/-- The entailed conclusions: slot-wise equality of the receive's and the send's payloads,
    excluding the (constant, already-equal) address slots. -/
def memEqConstraints (shape : MemoryBusShape) (S Rt : BusInteraction (Expression p)) :
    List (Expression p) :=
  ((List.range S.payload.length).filter (fun i => decide (i ∉ shape.addressFields))).map
    (fun i => eqExpr ((Rt.payload[i]?).getD (.const 0)) ((S.payload[i]?).getD (.const 0)))

theorem checkMemMatch_sound (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (hB : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, B[x]? = some b → (env x).val < b)
    (busId : Nat) (shape : MemoryBusShape)
    (S S' Rt : BusInteraction (Expression p)) (hdecl : bs.memoryBus busId = some shape)
    (hchk : checkMemMatch cs bs B busId shape S S' Rt = true)
    (env : String → ZMod p) (hsat : cs.satisfies bs env) :
    ∀ c ∈ memEqConstraints shape S Rt, c.eval env = 0 := by
  -- unpack the certificate
  unfold checkMemMatch at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1ne, h2ne⟩, htsb⟩, hSmem⟩, hS'mem⟩, hRtmem⟩, hSm⟩, hS'm⟩, hRtm⟩,
    haddrc⟩, hgap⟩, hsends⟩, hmatch⟩ := hchk
  have h1ne := of_decide_eq_true h1ne
  have h2ne := of_decide_eq_true h2ne
  have htsb := of_decide_eq_true htsb
  have hSmem := of_decide_eq_true hSmem
  have hS'mem := of_decide_eq_true hS'mem
  have hRtmem := of_decide_eq_true hRtmem
  have hSm := of_decide_eq_true hSm
  have hS'm := of_decide_eq_true hS'm
  have hRtm := of_decide_eq_true hRtm
  -- the timestamp gap
  obtain ⟨k, hk, hkpos, hkrange⟩ :
      ∃ k, constDiff (tsExprOf shape S) (tsExprOf shape S') = some k ∧
        0 < k.val ∧ shape.tsBound + k.val ≤ p := by
    unfold sendGapOk at hgap
    split at hgap
    · rename_i k hk
      rw [Bool.and_eq_true] at hgap
      exact ⟨k, hk, of_decide_eq_true hgap.1, of_decide_eq_true hgap.2⟩
    · exact absurd hgap (by simp)
  have hp : 0 < p := by omega
  -- the discipline for this bus
  obtain ⟨hc, hb, hd⟩ := hsat
  obtain ⟨c1, c2, c3, c4, c5, cmono⟩ := hd busId shape hdecl
  have hbus : ∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false := fun bi hbi => hb bi hbi
  -- evaluated multiplicities
  have hSev : (S.eval env).multiplicity = 1 := S.multiplicity.constValue?_sound 1 hSm env
  have hS'ev : (S'.eval env).multiplicity = 1 := S'.multiplicity.constValue?_sound 1 hS'm env
  -- membership of the evaluated messages
  have hmem : ∀ bi ∈ cs.busInteractions.filter (fun bi => bi.busId = busId),
      bi.eval env ∈ (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
        (fun bi => bi.eval env) := fun bi hbi => List.mem_map.2 ⟨bi, hbi, rfl⟩
  -- timestamp values
  have htsS : shape.tsVal (S.eval env) < shape.tsBound := by
    have := c3 (S.eval env) (hmem S hSmem) (by rw [hSev]; exact h1ne)
    exact this
  have htsS' : shape.tsVal (S'.eval env) = shape.tsVal (S.eval env) + k.val := by
    rw [tsVal_eval, tsVal_eval, constDiff_sound _ _ k hk env]
    exact ZMod.val_add_of_lt (by
      rw [← tsVal_eval]
      omega)
  have hlt : shape.tsVal (S.eval env) < shape.tsVal (S'.eval env) := by omega
  -- addresses agree
  have haddr := addrConstsEq_sound shape S S' haddrc env
  -- no active send strictly between
  have hnobetween : ∀ S'' ∈ (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => bi.eval env), S''.multiplicity = 1 →
      shape.address S'' = shape.address (S.eval env) →
      ¬(shape.tsVal (S.eval env) < shape.tsVal S'' ∧
        shape.tsVal S'' < shape.tsVal (S'.eval env)) := by
    intro S'' hS''mem hS''mult _
    obtain ⟨bi, hbi, rfl⟩ := List.mem_map.1 hS''mem
    have hcase := List.all_eq_true.mp hsends bi hbi
    rcases (Bool.or_eq_true _ _).mp hcase with hcase | hlast
    · rcases (Bool.or_eq_true _ _).mp hcase with hcase | hcase
      · have : bi = S := of_decide_eq_true hcase
        subst this
        omega
      · have : bi = S' := of_decide_eq_true hcase
        subst this
        omega
    · unfold notSend at hlast
      split at hlast
      · rename_i m hm
        have : (bi.eval env).multiplicity = m := bi.multiplicity.constValue?_sound m hm env
        rw [this] at hS''mult
        exact absurd hS''mult (of_decide_eq_true hlast)
      · exact absurd hlast (by simp)
  -- the discipline's in-window consumption clause
  obtain ⟨Rcv, hRcvMem, hRcvMult, hRcvPay⟩ :=
    c2 (S.eval env) (hmem S hSmem) (S'.eval env) (hmem S' hS'mem)
      hSev hS'ev haddr hlt hnobetween
  -- identify the receive: everything except `Rt` is refuted
  obtain ⟨bi, hbi, hbieq⟩ := List.mem_map.1 hRcvMem
  have hbiRt : bi = Rt := by
    have hcase := List.all_eq_true.mp hmatch bi hbi
    rcases (Bool.or_eq_true _ _).mp hcase with hcase | hcase
    · exact of_decide_eq_true hcase
    · exfalso
      unfold notMatch at hcase
      rcases (Bool.or_eq_true _ _).mp hcase with hcase | href
      · split at hcase
        · rename_i m hm
          have hmne : m ≠ -1 := of_decide_eq_true hcase
          have hme : (bi.eval env).multiplicity = m := bi.multiplicity.constValue?_sound m hm env
          apply hmne
          rw [← hme, hbieq]
          exact hRcvMult
        · exact absurd hcase (by simp)
      · -- payload equality forces timestamp equality, contradicting the refutation
        have hpay : bi.payload.map (fun e => e.eval env)
            = S.payload.map (fun e => e.eval env) := by
          have := hRcvPay
          rw [← hbieq] at this
          exact this
        have := payloadSlot_eval_eq bi.payload S.payload env hpay shape.tsField
        exact tsRefuted_sound B shape S bi hp href env (hB env hbus) this
  -- the payload equality, slot by slot, gives the conclusions
  have hpay : Rt.payload.map (fun e => e.eval env) = S.payload.map (fun e => e.eval env) := by
    have h' := hRcvPay
    rw [← hbieq, hbiRt] at h'
    exact h'
  intro c hcmem
  unfold memEqConstraints at hcmem
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hcmem
  rw [eqExpr_eval, payloadSlot_eval_eq Rt.payload S.payload env hpay i]
  ring

/-! ## The pass -/

/-- Proof-free candidate search: a declared bus with exactly two constant-multiplicity sends
    and some receive that `checkMemMatch` accepts. -/
def findMemMatch (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat) :
    Option (Nat × BusInteraction (Expression p) × BusInteraction (Expression p)
      × BusInteraction (Expression p)) :=
  ((cs.busInteractions.map (fun bi => bi.busId)).dedup).findSome? (fun busId =>
    match bs.memoryBus busId with
    | none => none
    | some shape =>
      let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
      match L.filter (fun bi => multConst bi = some 1) with
      | [A, A'] =>
        (L.filter (fun bi => multConst bi = some (-1))).findSome? (fun Rt =>
          if checkMemMatch cs bs B busId shape A A' Rt then some (busId, A, A', Rt)
          else if checkMemMatch cs bs B busId shape A' A Rt then some (busId, A', A, Rt)
          else none)
      | _ => none)

/-- The memory-unification pass: add the entailed receive-equals-send equations for a checked
    match (skipping equations already present or trivially zero, so the pass is idempotent).
    The affine/domain passes then eliminate the receive's witness variables. -/
def memoryUnifyPass : VerifiedPassW p := fun cs bs facts =>
  let Bm : BoundsMap p cs bs := BoundsMap.build facts
  match findMemMatch cs bs Bm.map with
  | none => ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
  | some (busId, S, S', Rt) =>
    match hdecl : bs.memoryBus busId with
    | none => ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
    | some shape =>
      if hchk : checkMemMatch cs bs Bm.map busId shape S S' Rt = true then
        let new := (memEqConstraints shape S Rt).filter
          (fun c => !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c)
        ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new },
         cs.addConstraints_correct bs new (fun env hsat c hc =>
           checkMemMatch_sound cs bs Bm.map Bm.sound busId shape S S' Rt hdecl hchk env hsat
             c (List.mem_of_mem_filter hc))⟩
      else ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
