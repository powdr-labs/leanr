import Leanr.Implementation.OptimizerPasses.BusUnify
import Leanr.Implementation.OptimizerPasses.DomainProp
import Leanr.Implementation.OptimizerPasses.SubstMap
import Leanr.Implementation.MemoryBusDrop

set_option autoImplicit false

/-! # Cancelling matched send/receive pairs on a memory bus

After `busUnifyPass` and the affine/Gauss machinery, a memory access chain leaves the bus with a
*send* `S` (multiplicity `1`) and a later *receive* `R` (multiplicity `-1`) carrying the **same
payload** — the write of one access and the read of the next, unified to the same tuple. These two
messages have opposite multiplicity on the same tuple, so they contribute `0` to every message's
net multiplicity: dropping **both** leaves the bus state (`≈`) unchanged and shrinks the circuit.
It is exactly powdr's memory-interaction cancellation.

Under the spec this is sound because:

* **soundness** (`out.implies cs`): re-adding the pair to reach a witness of `cs` imposes no
  obligation — the send never violates (the `recvByteSlots` contract), and the receive's only
  obligation is that its declared byte slots are bytes, which the pass *justifies from the
  remaining system*: each dropped byte-slot entry is a constant `< 256`, a variable whose proven
  bus-fact bound from a remaining interaction is `≤ 256` (`byteJustified`), or — on prime `p` — a
  variable whose defining constraint pins it to a byte on every point of its selector flags'
  proven finite domains (`deepBoundOk`, the one-hot byte-selection shape). When even that fails,
  the pass *materializes* the obligation as an explicit self-check on a `byteCheck` bus
  (`emitOk`), still a net bus win. The pair's net side-effect contribution is `0`;
* **completeness** (`cs.impliesAdmissible out`): removing the pair preserves the VM's `admissible`
  predicate (`admissible_dropPair`), provided `S` is the *earliest* active send to its address —
  otherwise the removal could expose a fresh consecutive send→receive pair with mismatched payloads.
  This side condition holds for the standard receive-before-send access discipline. Any emitted
  check is *implied* by the dropped receive's own accepted message, so real traces satisfy it. -/

variable {p : ℕ}

/-! ## Byte justification for the dropped receive's obligation

Under semantics where a memory *receive* of a non-byte word violates (see the OpenVM `violates`),
re-adding a dropped receive is only free when its data limbs are provably bytes under every
assignment satisfying the remaining system. The pass justifies each declared byte slot of the
dropped pair's payload from the *remaining* interactions, so no justification can cite the pair
being dropped. -/

/-- Cap on the number of enumerated flag assignments per deep-justification attempt. -/
def maxDeepPoints : Nat := 64

/-- Cap on a single enumerated variable's domain size in the deep justification. -/
def maxDeepDomain : Nat := 4

/-- Cap on the number of candidate defining constraints tried per deep justification. -/
def maxDeepConstraints : Nat := 4

/-- Cap on a candidate constraint's number of distinct other variables (wider constraints
    cannot collapse to the ≤2-term linear shapes `pointByteOk` accepts anyway). -/
def maxDeepVars : Nat := 8

/-- Does the expression mention `x`? (No allocation — `Expression.vars` would materialize a
    fresh list per constraint on every deep-justification scan.) -/
def Expression.containsVar (x : Variable) : Expression p → Bool
  | .const _ => false
  | .var y => y == x
  | .add a b => a.containsVar x || b.containsVar x
  | .mul a b => a.containsVar x || b.containsVar x

/-- The expression's single distinct variable: `some (some v)` when exactly `v` occurs,
    `some none` when no variable occurs, `none` when several distinct variables occur.
    Cheap pre-filter for the constraints `findDomainAlg` can actually derive a domain from. -/
def Expression.singleVarAux : Expression p → Option (Option Variable)
  | .const _ => some none
  | .var y => some (some y)
  | .add a b | .mul a b =>
    match a.singleVarAux, b.singleVarAux with
    | some none, r => r
    | r, some none => r
    | some (some u), some (some v) => if u == v then some (some u) else none
    | _, _ => none

/-- Is the expression a single-variable expression (exactly one distinct variable)? -/
def Expression.isSingleVar (e : Expression p) : Bool :=
  match e.singleVarAux with
  | some (some _) => true
  | _ => false

/-- Per-point core of the deep justification. The point `pt` fixes the enumerable variables
    `keys` of the constraint `c`; after substituting and folding, the constraint must be linear
    and — once normalized — either pin `x` to a re-checked byte constant, or equate `x`
    (coefficient-for-coefficient, no constant) to a single variable in `byteVars` (the
    precomputed byte-bounded variables — so the per-point work is allocation-light and scans
    nothing). -/
def pointByteOk (x : Variable) (c : Expression p) (byteVars : List Variable)
    (keys : List Variable) (pt : List (Variable × ZMod p)) : Bool :=
  match linearize ((c.substF (fun v =>
      if keys.contains v then some (.const (envOf pt v)) else none)).fold) with
  | none => false
  | some l =>
    match (LinExpr.norm l).terms with
    | [(v, a)] =>
      -- `x` is pinned to the (re-checked) root; it must be a byte
      decide (v = x) && decide (a ≠ 0) &&
        decide (a * (-(a⁻¹ * (LinExpr.norm l).const)) + (LinExpr.norm l).const = 0) &&
        decide ((-(a⁻¹ * (LinExpr.norm l).const) : ZMod p).val < 256)
    | [(v1, a1), (v2, a2)] =>
      -- `x = other` (opposite coefficients, no constant); the other side is byte-bounded
      decide ((LinExpr.norm l).const = 0) &&
      (if v1 = x then
        decide (a2 = -a1) && decide (a1 ≠ 0) && byteVars.contains v2
       else if v2 = x then
        decide (a1 = -a2) && decide (a2 ≠ 0) && byteVars.contains v1
       else false)
    | _ => false

/-- The variables of `c` (other than `x`) with a proven byte bound from the remaining
    interactions — computed once per candidate, not once per enumeration point. -/
def deepByteVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (Expression p))) (x : Variable) (c : Expression p) :
    List Variable :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filter (fun v =>
    match findVarBound bs facts rest v with
    | some b => decide (b ≤ 256)
    | none => false)

/-- The variables of `c` other than `x` that carry a small proven *constraint-derived* finite
    domain (selector flags) — the candidates for enumeration in the deep justification.
    `domCs` is the pre-filtered single-variable constraint list (the only constraints
    `findDomainAlg` can use); bus-fact domains are deliberately not consulted: they are
    byte/range-sized (never ≤ `maxDeepDomain`), and materializing them just to discard them
    dominated the pass's runtime — the range-checked variables stay symbolic, which is what
    `pointByteOk` wants. -/
def deepEnumDoms (domCs : List (Expression p)) (x : Variable) (c : Expression p) :
    List (Variable × List (ZMod p)) :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filterMap (fun v =>
    match findDomainAlg domCs v with
    | some d => if d.length ≤ maxDeepDomain then some (v, d) else none
    | none => none)

/-- Deep byte bound for `x` from one constraint `c`: enumerate the small proven finite domains
    of `c`'s other variables (e.g. one-hot selector flags) and require `pointByteOk` at every
    point. This resolves byte *selections* `x = Σ (flag polynomial)·yⱼ` over byte-bounded `yⱼ` —
    the shape a memory receive of an unaligned sub-word load leaves behind. -/
def deepBoundOk (domCs : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (Expression p))) (x : Variable) (c : Expression p) : Bool :=
  if (c.vars.dedup.filter (fun v => v ≠ x)).length ≤ maxDeepVars &&
      ((deepEnumDoms domCs x c).map (fun vd => vd.2.length)).prod ≤ maxDeepPoints then
    (assignments (deepEnumDoms domCs x c)).all
      (pointByteOk x c (deepByteVars bs facts rest x c) ((deepEnumDoms domCs x c).map Prod.fst))
  else false

/-- Deep byte justification for `x`: one of the first `maxDeepConstraints` constraints
    mentioning `x` pins it via `deepBoundOk`. Domains are looked up only in the
    single-variable constraints (the only ones `findDomainAlg` can use). -/
def deepByteJustified (all : List (Expression p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (Expression p))) (x : Variable) : Bool :=
  ((all.filter (Expression.containsVar x)).take maxDeepConstraints).any
    (fun c => deepBoundOk (all.filter Expression.isSingleVar) bs facts rest x c)

theorem pointByteOk_sound [Fact p.Prime] (x : Variable) (c : Expression p)
    (byteVars : List Variable)
    (keys : List Variable) (pt : List (Variable × ZMod p))
    (h : pointByteOk x c byteVars keys pt = true) (env : Variable → ZMod p)
    (hpt : ∀ y, keys.contains y = true → envOf pt y = env y)
    (hc0 : c.eval env = 0)
    (hbyteVars : ∀ v ∈ byteVars, (env v).val < 256) :
    (env x).val < 256 := by
  unfold pointByteOk at h
  -- the substitution is transparent under `env`
  have hsub : ((c.substF (fun v =>
      if keys.contains v then some (.const (envOf pt v)) else none)).fold).eval env = 0 := by
    rw [Expression.fold_eval, Expression.eval_substF, envF_eq_self]
    · exact hc0
    · intro y t hy
      split_ifs at hy with hk
      · simp only [Option.some.injEq] at hy
        subst hy
        exact (hpt y hk).symm
  cases hl : linearize ((c.substF (fun v =>
      if keys.contains v then some (.const (envOf pt v)) else none)).fold) with
  | none => rw [hl] at h; simp at h
  | some l =>
    rw [hl] at h
    dsimp only at h
    have hleval : (LinExpr.norm l).const
        + ((LinExpr.norm l).terms.map (fun t => t.2 * env t.1)).sum = 0 := by
      have h1 : (LinExpr.norm l).eval env = 0 := by
        rw [LinExpr.norm_eval, ← linearize_eval _ l hl]
        exact hsub
      simpa [LinExpr.eval] using h1
    cases hterms : (LinExpr.norm l).terms with
    | nil => rw [hterms] at h; simp at h
    | cons t1 tail =>
      cases t1 with
      | mk v a =>
        cases tail with
        | nil =>
          -- single pinned term: `x = r`, a byte
          rw [hterms] at h hleval
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hleval
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
          obtain ⟨⟨⟨hvx, ha⟩, hroot⟩, hbyte⟩ := h
          have hvx' := of_decide_eq_true hvx
          have ha' := of_decide_eq_true ha
          have hroot' := of_decide_eq_true hroot
          rw [← hvx']
          have hcancel : a * env v = a * (-(a⁻¹ * (LinExpr.norm l).const)) := by
            have h1 : a * env v = -(LinExpr.norm l).const := by linear_combination hleval
            have h2 : a * (-(a⁻¹ * (LinExpr.norm l).const)) = -(LinExpr.norm l).const := by
              linear_combination hroot'
            rw [h1, h2]
          rw [mul_left_cancel₀ ha' hcancel]
          exact of_decide_eq_true hbyte
        | cons t2 tail2 =>
          cases t2 with
          | mk v2 a2 =>
            cases tail2 with
            | nil =>
              -- `x = other`: opposite coefficients, no constant
              rw [hterms] at h hleval
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                add_zero] at hleval
              rw [Bool.and_eq_true] at h
              obtain ⟨hconst, hbr⟩ := h
              have hconst' := of_decide_eq_true hconst
              rw [hconst', zero_add] at hleval
              split_ifs at hbr with hv1 hv2
              · -- v = x, bound v2
                rw [← hv1]
                rw [Bool.and_eq_true, Bool.and_eq_true] at hbr
                obtain ⟨⟨hopp, hne⟩, hbound⟩ := hbr
                have hopp' := of_decide_eq_true hopp
                have hne' := of_decide_eq_true hne
                have heqv : env v = env v2 := by
                  have : a * (env v - env v2) = 0 := by
                    rw [hopp'] at hleval; linear_combination hleval
                  rcases mul_eq_zero.mp this with h' | h'
                  · exact absurd h' hne'
                  · exact sub_eq_zero.mp h'
                rw [heqv]
                exact hbyteVars v2 (List.contains_iff_mem.mp hbound)
              · -- v2 = x, bound v
                rw [← hv2]
                rw [Bool.and_eq_true, Bool.and_eq_true] at hbr
                obtain ⟨⟨hopp, hne⟩, hbound⟩ := hbr
                have hopp' := of_decide_eq_true hopp
                have hne' := of_decide_eq_true hne
                have heqv : env v2 = env v := by
                  have : a2 * (env v2 - env v) = 0 := by
                    rw [hopp'] at hleval; linear_combination hleval
                  rcases mul_eq_zero.mp this with h' | h'
                  · exact absurd h' hne'
                  · exact sub_eq_zero.mp h'
                rw [heqv]
                exact hbyteVars v (List.contains_iff_mem.mp hbound)
            | cons t3 tail3 =>
              rw [hterms] at h; simp at h

theorem deepBoundOk_sound [Fact p.Prime] (domCs : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (Expression p))) (x : Variable) (c : Expression p)
    (h : deepBoundOk domCs bs facts rest x c = true) (env : Variable → ZMod p)
    (hdom : ∀ c' ∈ domCs, c'.eval env = 0) (hc0 : c.eval env = 0)
    (hbus : ∀ bi ∈ rest, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (env x).val < 256 := by
  unfold deepBoundOk at h
  split_ifs at h with hcap
  -- every enumerated variable's value lies in its domain
  have hdomsound : ∀ vd ∈ deepEnumDoms domCs x c, env vd.1 ∈ vd.2 := by
    intro vd hvd
    unfold deepEnumDoms at hvd
    obtain ⟨v, _, hfn⟩ := List.mem_filterMap.mp hvd
    cases hfd : findDomainAlg domCs v with
    | none => rw [hfd] at hfn; exact absurd hfn (by simp)
    | some d =>
      rw [hfd] at hfn
      dsimp only at hfn
      split_ifs at hfn
      simp only [Option.some.injEq] at hfn
      subst hfn
      exact findDomainAlg_sound domCs v d hfd env hdom
  -- the precomputed byte-bounded variables really are bytes under `env`
  have hbyteVars : ∀ v ∈ deepByteVars bs facts rest x c, (env v).val < 256 := by
    intro v hv
    unfold deepByteVars at hv
    obtain ⟨hv1, hv2⟩ := List.mem_filter.mp hv
    cases hb : findVarBound bs facts rest v with
    | none => rw [hb] at hv2; simp at hv2
    | some b =>
      rw [hb] at hv2
      dsimp only at hv2
      exact lt_of_lt_of_le (findVarBound_sound bs facts rest v b hb env hbus)
        (of_decide_eq_true hv2)
  -- `env`'s restriction to the enumerated domains is one of the checked points
  have hmem : (deepEnumDoms domCs x c).map (fun vd => (vd.1, env vd.1))
      ∈ assignments (deepEnumDoms domCs x c) :=
    mem_assignments _ env hdomsound
  have hpoint := List.all_eq_true.mp h _ hmem
  refine pointByteOk_sound x c (deepByteVars bs facts rest x c)
    ((deepEnumDoms domCs x c).map Prod.fst)
    ((deepEnumDoms domCs x c).map (fun vd => (vd.1, env vd.1))) hpoint env ?_
    hc0 hbyteVars
  intro y hy
  exact envOf_map (deepEnumDoms domCs x c) env y (List.contains_iff_mem.mp hy)

theorem deepByteJustified_sound [Fact p.Prime] [NeZero p] (all : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (Expression p))) (x : Variable)
    (h : deepByteJustified all bs facts rest x = true) (env : Variable → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ rest, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (env x).val < 256 := by
  obtain ⟨c, hc, hck⟩ := List.any_eq_true.1 h
  have hc' : c ∈ all := List.mem_of_mem_filter (List.mem_of_mem_take hc)
  exact deepBoundOk_sound (all.filter Expression.isSingleVar) bs facts rest x c hck env
    (fun c' hc'' => hall c' (List.mem_of_mem_filter hc'')) (hall c hc') hbus

/-- Is `e` provably a byte under every assignment satisfying the remaining system? Either a
    constant `< 256`, a variable with a proven bus-fact bound `≤ 256` derived from the remaining
    interactions `rest` (e.g. another receive of the same word, or an explicit byte-check
    lookup), or — when `deep` is set (prime `p` only) — a variable whose constraint-derived
    finite domain (`findDomainAlg`, e.g. `x·(x−255) = 0`) contains only bytes, a variable a
    constraint pins to a byte on every point of its selector flags' proven finite domains
    (`deepBoundOk`), or (any expression) an explicit self-check `[e, e, 0, 1]` on a `byteCheck`
    bus among the remaining interactions — the carrier the pass itself emits for
    otherwise-unjustified slots, matched syntactically. -/
def byteJustified (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p)))
    (e : Expression p) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < 256)
  | none =>
    (match e with
     | .var x =>
       (match findVarBound bs facts rest x with
        | some bound => decide (bound ≤ 256)
        | none => false) ||
       (deep && ((match findDomainAlg all x with
                  | some dom => dom.all (fun v => decide (v.val < 256))
                  | none => false) ||
                 deepByteJustified all bs facts rest x))
     | _ => false) ||
    (deep && rest.any (fun bi =>
      facts.byteCheck bi.busId &&
      decide (bi.multiplicity = (.const 1 : Expression p)) &&
      decide (bi.payload = [e, e, (.const 0 : Expression p), (.const 1 : Expression p)])))

theorem byteJustified_sound (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p))) (e : Expression p)
    (hdeep : deep = true → p.Prime)
    (h : byteJustified deep all bs facts rest e = true) (env : Variable → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ rest, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (e.eval env).val < 256 := by
  unfold byteJustified at h
  cases hc : e.constValue? with
  | some c =>
    rw [hc] at h
    dsimp only at h
    rw [e.constValue?_sound c hc env]
    exact of_decide_eq_true h
  | none =>
    rw [hc] at h
    dsimp only at h
    rcases Bool.or_eq_true _ _ |>.mp h with h | hcarrier
    · cases e with
      | var x =>
        dsimp only at h
        show (env x).val < 256
        rcases Bool.or_eq_true _ _ |>.mp h with h' | h'
        · cases hb : findVarBound bs facts rest x with
          | some bound =>
            rw [hb] at h'
            dsimp only at h'
            exact lt_of_lt_of_le (findVarBound_sound bs facts rest x bound hb env hbus)
              (of_decide_eq_true h')
          | none => rw [hb] at h'; simp at h'
        · rw [Bool.and_eq_true] at h'
          haveI : Fact p.Prime := ⟨hdeep h'.1⟩
          haveI : NeZero p := ⟨(hdeep h'.1).ne_zero⟩
          rcases Bool.or_eq_true _ _ |>.mp h'.2 with hdom | hdeepb
          · cases hd : findDomainAlg all x with
            | some dom =>
              rw [hd] at hdom
              dsimp only at hdom
              have hmem := findDomainAlg_sound all x dom hd env hall
              exact of_decide_eq_true (List.all_eq_true.mp hdom _ hmem)
            | none => rw [hd] at hdom; simp at hdom
          · exact deepByteJustified_sound all bs facts rest x hdeepb env hall hbus
      | const n => simp at h
      | add a b => simp at h
      | mul a b => simp at h
    · -- an explicit self-check on a `byteCheck` bus among `rest` carries `e`'s byte obligation
      rw [Bool.and_eq_true] at hcarrier
      haveI : Fact (1 < p) := ⟨(hdeep hcarrier.1).one_lt⟩
      obtain ⟨bi, hbi, hform⟩ := List.any_eq_true.1 hcarrier.2
      rw [Bool.and_eq_true, Bool.and_eq_true] at hform
      obtain ⟨⟨hbc, hmd⟩, hpayd⟩ := hform
      have hmult : bi.multiplicity = (.const 1 : Expression p) := of_decide_eq_true hmd
      have hpayload : bi.payload
          = [e, e, (.const 0 : Expression p), (.const 1 : Expression p)] :=
        of_decide_eq_true hpayd
      obtain ⟨_, _, hviol⟩ := facts.byteCheck_sound bi.busId hbc
      have hEv : bi.eval env
          = { busId := bi.busId, multiplicity := (1 : ZMod p),
              payload := [e.eval env, e.eval env, (0 : ZMod p), (1 : ZMod p)] } := by
        unfold BusInteraction.eval
        rw [hmult, hpayload]
        rfl
      have hok := hbus bi hbi (by rw [hEv]; exact one_ne_zero)
      rw [hEv] at hok
      exact (hviol (e.eval env) 1).mp hok

/-- Are all of `R`'s payload entries at the declared byte slots justified from `rest`? -/
def recvSlotsJustified (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p))) (slots : List Nat)
    (R : BusInteraction (Expression p)) : Bool :=
  slots.all (fun slot =>
    match R.payload[slot]? with
    | some e => byteJustified deep all bs facts rest e
    | none => true)

theorem recvSlotsJustified_sound (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p))) (slots : List Nat)
    (R : BusInteraction (Expression p)) (hdeep : deep = true → p.Prime)
    (h : recvSlotsJustified deep all bs facts rest slots R = true)
    (env : Variable → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ rest, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    ∀ slot ∈ slots, ∀ x : ZMod p, (R.eval env).payload[slot]? = some x → x.val < 256 := by
  intro slot hslot x hget
  have hcheck := List.all_eq_true.mp h slot hslot
  -- the evaluated payload entry is the evaluation of the syntactic entry
  have hget' : (R.payload[slot]?).map (fun e => e.eval env) = some x := by
    rw [← List.getElem?_map]
    exact hget
  cases he : R.payload[slot]? with
  | none => rw [he] at hget'; exact absurd hget' (by simp)
  | some e =>
    rw [he] at hget' hcheck
    simp only [Option.map_some, Option.some.injEq] at hget'
    subst hget'
    exact byteJustified_sound deep all bs facts rest e hdeep hcheck env hall hbus

/-! ## Net-multiplicity bookkeeping -/

/-- Net multiplicity is additive over concatenation of bus states. -/
theorem multiplicitySum_append (msg : BusMessage p) (s t : BusState p) :
    multiplicitySum msg (s ++ t) = multiplicitySum msg s + multiplicitySum msg t := by
  induction s with
  | nil => simp [multiplicitySum]
  | cons hd tl ih =>
      simp only [List.cons_append, multiplicitySum, ih]
      ring

/-- The stateful side-effect state of a raw interaction list under `env` (what `sideEffects`
    computes). -/
def toBusState (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p))) : BusState p :=
  (L.filter (fun bi => bs.isStateful bi.busId)).map
    (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity))

theorem toBusState_append (bs : BusSemantics p) (env : Variable → ZMod p)
    (L1 L2 : List (BusInteraction (Expression p))) :
    toBusState bs env (L1 ++ L2) = toBusState bs env L1 ++ toBusState bs env L2 := by
  simp only [toBusState, List.filter_append, List.map_append]

theorem toBusState_cons_stateful (bs : BusSemantics p) (env : Variable → ZMod p)
    (bi : BusInteraction (Expression p)) (L : List (BusInteraction (Expression p)))
    (h : bs.isStateful bi.busId = true) :
    toBusState bs env (bi :: L)
    = (let m := bi.eval env; ((m.busId, m.payload), m.multiplicity)) :: toBusState bs env L := by
  simp only [toBusState]
  rw [List.filter_cons_of_pos (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) h,
    List.map_cons]

/-- Dropping a matched send/receive pair (equal evaluated message, opposite multiplicities) leaves
    every message's net multiplicity unchanged: the `+1` and `-1` contributions cancel. -/
theorem sideEffects_dropPair_equiv (bs : BusSemantics p) (env : Variable → ZMod p)
    (A B C : List (BusInteraction (Expression p))) (S R : BusInteraction (Expression p))
    (hSstate : bs.isStateful S.busId = true) (hRstate : bs.isStateful R.busId = true)
    (hSm : (S.eval env).multiplicity = 1) (hRm : (R.eval env).multiplicity = -1)
    (hbusEq : (S.eval env).busId = (R.eval env).busId)
    (hpay : (S.eval env).payload = (R.eval env).payload) :
    toBusState bs env (A ++ S :: B ++ R :: C) ≈ toBusState bs env (A ++ B ++ C) := by
  intro msg
  have hstructFull : A ++ S :: B ++ R :: C = (A ++ S :: B) ++ (R :: C) := by
    simp only [List.append_assoc, List.cons_append]
  have hstructOut : A ++ B ++ C = (A ++ B) ++ C := rfl
  rw [hstructFull, toBusState_append, toBusState_cons_stateful bs env R C hRstate,
    toBusState_append, toBusState_cons_stateful bs env S B hSstate]
  rw [hstructOut, toBusState_append, toBusState_append]
  have hmsgEq : ((S.eval env).busId, (S.eval env).payload)
      = ((R.eval env).busId, (R.eval env).payload) := by rw [hbusEq, hpay]
  simp only [multiplicitySum_append, multiplicitySum, hmsgEq, hSm, hRm]
  split_ifs <;> ring

/-! ## The active∧stateful evaluated messages (what `admissible` inspects) -/

/-- The active, stateful evaluated messages of a raw interaction list — the argument
    `ConstraintSystem.admissible` passes to `bs.admissible`. -/
def activeStatefulMsgs (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p))) : List (BusInteraction (ZMod p)) :=
  (L.map (fun bi => bi.eval env)).filter
    (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)

theorem activeStatefulMsgs_append (bs : BusSemantics p) (env : Variable → ZMod p)
    (L1 L2 : List (BusInteraction (Expression p))) :
    activeStatefulMsgs bs env (L1 ++ L2)
    = activeStatefulMsgs bs env L1 ++ activeStatefulMsgs bs env L2 := by
  simp only [activeStatefulMsgs, List.map_append, List.filter_append]

theorem activeStatefulMsgs_cons_survive (bs : BusSemantics p) (env : Variable → ZMod p)
    (bi : BusInteraction (Expression p)) (L : List (BusInteraction (Expression p)))
    (h : (decide ((bi.eval env).multiplicity ≠ 0) && bs.isStateful (bi.eval env).busId) = true) :
    activeStatefulMsgs bs env (bi :: L) = bi.eval env :: activeStatefulMsgs bs env L := by
  simp only [activeStatefulMsgs, List.map_cons]
  rw [List.filter_cons_of_pos
    (p := fun m : BusInteraction (ZMod p) => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) h]

theorem mem_activeStatefulMsgs (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p))) (m : BusInteraction (ZMod p))
    (hm : m ∈ activeStatefulMsgs bs env L) :
    ∃ m0 ∈ L, m0.eval env = m := by
  unfold activeStatefulMsgs at hm
  obtain ⟨hmem, _⟩ := List.mem_filter.mp hm
  obtain ⟨m0, hm0, hev⟩ := List.mem_map.mp hmem
  exact ⟨m0, hm0, hev⟩

/-- A list of stateless interactions contributes nothing to the bus state. -/
theorem toBusState_stateless (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p)))
    (h : ∀ bi ∈ L, bs.isStateful bi.busId = false) :
    toBusState bs env L = [] := by
  unfold toBusState
  rw [List.filter_eq_nil_iff.mpr (fun bi hbi => by simp [h bi hbi])]
  rfl

/-- A list of stateless interactions contributes nothing to the active∧stateful messages. -/
theorem activeStatefulMsgs_stateless (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p)))
    (h : ∀ bi ∈ L, bs.isStateful bi.busId = false) :
    activeStatefulMsgs bs env L = [] := by
  unfold activeStatefulMsgs
  apply List.filter_eq_nil_iff.mpr
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
  simp [BusInteraction.eval, h m0 hm0]

/-! ## The core correctness of dropping a matched pair -/

/-- **Correctness of dropping one matched consecutive send/receive pair, optionally emitting
    replacement byte checks.** `S` (a send) and `R` (a later receive) carry the same payload
    (`hpay`), are on a bus `busId` with a declared `shape` and a `recvByteSlots` contract whose
    byte obligation for `R` is justified by the remaining interactions *including the emitted
    checks* (`hbyte`), with no active same-address message between them (`hmidEval`) and no
    active same-address send before `S` (`hpreEval`). Each emitted check is stateless, implied
    by `R`'s own accepted receive, invariant-free, and adds no variables (`hchecks`) — when
    the remaining system already justifies `R`'s byte slots, `checks` is simply `[]`. Dropping
    the pair and appending the checks is `PassCorrect`. -/
theorem dropPair_correct (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0)
    (A B C : List (BusInteraction (Expression p))) (S R : BusInteraction (Expression p))
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (slots : List Nat) (hslots : facts.recvByteSlots busId = some slots)
    (checks : List (BusInteraction (Expression p)))
    (hchecks : ∀ ck ∈ checks,
      bs.isStateful ck.busId = false ∧
      (∀ env, bs.violatesConstraint (R.eval env) = false →
        bs.violatesConstraint (ck.eval env) = false) ∧
      (∀ env, bs.breaksInvariant (ck.eval env) = false) ∧
      (∀ v ∈ ck.vars, v ∈ R.vars))
    (hbyte : ∀ (env : Variable → ZMod p),
      (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) →
      (∀ bi ∈ A ++ B ++ C ++ checks, (bi.eval env).multiplicity ≠ 0 →
        bs.violatesConstraint (bi.eval env) = false) →
      ∀ slot ∈ slots, ∀ x : ZMod p, (R.eval env).payload[slot]? = some x → x.val < 256)
    (hsplit : cs.busInteractions = A ++ S :: B ++ R :: C)
    (hSbus : S.busId = busId) (hRbus : R.busId = busId)
    (hSm : S.multiplicity.constValue? = some 1) (hRm : R.multiplicity.constValue? = some (-1))
    (hpay : S.payload = R.payload)
    (hmidEval : ∀ (env : Variable → ZMod p), ∀ m0 ∈ B, (m0.eval env).busId = busId →
        (m0.eval env).multiplicity ≠ 0 →
        shape.address (m0.eval env) = shape.address (S.eval env) → False)
    (hpreEval : ∀ (env : Variable → ZMod p), ∀ m0 ∈ A, (m0.eval env).busId = busId →
        (m0.eval env).multiplicity ≠ 0 →
        shape.address (m0.eval env) = shape.address (S.eval env) → (m0.eval env).multiplicity ≠ 1) :
    PassCorrect cs { cs with busInteractions := A ++ B ++ C ++ checks } [] bs := by
  set out : ConstraintSystem p := { cs with busInteractions := A ++ B ++ C ++ checks } with hout
  have houtb : out.busInteractions = A ++ B ++ C ++ checks := rfl
  have hchecksStateless : ∀ bi ∈ checks, bs.isStateful bi.busId = false :=
    fun bi hbi => (hchecks bi hbi).1
  have hRmem : R ∈ cs.busInteractions := by
    rw [hsplit]
    exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
  -- Common facts.
  have hStateful : bs.isStateful busId = true := facts.memShape_stateful busId shape hshape
  have hSstate : bs.isStateful S.busId = true := hSbus ▸ hStateful
  have hRstate : bs.isStateful R.busId = true := hRbus ▸ hStateful
  have hSmEv : ∀ env, (S.eval env).multiplicity = 1 :=
    fun env => S.multiplicity.constValue?_sound 1 hSm env
  have hRmEv : ∀ env, (R.eval env).multiplicity = -1 :=
    fun env => R.multiplicity.constValue?_sound (-1) hRm env
  have hSactive : ∀ env, (S.eval env).multiplicity ≠ 0 := fun env => by rw [hSmEv env]; exact hp1
  have hRactive : ∀ env, (R.eval env).multiplicity ≠ 0 :=
    fun env => by rw [hRmEv env]; exact neg_ne_zero.mpr hp1
  have hpayEv : ∀ env, (S.eval env).payload = (R.eval env).payload := fun env => by
    show S.payload.map (fun e => e.eval env) = R.payload.map (fun e => e.eval env); rw [hpay]
  have haddrEv : ∀ env, shape.address (S.eval env) = shape.address (R.eval env) := fun env => by
    simp only [MemoryBusShape.address, hpayEv env]
  -- Membership: the kept core `A ++ B ++ C` is among `cs`'s interactions.
  have hmem_core : ∀ bi, bi ∈ A ++ B ++ C → bi ∈ cs.busInteractions := by
    intro bi hbi
    rw [hsplit]
    simp only [List.mem_append, List.mem_cons] at hbi ⊢; tauto
  -- Re-adding the dropped pair imposes no obligation: the send never violates (the
  -- `recvByteSlots` contract), and the receive's byte slots are justified from the remaining
  -- interactions, whose obligations hold under any `out`-satisfying assignment.
  have hnvS : ∀ env, bs.violatesConstraint (S.eval env) = false := fun env =>
    (facts.recvByteSlots_sound busId slots hslots (S.eval env)
      (show (S.eval env).busId = busId from hSbus)).1 (hSmEv env)
  have hnvR : ∀ env, out.satisfies bs env → bs.violatesConstraint (R.eval env) = false := by
    intro env hsat
    refine (facts.recvByteSlots_sound busId slots hslots (R.eval env)
      (show (R.eval env).busId = busId from hRbus)).2 (hRmEv env)
      (hbyte env (fun c hc => hsat.1 c hc) ?_)
    intro bi hbi hne
    exact hsat.2 bi (by rw [houtb]; exact hbi) hne
  -- Side effects are `≈`-equal (the pair contributes `0` net; the checks are stateless).
  have hSE : ∀ env, cs.sideEffects bs env ≈ out.sideEffects bs env := by
    intro env
    have e1 : cs.sideEffects bs env = toBusState bs env (A ++ S :: B ++ R :: C) := by
      show toBusState bs env cs.busInteractions = toBusState bs env (A ++ S :: B ++ R :: C)
      rw [hsplit]
    have e2 : out.sideEffects bs env = toBusState bs env (A ++ B ++ C) := by
      show toBusState bs env (A ++ B ++ C ++ checks) = toBusState bs env (A ++ B ++ C)
      rw [toBusState_append, toBusState_stateless bs env checks hchecksStateless,
        List.append_nil]
    rw [e1, e2]
    exact sideEffects_dropPair_equiv bs env A B C S R hSstate hRstate (hSmEv env) (hRmEv env)
      (by rw [show (S.eval env).busId = busId from hSbus, show (R.eval env).busId = busId from hRbus])
      (hpayEv env)
  -- `cs.satisfies` implies `out.satisfies` (the kept core has fewer obligations; each emitted
  -- check is implied by `R`'s own obligation, which `cs.satisfies` includes).
  have hsat_cs_out : ∀ env, cs.satisfies bs env → out.satisfies bs env := by
    intro env hsat
    refine ⟨hsat.1, ?_⟩
    intro bi hbi
    rw [houtb] at hbi
    rcases List.mem_append.1 hbi with hbi | hbi
    · exact hsat.2 bi (hmem_core bi hbi)
    · exact fun _ => (hchecks bi hbi).2.1 env (hsat.2 R hRmem (hRactive env))
  -- `out.satisfies` implies `cs.satisfies` (the extra pair never violates).
  have hsat_out_cs : ∀ env, out.satisfies bs env → cs.satisfies bs env := by
    intro env hsat
    refine ⟨hsat.1, ?_⟩
    intro bi hbi
    rw [hsplit] at hbi
    simp only [List.mem_append, List.mem_cons] at hbi
    rcases hbi with (hbi | rfl | hbi) | (rfl | hbi)
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
    · exact fun _ => hnvS env
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
    · exact fun _ => hnvR env hsat
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
  -- `admissible` is preserved (completeness).
  have hadm_cs_out : ∀ env, cs.admissible bs env → out.admissible bs env := by
    intro env hadm
    have hSsurv : (decide ((S.eval env).multiplicity ≠ 0) && bs.isStateful (S.eval env).busId) = true := by
      rw [show bs.isStateful (S.eval env).busId = true from hSstate, Bool.and_true, decide_eq_true_eq]
      exact hSactive env
    have hRsurv : (decide ((R.eval env).multiplicity ≠ 0) && bs.isStateful (R.eval env).busId) = true := by
      rw [show bs.isStateful (R.eval env).busId = true from hRstate, Bool.and_true, decide_eq_true_eq]
      exact hRactive env
    -- Rewrite both admissible arguments into split form.
    have hasmFull : activeStatefulMsgs bs env cs.busInteractions
        = activeStatefulMsgs bs env A ++ (S.eval env) :: activeStatefulMsgs bs env B
          ++ (R.eval env) :: activeStatefulMsgs bs env C := by
      rw [hsplit, show A ++ S :: B ++ R :: C = (A ++ S :: B) ++ (R :: C) from by
            simp only [List.append_assoc, List.cons_append],
        activeStatefulMsgs_append, activeStatefulMsgs_cons_survive bs env R C hRsurv,
        activeStatefulMsgs_append, activeStatefulMsgs_cons_survive bs env S B hSsurv]
    have hasmOut : activeStatefulMsgs bs env out.busInteractions
        = activeStatefulMsgs bs env A ++ activeStatefulMsgs bs env B
          ++ activeStatefulMsgs bs env C := by
      show activeStatefulMsgs bs env (A ++ B ++ C ++ checks) = _
      rw [activeStatefulMsgs_append, activeStatefulMsgs_stateless bs env checks hchecksStateless,
        List.append_nil, activeStatefulMsgs_append, activeStatefulMsgs_append]
    have hadm' : bs.admissible (activeStatefulMsgs bs env A ++ (S.eval env)
        :: activeStatefulMsgs bs env B ++ (R.eval env) :: activeStatefulMsgs bs env C) := by
      have : bs.admissible (activeStatefulMsgs bs env cs.busInteractions) := hadm
      rwa [hasmFull] at this
    show bs.admissible (activeStatefulMsgs bs env out.busInteractions)
    rw [hasmOut]
    refine facts.admissible_dropPair hp1 busId shape hshape _ _ _ (S.eval env) (R.eval env)
      hSbus hRbus (hSmEv env) (hRmEv env) (haddrEv env) ?_ ?_ hadm'
    · intro m hm hbid hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := mem_activeStatefulMsgs bs env B m hm
      exact hmidEval env m0 hm0 hbid hmne hmaddr
    · intro m hm hbid hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := mem_activeStatefulMsgs bs env A m hm
      exact hpreEval env m0 hm0 hbid hmne hmaddr
  -- Variables only shrink (the pair is dropped; each emitted check's variables come from `R`).
  have hsub : ∀ v ∈ out.vars, v ∈ cs.vars := by
    intro v hv
    rw [ConstraintSystem.mem_vars] at hv ⊢
    rcases hv with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hbiv⟩
    · exact Or.inl ⟨c, hc, hvc⟩
    · rcases List.mem_append.1 (by rw [houtb] at hbi; exact hbi) with hbi' | hbi'
      · exact Or.inr ⟨bi, hmem_core bi hbi', hbiv⟩
      · -- `bi` is an emitted check: its variables are among `R`'s
        have hv' : v ∈ bi.vars := by
          rw [BusInteraction.vars, List.mem_append]
          rcases hbiv with hm | ⟨e, he, hve⟩
          · exact Or.inl hm
          · exact Or.inr (List.mem_flatMap.2 ⟨e, he, hve⟩)
        have hvR : v ∈ R.vars := (hchecks bi hbi').2.2.2 v hv'
        rw [BusInteraction.vars, List.mem_append] at hvR
        refine Or.inr ⟨R, hRmem, ?_⟩
        rcases hvR with h | h
        · exact Or.inl h
        · obtain ⟨e, he, hve⟩ := List.mem_flatMap.1 h
          exact Or.inr ⟨e, he, hve⟩
  -- Assemble via `ofEnvEq` (completeness witness is the input assignment; no derivations).
  exact PassCorrect.ofEnvEq
    (fun env hsat => ⟨env, hsat_out_cs env hsat, BusState.equiv_symm (hSE env)⟩)
    (fun hinv env hsat bi hbi => by
      rcases List.mem_append.1 (by rw [houtb] at hbi; exact hbi) with hbi' | hbi'
      · exact hinv env (hsat_out_cs env hsat) bi (hmem_core bi hbi')
      · exact fun _ => (hchecks bi hbi').2.2.1 env)
    hsub
    (fun env hadm hsat => ⟨hsat_cs_out env hsat, hadm_cs_out env hadm, hSE env⟩)

/-! ## The pass: detect and drop matched pairs -/

/-- Scan for the first matching receive `R` for a send `S`: constant `-1` multiplicity, on `busId`,
    carrying `S`'s payload. Returns `(B, R, C)` — the scanned prefix `B`, the receive `R`, and the
    remainder `C`. -/
def findMatchRecv (busId : Nat) (S : BusInteraction (Expression p)) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    Option (List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)))
  | _, [] => none
  | revB, R :: rest =>
      if decide (multConst R = some (-1)) && decide (R.busId = busId)
         && decide (S.payload = R.payload) then
        some (revB.reverse, R, rest)
      else findMatchRecv busId S (R :: revB) rest

/-- Refute `m` as an active same-address message on `busId` (the "between" region test). -/
def midRefuted (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p)) : Bool :=
  decide (m.busId ≠ busId) || decide (multConst m = some 0) || addrConstsNeq shape S m

/-- Refute `m` as an active same-address *send* on `busId` (the "before" region test: earliest-send). -/
def preRefuted (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p)) : Bool :=
  midRefuted shape busId S m ||
    (match multConst m with | some c => decide (c ≠ 1) | none => false)

theorem midRefuted_sound (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p))
    (h : midRefuted shape busId S m = true) (env : Variable → ZMod p)
    (hbid : (m.eval env).busId = busId) (hmne : (m.eval env).multiplicity ≠ 0)
    (hmaddr : shape.address (m.eval env) = shape.address (S.eval env)) : False := by
  unfold midRefuted at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact absurd hbid (of_decide_eq_true h)
  · exact hmne (m.multiplicity.constValue?_sound 0 (of_decide_eq_true h) env)
  · exact addrConstsNeq_sound shape S m h env hmaddr.symm

theorem preRefuted_sound (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p))
    (h : preRefuted shape busId S m = true) (env : Variable → ZMod p)
    (hbid : (m.eval env).busId = busId) (hmne : (m.eval env).multiplicity ≠ 0)
    (hmaddr : shape.address (m.eval env) = shape.address (S.eval env)) :
    (m.eval env).multiplicity ≠ 1 := by
  unfold preRefuted at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact (midRefuted_sound shape busId S m h env hbid hmne hmaddr).elim
  · cases hc : multConst m with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      have heval : (m.eval env).multiplicity = c := m.multiplicity.constValue?_sound c hc env
      rw [heval]
      exact of_decide_eq_true h

/-! ## Emitted byte checks

When the remaining system does not justify a byte slot of the dropped receive, the receive was
that limb's *only* byte guarantee — silently dropping it would widen the satisfying set (a real
soundness issue, not a proof artifact). The pass then *materializes* the obligation as an
explicit self-check `[e, e, 0, 1]` (multiplicity 1) on a `byteCheck` bus: still a net
bus-interaction win (2 dropped, 1 added), and later cancellations of the same chain are
justified by the emitted check. -/

/-- Certificate that an emitted check is a faithful carrier of `R`'s byte obligation: it sits on
    a `byteCheck` bus, has multiplicity 1 and self-check payload `[e, e, 0, 1]` where `e` is one
    of `R`'s declared byte-slot entries whose byte-ness `R`'s own accepted receive implies (a
    `slotBound` of at most 256 at that slot, at multiplicity `-1`, against `R`'s own constant
    pattern). -/
def emitOk (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat) (slots : List Nat)
    (R ck : BusInteraction (Expression p)) : Bool :=
  facts.byteCheck ck.busId &&
  decide (ck.multiplicity = (.const 1 : Expression p)) &&
  (match ck.payload with
   | [e1, e2, z, o] =>
     decide (e1 = e2) && decide (z = (.const 0 : Expression p)) &&
     decide (o = (.const 1 : Expression p)) &&
     slots.any (fun slot =>
       decide (R.payload[slot]? = some e1) &&
       (match facts.slotBound busId (-1) (R.payload.map Expression.constValue?) slot with
        | some b => decide (b ≤ 256)
        | none => false))
   | _ => false)

theorem emitOk_sound (bs : BusSemantics p) (facts : BusFacts p bs) (busId : Nat)
    (slots : List Nat) (R ck : BusInteraction (Expression p))
    (h : emitOk bs facts busId slots R ck = true)
    (hRbus : R.busId = busId) (hRmEv : ∀ env, (R.eval env).multiplicity = -1) :
    bs.isStateful ck.busId = false ∧
    (∀ env, bs.violatesConstraint (R.eval env) = false →
      bs.violatesConstraint (ck.eval env) = false) ∧
    (∀ env, bs.breaksInvariant (ck.eval env) = false) ∧
    (∀ v ∈ ck.vars, v ∈ R.vars) := by
  unfold emitOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hbc, hmultd⟩, hrest⟩ := h
  have hmult := of_decide_eq_true hmultd
  obtain ⟨hstateless, hbreak, hviol⟩ := facts.byteCheck_sound ck.busId hbc
  split at hrest
  · rename_i e1 e2 z o heq
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hrest
    obtain ⟨⟨⟨he12d, hzd⟩, hod⟩, hany⟩ := hrest
    have he12 := of_decide_eq_true he12d
    have hz := of_decide_eq_true hzd
    have ho := of_decide_eq_true hod
    obtain ⟨slot, hslotmem, hslot⟩ := List.any_eq_true.1 hany
    rw [Bool.and_eq_true] at hslot
    obtain ⟨hgetd, hbnd⟩ := hslot
    have hget := of_decide_eq_true hgetd
    -- the evaluated check is a literal self-check on `e1`'s value
    have hev : ∀ env, ck.eval env =
        { busId := ck.busId, multiplicity := (1 : ZMod p),
          payload := [e1.eval env, e1.eval env, (0 : ZMod p), (1 : ZMod p)] } := by
      intro env
      simp only [BusInteraction.eval, heq, hmult, hz, ho, List.map_cons, List.map_nil,
        Expression.eval, ← he12]
    -- `e1` sits in `R`'s payload
    have he1mem : e1 ∈ R.payload := by
      have := List.getElem?_eq_some_iff.mp hget
      obtain ⟨hlt, hgetE⟩ := this
      exact hgetE ▸ List.getElem_mem hlt
    refine ⟨hstateless, ?_, ?_, ?_⟩
    · -- the check is implied by `R`'s own accepted receive
      intro env hRok
      cases hb : facts.slotBound busId (-1) (R.payload.map Expression.constValue?) slot with
      | none => rw [hb] at hbnd; simp at hbnd
      | some b =>
        rw [hb] at hbnd
        dsimp only at hbnd
        have hgetEv : (R.eval env).payload[slot]? = some (e1.eval env) := by
          show (R.payload.map (fun e => e.eval env))[slot]? = some (e1.eval env)
          rw [List.getElem?_map, hget]; rfl
        have hfact : facts.slotBound (R.eval env).busId (R.eval env).multiplicity
            (R.payload.map Expression.constValue?) slot = some b := by
          rw [hRmEv env, show (R.eval env).busId = busId from hRbus]
          exact hb
        have hbyteE : (e1.eval env).val < 256 :=
          lt_of_lt_of_le
            (facts.slotBound_sound (R.eval env) (R.payload.map Expression.constValue?)
              slot b (e1.eval env) hfact (matches_evalPattern R.payload env) hRok hgetEv)
            (of_decide_eq_true hbnd)
        rw [hev env]
        exact (hviol (e1.eval env) 1).mpr hbyteE
    · -- the check breaks no invariant
      intro env
      rw [hev env]
      exact hbreak (e1.eval env)
    · -- the check's variables are `e1`'s, which are `R`'s
      intro v hv
      rw [BusInteraction.vars, List.mem_append] at hv
      have hvE : v ∈ e1.vars := by
        rcases hv with hm | hm
        · rw [hmult] at hm; simp [Expression.vars] at hm
        · rw [heq] at hm
          obtain ⟨e, he, hve⟩ := List.mem_flatMap.1 hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl
          · exact hve
          · rw [← he12] at hve; exact hve
          · rw [hz] at hve; simp [Expression.vars] at hve
          · rw [ho] at hve; simp [Expression.vars] at hve
      rw [BusInteraction.vars, List.mem_append]
      exact Or.inr (List.mem_flatMap.2 ⟨e1, he1mem, hvE⟩)
  · exact absurd hrest (by simp)

/-- The declared byte slots of `R` whose payload entries `rest` does not justify. -/
def unjustifiedSlots (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p))) (slots : List Nat)
    (R : BusInteraction (Expression p)) : List Nat :=
  slots.filter (fun slot =>
    match R.payload[slot]? with
    | some e => !byteJustified deep all bs facts rest e
    | none => false)

/-- The per-candidate check (address/multiplicity/payload of the pair, the between/before
    region tests, the emitted checks' certificates, plus the byte justification of the dropped
    receive's declared byte slots from the remaining interactions *including* the emitted
    checks). The split equation `cs.busInteractions = A ++ S :: B ++ R :: C` is *not* checked
    here — it is supplied separately (decided once for the chosen candidate) to avoid an O(n)
    whole-list comparison per candidate. The justification scans are the last conjuncts, so
    they only run for candidates that already match. -/
def checkCancel (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (shape : MemoryBusShape)
    (busId : Nat) (slots : List Nat)
    (A : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (B : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p))
    (C : List (BusInteraction (Expression p)))
    (checks : List (BusInteraction (Expression p))) : Bool :=
  decide (S.busId = busId) && decide (R.busId = busId) &&
  decide (multConst S = some 1) && decide (multConst R = some (-1)) &&
  decide (S.payload = R.payload) &&
  B.all (midRefuted shape busId S) &&
  A.all (preRefuted shape busId S) &&
  checks.all (emitOk bs facts busId slots R) &&
  recvSlotsJustified deep all bs facts (A ++ B ++ C ++ checks) slots R

/-- A passing `checkCancel` (with the split equation) yields `PassCorrect` via `dropPair_correct`. -/
theorem checkCancel_sound (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape)
    (slots : List Nat) (hslots : facts.recvByteSlots busId = some slots)
    (A : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (B : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p))
    (C : List (BusInteraction (Expression p)))
    (checks : List (BusInteraction (Expression p)))
    (hsplit : cs.busInteractions = A ++ S :: B ++ R :: C)
    (h : checkCancel deep cs.algebraicConstraints bs facts shape busId slots A S B R C checks
      = true) :
    PassCorrect cs { cs with busInteractions := A ++ B ++ C ++ checks } [] bs := by
  unfold checkCancel at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hSb, hRb⟩, hSm⟩, hRm⟩, hpay⟩, hmid⟩, hpre⟩, hemit⟩, hjust⟩ := h
  have hRmEv : ∀ env, (R.eval env).multiplicity = -1 :=
    fun env => R.multiplicity.constValue?_sound (-1) (of_decide_eq_true hRm) env
  refine dropPair_correct cs bs facts hp1 A B C S R busId shape hshape slots hslots checks
    (fun ck hck => emitOk_sound bs facts busId slots R ck
      (List.all_eq_true.mp hemit ck hck) (of_decide_eq_true hRb) hRmEv)
    (fun env hall hbus => recvSlotsJustified_sound deep cs.algebraicConstraints bs facts
      (A ++ B ++ C ++ checks) slots R hdeep hjust env hall hbus)
    hsplit
    (of_decide_eq_true hSb) (of_decide_eq_true hRb)
    (of_decide_eq_true hSm) (of_decide_eq_true hRm) (of_decide_eq_true hpay) ?_ ?_
  · intro env m0 hm0 hbid hmne hmaddr
    exact midRefuted_sound shape busId S m0 (List.all_eq_true.mp hmid m0 hm0) env hbid hmne hmaddr
  · intro env m0 hm0 hbid hmne hmaddr
    exact preRefuted_sound shape busId S m0 (List.all_eq_true.mp hpre m0 hm0) env hbid hmne hmaddr

/-- Fused left-to-right scan for the first droppable pair on `busId`: at each send `S` (accumulating
    the reversed prefix `revA`), find its matching receive and run the cheap `checkCancel`; the O(n)
    split-equation decide runs only when `checkCancel` passes. Stops at the first hit, so each pass
    invocation is linear (no eager materialization of all candidates). -/
def findCancelGo (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape)
    (slots : List Nat) (hslots : facts.recvByteSlots busId = some slots)
    (bcBus? : Option Nat)
    (revA : List (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) →
    Option (PassResult cs bs)
  | [] => none
  | S :: rest =>
    if decide (multConst S = some 1) && decide (S.busId = busId) then
      match findMatchRecv busId S [] rest with
      | some (B, R, C) =>
        let A := revA.reverse
        -- Cheap region tests first: only an otherwise-valid candidate pays the byte
        -- justification scan (`checkCancel` re-verifies everything).
        if B.all (midRefuted shape busId S) && A.all (preRefuted shape busId S) then
        -- Byte slots the remaining system does not justify are materialized as a single
        -- explicit self-check on the byte-check bus (more than one would not shrink the bus
        -- count and would stall the cancellation loop). One check suffices whenever all the
        -- unjustified slots carry the *same* expression (`byteJustified`'s carrier branch then
        -- justifies each of them); when they don't, or there is no byte-check bus, skip the
        -- certificate re-check — the justification scan is the expensive part.
        let unjust := unjustifiedSlots deep cs.algebraicConstraints bs facts (A ++ B ++ C)
          slots R
        let checks : List (BusInteraction (Expression p)) :=
          match bcBus?, unjust.filterMap (fun slot => R.payload[slot]?) with
          | some bcBus, e :: es =>
              if es.all (fun e' => e' == e) then
                [{ busId := bcBus, multiplicity := .const 1,
                   payload := [e, e, .const 0, .const 1] }]
              else []
          | _, _ => []
        if unjust.isEmpty || !checks.isEmpty then
        if hchk : checkCancel deep cs.algebraicConstraints bs facts shape busId slots
            A S B R C checks = true then
          if hsplit : cs.busInteractions = A ++ S :: B ++ R :: C then
            some ⟨{ cs with busInteractions := A ++ B ++ C ++ checks }, [],
                  checkCancel_sound cs bs facts hp1 deep hdeep busId shape hshape slots hslots
                    A S B R C checks hsplit hchk⟩
          else findCancelGo cs bs facts hp1 deep hdeep busId shape hshape slots hslots bcBus?
            (S :: revA) rest
        else findCancelGo cs bs facts hp1 deep hdeep busId shape hshape slots hslots bcBus?
          (S :: revA) rest
        else findCancelGo cs bs facts hp1 deep hdeep busId shape hshape slots hslots bcBus?
          (S :: revA) rest
        else findCancelGo cs bs facts hp1 deep hdeep busId shape hshape slots hslots bcBus?
          (S :: revA) rest
      | none => findCancelGo cs bs facts hp1 deep hdeep busId shape hshape slots hslots bcBus?
          (S :: revA) rest
    else findCancelGo cs bs facts hp1 deep hdeep busId shape hshape slots hslots bcBus?
        (S :: revA) rest

/-- Search one declared bus for a droppable pair. -/
def findCancelForBus (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape)
    (slots : List Nat) (hslots : facts.recvByteSlots busId = some slots)
    (bcBus? : Option Nat) :
    Option (PassResult cs bs) :=
  findCancelGo cs bs facts hp1 deep hdeep busId shape hshape slots hslots bcBus? []
    cs.busInteractions

/-- Search all declared buses. -/
def findCancel (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (bcBus? : Option Nat) :
    List Nat → Option (PassResult cs bs)
  | [] => none
  | busId :: rest =>
    match hshape : facts.memShape busId with
    | some shape =>
      match hslots : facts.recvByteSlots busId with
      | some slots =>
        match findCancelForBus cs bs facts hp1 deep hdeep busId shape hshape slots hslots
            bcBus? with
        | some r => some r
        | none => findCancel cs bs facts hp1 deep hdeep bcBus? rest
      | none => findCancel cs bs facts hp1 deep hdeep bcBus? rest
    | none => findCancel cs bs facts hp1 deep hdeep bcBus? rest

/-- Drop one matched consecutive send/receive pair on a declared memory bus with a
    `recvByteSlots` contract — justifying the dropped receive's byte obligation from the
    remaining interactions (shallow bus-fact bounds, or the deep one-hot-selection analysis on
    prime `p`), or materializing it as one explicit byte check on a `byteCheck` bus already
    present in the system. The cleanup loop iterates it to cancel a whole access chain. -/
def busPairCancelPass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    let busIds := (cs.busInteractions.map (fun bi => bi.busId)).dedup
    let deep : Bool := decide p.Prime
    match findCancel cs bs facts hp1 deep (fun h => of_decide_eq_true h)
        (busIds.find? facts.byteCheck) busIds with
    | some r => r
    | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
