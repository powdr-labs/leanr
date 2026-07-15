import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.MemoryBusDrop

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
  predicate (`admissible_dropPair`), provided the *shield* condition on the before-region `A`
  holds — every active same-address send in `A` is followed by an active same-address receive in
  `A` (`shieldOk`; strictly weaker than "`S` is the earliest active same-address send"). Otherwise
  the removal could expose a fresh consecutive send→receive pair with mismatched payloads; the
  trailing receive shields every earlier send, so none is exposed. This admits access chains led
  by an unmatched boundary store (the common read-modify-write shape). Any emitted check is
  *implied* by the dropped receive's own accepted message, so real traces satisfy it. -/

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
    let ln := LinExpr.norm l
    match ln.terms with
    | [(v, a)] =>
      -- `x` is pinned to the (re-checked) root; it must be a byte
      decide (v = x) && decide (a ≠ 0) &&
        decide (a * (-(a⁻¹ * ln.const)) + ln.const = 0) &&
        decide ((-(a⁻¹ * ln.const) : ZMod p).val < 256)
    | [(v1, a1), (v2, a2)] =>
      -- `x = other` (opposite coefficients, no constant); the other side is byte-bounded
      decide (ln.const = 0) &&
      (if v1 = x then
        decide (a2 = -a1) && decide (a1 ≠ 0) && byteVars.contains v2
       else if v2 = x then
        decide (a1 = -a2) && decide (a2 ≠ 0) && byteVars.contains v1
       else false)
    | _ => false

/-- The variables of `c` (other than `x`) with a proven byte bound from the remaining
    interactions — computed once per candidate, not once per enumeration point.

    The remaining interactions are consulted through a *witness lookup* `wits`: a function
    returning, per variable, a short list of interactions to try (`findVarBound` scans just
    those). Instantiating `wits := fun _ => rest` recovers the plain full-scan behaviour; the
    pass instead passes a per-sweep hash-indexed witness map (`ByteWits`), turning the
    per-candidate O(#interactions) rescan into an O(1) lookup. Soundness only ever needs
    `wits v ⊆ rest` (hypothesis `hwits` in the `_sound` lemmas). -/
def deepByteVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : Variable → List (BusInteraction (Expression p))) (x : Variable) (c : Expression p) :
    List Variable :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filter (fun v =>
    match findVarBound bs facts (wits v) v with
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
    (wits : Variable → List (BusInteraction (Expression p))) (x : Variable) (c : Expression p) :
    Bool :=
  let enum := deepEnumDoms domCs x c
  if (c.vars.dedup.filter (fun v => v ≠ x)).length ≤ maxDeepVars &&
      (enum.map (fun vd => vd.2.length)).prod ≤ maxDeepPoints then
    (assignments enum).all
      (pointByteOk x c (deepByteVars bs facts wits x c) (enum.map Prod.fst))
  else false

/-- Deep byte justification for `x`: one of the first `maxDeepConstraints` constraints
    mentioning `x` (the caller passes them as `cands`, e.g. from a prebuilt variable→constraints
    index) pins it via `deepBoundOk`. `domCs` are the single-variable constraints (the only ones
    `findDomainAlg` can use), likewise precomputed by the caller. -/
def deepByteJustified (domCs cands : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (wits : Variable → List (BusInteraction (Expression p))) (x : Variable) : Bool :=
  (cands.take maxDeepConstraints).any (fun c => deepBoundOk domCs bs facts wits x c)

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
    (wits : Variable → List (BusInteraction (Expression p))) (x : Variable) (c : Expression p)
    (h : deepBoundOk domCs bs facts wits x c = true) (env : Variable → ZMod p)
    (hdom : ∀ c' ∈ domCs, c'.eval env = 0) (hc0 : c.eval env = 0)
    (hbus : ∀ v, ∀ bi ∈ wits v, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (env x).val < 256 := by
  unfold deepBoundOk at h
  simp only [] at h
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
  have hbyteVars : ∀ v ∈ deepByteVars bs facts wits x c, (env v).val < 256 := by
    intro v hv
    unfold deepByteVars at hv
    obtain ⟨hv1, hv2⟩ := List.mem_filter.mp hv
    cases hb : findVarBound bs facts (wits v) v with
    | none => rw [hb] at hv2; simp at hv2
    | some b =>
      rw [hb] at hv2
      dsimp only at hv2
      exact lt_of_lt_of_le (findVarBound_sound bs facts (wits v) v b hb env (hbus v))
        (of_decide_eq_true hv2)
  -- `env`'s restriction to the enumerated domains is one of the checked points
  have hmem : (deepEnumDoms domCs x c).map (fun vd => (vd.1, env vd.1))
      ∈ assignments (deepEnumDoms domCs x c) :=
    mem_assignments _ env hdomsound
  have hpoint := List.all_eq_true.mp h _ hmem
  refine pointByteOk_sound x c (deepByteVars bs facts wits x c)
    ((deepEnumDoms domCs x c).map Prod.fst)
    ((deepEnumDoms domCs x c).map (fun vd => (vd.1, env vd.1))) hpoint env ?_
    hc0 hbyteVars
  intro y hy
  exact envOf_map (deepEnumDoms domCs x c) env y (List.contains_iff_mem.mp hy)

theorem deepByteJustified_sound [Fact p.Prime] [NeZero p] (all domCs cands : List (Expression p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : Variable → List (BusInteraction (Expression p))) (x : Variable)
    (hdomCs : ∀ c ∈ domCs, c ∈ all) (hcands : ∀ c ∈ cands, c ∈ all)
    (h : deepByteJustified domCs cands bs facts wits x = true) (env : Variable → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ v, ∀ bi ∈ wits v, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (env x).val < 256 := by
  obtain ⟨c, hc, hck⟩ := List.any_eq_true.1 h
  have hc' : c ∈ all := hcands c (List.mem_of_mem_take hc)
  exact deepBoundOk_sound domCs bs facts wits x c hck env
    (fun c' hc'' => hall c' (hdomCs c' hc'')) (hall c hc') hbus

/-- Evaluate the single-variable expression `e` with its variable fixed to `d` and check the
    result is a byte constant. `constValue? = none` (so `false`) whenever the fold is not a
    constant — i.e. `e` still mentions a variable other than the one fixed — so this only ever
    succeeds for a genuinely single-variable `e`. -/
def exprPointByte (e : Expression p) (x : Variable) (d : ZMod p) : Bool :=
  match (e.substF (fun v => if v = x then some (.const d) else none)).fold.constValue? with
  | some c => decide (c.val < 256)
  | none => false

/-- Is `e` a byte because its single variable `x` ranges over a small constraint-derived finite
    domain (`findDomainAlg`) at every point of which `e` evaluates to a byte? Generalises the raw
    byte-variable case to expressions like the sign-extension limb `255·b` (b boolean, values
    `{0, 255}`) that a signed memory load leaves in a word's high limbs. -/
def domainByteJustified (domCs : List (Expression p)) (e : Expression p) : Bool :=
  match e.singleVarAux with
  | some (some x) =>
    match findDomainAlg domCs x with
    | some d => decide (d.length ≤ maxDeepDomain) && d.all (exprPointByte e x)
    | none => false
  | _ => false

theorem domainByteJustified_sound [Fact p.Prime] (domCs : List (Expression p)) (e : Expression p)
    (h : domainByteJustified domCs e = true) (env : Variable → ZMod p)
    (hdom : ∀ c ∈ domCs, c.eval env = 0) :
    (e.eval env).val < 256 := by
  unfold domainByteJustified at h
  cases hsv : e.singleVarAux with
  | none => rw [hsv] at h; simp at h
  | some ov =>
    cases ov with
    | none => rw [hsv] at h; simp at h
    | some x =>
      rw [hsv] at h
      dsimp only at h
      cases hfd : findDomainAlg domCs x with
      | none => rw [hfd] at h; simp at h
      | some d =>
        rw [hfd, Bool.and_eq_true] at h
        obtain ⟨_, hall⟩ := h
        have hmem : env x ∈ d := findDomainAlg_sound domCs x d hfd env hdom
        have hpt : exprPointByte e x (env x) = true := List.all_eq_true.mp hall _ hmem
        unfold exprPointByte at hpt
        cases hcv : (e.substF (fun v => if v = x then some (.const (env x)) else none)).fold.constValue?
          with
        | none => rw [hcv] at hpt; simp at hpt
        | some c =>
          rw [hcv] at hpt
          have hbyte : c.val < 256 := of_decide_eq_true hpt
          have hfoldeval :
              (e.substF (fun v => if v = x then some (.const (env x)) else none)).fold.eval env = c :=
            Expression.constValue?_sound _ c hcv env
          have hsubeval :
              (e.substF (fun v => if v = x then some (.const (env x)) else none)).eval env
                = e.eval env := by
            rw [Expression.eval_substF, envF_eq_self]
            intro y t hy
            by_cases hk : y = x
            · subst y
              simp only [] at hy
              injection hy with hy'
              subst hy'
              rfl
            · simp only [if_neg hk] at hy; exact absurd hy (by simp)
          rw [Expression.fold_eval, hsubeval] at hfoldeval
          rw [hfoldeval]; exact hbyte

/-- Is `e` provably a byte under every assignment satisfying the remaining system? Either a
    constant `< 256`, a variable with a proven bus-fact bound `≤ 256` derived from the remaining
    interactions (e.g. another receive of the same word, or an explicit byte-check
    lookup), or — when `deep` is set (prime `p` only) — a variable a constraint pins to a byte
    on every point of its selector flags' finite domains (`deepBoundOk`), or a single-variable
    expression whose variable's finite domain makes `e` a byte at every point
    (`domainByteJustified`, e.g. the `255·b` sign-extension limbs).

    Parameterized form: the remaining interactions are consulted through the witness lookup
    `wits` (see `deepByteVars`), the single-variable constraints `domCs` and the per-variable
    candidate constraints `candsOf` are precomputed by the caller (once per pass invocation,
    instead of two full filters of the constraint list per query). -/
def byteJustifiedW (deep : Bool) (domCs : List (Expression p))
    (candsOf : Variable → List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits : Variable → List (BusInteraction (Expression p)))
    (e : Expression p) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < 256)
  | none =>
    (match e with
     | .var x =>
       (match findVarBound bs facts (wits x) x with
        | some bound => decide (bound ≤ 256)
        | none => false) ||
       (deep && deepByteJustified domCs (candsOf x) bs facts wits x)
     | _ => false) ||
    (deep && domainByteJustified domCs e)

/-- The plain full-scan form (used by the coda's `RedundantByteDrop`): witness lookup and
    precomputed constraint lists instantiated with the naive per-query filters. -/
def byteJustified (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p)))
    (e : Expression p) : Bool :=
  byteJustifiedW deep (all.filter Expression.isSingleVar)
    (fun x => all.filter (Expression.containsVar x)) bs facts (fun _ => rest) e

theorem byteJustifiedW_sound (deep : Bool) (all domCs : List (Expression p))
    (candsOf : Variable → List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p)))
    (wits : Variable → List (BusInteraction (Expression p))) (e : Expression p)
    (hdeep : deep = true → p.Prime)
    (hdomCs : ∀ c ∈ domCs, c ∈ all) (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ all)
    (hwits : ∀ v, ∀ bi ∈ wits v, bi ∈ rest)
    (h : byteJustifiedW deep domCs candsOf bs facts wits e = true) (env : Variable → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ rest, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (e.eval env).val < 256 := by
  have hbusW : ∀ v, ∀ bi ∈ wits v, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false :=
    fun v bi hbi => hbus bi (hwits v bi hbi)
  unfold byteJustifiedW at h
  cases hc : e.constValue? with
  | some c =>
    rw [hc] at h
    dsimp only at h
    rw [e.constValue?_sound c hc env]
    exact of_decide_eq_true h
  | none =>
    rw [hc] at h
    dsimp only at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · -- variable path (bus-fact bound or deep selector-flag justification)
      cases e with
      | var x =>
        dsimp only at h
        show (env x).val < 256
        rcases Bool.or_eq_true _ _ |>.mp h with h' | h'
        · cases hb : findVarBound bs facts (wits x) x with
          | some bound =>
            rw [hb] at h'
            dsimp only at h'
            exact lt_of_lt_of_le (findVarBound_sound bs facts (wits x) x bound hb env (hbusW x))
              (of_decide_eq_true h')
          | none => rw [hb] at h'; simp at h'
        · rw [Bool.and_eq_true] at h'
          haveI : Fact p.Prime := ⟨hdeep h'.1⟩
          haveI : NeZero p := ⟨(hdeep h'.1).ne_zero⟩
          exact deepByteJustified_sound all domCs (candsOf x) bs facts wits x hdomCs (hcands x)
            h'.2 env hall hbusW
      | const n => simp at h
      | add a b => simp at h
      | mul a b => simp at h
    · -- single-variable finite-domain expression path
      rw [Bool.and_eq_true] at h
      haveI : Fact p.Prime := ⟨hdeep h.1⟩
      exact domainByteJustified_sound domCs e h.2 env
        (fun c' hc' => hall c' (hdomCs c' hc'))

theorem byteJustified_sound (deep : Bool) (all : List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p))) (e : Expression p)
    (hdeep : deep = true → p.Prime)
    (h : byteJustified deep all bs facts rest e = true) (env : Variable → ZMod p)
    (hall : ∀ c' ∈ all, c'.eval env = 0)
    (hbus : ∀ bi ∈ rest, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) :
    (e.eval env).val < 256 :=
  byteJustifiedW_sound deep all (all.filter Expression.isSingleVar)
    (fun x => all.filter (Expression.containsVar x)) bs facts rest (fun _ => rest) e hdeep
    (fun _ hc => List.mem_of_mem_filter hc) (fun _ _ hc => List.mem_of_mem_filter hc)
    (fun _ _ hbi => hbi) h env hall hbus

/-- Are all of `R`'s payload entries at the declared byte slots justified (through the witness
    lookup `wits` and precomputed `domCs`/`candsOf`, see `byteJustifiedW`)? -/
def recvSlotsJustified (deep : Bool) (domCs : List (Expression p))
    (candsOf : Variable → List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits : Variable → List (BusInteraction (Expression p)))
    (slots : List Nat) (R : BusInteraction (Expression p)) : Bool :=
  slots.all (fun slot =>
    match R.payload[slot]? with
    | some e => byteJustifiedW deep domCs candsOf bs facts wits e
    | none => true)

theorem recvSlotsJustified_sound (deep : Bool) (all domCs : List (Expression p))
    (candsOf : Variable → List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (rest : List (BusInteraction (Expression p)))
    (wits : Variable → List (BusInteraction (Expression p))) (slots : List Nat)
    (R : BusInteraction (Expression p)) (hdeep : deep = true → p.Prime)
    (hdomCs : ∀ c ∈ domCs, c ∈ all) (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ all)
    (hwits : ∀ v, ∀ bi ∈ wits v, bi ∈ rest)
    (h : recvSlotsJustified deep domCs candsOf bs facts wits slots R = true)
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
    exact byteJustifiedW_sound deep all domCs candsOf bs facts rest wits e hdeep
      hdomCs hcands hwits hcheck env hall hbus

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

/-- A split of the active∧stateful evaluated messages of `A` lifts to a syntactic split of `A`
    whose evaluated tail is the split's tail (via `filter_split` + `map_split`). Lets the pass's
    *syntactic* shield discharge the `admissible_dropPair` shield stated over `activeStatefulMsgs`. -/
theorem activeStatefulMsgs_split (bs : BusSemantics p) (env : Variable → ZMod p)
    (A : List (BusInteraction (Expression p))) (A₁ A₂ : List (BusInteraction (ZMod p)))
    (Sx : BusInteraction (ZMod p)) (h : activeStatefulMsgs bs env A = A₁ ++ Sx :: A₂) :
    ∃ (A_pre : List (BusInteraction (Expression p))) (m0 : BusInteraction (Expression p))
      (A_suf : List (BusInteraction (Expression p))),
      A = A_pre ++ m0 :: A_suf ∧ m0.eval env = Sx ∧ activeStatefulMsgs bs env A_suf = A₂ := by
  have h' : (A.map (fun bi => bi.eval env)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) = A₁ ++ Sx :: A₂ := h
  have hfs := filter_split (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) Sx
      (A.map (fun bi => bi.eval env)) A₁ A₂ h'
  obtain ⟨M_pre, M_suf, hmapeq, _, hMsuf⟩ := hfs
  have hms := map_split (fun bi => bi.eval env) Sx A M_pre M_suf hmapeq
  obtain ⟨A_pre, m0, A_suf, hAeq, _, hm0, hAsuf⟩ := hms
  refine ⟨A_pre, m0, A_suf, hAeq, hm0, ?_⟩
  show (A_suf.map (fun bi => bi.eval env)).filter
    (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) = A₂
  rw [hAsuf]; exact hMsuf

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
    (pattern : List (Option (ZMod p))) (slots : List Nat)
    (hslots : facts.recvByteSlots busId pattern = some slots)
    (hRmatch : ∀ env, Matches (R.eval env).payload pattern)
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
    (hpayEval : ∀ (env : Variable → ZMod p), (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) →
      (S.eval env).payload = (R.eval env).payload)
    (hmidEval : ∀ (env : Variable → ZMod p), (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) →
        ∀ m0 ∈ B, (m0.eval env).busId = busId →
        (m0.eval env).multiplicity ≠ 0 →
        shape.address (m0.eval env) = shape.address (S.eval env) → False)
    (hpreEval : ∀ (env : Variable → ZMod p), (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) →
        ∀ (A_pre : List (BusInteraction (Expression p)))
        (m0 : BusInteraction (Expression p)) (A_suf : List (BusInteraction (Expression p))),
        A = A_pre ++ m0 :: A_suf → (m0.eval env).busId = busId →
        (m0.eval env).multiplicity ≠ 0 →
        shape.address (m0.eval env) = shape.address (S.eval env) →
        (m0.eval env).multiplicity = 1 →
        ∃ Rp ∈ A_suf, (Rp.eval env).busId = busId ∧ (Rp.eval env).multiplicity ≠ 0 ∧
          shape.address (Rp.eval env) = shape.address (S.eval env) ∧
          (Rp.eval env).multiplicity = -1) :
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
  have haddrEv : ∀ env, (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) →
      shape.address (S.eval env) = shape.address (R.eval env) := fun env hcon => by
    simp only [MemoryBusShape.address, hpayEval env hcon]
  -- Membership: the kept core `A ++ B ++ C` is among `cs`'s interactions.
  have hmem_core : ∀ bi, bi ∈ A ++ B ++ C → bi ∈ cs.busInteractions := by
    intro bi hbi
    rw [hsplit]
    simp only [List.mem_append, List.mem_cons] at hbi ⊢; tauto
  -- Re-adding the dropped pair imposes no obligation: the send never violates (the
  -- `recvByteSlots` contract), and the receive's byte slots are justified from the remaining
  -- interactions, whose obligations hold under any `out`-satisfying assignment.
  have hnvS : ∀ env, bs.violatesConstraint (S.eval env) = false := fun env =>
    (facts.recvByteSlots_sound busId pattern slots hslots (S.eval env)
      (show (S.eval env).busId = busId from hSbus)).1 (hSmEv env)
  have hnvR : ∀ env, out.satisfies bs env → bs.violatesConstraint (R.eval env) = false := by
    intro env hsat
    refine (facts.recvByteSlots_sound busId pattern slots hslots (R.eval env)
      (show (R.eval env).busId = busId from hRbus)).2 (hRmEv env) (hRmatch env)
      (hbyte env (fun c hc => hsat.1 c hc) ?_)
    intro bi hbi hne
    exact hsat.2 bi (by rw [houtb]; exact hbi) hne
  -- Side effects are `≈`-equal (the pair contributes `0` net; the checks are stateless). The
  -- evaluated-payload equality is discharged from the constraints, which hold in **both**
  -- refinement directions — a drop leaves `algebraicConstraints` untouched.
  have hSE : ∀ env, (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) →
      cs.sideEffects bs env ≈ out.sideEffects bs env := by
    intro env hcon
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
      (hpayEval env hcon)
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
  -- `admissible` is preserved (completeness; the constraint satisfaction feeds the two-root
  -- address-disequality certificates inside the region tests).
  have hadm_cs_out : ∀ env, cs.admissible bs env →
      (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) → out.admissible bs env := by
    intro env hadm hcon
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
      hSbus hRbus (hSmEv env) (hRmEv env) (haddrEv env hcon) ?_ ?_ hadm'
    · intro m hm hbid hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := mem_activeStatefulMsgs bs env B m hm
      exact hmidEval env hcon m0 hm0 hbid hmne hmaddr
    · -- shield: lift the split of `activeStatefulMsgs A` to a syntactic split of `A`, apply the
      -- syntactic shield `hpreEval`, then push the resulting receive back into the filtered tail.
      intro A₁ Sx A₂ hAsplit hbid hne haddr hmult
      obtain ⟨A_pre, m0, A_suf, hAeq, hm0, hAsuf⟩ :=
        activeStatefulMsgs_split bs env A A₁ A₂ Sx hAsplit
      subst hm0
      obtain ⟨Rp, hRpmem, hRpbid, hRpne, hRpaddr, hRpmult⟩ :=
        hpreEval env hcon A_pre m0 A_suf hAeq hbid hne haddr hmult
      refine ⟨Rp.eval env, ?_, hRpbid, hRpne, hRpaddr, hRpmult⟩
      rw [← hAsuf]
      unfold activeStatefulMsgs
      refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨Rp, hRpmem, rfl⟩, ?_⟩
      rw [show bs.isStateful (Rp.eval env).busId = true from by rw [hRpbid]; exact hStateful]
      rw [Bool.and_true, decide_eq_true_eq]; exact hRpne
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
    (fun env hsat => ⟨env, hsat_out_cs env hsat, BusState.equiv_symm (hSE env hsat.1)⟩)
    (fun hinv env hsat bi hbi => by
      rcases List.mem_append.1 (by rw [houtb] at hbi; exact hbi) with hbi' | hbi'
      · exact hinv env (hsat_out_cs env hsat) bi (hmem_core bi hbi')
      · exact fun _ => (hchecks bi hbi').2.2.1 env)
    hsub
    (fun env hadm hsat => ⟨hsat_cs_out env hsat, hadm_cs_out env hadm hsat.1, hSE env hsat.1⟩)

/-! ## The pass: detect and drop matched pairs -/

/-! ### Hash-indexed receive lookup

`findCancelGo` probed every send against the whole remaining list, structurally comparing
payloads — ~90% of the pass's runtime, repeated once per dropped pair. The candidate receives
(constant `-1` multiplicity, on the bus) are instead indexed **once per invocation** by a
structural payload hash; a send probe is then a hash lookup plus an exact payload comparison on
the (rare) hash hits. Hash inequality proves payload inequality, and hits are re-verified
structurally, so exactly the same first matching receive is found — the pass's output is
unchanged, and its correctness never depended on the search (the accepted candidate is
re-verified by `checkCancel` and the decided split equation). -/

/-- Structural hash of a payload (order-sensitive). -/
def payloadHash (pl : List (Expression p)) : UInt64 :=
  pl.foldl (fun h e => mixHash h e.structHash) 7

/-- Structural hash of the address slots of a payload (order-sensitive over
    `shape.addressFields`) — the receive-index key for entailed payload matching: value slots
    may differ syntactically, addresses must not. -/
def addrHash (shape : MemoryBusShape) (pl : List (Expression p)) : UInt64 :=
  shape.addressFields.foldl (fun h slot => mixHash h ((pl[slot]?).elim 5 Expression.structHash)) 7

/-- Positions (ascending) of the candidate receives (constant `-1` multiplicity) on **every**
    memory-shaped bus, keyed by the bus id mixed with the payload hash — one build serves the
    whole sweep, instead of one O(#interactions) rebuild per bus. In the cycle
    (`aggressive = false`) the payload part of the key is the exact payload hash — tiny buckets,
    cheap syntactic probes. In the coda (`aggressive = true`) it is the *address-slot* hash
    (`addrHash`, computed against the bus's own declared shape), a coarsening under which
    entailed-equal value slots still land in the probed bucket while addresses must agree
    syntactically to be found at all. Purely heuristic: probes re-verify the bus id and payload,
    so a hash collision can only cost time, never a wrong drop. -/
def recvIndexAll {bs : BusSemantics p} (facts : BusFacts p bs) (aggressive : Bool)
    (arr : Array (BusInteraction (Expression p))) :
    Std.HashMap UInt64 (List Nat) :=
  (arr.toList.zipIdx).foldr (fun bij m =>
    if decide (multConst bij.1 = some (-1)) then
      match facts.memShape bij.1.busId with
      | some shape =>
        let h := mixHash (hash bij.1.busId)
          (if aggressive then addrHash shape bij.1.payload else payloadHash bij.1.payload)
        m.insert h (bij.2 :: m.getD h [])
      | none => m
    else m) ∅

/-- Every element of a two-point split other than the two distinguished ones lies in the
    remaining region. -/
theorem mem_core_of_ne {α : Type _} {l A B C : List α} {S R x : α}
    (hsplit : l = A ++ S :: B ++ R :: C) (hx : x ∈ l) (hxS : x ≠ S) (hxR : x ≠ R) :
    x ∈ A ++ B ++ C := by
  subst hsplit
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  tauto

/-! ### The per-invocation candidate-constraint index

`deepByteJustified` consulted the constraint list through two full filters per queried variable
(`all.filter Expression.isSingleVar` and `all.filter (containsVar x) |>.take maxDeepConstraints`).
Both are precomputed once per pass invocation — the constraints never change across the drops of
one invocation (`cancelLoop` transports the thunks) — as the plain `domCs` list and this
proof-carrying variable→constraints index (first `maxDeepConstraints` per variable, in list
order, exactly what the filters produced). -/

structure VarCsIdx (p : ℕ) (constraints : List (Expression p)) where
  map : Std.HashMap Variable (List (Expression p))
  sound : ∀ (x : Variable) (l : List (Expression p)),
    map[x]? = some l → ∀ c ∈ l, c ∈ constraints

namespace VarCsIdx

variable {constraints : List (Expression p)}

def empty : VarCsIdx p constraints where
  map := ∅
  sound := by
    intro x l h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)

/-- Append `c` at the end of `x`'s bucket (so buckets stay in traversal order), capped. -/
def insertC (I : VarCsIdx p constraints) (x : Variable) (c : Expression p)
    (hc : c ∈ constraints) : VarCsIdx p constraints :=
  match hb : I.map[x]? with
  | none =>
    { map := I.map.insert x [c],
      sound := by
        intro y l hl c' hc'
        rw [Std.HashMap.getElem?_insert] at hl
        by_cases hxy : (x == y) = true
        · rw [if_pos hxy] at hl
          have hle : [c] = l := by simpa using hl
          rw [← hle, List.mem_singleton] at hc'
          exact hc' ▸ hc
        · rw [if_neg hxy] at hl
          exact I.sound y l hl c' hc' }
  | some old =>
    if old.length < maxDeepConstraints then
      { map := I.map.insert x (old ++ [c]),
        sound := by
          intro y l hl c' hc'
          rw [Std.HashMap.getElem?_insert] at hl
          by_cases hxy : (x == y) = true
          · rw [if_pos hxy] at hl
            have hle : old ++ [c] = l := by simpa using hl
            rw [← hle, List.mem_append] at hc'
            rcases hc' with h' | h'
            · exact I.sound x old hb c' h'
            · rw [List.mem_singleton] at h'
              exact h' ▸ hc
          · rw [if_neg hxy] at hl
            exact I.sound y l hl c' hc' }
    else I

/-- Record `c` under each of its variables. -/
def addConstraint (I : VarCsIdx p constraints) (c : Expression p)
    (hc : c ∈ constraints) : VarCsIdx p constraints :=
  c.vars.dedup.foldl (fun I x => I.insertC x c hc) I

def addAll : VarCsIdx p constraints → (pending : List (Expression p)) →
    (∀ c ∈ pending, c ∈ constraints) → VarCsIdx p constraints
  | I, [], _ => I
  | I, c :: rest, hmem =>
    addAll (I.addConstraint c (hmem c (List.mem_cons_self ..))) rest
      (fun c' h => hmem c' (List.mem_cons_of_mem _ h))

def build (constraints : List (Expression p)) : VarCsIdx p constraints :=
  addAll empty constraints (fun _ h => h)

def lookup (I : VarCsIdx p constraints) (x : Variable) : List (Expression p) :=
  (I.map[x]?).getD []

theorem lookup_mem (I : VarCsIdx p constraints) (x : Variable) :
    ∀ c ∈ I.lookup x, c ∈ constraints := by
  intro c hc
  unfold lookup at hc
  cases hb : I.map[x]? with
  | none => rw [hb] at hc; simp at hc
  | some l =>
    rw [hb] at hc
    exact I.sound x l hb c hc

end VarCsIdx

/-! ### The split equation, by construction

The scan walks the interaction *array*; a drop certificate needs the list-level split
`cs.busInteractions = A ++ S :: B ++ R :: C`. Deciding that equation at runtime is an
O(#interactions) deep structural comparison per accepted drop; instead it follows by
construction from the way `A`/`B`/`C` are extracted. -/

/-- A list splits at two positions into take/drop segments, nested-parenthesization form. -/
theorem list_split_two_aux {α : Type _} {l : List α} {i j : Nat} (hij : i < j)
    (hj : j < l.length) :
    l = l.take i ++ l[i]'(Nat.lt_trans hij hj) ::
      ((l.drop (i + 1)).take (j - (i + 1)) ++ (l[j]'hj :: l.drop (j + 1))) := by
  have hi : i < l.length := Nat.lt_trans hij hj
  conv_lhs => rw [← List.take_append_drop i l]
  congr 1
  rw [List.drop_eq_getElem_cons hi]
  congr 1
  conv_lhs => rw [← List.take_append_drop (j - (i + 1)) (l.drop (i + 1))]
  congr 1
  rw [List.drop_drop]
  have hjj : i + 1 + (j - (i + 1)) = j := by omega
  rw [hjj, List.drop_eq_getElem_cons hj]

/-- A list splits at two positions into take/drop segments (the `A ++ S :: B ++ R :: C`
    parenthesization the drop certificate uses). -/
theorem list_split_two {α : Type _} {l : List α} {i j : Nat} (hij : i < j) (hj : j < l.length) :
    l = l.take i ++ l[i]'(Nat.lt_trans hij hj) ::
      (l.drop (i + 1)).take (j - (i + 1)) ++ l[j]'hj :: l.drop (j + 1) := by
  conv_lhs => rw [list_split_two_aux hij hj]
  simp [List.append_assoc, List.cons_append]

/-- The array-extract form of `list_split_two`: the segments the scan materializes recompose to
    the underlying list, so the split equation holds with no runtime comparison. -/
theorem split_of_extracts {α : Type _} {l : List α} {arr : Array α}
    (harr : arr = l.toArray) {i j : Nat} (hij : i < j) (hi : i < arr.size) {R : α}
    (hR : arr[j]? = some R) :
    l = (arr.extract 0 i).toList ++ arr[i] ::
        (arr.extract (i + 1) j).toList ++ R :: (arr.extract (j + 1) arr.size).toList := by
  subst harr
  obtain ⟨hj, hRj⟩ := Array.getElem?_eq_some_iff.mp hR
  have hjl : j < l.length := by simpa using hj
  subst hRj
  simp only [Array.toList_extract, List.extract_eq_take_drop, List.getElem_toArray,
    List.size_toArray, List.drop_zero, Nat.sub_zero]
  rw [List.take_of_length_le (l := l.drop (j + 1)) (by simp)]
  exact list_split_two hij hjl

/-! ### Constraint-entailed payload matching

A send and its matching receive can carry *syntactically different* value slots that the
algebraic constraints force equal — e.g. `busUnify` adds the slot equality
`read_data − ((1−flag)·srd0 + flag·srd1) = 0` but Gauss cannot apply it within the degree
bound, so the payloads never become syntactically identical. The pair still cancels: the
net-zero side-effect argument needs only *evaluated* payload equality, which the constraints
force — and constraint satisfaction is available in **both** refinement directions because a
drop leaves `algebraicConstraints` untouched. `EqConstraintMap` indexes the normalized
constraints by structural hash, so a slot difference is decided by one `normalize` and a hash
probe (mirroring `TwoRootMap`'s once-per-invocation, proof-carrying design). -/

/-- Normalized constraint forms, bucketed by structural hash; every bucket entry is witnessed
    as the normalization of an actual constraint. -/
structure EqConstraintMap (p : ℕ) (constraints : List (Expression p)) where
  map : Std.HashMap UInt64 (List (Expression p))
  sound : ∀ (h : UInt64) (ns : List (Expression p)), map[h]? = some ns →
    ∀ n ∈ ns, ∃ c ∈ constraints, c.normalize = n

namespace EqConstraintMap

variable {constraints : List (Expression p)}

def empty : EqConstraintMap p constraints where
  map := ∅
  sound := by
    intro h ns hns
    rw [Std.HashMap.getElem?_empty] at hns
    exact absurd hns (by simp)

/-- Prepend a witnessed normalized form to its hash bucket. -/
def insertNorm (M : EqConstraintMap p constraints) (n : Expression p)
    (hw : ∃ c ∈ constraints, c.normalize = n) : EqConstraintMap p constraints where
  map := M.map.insert n.structHash (n :: (M.map[n.structHash]?).getD [])
  sound := by
    intro h ns hns m hm
    rw [Std.HashMap.getElem?_insert] at hns
    by_cases hh : (n.structHash == h) = true
    · rw [if_pos hh] at hns
      have hns' : n :: (M.map[n.structHash]?).getD [] = ns := by simpa using hns
      rw [← hns'] at hm
      rcases List.mem_cons.1 hm with rfl | hm'
      · exact hw
      · cases hb : M.map[n.structHash]? with
        | none => rw [hb] at hm'; simp at hm'
        | some old =>
          rw [hb] at hm'
          exact M.sound n.structHash old hb m (by simpa using hm')
    · rw [if_neg hh] at hns
      exact M.sound h ns hns m hm

/-- Fold the normalizations of `pending` (all members of `constraints`) into the map. -/
def addAll : EqConstraintMap p constraints → (pending : List (Expression p)) →
    (∀ c ∈ pending, c ∈ constraints) → EqConstraintMap p constraints
  | M, [], _ => M
  | M, c :: rest, hmem =>
    addAll (M.insertNorm c.normalize ⟨c, hmem c (List.mem_cons_self ..), rfl⟩) rest
      (fun c' h => hmem c' (List.mem_cons_of_mem _ h))

/-- Build the map for a constraint list. -/
def build (constraints : List (Expression p)) : EqConstraintMap p constraints :=
  addAll empty constraints (fun _ h => h)

/-- Is (the normalized) `d` one of the normalized constraints? -/
def test (M : EqConstraintMap p constraints) (d : Expression p) : Bool :=
  match M.map[d.structHash]? with
  | some ns => ns.any (fun n => decide (n = d))
  | none => false

/-- A passing `test d` means `d` evaluates to zero whenever the constraints hold. -/
theorem test_sound (M : EqConstraintMap p constraints) (d : Expression p)
    (h : M.test d = true) (env : Variable → ZMod p)
    (hcon : ∀ c ∈ constraints, c.eval env = 0) : d.eval env = 0 := by
  unfold test at h
  cases hb : M.map[d.structHash]? with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some ns =>
    rw [hb] at h
    obtain ⟨n, hn, heq⟩ := List.any_eq_true.1 h
    obtain ⟨c, hc, hcn⟩ := M.sound d.structHash ns hb n hn
    have hnd : n = d := of_decide_eq_true heq
    rw [← hnd, ← hcn, Expression.normalize_eval]
    exact hcon c hc

end EqConstraintMap

/-- `e − e'` as an expression (`e + (−1)·e'`). -/
def diffE (e e' : Expression p) : Expression p := .add e (.mul (.const (-1)) e')

theorem diffE_eval (e e' : Expression p) (env : Variable → ZMod p) :
    (diffE e e').eval env = e.eval env - e'.eval env := by
  simp only [diffE, Expression.eval]; ring

/-- Slot-wise payload match with the entailed-equality escape hatch: each slot pair is
    syntactically equal, or its (normalized) difference — in either orientation — is a
    normalized constraint. The `Thunk` is forced only at the first syntactic mismatch, so
    fully-identical payloads never pay for the map. -/
def payloadEntailedEq {constraints : List (Expression p)}
    (M : Thunk (EqConstraintMap p constraints)) :
    List (Expression p) → List (Expression p) → Bool
  | [], [] => true
  | e :: es, e' :: es' =>
    (decide (e = e') || M.get.test (diffE e e').normalize
      || M.get.test (diffE e' e).normalize) && payloadEntailedEq M es es'
  | _, _ => false

/-- A passing match makes the *evaluated* payloads equal whenever the constraints hold. -/
theorem payloadEntailedEq_sound {constraints : List (Expression p)}
    (M : Thunk (EqConstraintMap p constraints)) :
    ∀ (pl pl' : List (Expression p)), payloadEntailedEq M pl pl' = true →
    ∀ (env : Variable → ZMod p), (∀ c ∈ constraints, c.eval env = 0) →
      pl.map (fun e => e.eval env) = pl'.map (fun e => e.eval env)
  | [], [], _, _, _ => rfl
  | e :: es, e' :: es', h, env, hcon => by
    rw [payloadEntailedEq, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
    obtain ⟨hslot, hrest⟩ := h
    have hev : e.eval env = e'.eval env := by
      rcases hslot with (hs | hs) | hs
      · rw [of_decide_eq_true hs]
      · have := M.get.test_sound _ hs env hcon
        rw [Expression.normalize_eval, diffE_eval] at this
        exact sub_eq_zero.mp this
      · have := M.get.test_sound _ hs env hcon
        rw [Expression.normalize_eval, diffE_eval] at this
        exact (sub_eq_zero.mp this).symm
    simp only [List.map_cons, hev,
      payloadEntailedEq_sound M es es' hrest env hcon]
  | [], _ :: _, h, _, _ => by simp [payloadEntailedEq] at h
  | _ :: _, [], h, _, _ => by simp [payloadEntailedEq] at h

/-- The first indexed position strictly after `i` on `busId` whose payload matches `S.payload`
    (positions ascending; the hash bucket pre-filters, the bus-id check and the slot-wise
    entailed comparison decide). -/
def firstMatchAt {constraints : List (Expression p)}
    (M : Thunk (EqConstraintMap p constraints)) (arr : Array (BusInteraction (Expression p)))
    (busId : Nat) (S : BusInteraction (Expression p)) (i : Nat) : List Nat → Option Nat
  | [] => none
  | j :: rest =>
    if i < j then
      match arr[j]? with
      | some R =>
        if decide (R.busId = busId) && payloadEntailedEq M S.payload R.payload then some j
        else firstMatchAt M arr busId S i rest
      | none => firstMatchAt M arr busId S i rest
    else firstMatchAt M arr busId S i rest

/-- Refute `m` as an active same-address message on `busId` (the "between" region test). The
    two-root address-disequality (`addrTwoRootNeq`) lets this step over interleaved other-pointer
    heap accesses whose addresses are pointer *expressions* rather than constants — the enabler
    for interior-pair telescoping on the heap. Sound under the constraints `T` was built from
    (`midRefuted_sound` takes their satisfaction). -/
def midRefuted (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat) (S m : BusInteraction (Expression p)) : Bool :=
  decide (m.busId ≠ busId) || decide (multConst m = some 0) || addrConstsNeq shape S m
    || addrAffineNeq shape S m || addrTwoRootNeq shape T.get S m

/-- Refute `m` as an active same-address *send* on `busId` (the "before" region test: earliest-send). -/
def preRefuted (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat) (S m : BusInteraction (Expression p)) : Bool :=
  midRefuted shape T busId S m ||
    (match multConst m with | some c => decide (c ≠ 1) | none => false)

theorem midRefuted_sound (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat) (S m : BusInteraction (Expression p))
    (h : midRefuted shape T busId S m = true) (env : Variable → ZMod p)
    (hcon : ∀ c ∈ constraints, c.eval env = 0)
    (hbid : (m.eval env).busId = busId) (hmne : (m.eval env).multiplicity ≠ 0)
    (hmaddr : shape.address (m.eval env) = shape.address (S.eval env)) : False := by
  unfold midRefuted at h
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · exact absurd hbid (of_decide_eq_true h)
  · exact hmne (m.multiplicity.constValue?_sound 0 (of_decide_eq_true h) env)
  · exact addrConstsNeq_sound shape S m h env hmaddr.symm
  · exact addrAffineNeq_sound shape S m h env hmaddr.symm
  · exact addrTwoRootNeq_sound shape T.get S m h env hcon hmaddr.symm

theorem preRefuted_sound (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat) (S m : BusInteraction (Expression p))
    (h : preRefuted shape T busId S m = true) (env : Variable → ZMod p)
    (hcon : ∀ c ∈ constraints, c.eval env = 0)
    (hbid : (m.eval env).busId = busId) (hmne : (m.eval env).multiplicity ≠ 0)
    (hmaddr : shape.address (m.eval env) = shape.address (S.eval env)) :
    (m.eval env).multiplicity ≠ 1 := by
  unfold preRefuted at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact (midRefuted_sound shape T busId S m h env hcon hbid hmne hmaddr).elim
  · cases hc : multConst m with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      have heval : (m.eval env).multiplicity = c := m.multiplicity.constValue?_sound c hc env
      rw [heval]
      exact of_decide_eq_true h

/-- `m` is a *provable* active same-address receive on `busId`: on-bus, constant `-1`
    multiplicity, and a constant address equal to `S`'s. -/
def provRecv (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p)) : Bool :=
  decide (m.busId = busId) && addrConstsEq shape S m && decide (multConst m = some (-1))

theorem provRecv_sound (shape : MemoryBusShape) (busId : Nat) (hp1 : (1 : ZMod p) ≠ 0)
    (S m : BusInteraction (Expression p)) (h : provRecv shape busId S m = true)
    (env : Variable → ZMod p) :
    (m.eval env).busId = busId ∧ (m.eval env).multiplicity ≠ 0 ∧
    shape.address (m.eval env) = shape.address (S.eval env) ∧ (m.eval env).multiplicity = -1 := by
  unfold provRecv at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hbid, haddr⟩, hmult⟩ := h
  have hmult' : (m.eval env).multiplicity = -1 :=
    m.multiplicity.constValue?_sound (-1) (of_decide_eq_true hmult) env
  refine ⟨of_decide_eq_true hbid, ?_, (addrConstsEq_sound shape S m haddr env).symm, hmult'⟩
  rw [hmult']; exact neg_ne_zero.mpr hp1

/-- Single right-to-left pass returning `(hasRecvSoFar, ok)`: `hasRecvSoFar` is whether the tail
    processed so far (everything to the right) contains a provable active same-address receive; `ok`
    is whether every not-`preRefuted` message so far is followed by such a receive. O(n). -/
def shieldScan (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat) (S : BusInteraction (Expression p)) :
    List (BusInteraction (Expression p)) → Bool × Bool
  | [] => (false, true)
  | m0 :: rest =>
    let r := shieldScan shape T busId S rest
    (r.1 || provRecv shape busId S m0, r.2 && (preRefuted shape T busId S m0 || r.1))

/-- The *shield* check on the before-region: every message that is **not** provably a
    non-(active-same-address-send) (`¬preRefuted`) is followed by a provable active same-address
    receive (`provRecv`). Certifies "every active same-address send in the region has an active
    same-address receive after it" — the relaxed completeness side condition that admits chains led
    by a boundary store. Computed in one O(n) pass (`shieldScan`). -/
def shieldOk (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat) (S : BusInteraction (Expression p))
    (l : List (BusInteraction (Expression p))) : Bool :=
  (shieldScan shape T busId S l).2

/-- If the scan's `hasRecv` flag is set, the list contains a provable receive. -/
theorem shieldScan_hasRecv (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat)
    (S : BusInteraction (Expression p)) :
    ∀ (l : List (BusInteraction (Expression p))), (shieldScan shape T busId S l).1 = true →
      ∃ Rp ∈ l, provRecv shape busId S Rp = true
  | [], h => by simp [shieldScan] at h
  | m0 :: rest, h => by
      rw [shieldScan] at h
      dsimp only at h
      rcases Bool.or_eq_true _ _ |>.mp h with h1 | h1
      · obtain ⟨Rp, hRp, hprov⟩ := shieldScan_hasRecv shape T busId S rest h1
        exact ⟨Rp, List.mem_cons_of_mem _ hRp, hprov⟩
      · exact ⟨m0, List.mem_cons_self .., h1⟩

/-- From a passing `shieldOk` and a syntactic split `A_pre ++ m0 :: A_suf` whose `m0` is not
    provably excluded (`¬preRefuted`), the suffix `A_suf` carries a provable active same-address
    receive. -/
theorem shieldOk_sound (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : Thunk (TwoRootMap p constraints)) (busId : Nat)
    (S m0 : BusInteraction (Expression p)) (A_suf : List (BusInteraction (Expression p))) :
    ∀ (A_pre : List (BusInteraction (Expression p))),
      shieldOk shape T busId S (A_pre ++ m0 :: A_suf) = true →
      preRefuted shape T busId S m0 = false →
      ∃ Rp ∈ A_suf, provRecv shape busId S Rp = true
  | [], h, hpre => by
      unfold shieldOk at h
      rw [List.nil_append, shieldScan] at h
      dsimp only at h
      rw [Bool.and_eq_true] at h
      obtain ⟨_, h2⟩ := h
      rw [hpre, Bool.false_or] at h2
      exact shieldScan_hasRecv shape T busId S A_suf h2
  | a :: A_pre', h, hpre => by
      unfold shieldOk at h
      rw [List.cons_append, shieldScan] at h
      dsimp only at h
      rw [Bool.and_eq_true] at h
      exact shieldOk_sound shape T busId S m0 A_suf A_pre' h.1 hpre

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

/-- The declared byte slots of `R` whose payload entries the witnesses do not justify. -/
def unjustifiedSlots (deep : Bool) (domCs : List (Expression p))
    (candsOf : Variable → List (Expression p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits : Variable → List (BusInteraction (Expression p)))
    (slots : List Nat) (R : BusInteraction (Expression p)) : List Nat :=
  slots.filter (fun slot =>
    match R.payload[slot]? with
    | some e => !byteJustifiedW deep domCs candsOf bs facts wits e
    | none => false)

/-- The per-candidate certificate: address/multiplicity/payload of the pair, the emitted
    checks' certificates, plus the byte justification of the dropped receive's declared byte
    slots through the witness lookup `wits`. The split equation, the between-region refutation
    and the before-region shield are *not* re-checked here — the scan established them already
    and supplies them to `checkCancel_sound` as hypotheses. The justification scan is the last
    conjunct, so it only runs for candidates that already match. -/
def checkCancel (deep : Bool) {all : List (Expression p)} (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (M : Thunk (EqConstraintMap p all))
    (domCs : List (Expression p)) (candsOf : Variable → List (Expression p))
    (wits : Variable → List (BusInteraction (Expression p)))
    (busId : Nat) (slots : List Nat)
    (S R : BusInteraction (Expression p))
    (checks : List (BusInteraction (Expression p))) : Bool :=
  decide (S.busId = busId) && decide (R.busId = busId) &&
  decide (multConst S = some 1) && decide (multConst R = some (-1)) &&
  payloadEntailedEq M S.payload R.payload &&
  checks.all (emitOk bs facts busId slots R) &&
  recvSlotsJustified deep domCs candsOf bs facts wits slots R

/-- A passing `checkCancel` — together with the split equation, the region hypotheses the scan
    established, and the witness/index membership facts — yields `PassCorrect` via
    `dropPair_correct`. -/
theorem checkCancel_sound (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape)
    (slots : List Nat)
    (T : Thunk (TwoRootMap p cs.algebraicConstraints))
    (M : Thunk (EqConstraintMap p cs.algebraicConstraints))
    (domCs : List (Expression p)) (candsOf : Variable → List (Expression p))
    (wits : Variable → List (BusInteraction (Expression p)))
    (A : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (B : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p))
    (C : List (BusInteraction (Expression p)))
    (hslots : facts.recvByteSlots busId (R.payload.map Expression.constValue?) = some slots)
    (checks : List (BusInteraction (Expression p)))
    (hsplit : cs.busInteractions = A ++ S :: B ++ R :: C)
    (hdomCs : ∀ c ∈ domCs, c ∈ cs.algebraicConstraints)
    (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ cs.algebraicConstraints)
    (hwits : ∀ v, ∀ bi ∈ wits v, bi ∈ A ++ B ++ C ++ checks)
    (hmid : ∀ m0 ∈ B, midRefuted shape T busId S m0 = true)
    (hshield : shieldOk shape T busId S A = true)
    (h : checkCancel deep bs facts M domCs candsOf wits busId slots S R checks = true) :
    PassCorrect cs { cs with busInteractions := A ++ B ++ C ++ checks } [] bs := by
  unfold checkCancel at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hSb, hRb⟩, hSm⟩, hRm⟩, hpay⟩, hemit⟩, hjust⟩ := h
  have hRmEv : ∀ env, (R.eval env).multiplicity = -1 :=
    fun env => R.multiplicity.constValue?_sound (-1) (of_decide_eq_true hRm) env
  refine dropPair_correct cs bs facts hp1 A B C S R busId shape hshape
    (R.payload.map Expression.constValue?) slots hslots
    (fun env => matches_evalPattern R.payload env) checks
    (fun ck hck => emitOk_sound bs facts busId slots R ck
      (List.all_eq_true.mp hemit ck hck) (of_decide_eq_true hRb) hRmEv)
    (fun env hall hbus => recvSlotsJustified_sound deep cs.algebraicConstraints domCs candsOf
      bs facts (A ++ B ++ C ++ checks) wits slots R hdeep hdomCs hcands hwits hjust env hall hbus)
    hsplit
    (of_decide_eq_true hSb) (of_decide_eq_true hRb)
    (of_decide_eq_true hSm) (of_decide_eq_true hRm)
    (fun env hcon => payloadEntailedEq_sound M S.payload R.payload hpay env hcon) ?_ ?_
  · intro env hcon m0 hm0 hbid hmne hmaddr
    exact midRefuted_sound shape T busId S m0 (hmid m0 hm0) env hcon
      hbid hmne hmaddr
  · intro env hcon A_pre m0 A_suf hAeq hbid hmne hmaddr hmult
    have hnp : preRefuted shape T busId S m0 = false := by
      by_contra hp'
      rw [Bool.not_eq_false] at hp'
      exact (preRefuted_sound shape T busId S m0 hp' env hcon hbid hmne hmaddr) hmult
    obtain ⟨Rp, hRpmem, hRpprov⟩ := shieldOk_sound shape T busId S m0 A_suf A_pre
      (hAeq ▸ hshield) hnp
    exact ⟨Rp, hRpmem, provRecv_sound shape busId hp1 S Rp hRpprov env⟩

/-- The scan behind `dropWits`: the first interaction of `arr` (positions ascending from `k`,
    skipping any value equal to the dropped pair) that derives an `interactionBound` for `v` —
    exactly the interaction `findVarBound` over the remaining region finds first, at the same
    early-exit cost, with no region list materialized. (Fuel-structured for the easy induction;
    called with `fuel := arr.size`, which reaches every position.) -/
def dropWitsGo {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (Expression p))) (S R : BusInteraction (Expression p))
    (v : Variable) : Nat → Nat → Option (BusInteraction (Expression p))
  | 0, _ => none
  | fuel + 1, k =>
    if h : k < arr.size then
      if !decide (arr[k] = S) && !decide (arr[k] = R) then
        match interactionBound bs facts arr[k] v with
        | some _ => some arr[k]
        | none => dropWitsGo facts arr S R v fuel (k + 1)
      else dropWitsGo facts arr S R v fuel (k + 1)
    else none

/-- The witness lookup for a candidate drop: the first bound-deriving interaction other than
    the dropped pair, then the emitted checks. Every returned interaction is a member of the
    remaining region (`dropWits_mem`). -/
def dropWits {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (Expression p))) (S R : BusInteraction (Expression p))
    (checks : List (BusInteraction (Expression p))) (v : Variable) :
    List (BusInteraction (Expression p)) :=
  match dropWitsGo facts arr S R v arr.size 0 with
  | some bi => bi :: checks
  | none => checks

theorem dropWitsGo_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (Expression p))) (S R : BusInteraction (Expression p))
    (v : Variable) (fuel : Nat) :
    ∀ (k : Nat) {bi : BusInteraction (Expression p)},
      dropWitsGo facts arr S R v fuel k = some bi →
      bi ∈ arr.toList ∧ bi ≠ S ∧ bi ≠ R := by
  induction fuel with
  | zero =>
    intro k bi h
    exact absurd h (by simp [dropWitsGo])
  | succ fuel ih =>
    intro k bi h
    rw [dropWitsGo] at h
    split_ifs at h with hk hne
    · -- in range, not the dropped pair
      revert h
      cases hb : interactionBound bs facts arr[k] v with
      | some b =>
        intro h
        obtain rfl := Option.some.inj h
        rw [Bool.and_eq_true] at hne
        exact ⟨by simp [Array.getElem_mem hk],
          fun he => by simp [he] at hne, fun he => by simp [he] at hne⟩
      | none =>
        intro h
        exact ih (k + 1) h
    · exact ih (k + 1) h

theorem dropWits_mem {cs : ConstraintSystem p} {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (Expression p)))
    (harr : arr = cs.busInteractions.toArray)
    (S R : BusInteraction (Expression p)) (checks : List (BusInteraction (Expression p)))
    {A B C : List (BusInteraction (Expression p))}
    (hsplit : cs.busInteractions = A ++ S :: B ++ R :: C) :
    ∀ v, ∀ bi ∈ dropWits facts arr S R checks v, bi ∈ A ++ B ++ C ++ checks := by
  intro v bi hbi
  unfold dropWits at hbi
  cases hgo : dropWitsGo facts arr S R v arr.size 0 with
  | none =>
    rw [hgo] at hbi
    simp only [List.mem_append]
    exact Or.inr hbi
  | some bi' =>
    rw [hgo] at hbi
    rcases List.mem_cons.1 hbi with rfl | hbi
    · obtain ⟨hmem, hne1, hne2⟩ := dropWitsGo_mem facts arr S R v arr.size 0 hgo
      have hmem' : bi ∈ cs.busInteractions := by
        rw [harr] at hmem
        simpa using hmem
      have := mem_core_of_ne hsplit hmem' hne1 hne2
      simp only [List.mem_append] at this ⊢
      tauto
    · simp only [List.mem_append]
      exact Or.inr hbi

/-- Indexed left-to-right scan for the first droppable pair on `busId`, starting at position `i`:
    at each send `S` (position in `arr`), find its matching receive through the hash index (the
    first position after it with an equal payload on the bus — exactly what the linear scan
    found) and run the cheap region tests; the byte-justification lookup runs only for
    candidates that already match, and the split equation holds by construction
    (`split_of_extracts`) rather than by an O(n) whole-list comparison. Stops at the first hit,
    returning the pass result together with the send's position and whether a byte check was
    emitted (which the caller uses to decide where to resume the enclosing fixpoint). -/
def findCancelGoIdx (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (aggressive : Bool)
    (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape)
    (T : Thunk (TwoRootMap p cs.algebraicConstraints))
    (M : Thunk (EqConstraintMap p cs.algebraicConstraints))
    (domCsT : Thunk { l : List (Expression p) // ∀ c ∈ l, c ∈ cs.algebraicConstraints })
    (candsT : Thunk (VarCsIdx p cs.algebraicConstraints))
    (bcBus? : Option Nat)
    (arr : Array (BusInteraction (Expression p)))
    (harr : arr = cs.busInteractions.toArray)
    (idx : Std.HashMap UInt64 (List Nat))
    (i : Nat) :
    Option ({ r : PassResult cs bs // r.out.algebraicConstraints = cs.algebraicConstraints }
      × Nat × Bool) :=
  if hi : i < arr.size then
    let S := arr[i]
    -- (thunked: Lean is strict, and the continuation must not run once a pair is accepted)
    let next := fun (_ : Unit) => findCancelGoIdx cs bs facts hp1 deep hdeep aggressive busId shape hshape
      T M domCsT candsT bcBus? arr harr idx (i + 1)
    if decide (multConst S = some 1) && decide (S.busId = busId) then
      match firstMatchAt M arr busId S i (idx.getD
          (mixHash (hash busId)
            (if aggressive then addrHash shape S.payload else payloadHash S.payload)) []) with
      | some j =>
        match hR : arr[j]? with
        | some R =>
          if hij : i < j then
            -- Cheap region tests first — only an otherwise-valid candidate pays the byte
            -- justification lookup.
            let B := (arr.extract (i + 1) j).toList
            if hmidB : B.all (midRefuted shape T busId S) = true then
            let A := (arr.extract 0 i).toList
            if hshieldA : shieldOk shape T busId S A = true then
            let C := (arr.extract (j + 1) arr.size).toList
            have hsplit : cs.busInteractions = A ++ S :: B ++ R :: C :=
              split_of_extracts harr hij hi hR
            have hmid : ∀ m0 ∈ B, midRefuted shape T busId S m0 = true :=
              fun m0 hm0 => List.all_eq_true.mp hmidB m0 hm0
            -- The receive `R`'s byte obligation depends on its own constant pattern (e.g. a
            -- memory receive whose address-space slot is a known constant ∉ {1,2} carries no
            -- obligation), so `slots` is resolved per candidate, not per bus.
            match hslots : facts.recvByteSlots busId (R.payload.map Expression.constValue?) with
            | none => next ()
            | some slots =>
            -- Try the certificate with no emitted checks first: it passes iff every declared
            -- byte slot is justified — the same predicate `unjustifiedSlots` decides — and the
            -- common fully-justified drop pays the justification lookup **once**.
            if hchk0 : checkCancel deep bs facts M domCsT.get.val candsT.get.lookup
                (dropWits facts arr S R []) busId slots S R [] = true then
              some (⟨⟨{ cs with busInteractions := A ++ B ++ C ++ [] }, [],
                    checkCancel_sound cs bs facts hp1 deep hdeep busId shape hshape slots
                      T M domCsT.get.val candsT.get.lookup (dropWits facts arr S R [])
                      A S B R C hslots []
                      hsplit domCsT.get.property (fun x => candsT.get.lookup_mem x)
                      (dropWits_mem facts arr harr S R [] hsplit) hmid hshieldA hchk0⟩, rfl⟩,
                i, false)
            else
            -- Some slot is unjustified. Such slots are materialized as a single explicit
            -- self-check on the byte-check bus (more than one would not shrink the bus count and
            -- would stall the cancellation loop); when the justification cannot pass (≥ 2
            -- unjustified slots, or no byte-check bus), skip the certificate re-check — the
            -- justification scan is the expensive part.
            let unjust := unjustifiedSlots deep domCsT.get.val candsT.get.lookup bs facts
              (dropWits facts arr S R []) slots R
            let checks : List (BusInteraction (Expression p)) :=
              match unjust, bcBus? with
              | [slot], some bcBus => (R.payload[slot]?).elim [] (fun e =>
                  [{ busId := bcBus, multiplicity := .const 1,
                     payload := [e, e, .const 0, .const 1] }])
              | _, _ => []
            -- Emission-path drops are restricted to *syntactically* equal payloads unless
            -- `aggressive`: an entailed-matched pair otherwise fires only when every byte slot
            -- is already justified (`checks = []`). Measured (apc_005 class): mid-cycle entailed
            -- drops on unjustified receives trade one emitted self-check per pair for
            -- obligations the deferred syntactic cancellation discharges for free — a net bus
            -- regression. The `aggressive` form runs once, in the coda, where the race is over:
            -- each drop is then locally net −1 bus at worst (2 dropped, ≤1 emitted).
            if !checks.isEmpty && (aggressive || decide (S.payload = R.payload)) then
              if hchk : checkCancel deep bs facts M domCsT.get.val candsT.get.lookup
                  (dropWits facts arr S R checks) busId slots S R checks = true then
                some (⟨⟨{ cs with busInteractions := A ++ B ++ C ++ checks }, [],
                      checkCancel_sound cs bs facts hp1 deep hdeep busId shape hshape slots
                        T M domCsT.get.val candsT.get.lookup (dropWits facts arr S R checks)
                        A S B R C hslots checks hsplit domCsT.get.property
                        (fun x => candsT.get.lookup_mem x)
                        (dropWits_mem facts arr harr S R checks hsplit) hmid hshieldA hchk⟩, rfl⟩,
                  i, true)
              else next ()
            else next ()
            else next ()
            else next ()
          else next ()
        | none => next ()
      | none => next ()
    else next ()
  else none
  termination_by arr.size - i

/-- Search declared buses from list index `curIdx` for a droppable pair, honouring a resume hint:
    buses before `resumeIdx` are skipped (they were exhausted on the previous sweep and — since a
    drop on one bus never re-enables a candidate on another, region tests refute cross-bus messages
    outright — stay exhausted), the bus at `resumeIdx` resumes at `resumePos`, and later buses start
    from `0`. The interaction array, the consolidated receive index and the byte-witness map are
    built once per sweep by the caller and shared by every bus (the byte justification scans the
    array directly, with the old early-exit cost but no region list materialized). Returns the
    pass result together with the list index and position of the accepted send and whether a
    byte check was emitted. -/
def findCancel (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (aggressive : Bool)
    (T : Thunk (TwoRootMap p cs.algebraicConstraints))
    (M : Thunk (EqConstraintMap p cs.algebraicConstraints))
    (domCsT : Thunk { l : List (Expression p) // ∀ c ∈ l, c ∈ cs.algebraicConstraints })
    (candsT : Thunk (VarCsIdx p cs.algebraicConstraints))
    (arr : Array (BusInteraction (Expression p)))
    (harr : arr = cs.busInteractions.toArray)
    (idx : Std.HashMap UInt64 (List Nat))
    (bcBus? : Option Nat) (resumeIdx resumePos : Nat) :
    Nat → List Nat →
      Option ({ r : PassResult cs bs // r.out.algebraicConstraints = cs.algebraicConstraints }
        × Nat × Nat × Bool)
  | _, [] => none
  | curIdx, busId :: rest =>
    if curIdx < resumeIdx then
      findCancel cs bs facts hp1 deep hdeep aggressive T M domCsT candsT arr harr idx bcBus?
        resumeIdx resumePos (curIdx + 1) rest
    else
      let startPos := if curIdx = resumeIdx then resumePos else 0
      match hshape : facts.memShape busId with
      | some shape =>
        match findCancelGoIdx cs bs facts hp1 deep hdeep aggressive busId shape hshape
            T M domCsT candsT bcBus? arr harr idx startPos with
        | some (r, pos, emitted) => some (r, curIdx, pos, emitted)
        | none => findCancel cs bs facts hp1 deep hdeep aggressive T M domCsT candsT arr harr
            idx bcBus? resumeIdx resumePos (curIdx + 1) rest
      | none => findCancel cs bs facts hp1 deep hdeep aggressive T M domCsT candsT arr harr
          idx bcBus? resumeIdx resumePos (curIdx + 1) rest

/-- A `PassResult` is inhabited by the identity pass (its input, unchanged) — needed so the
    fixpoint loop below can be a `partial def`. -/
instance instInhabitedPassResult (cs : ConstraintSystem p) (bs : BusSemantics p) :
    Inhabited (PassResult cs bs) := ⟨⟨cs, [], PassCorrect.refl cs bs⟩⟩

/-- Cancel every droppable pair, iterating to a fixpoint in a single pass invocation. Each accepted
    drop is certified by `checkCancel_sound` exactly as before, and the composite is correct by
    `PassCorrect.andThen`; the loop only controls the *search order*, so the set and order of drops —
    hence the output — is identical to restarting `findCancel` from the top after each drop. The
    speedup: after a drop that emitted no byte check, the scan resumes at the drop's own bus/position
    (`resumeIdx`/`resumePos`) rather than rescanning the already-rejected prefix, which cannot
    contain a newly-droppable pair; a drop that *did* emit a byte check may make an earlier pair
    justifiable (the check joins the remaining interactions), so the scan restarts from the top.
    The interaction array and the consolidated receive index are rebuilt once per sweep — the
    interactions changed — while the constraint-derived thunks (`T`/`M`/`domCsT`/`candsT`)
    transport across drops. -/
partial def cancelLoop (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (aggressive : Bool)
    (T : Thunk (TwoRootMap p cs.algebraicConstraints))
    (M : Thunk (EqConstraintMap p cs.algebraicConstraints))
    (domCsT : Thunk { l : List (Expression p) // ∀ c ∈ l, c ∈ cs.algebraicConstraints })
    (candsT : Thunk (VarCsIdx p cs.algebraicConstraints))
    (bcBus? : Option Nat) (busIds : List Nat) (resumeIdx resumePos : Nat) : PassResult cs bs :=
  let arr := cs.busInteractions.toArray
  let idx := recvIndexAll facts aggressive arr
  match findCancel cs bs facts hp1 deep hdeep aggressive T M domCsT candsT arr rfl idx bcBus?
      resumeIdx resumePos 0 busIds with
  | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  | some (⟨r, hpres⟩, dropIdx, dropPos, emitted) =>
    let nextIdx := if emitted then 0 else dropIdx
    let nextPos := if emitted then 0 else dropPos
    -- A drop changes only `busInteractions` (`hpres`), so the constraint-derived maps — built
    -- once per pass invocation — transport to the recursive call instead of being rebuilt per
    -- drop.
    let r2 := cancelLoop r.out bs facts hp1 deep hdeep aggressive (hpres.symm ▸ T) (hpres.symm ▸ M)
      (hpres.symm ▸ domCsT) (hpres.symm ▸ candsT) bcBus? busIds nextIdx nextPos
    ⟨r2.out, r.derivs ++ r2.derivs, r.correct.andThen r2.correct⟩

/-- Drop every matched consecutive send/receive pair on the declared memory buses with a
    `recvByteSlots` contract — justifying each dropped receive's byte obligation from the
    remaining interactions (shallow bus-fact bounds, or the deep one-hot-selection analysis on
    prime `p`), or materializing it as one explicit byte check on a `byteCheck` bus already
    present in the system. Runs its own cancellation fixpoint (`cancelLoop`), so a whole access
    chain is cancelled in a single invocation. -/
def busPairCancelPass (aggressive : Bool) : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    let busIds := (cs.busInteractions.map (fun bi => bi.busId)).dedup
    let deep : Bool := decide p.Prime
    -- Two-root decomposition data (address disequality), normalized-constraint index (entailed
    -- payload equality), single-variable constraints and the variable→constraints index (deep
    -- byte justification): `Thunk`s, so each is built at most once per invocation — on the
    -- first candidate that actually consults it — and reused across every drop (drops leave
    -- `algebraicConstraints` untouched, so `cancelLoop` transports them).
    let T : Thunk (TwoRootMap p cs.algebraicConstraints) :=
      Thunk.mk fun _ => TwoRootMap.build cs.algebraicConstraints
    let M : Thunk (EqConstraintMap p cs.algebraicConstraints) :=
      Thunk.mk fun _ =>
        if aggressive then EqConstraintMap.build cs.algebraicConstraints
        else EqConstraintMap.empty
    let domCsT : Thunk { l : List (Expression p) // ∀ c ∈ l, c ∈ cs.algebraicConstraints } :=
      Thunk.mk fun _ => ⟨cs.algebraicConstraints.filter Expression.isSingleVar,
        fun _ hc => List.mem_of_mem_filter hc⟩
    let candsT : Thunk (VarCsIdx p cs.algebraicConstraints) :=
      Thunk.mk fun _ => VarCsIdx.build cs.algebraicConstraints
    cancelLoop cs bs facts hp1 deep (fun h => of_decide_eq_true h) aggressive T M domCsT candsT
      (busIds.find? facts.byteCheck) busIds 0 0
  else ⟨cs, [], PassCorrect.refl cs bs⟩
