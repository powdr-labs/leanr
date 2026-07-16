import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Carry-branch resolution (interval analysis on product factors)

Byte-decomposed adders leave degree-2 *carry-branch* constraints of the shape
`(b₀ − a₀) · (b₀ − a₀ − 256) = 0` — "the difference is either `0` or `256`". When both operands
are provably bytes (via the proven bus-fact bounds: memory receives, bitwise checks, range
checks), the second factor can *never* vanish: its value, viewed through the bounds, lies in the
integer interval `[p − 511, p − 1]`, which excludes `0` and wraps past no multiple of `p`. The
product then collapses to the linear factor `b₀ − a₀`, which the affine/Gauss passes substitute
away — eliminating the whole copied word and its carry chain (the higher limbs' cross terms
cancel once the lower limb is unified, so the chain cascades across cleanup iterations). The same
lever collapses the `(L₁)·(L₂) = 0` carry constraints of memory-pointer-limb decompositions.

The certificate (`splitSumMax`): normalize a factor to an affine form `c + Σ aᵢ·vᵢ`, give every
variable a fact-derived bound `vᵢ.val < Bᵢ` (`BoundsMap`, built from `BusFacts.slotBound`), and
choose per term the representation — positive `aᵢ·vᵢ` or negative `−((−aᵢ)·vᵢ)` — with the
smaller maximal magnitude. With `maxNeg < c.val` and `c.val + maxPos < p`, the factor's value
lies in `[c.val − maxNeg, c.val + maxPos] ⊆ (0, p)`, so it is never zero
(`linNeverZeroSplit`; this generalizes `MemoryUnify.linNeverZero`, which handles only the
all-negative case). Since `p` is prime (checked at runtime, like the other field-dependent
passes), `f·g = 0` is then *equivalent* to `f = 0` — the rewrite preserves the satisfying set
exactly, so both `PassCorrect` directions use the unchanged assignment.

The pass is generic: it consumes only `BusFacts.slotBound` (any semantics), and degrades to the
identity with `BusFacts.trivial` (no bounds ⇒ no certificate) or composite `p`. -/

variable {p : ℕ}

/-! ## The two-sided interval certificate -/

/-- Interval split of a term list's possible values: `some (maxPos, maxNeg)` when every term's
    variable carries a bound in `B`. Each term `a·v` contributes to `maxPos` as `a.val·(B−1)` or
    to `maxNeg` as `(−a).val·(B−1)`, whichever is smaller — small positive coefficients count
    positively, small negative ones negatively. The sum is then provably `P − N` with
    `P.val ≤ maxPos` and `N.val ≤ maxNeg` (`splitSum_val`). -/
def splitSumMax (B : Std.HashMap Variable Nat) :
    List (Variable × ZMod p) → Option (Nat × Nat)
  | [] => some (0, 0)
  | (v, a) :: rest =>
    match B[v]?, splitSumMax B rest with
    | some bound, some acc =>
      if 1 ≤ bound then
        if a.val * (bound - 1) ≤ (-a).val * (bound - 1) then
          some (a.val * (bound - 1) + acc.1, acc.2)
        else
          some (acc.1, (-a).val * (bound - 1) + acc.2)
      else none
    | _, _ => none

theorem splitSum_val (B : Std.HashMap Variable Nat)
    (terms : List (Variable × ZMod p)) (mp mn : Nat)
    (h : splitSumMax B terms = some (mp, mn)) (hmp : mp < p) (hmn : mn < p)
    (env : Variable → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    ∃ P N : ZMod p, (terms.map (fun t => t.2 * env t.1)).sum = P - N ∧
      P.val ≤ mp ∧ N.val ≤ mn := by
  induction terms generalizing mp mn with
  | nil =>
      simp only [splitSumMax, Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨0, 0, by simp, ?_, ?_⟩ <;> simp [← h.1, ← h.2]
  | cons t rest ih =>
      obtain ⟨v, a⟩ := t
      rw [splitSumMax] at h
      split at h
      case _ bound acc hBd hrest =>
        obtain ⟨mp', mn'⟩ := acc
        have hv : (env v).val < bound := hB v bound hBd
        split_ifs at h with hb1 hcmp
        · -- positive branch: the head contributes `a.val·(bound−1)` to `maxPos`
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨P', N', hsum', hP'le, hN'le⟩ := ih mp' mn' hrest (by omega) hmn
          have hle : a.val * (env v).val ≤ a.val * (bound - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have hheadval : (a * env v).val = a.val * (env v).val :=
            ZMod.val_mul_of_lt (by omega)
          have haddlt : (a * env v).val + P'.val < p := by rw [hheadval]; omega
          refine ⟨a * env v + P', N', ?_, ?_, hN'le⟩
          · simp only [List.map_cons, List.sum_cons, hsum']; ring
          · rw [ZMod.val_add_of_lt haddlt, hheadval]; omega
        · -- negative branch: the head contributes `(−a).val·(bound−1)` to `maxNeg`
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨P', N', hsum', hP'le, hN'le⟩ := ih mp' mn' hrest hmp (by omega)
          have hle : (-a).val * (env v).val ≤ (-a).val * (bound - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have hheadval : ((-a) * env v).val = (-a).val * (env v).val :=
            ZMod.val_mul_of_lt (by omega)
          have haddlt : ((-a) * env v).val + N'.val < p := by rw [hheadval]; omega
          refine ⟨P', (-a) * env v + N', ?_, hP'le, ?_⟩
          · simp only [List.map_cons, List.sum_cons, hsum']; ring
          · rw [ZMod.val_add_of_lt haddlt, hheadval]; omega
      case _ => exact absurd h (by simp)

/-- The never-zero certificate: an affine form whose bounded value interval
    `[const.val − maxNeg, const.val + maxPos]` stays strictly inside `(0, p)` can never evaluate
    to zero. Two-sided generalization of `linNeverZero`. -/
theorem linNeverZeroSplit (B : Std.HashMap Variable Nat) (l : LinExpr p) (mp mn : Nat)
    (hp : 0 < p) (h : splitSumMax B l.terms = some (mp, mn))
    (hlo : mn < l.const.val) (hhi : l.const.val + mp < p)
    (env : Variable → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    l.eval env ≠ 0 := by
  intro h0
  haveI : NeZero p := ⟨hp.ne'⟩
  have hcp : l.const.val < p := ZMod.val_lt l.const
  obtain ⟨P, N, hsum, hPle, hNle⟩ :=
    splitSum_val B l.terms mp mn h (by omega) (by omega) env hB
  have hPN : N = l.const + P := by
    rw [LinExpr.eval, hsum] at h0
    linear_combination -h0
  have hval : (l.const + P).val = l.const.val + P.val :=
    ZMod.val_add_of_lt (by omega)
  rw [hPN, hval] at hNle
  omega

/-- The interval condition on one concrete normalized form. -/
def intervalCert (B : Std.HashMap Variable Nat) (l : LinExpr p) : Bool :=
  match splitSumMax B l.terms with
  | none => false
  | some acc =>
    decide (acc.2 < l.const.val) && decide (l.const.val + acc.1 < p)

theorem intervalCert_sound (hp : 0 < p) (B : Std.HashMap Variable Nat) (l : LinExpr p)
    (h : intervalCert B l = true) (env : Variable → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    l.eval env ≠ 0 := by
  unfold intervalCert at h
  split at h
  · exact absurd h (by simp)
  · rename_i acc hacc
    obtain ⟨mp, mn⟩ := acc
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact linNeverZeroSplit B l mp mn hp hacc h.1 h.2 env hB

/-- Checked never-zero certificate for an expression: linearize, normalize, and verify the
    interval condition against the bounds map — under a *candidate rescaling*. A factor's zero
    set is invariant under scaling by a constant, but the interval certificate is not (the
    mid-pipeline carry factors read `−1 + 256⁻¹·b₀ − 256⁻¹·a₀`, whose raw coefficient values
    overflow every bound), so each coefficient's and the constant's field inverse is tried as a
    scalar. Soundness needs nothing about the candidate: if the scaled form never vanishes,
    neither does the original (`k·0 = 0`). -/
def neverZeroB (B : Std.HashMap Variable Nat) (e : Expression p) : Bool :=
  match linearize e with
  | none => false
  | some l =>
    let n := l.norm
    (1 :: n.const⁻¹ :: n.terms.map (fun t => t.2⁻¹)).any (fun k =>
      intervalCert B ((n.scale k).norm))

theorem neverZeroB_sound (hp : 0 < p) (B : Std.HashMap Variable Nat) (e : Expression p)
    (h : neverZeroB B e = true) (env : Variable → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    e.eval env ≠ 0 := by
  unfold neverZeroB at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hl
    rw [List.any_eq_true] at h
    obtain ⟨k, _, hcert⟩ := h
    intro h0
    have hs : ((l.norm.scale k).norm).eval env = 0 := by
      rw [LinExpr.norm_eval, LinExpr.scale_eval, LinExpr.norm_eval,
          ← linearize_eval e l hl, h0, mul_zero]
    exact intervalCert_sound hp B _ hcert env hB hs

/-! ## Resolving product constraints -/

/-- Rewrite a constraint, collapsing products with a certified never-vanishing factor to the
    other factor (recursively, so `c·f·g` also resolves). Non-products are left unchanged. -/
def resolveExpr (B : Std.HashMap Variable Nat) : Expression p → Expression p
  | .mul f g =>
      if neverZeroB B g then resolveExpr B f
      else if neverZeroB B f then resolveExpr B g
      else .mul f g
  | e => e

theorem resolveExpr_vars (B : Std.HashMap Variable Nat) (e : Expression p) :
    ∀ x ∈ (resolveExpr B e).vars, x ∈ e.vars := by
  induction e with
  | mul f g ihf ihg =>
      intro x hx
      simp only [resolveExpr] at hx
      simp only [Expression.vars, List.mem_append]
      split_ifs at hx with h1 h2
      · exact Or.inl (ihf x hx)
      · exact Or.inr (ihg x hx)
      · simpa only [Expression.vars, List.mem_append] using hx
  | const n => intro x hx; simpa only [resolveExpr] using hx
  | var y => intro x hx; simpa only [resolveExpr] using hx
  | add a b iha ihb => intro x hx; simpa only [resolveExpr] using hx

/-- The resolution is an *equivalence* on satisfying assignments: with the bounds valid (bus
    obligations hold) and `p` prime (so `ZMod p` has no zero divisors), `f·g = 0 ↔ f = 0`
    whenever `g` is certified never-zero. -/
theorem resolveExpr_eval_iff [Fact p.Prime] (B : Std.HashMap Variable Nat) (e : Expression p)
    (env : Variable → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) :
    (resolveExpr B e).eval env = 0 ↔ e.eval env = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction e with
  | mul f g ihf ihg =>
      simp only [resolveExpr]
      split_ifs with h1 h2
      · have hg : g.eval env ≠ 0 := neverZeroB_sound hp B g h1 env hB
        refine ihf.trans ?_
        show f.eval env = 0 ↔ f.eval env * g.eval env = 0
        exact ⟨fun h => by rw [h, zero_mul], fun h => (mul_eq_zero.mp h).resolve_right hg⟩
      · have hf : f.eval env ≠ 0 := neverZeroB_sound hp B f h2 env hB
        refine ihg.trans ?_
        show g.eval env = 0 ↔ f.eval env * g.eval env = 0
        exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hf⟩
      · exact Iff.rfl
  | const n => exact Iff.rfl
  | var x => exact Iff.rfl
  | add a b iha ihb => exact Iff.rfl

/-! ## The pass -/

/-- Rewriting every constraint through `resolveExpr` is `PassCorrect`: the satisfying set is
    unchanged (both directions use the input assignment — the bus interactions, side effects, and
    `admissible` are untouched), and no variable is introduced. -/
theorem resolveMap_correct [Fact p.Prime] (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bm : BoundsMap p cs bs) :
    PassCorrect cs
      { cs with algebraicConstraints := cs.algebraicConstraints.map (resolveExpr Bm.map) }
      [] bs := by
  have hsame : ∀ env, cs.satisfies bs env ↔
      (ConstraintSystem.satisfies
        { cs with algebraicConstraints := cs.algebraicConstraints.map (resolveExpr Bm.map) }
        bs env) := by
    intro env
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨fun c' hc' => ?_, hb⟩
      obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
      exact (resolveExpr_eval_iff Bm.map c env
        (Bm.sound env (fun bi hbi => hb bi hbi))).mpr (hc c hcmem)
    · rintro ⟨hc, hb⟩
      refine ⟨fun c hcmem => ?_, hb⟩
      exact (resolveExpr_eval_iff Bm.map c env
        (Bm.sound env (fun bi hbi => hb bi hbi))).mp
        (hc _ (List.mem_map_of_mem hcmem))
  refine PassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  · -- soundness: the same assignment satisfies the input
    intro env hsat
    exact ⟨env, (hsame env).mpr hsat, BusState.equiv_refl _⟩
  · -- invariant preservation
    intro hinv env hsat
    exact hinv env ((hsame env).mpr hsat)
  · -- no new variables
    intro x hx
    rw [ConstraintSystem.mem_vars] at hx
    rcases hx with ⟨c', hc', hxc⟩ | ⟨bi, hbi, hxbi⟩
    · obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
      exact ConstraintSystem.mem_vars_of_constraint hcmem (resolveExpr_vars Bm.map c x hxc)
    · rcases hxbi with hm | ⟨e, he, hxe⟩
      · exact ConstraintSystem.mem_vars_of_mult hbi hm
      · exact ConstraintSystem.mem_vars_of_payload hbi he hxe
  · -- completeness: same assignment, same side effects, `admissible` untouched
    intro env hadm hsat
    exact ⟨(hsame env).mp hsat, hadm, BusState.equiv_refl _⟩

/-- The carry-branch-resolution pass: collapse every product constraint with a certified
    never-vanishing factor to its other factor. Needs prime `p` (zero divisors would break the
    factoring); identity otherwise, and identity with `BusFacts.trivial` (no bounds ⇒ no
    certificate ever fires). -/
def carryBranchPass (pw : PrimeWitness p) : VerifiedPassW p := fun cs bs facts =>
  if hpB : pw.isPrime = true then
    haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    let Bm : BoundsMap p cs bs := BoundsMap.build facts
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints.map (resolveExpr Bm.map) }, [],
      resolveMap_correct cs bs Bm⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
