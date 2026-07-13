import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify
import ApcOptimizer.Implementation.OptimizerPasses.Affine
import Mathlib.Data.List.Sort

set_option autoImplicit false

/-! # Fold positional decompositions of a compile-time constant (C5)

powdr-exported blocks that end in a jump (JAL/JALR) — and, more generally, any block whose result is
a compile-time constant — carry byte/limb *decompositions of a field constant*: an affine constraint
`Σ cᵢ·xᵢ = K` (`K` a field literal) in which the `xᵢ` are range-checked limbs and the coefficients
`cᵢ` form a **non-overlapping positional (mixed-radix) system** — e.g. `x₀ + 256·x₁ + 65536·x₂ = K`
with each `xᵢ < 256`. When the whole representation cannot wrap the field
(`Σ cᵢ·(Bᵢ−1) < p`), such a constraint forces **every** limb to a specific digit of `K`
(`xᵢ = digitᵢ(K)`, obtained by iterated `div`/`mod`), by uniqueness of a bounded mixed-radix
representation. The optimizer's Gaussian elimination cannot crack this — the digit is a nonlinear
function of `K` — so the limbs survive as free variables; powdr folds each to its literal.

This pass adds the *entailed* per-limb equalities `xᵢ − digitᵢ(K) = 0` (keeping all interactions),
which the downstream affine/Gauss passes then consume to eliminate the limbs — a variable win (and,
once a limb is a literal, its range check becomes a constant lookup the tautology/byte passes drop).

The mechanism is a single `ConstraintSystem.addConstraints_correct`: soundness drops the added
constraints; the only content is that each added equality *holds* on every satisfying assignment,
which is exactly the mixed-radix uniqueness (`annDecode_forces`). The value arithmetic uses
`ZMod.val` with an explicit no-wrap side condition (`annSum_val`), so no primality is needed — the
range-check bus facts (via `BoundsMap`) carry all the strength. Both sign orientations of the
constraint are tried (the coefficients are positive-small in exactly one), so `Σ cᵢxᵢ = K` and
`K = Σ cᵢxᵢ` are handled uniformly; terms are sorted by descending coefficient so the recognizer is
independent of the exported term order. -/

namespace ConstDecomp

variable {p : ℕ}

/-- An affine term annotated with a range bound: coefficient `a` on variable `v`, and a bound `B`
    carrying the intended invariant `(env v).val < B`. -/
structure AnnTerm (p : ℕ) where
  v : Variable
  a : ZMod p
  B : Nat

/-- Maximal nat value of `Σ a.val · x` over the bounds `x ≤ B − 1`. -/
def annRestMax : List (AnnTerm p) → Nat
  | [] => 0
  | e :: t => e.a.val * (e.B - 1) + annRestMax t

/-- The realized nat sum `Σ a.val · (env v).val`. -/
def annNatSum (L : List (AnnTerm p)) (env : Variable → ZMod p) : Nat :=
  (L.map (fun e => e.a.val * (env e.v).val)).sum

/-- The realized field sum `Σ a · (env v)`. -/
def annFieldSum (L : List (AnnTerm p)) (env : Variable → ZMod p) : ZMod p :=
  (L.map (fun e => e.a * env e.v)).sum

/-- Positional digit decoder: process the terms from most significant (head) to least, requiring at
    each step that the whole *rest* cannot reach the head coefficient (`annRestMax t < e.a.val`), and
    peeling the digit `K / e.a.val` (checked `< e.B`). Succeeds only on a genuine non-overlapping
    positional system in descending-coefficient order. -/
def annDecode : List (AnnTerm p) → Nat → Option (List (Variable × Nat))
  | [], K => if K = 0 then some [] else none
  | e :: t, K =>
      if 1 ≤ e.a.val ∧ 1 ≤ e.B ∧ annRestMax t < e.a.val ∧ K / e.a.val < e.B then
        (annDecode t (K % e.a.val)).map (fun ds => (e.v, K / e.a.val) :: ds)
      else none

/-- The realized nat sum is bounded by the positional maximum. -/
theorem annNatSum_le (env : Variable → ZMod p) :
    ∀ (L : List (AnnTerm p)), (∀ e ∈ L, (env e.v).val < e.B) →
      annNatSum L env ≤ annRestMax L := by
  intro L
  induction L with
  | nil => intro _; simp [annNatSum, annRestMax]
  | cons e t ih =>
    intro hb
    have hbe := hb e (List.mem_cons_self ..)
    have iht := ih (fun e' he' => hb e' (List.mem_cons_of_mem _ he'))
    simp only [annNatSum, annRestMax, List.map_cons, List.sum_cons]
    simp only [annNatSum] at iht
    exact Nat.add_le_add (Nat.mul_le_mul (le_refl _) (by omega)) iht

/-- **Mixed-radix uniqueness.** If the positional decoder accepts `L` at target `K`, then every
    assignment whose limbs are in range and whose realized sum is `K` must hold exactly the decoded
    digits. This is the entailment the pass relies on. -/
theorem annDecode_forces (env : Variable → ZMod p) :
    ∀ (L : List (AnnTerm p)) (K : Nat) (ds : List (Variable × Nat)),
      annDecode L K = some ds → (∀ e ∈ L, (env e.v).val < e.B) → annNatSum L env = K →
      ∀ v d, (v, d) ∈ ds → (env v).val = d := by
  intro L
  induction L with
  | nil =>
    intro K ds hdec _ _ v d hvd
    rw [annDecode] at hdec
    split at hdec
    · simp only [Option.some.injEq] at hdec; subst hdec; simp at hvd
    · exact absurd hdec (by simp)
  | cons e t ih =>
    intro K ds hdec hb hK
    rw [annDecode] at hdec
    split at hdec
    · rename_i hcond
      obtain ⟨hc1, hcB, hrest, hKB⟩ := hcond
      rw [Option.map_eq_some_iff] at hdec
      obtain ⟨ds', hdt, rfl⟩ := hdec
      have hbt : ∀ e' ∈ t, (env e'.v).val < e'.B := fun e' he' => hb e' (List.mem_cons_of_mem _ he')
      have htail_le : annNatSum t env ≤ annRestMax t := annNatSum_le env t hbt
      have htaillt : annNatSum t env < e.a.val := lt_of_le_of_lt htail_le hrest
      have hexp : annNatSum (e :: t) env = e.a.val * (env e.v).val + annNatSum t env := by
        simp only [annNatSum, List.map_cons, List.sum_cons]
      rw [hexp] at hK
      have hc1' : 0 < e.a.val := hc1
      have hdiv : K / e.a.val = (env e.v).val := by
        rw [← hK, Nat.mul_add_div hc1', Nat.div_eq_of_lt htaillt, Nat.add_zero]
      have hmod : K % e.a.val = annNatSum t env := by
        rw [← hK, Nat.mul_add_mod, Nat.mod_eq_of_lt htaillt]
      have htf := ih (K % e.a.val) ds' hdt hbt hmod.symm
      intro v d hvd
      rcases List.mem_cons.1 hvd with h | h
      · injection h with hv hd; subst hv; subst hd; exact hdiv.symm
      · exact htf v d h
    · exact absurd hdec (by simp)

/-- The variables of the decoded digits are among the term variables. -/
theorem annDecode_vars :
    ∀ (L : List (AnnTerm p)) (K : Nat) (ds : List (Variable × Nat)),
      annDecode L K = some ds → ∀ v d, (v, d) ∈ ds → v ∈ L.map (fun e => e.v) := by
  intro L
  induction L with
  | nil =>
    intro K ds hdec v d hvd
    rw [annDecode] at hdec
    split at hdec
    · simp only [Option.some.injEq] at hdec; subst hdec; simp at hvd
    · exact absurd hdec (by simp)
  | cons e t ih =>
    intro K ds hdec v d hvd
    rw [annDecode] at hdec
    split at hdec
    · rw [Option.map_eq_some_iff] at hdec
      obtain ⟨ds', hdt, rfl⟩ := hdec
      rcases List.mem_cons.1 hvd with h | h
      · injection h with hv _; subst hv; simp
      · have := ih (K % e.a.val) ds' hdt v d h
        simp only [List.map_cons, List.mem_cons]; exact Or.inr this
    · exact absurd hdec (by simp)

/-- **Field-to-nat lifting.** With every limb in range and the positional maximum below the field
    size, the field sum's `val` is the realized nat sum (no wrap-around). -/
theorem annSum_val (env : Variable → ZMod p) :
    ∀ (L : List (AnnTerm p)), (∀ e ∈ L, (env e.v).val < e.B) → annRestMax L < p →
      (annFieldSum L env).val = annNatSum L env := by
  intro L
  induction L with
  | nil =>
    intro _ hp
    simp only [annRestMax] at hp
    haveI : NeZero p := ⟨(by omega : (0 : ℕ) < p).ne'⟩
    simp [annFieldSum, annNatSum, ZMod.val_zero]
  | cons e t ih =>
    intro hb hp
    have hbe := hb e (List.mem_cons_self ..)
    have hbt : ∀ e' ∈ t, (env e'.v).val < e'.B := fun e' he' => hb e' (List.mem_cons_of_mem _ he')
    simp only [annRestMax] at hp
    haveI : NeZero p := ⟨(by omega : (0 : ℕ) < p).ne'⟩
    have hpt : annRestMax t < p := by omega
    have iht := ih hbt hpt
    have htnat : annNatSum t env ≤ annRestMax t := annNatSum_le env t hbt
    have hmul : (e.a * env e.v).val = e.a.val * (env e.v).val := by
      apply ZMod.val_mul_of_lt
      have h1 : e.a.val * (env e.v).val ≤ e.a.val * (e.B - 1) := Nat.mul_le_mul (le_refl _) (by omega)
      omega
    have hadd : (e.a * env e.v + annFieldSum t env).val
              = e.a.val * (env e.v).val + annNatSum t env := by
      have hlt : (e.a * env e.v).val + (annFieldSum t env).val < p := by
        rw [hmul, iht]
        have h1 : e.a.val * (env e.v).val ≤ e.a.val * (e.B - 1) := Nat.mul_le_mul (le_refl _) (by omega)
        omega
      rw [ZMod.val_add_of_lt hlt, hmul, iht]
    have hfs : annFieldSum (e :: t) env = e.a * env e.v + annFieldSum t env := by
      simp only [annFieldSum, List.map_cons, List.sum_cons]
    have hns : annNatSum (e :: t) env = e.a.val * (env e.v).val + annNatSum t env := by
      simp only [annNatSum, List.map_cons, List.sum_cons]
    rw [hfs, hns, hadd]

/-! ## The recognizer -/

/-- Annotate each `(variable, coefficient)` term with its value bound; `none` if any is unbounded. -/
def annotate (Bmap : Std.HashMap Variable Nat) : List (Variable × ZMod p) → Option (List (AnnTerm p))
  | [] => some []
  | (v, a) :: rest =>
      match Bmap[v]?, annotate Bmap rest with
      | some B, some anns => some (⟨v, a, B⟩ :: anns)
      | _, _ => none

theorem annotate_map (Bmap : Std.HashMap Variable Nat) :
    ∀ (terms : List (Variable × ZMod p)) (L : List (AnnTerm p)),
      annotate Bmap terms = some L → L.map (fun e => (e.v, e.a)) = terms := by
  intro terms
  induction terms with
  | nil => intro L h; rw [annotate] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | cons t rest ih =>
    intro L h
    obtain ⟨v, a⟩ := t
    rw [annotate] at h
    split at h
    · rename_i B anns hB hrest
      simp only [Option.some.injEq] at h; subst h
      simp only [List.map_cons]; rw [ih anns hrest]
    · exact absurd h (by simp)

theorem annotate_bounds (Bmap : Std.HashMap Variable Nat) :
    ∀ (terms : List (Variable × ZMod p)) (L : List (AnnTerm p)),
      annotate Bmap terms = some L → ∀ e ∈ L, Bmap[e.v]? = some e.B := by
  intro terms
  induction terms with
  | nil => intro L h; rw [annotate] at h; simp only [Option.some.injEq] at h; subst h; simp
  | cons t rest ih =>
    intro L h
    obtain ⟨v, a⟩ := t
    rw [annotate] at h
    split at h
    · rename_i B anns hB hrest
      simp only [Option.some.injEq] at h; subst h
      intro e he
      rcases List.mem_cons.1 he with h' | h'
      · subst h'; exact hB
      · exact ih anns hrest e h'
    · exact absurd h (by simp)

/-- The comparator sorting annotated terms by descending coefficient value. -/
def cmpDesc (x y : AnnTerm p) : Bool := decide (y.a.val ≤ x.a.val)

/-- Emit the entailed digit equalities from an already-sorted term list and a nat target. -/
def foldSorted (Ls : List (AnnTerm p)) (K : Nat) : List (Expression p) :=
  match annDecode Ls K with
  | some ds => ds.map (fun vd => eqExpr (Expression.var vd.1) (Expression.const ((vd.2 : ℕ) : ZMod p)))
  | none => []

theorem foldSorted_sound (Ls : List (AnnTerm p)) (K : Nat) (env : Variable → ZMod p)
    (hp0 : 0 < p) (hbLs : ∀ e ∈ Ls, (env e.v).val < e.B) (hKeq : annNatSum Ls env = K) :
    ∀ nc ∈ foldSorted Ls K, nc.eval env = 0 := by
  haveI : NeZero p := ⟨hp0.ne'⟩
  intro nc hnc
  unfold foldSorted at hnc
  split at hnc
  · rename_i ds hdec
    obtain ⟨vd, hvdmem, rfl⟩ := List.mem_map.1 hnc
    obtain ⟨v, d⟩ := vd
    have hvval := annDecode_forces env Ls K ds hdec hbLs hKeq v d hvdmem
    rw [eqExpr_eval]
    simp only [Expression.eval]
    rw [← hvval, ZMod.natCast_rightInverse (env v)]
    ring
  · simp at hnc

theorem foldSorted_vars (Ls : List (AnnTerm p)) (K : Nat) :
    ∀ nc ∈ foldSorted Ls K, ∀ x ∈ nc.vars, x ∈ Ls.map (fun e => e.v) := by
  intro nc hnc x hx
  unfold foldSorted at hnc
  split at hnc
  · rename_i ds hdec
    obtain ⟨vd, hvdmem, rfl⟩ := List.mem_map.1 hnc
    obtain ⟨v, d⟩ := vd
    have hxv : x = v := by
      simp only [eqExpr, Expression.vars] at hx
      simpa using hx
    rw [hxv]
    exact annDecode_vars Ls K ds hdec v d hvdmem
  · simp at hnc

/-- For one orientation `m` of the affine form, try to recognize a positional constant decomposition
    and emit the entailed digit equalities. -/
def tryFold (Bmap : Std.HashMap Variable Nat) (m : LinExpr p) : List (Expression p) :=
  match annotate Bmap m.terms with
  | none => []
  | some L =>
      if annRestMax (L.mergeSort cmpDesc) < p then
        foldSorted (L.mergeSort cmpDesc) ((-(m.const)).val)
      else []

theorem tryFold_sound (Bmap : Std.HashMap Variable Nat) (m : LinExpr p) (env : Variable → ZMod p)
    (hm : m.eval env = 0) (hbnd : ∀ v b, Bmap[v]? = some b → (env v).val < b) :
    ∀ nc ∈ tryFold Bmap m, nc.eval env = 0 := by
  intro nc hnc
  unfold tryFold at hnc
  split at hnc
  · simp at hnc
  · rename_i L hann
    split at hnc
    · rename_i hp
      set Ls := L.mergeSort (cmpDesc (p := p)) with hLs
      have hperm : List.Perm Ls L := List.mergeSort_perm L _
      have hbL : ∀ e ∈ L, (env e.v).val < e.B :=
        fun e he => hbnd e.v e.B (annotate_bounds Bmap m.terms L hann e he)
      have hbLs : ∀ e ∈ Ls, (env e.v).val < e.B :=
        fun e he => hbL e ((List.Perm.mem_iff hperm).1 he)
      have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hp
      have hfsval : (annFieldSum Ls env).val = annNatSum Ls env := annSum_val env Ls hbLs hp
      have hfs_eq : annFieldSum Ls env = -(m.const) := by
        have h1 : annFieldSum Ls env = annFieldSum L env := by
          unfold annFieldSum
          exact (List.Perm.map (fun e => e.a * env e.v) hperm).sum_eq
        have h2 : annFieldSum L env = (m.terms.map (fun t => t.2 * env t.1)).sum := by
          unfold annFieldSum
          conv_rhs => rw [← annotate_map Bmap m.terms L hann]
          rw [List.map_map]; rfl
        have h3 : m.const + (m.terms.map (fun t => t.2 * env t.1)).sum = 0 := by
          have := hm; simp only [LinExpr.eval] at this; exact this
        rw [h1, h2]; linear_combination h3
      have hKeq : annNatSum Ls env = (-(m.const)).val := by rw [← hfsval, hfs_eq]
      exact foldSorted_sound Ls ((-(m.const)).val) env hp0 hbLs hKeq nc hnc
    · simp at hnc

theorem tryFold_vars (Bmap : Std.HashMap Variable Nat) (m : LinExpr p) :
    ∀ nc ∈ tryFold Bmap m, ∀ x ∈ nc.vars, x ∈ m.terms.map Prod.fst := by
  intro nc hnc x hx
  unfold tryFold at hnc
  split at hnc
  · simp at hnc
  · rename_i L hann
    split at hnc
    · set Ls := L.mergeSort (cmpDesc (p := p)) with hLs
      have hperm : List.Perm Ls L := List.mergeSort_perm L _
      have hxLs : x ∈ Ls.map (fun e => e.v) := foldSorted_vars Ls _ nc hnc x hx
      have hxL : x ∈ L.map (fun e => e.v) := (List.Perm.mem_iff (List.Perm.map _ hperm)).1 hxLs
      have hLmap : L.map (fun e => e.v) = m.terms.map Prod.fst := by
        rw [← annotate_map Bmap m.terms L hann, List.map_map]; rfl
      rwa [hLmap] at hxL
    · simp at hnc

/-- Emit the entailed digit equalities for one constraint (both sign orientations tried). -/
def foldExprConstraints (Bmap : Std.HashMap Variable Nat) (c : Expression p) : List (Expression p) :=
  match linearize c with
  | none => []
  | some l => tryFold Bmap l ++ tryFold Bmap (l.scale (-1))

theorem foldExprConstraints_sound (Bmap : Std.HashMap Variable Nat) (c : Expression p)
    (env : Variable → ZMod p) (hc : c.eval env = 0)
    (hbnd : ∀ v b, Bmap[v]? = some b → (env v).val < b) :
    ∀ nc ∈ foldExprConstraints Bmap c, nc.eval env = 0 := by
  intro nc hnc
  unfold foldExprConstraints at hnc
  split at hnc
  · simp at hnc
  · rename_i l hlin
    have hlev : l.eval env = 0 := by rw [← linearize_eval c l hlin env]; exact hc
    rcases List.mem_append.1 hnc with h | h
    · exact tryFold_sound Bmap l env hlev hbnd nc h
    · have hsev : (l.scale (-1)).eval env = 0 := by rw [LinExpr.scale_eval, hlev, mul_zero]
      exact tryFold_sound Bmap (l.scale (-1)) env hsev hbnd nc h

theorem foldExprConstraints_vars (Bmap : Std.HashMap Variable Nat) (c : Expression p) :
    ∀ nc ∈ foldExprConstraints Bmap c, ∀ x ∈ nc.vars, x ∈ c.vars := by
  intro nc hnc x hx
  unfold foldExprConstraints at hnc
  split at hnc
  · simp at hnc
  · rename_i l hlin
    rcases List.mem_append.1 hnc with h | h
    · exact linearize_vars c l hlin x (tryFold_vars Bmap l nc h x hx)
    · have hx' : x ∈ (l.scale (-1)).terms.map Prod.fst := tryFold_vars Bmap (l.scale (-1)) nc h x hx
      rw [LinExpr.scale_terms_fst] at hx'
      exact linearize_vars c l hlin x hx'

/-- Variables occurring in a **stateful** bus interaction's payload. Pinning such a limb to a
    constant would strip the variable-shaped range check that memory send/receive pair-cancellation
    (`busPairCancel`/`busUnify`) relies on for byte-justification, turning a cancellable pair into two
    surviving interactions — a bus regression with no compensating variable win on that limb. We
    therefore *skip* folding any limb that feeds a stateful payload; the field win is kept only where
    it is genuinely free. -/
def statefulPayloadVars (cs : ConstraintSystem p) (bs : BusSemantics p) : List Variable :=
  (cs.busInteractions.filter (fun bi => bs.isStateful bi.busId)).flatMap
    (fun bi => bi.payload.flatMap Expression.vars)

/-- The pass: add every entailed positional-constant digit equality **whose pinned limb does not
    feed a stateful bus payload** (see `statefulPayloadVars`), keeping all interactions. The
    downstream affine/Gauss passes eliminate the now-pinned limbs. The gate makes `new` a *sublist*
    of the entailed constraints, so soundness/variable-subset carry over unchanged. -/
def constDecompPass : VerifiedPassW p := fun cs bs facts =>
  let T : BoundsMap p cs bs := BoundsMap.build facts
  let unsafeVars := statefulPayloadVars cs bs
  let new := (cs.algebraicConstraints.flatMap (foldExprConstraints T.map)).filter
    (fun nc => nc.vars.all (fun v => !unsafeVars.contains v))
  ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
    cs.addConstraints_correct bs new
      (fun env _hadm hsat nc hnc => by
        obtain ⟨sc, hsc, hncsc⟩ := List.mem_flatMap.1 (List.mem_of_mem_filter hnc)
        exact foldExprConstraints_sound T.map sc env (hsat.1 sc hsc)
          (T.sound env hsat.2) nc hncsc)
      (fun nc hnc z hz => by
        obtain ⟨sc, hsc, hncsc⟩ := List.mem_flatMap.1 (List.mem_of_mem_filter hnc)
        exact ConstraintSystem.mem_vars_of_constraint hsc
          (foldExprConstraints_vars T.map sc nc hncsc z hz))⟩

end ConstDecomp
