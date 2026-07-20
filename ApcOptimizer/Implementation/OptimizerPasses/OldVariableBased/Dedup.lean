import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Syntactic duplicate removal

Two syntactically identical algebraic constraints impose the same equation twice; two identical
*stateless* interactions impose the same lookup obligation twice. Keeping one of each changes
neither the satisfying set, nor the (stateful-only) side effects, nor `admissible` — dropping
the copies is a pure constraint- and bus-count win. Stateful duplicates are **not** touched: they
are observable in `sideEffects` (two sends of the same message are two sends).

Until the two-root unification landed (log entry 57) the optimized outputs contained no
syntactic duplicates at all, so this pass would have been a no-op; unifying a duplicate
decomposition's limbs turns its carry constraints and its raw-slot range check into literal
copies of the survivor's, which this pass now collects.

A `List.filter` cannot express "keep the first occurrence" — identical elements get identical
predicate values — hence the explicit recursion carrying the kept-so-far list. Constraints use
`List.dedup` (only membership matters for `satisfies`, so which occurrence survives is
irrelevant). Field-free, fact-free. -/

variable {p : ℕ}

/-! ## Keep-first dedup of stateless interactions -/

/-- Drop a stateless interaction if an identical one was already kept; keep every stateful
    interaction unconditionally. -/
def dedupStateless (bs : BusSemantics p) :
    (seen : List (BusInteraction (Expression p))) → List (BusInteraction (Expression p)) →
    List (BusInteraction (Expression p))
  | _, [] => []
  | seen, bi :: rest =>
    if bs.isStateful bi.busId then bi :: dedupStateless bs seen rest
    else if bi ∈ seen then dedupStateless bs seen rest
    else bi :: dedupStateless bs (bi :: seen) rest

theorem dedupStateless_subset (bs : BusSemantics p) :
    ∀ (seen l : List (BusInteraction (Expression p))),
      ∀ bi ∈ dedupStateless bs seen l, bi ∈ l := by
  intro seen l
  induction l generalizing seen with
  | nil => intro bi h; simp [dedupStateless] at h
  | cons b rest ih =>
    intro bi h
    rw [dedupStateless] at h
    split_ifs at h with h1 h2
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih seen bi h')
    · exact List.mem_cons_of_mem _ (ih seen bi h)
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (b :: seen) bi h')

/-- Every original interaction is either kept or was already in `seen`. -/
theorem dedupStateless_covers (bs : BusSemantics p) :
    ∀ (seen l : List (BusInteraction (Expression p))),
      ∀ bi ∈ l, bi ∈ dedupStateless bs seen l ∨ bi ∈ seen := by
  intro seen l
  induction l generalizing seen with
  | nil => intro bi h; simp at h
  | cons b rest ih =>
    intro bi h
    rw [dedupStateless]
    split_ifs with h1 h2
    · rcases List.mem_cons.1 h with rfl | h'
      · exact Or.inl (List.mem_cons_self ..)
      · exact (ih seen bi h').imp (List.mem_cons_of_mem _) id
    · rcases List.mem_cons.1 h with rfl | h'
      · exact Or.inr h2
      · exact ih seen bi h'
    · rcases List.mem_cons.1 h with rfl | h'
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih (b :: seen) bi h' with hk | hs
        · exact Or.inl (List.mem_cons_of_mem _ hk)
        · rcases List.mem_cons.1 hs with rfl | hs'
          · exact Or.inl (List.mem_cons_self ..)
          · exact Or.inr hs'

/-- The stateful sublist is untouched (syntactically). -/
theorem dedupStateless_statefulFilter (bs : BusSemantics p) :
    ∀ (seen l : List (BusInteraction (Expression p))),
      (dedupStateless bs seen l).filter (fun bi => bs.isStateful bi.busId)
        = l.filter (fun bi => bs.isStateful bi.busId) := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons b rest ih =>
    rw [dedupStateless]
    split_ifs with h1 h2
    · rw [List.filter_cons_of_pos (by simpa using h1),
          List.filter_cons_of_pos (by simpa using h1), ih]
    · rw [List.filter_cons_of_neg (by simpa using h1), ih]
    · rw [List.filter_cons_of_neg (by simpa using h1),
          List.filter_cons_of_neg (by simpa using h1), ih]

/-- The active∧stateful *evaluated* message list is untouched (what `admissible` consults). -/
theorem dedupStateless_evalFilter (bs : BusSemantics p) (env : Variable → ZMod p) :
    ∀ (seen l : List (BusInteraction (Expression p))),
      ((dedupStateless bs seen l).map (fun bi => bi.eval env)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
        = (l.map (fun bi => bi.eval env)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons b rest ih =>
    rw [dedupStateless]
    have hbus : (b.eval env).busId = b.busId := rfl
    split_ifs with h1 h2
    · simp only [List.map_cons, List.filter_cons, hbus, h1, ih]
    · -- dropped: its evaluated message fails the `isStateful` conjunct anyway
      rw [List.map_cons,
        List.filter_cons_of_neg (by have hf : bs.isStateful (b.eval env).busId = false := (by simpa using h1); simp [hf]), ih]
    · rw [List.map_cons,
        List.filter_cons_of_neg (by have hf : bs.isStateful (b.eval env).busId = false := (by simpa using h1); simp [hf]),
        List.map_cons,
        List.filter_cons_of_neg (by have hf : bs.isStateful (b.eval env).busId = false := (by simpa using h1); simp [hf]), ih]

/-! ## Hash-bucketed stateless dedup

`dedupStateless`' membership test `bi ∈ seen` scans the whole kept-so-far list — quadratic in the
number of stateless interactions. Bucketing `seen` by a structural hash of the interaction turns
each test into a one-bucket scan; `dedupStatelessFast_eq` proves the bucketed version returns the
identical list, so the pass output — and the whole `dedup_correct` proof — are unchanged. -/

/-- A structural hash of an expression (for bucketing). -/
def Expression.bHash : Expression p → UInt64
  | .const n => mixHash 11 (hash n.val)
  | .var x => mixHash 13 (hash x)
  | .add a b => mixHash 17 (mixHash a.bHash b.bHash)
  | .mul a b => mixHash 19 (mixHash a.bHash b.bHash)

/-- A structural hash of an interaction (bus id, multiplicity, payload). -/
def BusInteraction.bHash (bi : BusInteraction (Expression p)) : UInt64 :=
  mixHash (hash bi.busId)
    (mixHash bi.multiplicity.bHash (bi.payload.foldl (fun h e => mixHash h e.bHash) 7))

/-- `dedupStateless` with the `seen` set bucketed by `BusInteraction.bHash`: each membership test
    scans only the matching bucket. -/
def dedupStatelessFast (bs : BusSemantics p)
    (seen : Std.HashMap UInt64 (List (BusInteraction (Expression p)))) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p))
  | [] => []
  | bi :: rest =>
    if bs.isStateful bi.busId then bi :: dedupStatelessFast bs seen rest
    else if bi ∈ seen.getD bi.bHash [] then dedupStatelessFast bs seen rest
    else bi :: dedupStatelessFast bs (seen.insert bi.bHash (bi :: seen.getD bi.bHash [])) rest

/-- The bucketed dedup returns the identical list to `dedupStateless`, given a `seen` hash-map that
    agrees with the `seen` list on membership (each interaction sits in its own hash bucket). -/
theorem dedupStatelessFast_eq (bs : BusSemantics p)
    (bis : List (BusInteraction (Expression p))) :
    ∀ (seenL : List (BusInteraction (Expression p)))
      (seenH : Std.HashMap UInt64 (List (BusInteraction (Expression p)))),
      (∀ bi, bi ∈ seenL ↔ bi ∈ seenH.getD bi.bHash []) →
      dedupStatelessFast bs seenH bis = dedupStateless bs seenL bis := by
  induction bis with
  | nil => intro _ _ _; rfl
  | cons bi rest ih =>
    intro seenL seenH h
    rw [dedupStatelessFast, dedupStateless]
    by_cases hst : bs.isStateful bi.busId = true
    · rw [if_pos hst, if_pos hst, ih seenL seenH h]
    · rw [if_neg hst, if_neg hst]
      by_cases hmem : bi ∈ seenL
      · rw [if_pos ((h bi).mp hmem), if_pos hmem, ih seenL seenH h]
      · rw [if_neg (fun hc => hmem ((h bi).mpr hc)), if_neg hmem,
          ih (bi :: seenL) (seenH.insert bi.bHash (bi :: seenH.getD bi.bHash []))
            (by
              intro x
              rw [Std.HashMap.getD_insert]
              by_cases hbh : bi.bHash = x.bHash
              · rw [if_pos (by simpa using hbh), List.mem_cons, List.mem_cons]
                have hx := h x
                rw [← hbh] at hx
                exact or_congr_right hx
              · have hxne : x ≠ bi := fun he => hbh (by rw [he])
                rw [if_neg (by simpa using hbh), List.mem_cons]
                exact (or_iff_right hxne).trans (h x))]

/-- The bucketed dedup, started empty, equals `dedupStateless` started empty. -/
theorem dedupStatelessFast_eq_nil (bs : BusSemantics p)
    (bis : List (BusInteraction (Expression p))) :
    dedupStatelessFast bs ∅ bis = dedupStateless bs [] bis :=
  dedupStatelessFast_eq bs bis [] ∅ (by intro bi; simp [Std.HashMap.getD_empty])

/-! ## Hash-bucketed constraint dedup

`List.dedup` on the constraint list is O(C²·E) structural comparisons (28k constraints on
keccak's first cycle); `HashedDedup.hashedDedup` is its proven-identical bucketed twin. -/

/-- The bucketed constraint dedup: identical output to `List.dedup`, one-bucket membership
    tests instead of whole-tail scans. -/
def dedupConstraintsFast (l : List (Expression p)) : List (Expression p) :=
  HashedDedup.hashedDedup Expression.bHash l

theorem dedupConstraintsFast_eq (l : List (Expression p)) :
    dedupConstraintsFast l = l.dedup :=
  HashedDedup.hashedDedup_eq Expression.bHash l

/-! ## The pass -/

/-- The deduplicated system. -/
def ConstraintSystem.dedup (cs : ConstraintSystem p) (bs : BusSemantics p) :
    ConstraintSystem p :=
  { algebraicConstraints := cs.algebraicConstraints.dedup,
    busInteractions := dedupStateless bs [] cs.busInteractions }

/-- Dropping syntactic duplicates is equivalence- and invariant-preserving. -/
theorem ConstraintSystem.dedup_correct (cs : ConstraintSystem p) (bs : BusSemantics p) :
    PassCorrect cs (cs.dedup bs) [] bs := by
  have hiff : ∀ env, (cs.dedup bs).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    simp only [ConstraintSystem.satisfies, ConstraintSystem.dedup]
    constructor
    · rintro ⟨hc, hb⟩
      refine ⟨fun c hcm => hc c (List.mem_dedup.2 hcm), fun bi hbm => ?_⟩
      rcases dedupStateless_covers bs [] cs.busInteractions bi hbm with hk | hs
      · exact hb bi hk
      · simp at hs
    · rintro ⟨hc, hb⟩
      exact ⟨fun c hcm => hc c (List.mem_dedup.1 hcm),
        fun bi hbm => hb bi (dedupStateless_subset bs [] cs.busInteractions bi hbm)⟩
  have hside : ∀ env, (cs.dedup bs).sideEffects bs env = cs.sideEffects bs env := by
    intro env
    simp only [ConstraintSystem.sideEffects, ConstraintSystem.dedup]
    rw [dedupStateless_statefulFilter bs [] cs.busInteractions]
  have hadm : ∀ env, (cs.dedup bs).admissible bs env ↔ cs.admissible bs env := by
    intro env
    unfold ConstraintSystem.admissible
    simp only [ConstraintSystem.dedup]
    rw [dedupStateless_evalFilter bs env [] cs.busInteractions]
  have hsub : ∀ v ∈ (cs.dedup bs).vars, v ∈ cs.vars := by
    intro v hv
    rw [ConstraintSystem.mem_vars] at hv ⊢
    rcases hv with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hvbi⟩
    · exact Or.inl ⟨c, List.mem_dedup.1 hc, hvc⟩
    · exact Or.inr ⟨bi, dedupStateless_subset bs [] cs.busInteractions bi hbi, hvbi⟩
  refine PassCorrect.ofEnvEq ?_ ?_ hsub ?_
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    exact hinv env ((hiff env).1 hsat) bi
      (dedupStateless_subset bs [] cs.busInteractions bi hbi)
  · intro env hadm' hsat
    exact ⟨(hiff env).2 hsat, (hadm env).2 hadm',
      by rw [hside]; exact BusState.equiv_refl _⟩

/-- The deduplicated system, computed with the hash-bucketed stateless dedup. Equal to
    `ConstraintSystem.dedup` (`dedupFast_eq`), so it inherits `dedup_correct`. -/
def ConstraintSystem.dedupFast (cs : ConstraintSystem p) (bs : BusSemantics p) :
    ConstraintSystem p :=
  { algebraicConstraints := dedupConstraintsFast cs.algebraicConstraints,
    busInteractions := dedupStatelessFast bs ∅ cs.busInteractions }

theorem ConstraintSystem.dedupFast_eq (cs : ConstraintSystem p) (bs : BusSemantics p) :
    cs.dedupFast bs = cs.dedup bs := by
  simp only [ConstraintSystem.dedupFast, ConstraintSystem.dedup, dedupStatelessFast_eq_nil,
    dedupConstraintsFast_eq]

/-- The duplicate-removal pass (runs the hash-bucketed dedup; correctness via `dedupFast_eq`). -/
def dedupPass : VerifiedPass p := fun cs bs =>
  ⟨cs.dedupFast bs, [], (cs.dedupFast_eq bs).symm ▸ cs.dedup_correct bs⟩
