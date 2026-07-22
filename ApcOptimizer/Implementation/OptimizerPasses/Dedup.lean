import ApcOptimizer.Implementation.OptimizerPasses.Adapter
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense syntactic-duplicate removal

Drops structurally-duplicate algebraic constraints and stateless bus interactions (keep-first),
keeping the first occurrence. Because dedup compares whole values structurally (equality of
`DenseExpr`/`BusInteraction (DenseExpr p)`), it only shrinks the constraint/interaction sets — the
satisfying set, the stateful-only side effects and `admissible` are all unchanged.

Correctness rests on the exact structural comparison (`denseDedupStateless`, `List.dedup`); the
hash-bucketed twins — `denseDedupStatelessFast` (interactions) and `denseDedupConstraintsFast`
(constraints, via `HashedDedup.hashedDedup`) — are proven to return the *identical* lists
(`denseDedupStatelessFast_eq`, `denseDedupConstraintsFast_eq`, both hash-agnostic), so the pass runs
the fast versions (`DenseConstraintSystem.dedupN`) while its correctness is stated over the exact
version. The `DensePassCorrect` proof and the pass itself live in `DedupProof.lean` (which imports
`Bridge`); this module stays `Bridge`-free so its runtime defs and structural helpers can be reused
by other dense modules (`DenseExpr.bHash`, `denseDedupStateless`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

-- `DenseExpr` has decidable equality (needed for `List.dedup` and the `∈ seen` membership test);
-- it also induces `DecidableEq (BusInteraction (DenseExpr p))` via the generic instance.
deriving instance DecidableEq for DenseExpr

/-! ## Dense keep-first stateless dedup (reference version) -/

/-- Drop a stateless interaction if an identical one was already kept; keep every stateful
    interaction unconditionally. -/
def denseDedupStateless (bs : BusSemantics p) :
    (seen : List (BusInteraction (DenseExpr p))) → List (BusInteraction (DenseExpr p)) →
    List (BusInteraction (DenseExpr p))
  | _, [] => []
  | seen, bi :: rest =>
    if bs.isStateful bi.busId then bi :: denseDedupStateless bs seen rest
    else if bi ∈ seen then denseDedupStateless bs seen rest
    else bi :: denseDedupStateless bs (bi :: seen) rest

/-- Every kept interaction was in the input. -/
theorem denseDedupStateless_subset (bs : BusSemantics p) :
    ∀ (seen l : List (BusInteraction (DenseExpr p))),
      ∀ bi ∈ denseDedupStateless bs seen l, bi ∈ l := by
  intro seen l
  induction l generalizing seen with
  | nil => intro bi h; simp [denseDedupStateless] at h
  | cons b rest ih =>
    intro bi h
    rw [denseDedupStateless] at h
    split_ifs at h with h1 h2
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih seen bi h')
    · exact List.mem_cons_of_mem _ (ih seen bi h)
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (b :: seen) bi h')

/-- Every original interaction is either kept or was already in `seen`. -/
theorem denseDedupStateless_covers (bs : BusSemantics p) :
    ∀ (seen l : List (BusInteraction (DenseExpr p))),
      ∀ bi ∈ l, bi ∈ denseDedupStateless bs seen l ∨ bi ∈ seen := by
  intro seen l
  induction l generalizing seen with
  | nil => intro bi h; simp at h
  | cons b rest ih =>
    intro bi h
    rw [denseDedupStateless]
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
theorem denseDedupStateless_statefulFilter (bs : BusSemantics p) :
    ∀ (seen l : List (BusInteraction (DenseExpr p))),
      (denseDedupStateless bs seen l).filter (fun bi => bs.isStateful bi.busId)
        = l.filter (fun bi => bs.isStateful bi.busId) := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons b rest ih =>
    rw [denseDedupStateless]
    split_ifs with h1 h2
    · rw [List.filter_cons_of_pos (by simpa using h1),
          List.filter_cons_of_pos (by simpa using h1), ih]
    · rw [List.filter_cons_of_neg (by simpa using h1), ih]
    · rw [List.filter_cons_of_neg (by simpa using h1),
          List.filter_cons_of_neg (by simpa using h1), ih]

/-! ## Hash-bucketed stateless dedup -/

/-- A structural hash of a dense expression (for bucketing; VarId-based at the leaves). -/
def DenseExpr.bHash : DenseExpr p → UInt64
  | .const n => mixHash 11 (hash n.val)
  | .var i => mixHash 13 (hash i)
  | .add a b => mixHash 17 (mixHash a.bHash b.bHash)
  | .mul a b => mixHash 19 (mixHash a.bHash b.bHash)

/-- A structural hash of a dense interaction (bus id, multiplicity, payload). -/
def denseBIbHash (bi : BusInteraction (DenseExpr p)) : UInt64 :=
  mixHash (hash bi.busId)
    (mixHash bi.multiplicity.bHash (bi.payload.foldl (fun h e => mixHash h e.bHash) 7))

/-- `denseDedupStateless` with the `seen` set bucketed by `denseBIbHash`: each membership test
    scans only the matching bucket. -/
def denseDedupStatelessFast (bs : BusSemantics p)
    (seen : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))) :
    List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p))
  | [] => []
  | bi :: rest =>
    if bs.isStateful bi.busId then bi :: denseDedupStatelessFast bs seen rest
    else if bi ∈ seen.getD (denseBIbHash bi) [] then denseDedupStatelessFast bs seen rest
    else bi :: denseDedupStatelessFast bs
      (seen.insert (denseBIbHash bi) (bi :: seen.getD (denseBIbHash bi) [])) rest

/-- The bucketed dedup returns the identical list to `denseDedupStateless`, given a `seen` hash-map
    that agrees with the `seen` list on membership. -/
theorem denseDedupStatelessFast_eq (bs : BusSemantics p)
    (bis : List (BusInteraction (DenseExpr p))) :
    ∀ (seenL : List (BusInteraction (DenseExpr p)))
      (seenH : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))),
      (∀ bi, bi ∈ seenL ↔ bi ∈ seenH.getD (denseBIbHash bi) []) →
      denseDedupStatelessFast bs seenH bis = denseDedupStateless bs seenL bis := by
  induction bis with
  | nil => intro _ _ _; rfl
  | cons bi rest ih =>
    intro seenL seenH h
    rw [denseDedupStatelessFast, denseDedupStateless]
    by_cases hst : bs.isStateful bi.busId = true
    · rw [if_pos hst, if_pos hst, ih seenL seenH h]
    · rw [if_neg hst, if_neg hst]
      by_cases hmem : bi ∈ seenL
      · rw [if_pos ((h bi).mp hmem), if_pos hmem, ih seenL seenH h]
      · rw [if_neg (fun hc => hmem ((h bi).mpr hc)), if_neg hmem,
          ih (bi :: seenL) (seenH.insert (denseBIbHash bi) (bi :: seenH.getD (denseBIbHash bi) []))
            (by
              intro x
              rw [Std.HashMap.getD_insert]
              by_cases hbh : denseBIbHash bi = denseBIbHash x
              · rw [if_pos (by simpa using hbh), List.mem_cons, List.mem_cons]
                have hx := h x
                rw [← hbh] at hx
                exact or_congr_right hx
              · have hxne : x ≠ bi := fun he => hbh (by rw [he])
                rw [if_neg (by simpa using hbh), List.mem_cons]
                exact (or_iff_right hxne).trans (h x))]

/-- The bucketed dedup, started empty, equals `denseDedupStateless` started empty. -/
theorem denseDedupStatelessFast_eq_nil (bs : BusSemantics p)
    (bis : List (BusInteraction (DenseExpr p))) :
    denseDedupStatelessFast bs ∅ bis = denseDedupStateless bs [] bis :=
  denseDedupStatelessFast_eq bs bis [] ∅ (by intro bi; simp [Std.HashMap.getD_empty])

/-! ## Hash-bucketed constraint dedup

`List.dedup` on the constraint list is O(C²·E) structural comparisons; `HashedDedup.hashedDedup`
is its proven-identical bucketed twin (the identity `hashedDedup_eq` is hash-agnostic, so the
output is byte-identical to `List.dedup`). -/

/-- The bucketed constraint dedup: identical output to `List.dedup`, one-bucket membership tests
    instead of whole-tail scans. -/
def denseDedupConstraintsFast (l : List (DenseExpr p)) : List (DenseExpr p) :=
  HashedDedup.hashedDedup DenseExpr.bHash l

theorem denseDedupConstraintsFast_eq (l : List (DenseExpr p)) :
    denseDedupConstraintsFast l = l.dedup :=
  HashedDedup.hashedDedup_eq DenseExpr.bHash l

/-! ## The deduplicated dense system -/

/-- The deduplicated dense system (reference: keep-first stateless dedup). -/
def DenseConstraintSystem.dedup (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.dedup,
    busInteractions := denseDedupStateless bs [] d.busInteractions }

/-- Dedup only drops interactions and constraints, so it preserves coverage. -/
theorem DenseConstraintSystem.dedup_covered {reg : VarRegistry} {d : DenseConstraintSystem p}
    {bs : BusSemantics p} (hc : d.CoveredBy reg) : (d.dedup bs).CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hc
  constructor
  · intro e he
    simp only [DenseConstraintSystem.dedup] at he
    exact hac e (List.mem_dedup.1 he)
  · intro bi hbimem
    simp only [DenseConstraintSystem.dedup] at hbimem
    exact hbi bi (denseDedupStateless_subset bs [] d.busInteractions bi hbimem)

/-! ## The fully hash-bucketed dense system -/

/-- The deduplicated dense system, computed with the hash-bucketed constraint dedup and the
    hash-bucketed keep-first stateless dedup. Equal to `DenseConstraintSystem.dedup`
    (`dedupN_eq`), so it inherits its correctness and coverage. -/
def DenseConstraintSystem.dedupN (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := denseDedupConstraintsFast d.algebraicConstraints,
    busInteractions := denseDedupStatelessFast bs ∅ d.busInteractions }

theorem DenseConstraintSystem.dedupN_eq (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    d.dedupN bs = d.dedup bs := by
  simp only [DenseConstraintSystem.dedupN, DenseConstraintSystem.dedup,
    denseDedupStatelessFast_eq_nil, denseDedupConstraintsFast_eq]

/-- `dedupN` preserves coverage (via `dedupN_eq` through `dedup_covered`). -/
theorem DenseConstraintSystem.dedupN_covered {reg : VarRegistry} {d : DenseConstraintSystem p}
    {bs : BusSemantics p} (hc : d.CoveredBy reg) : (d.dedupN bs).CoveredBy reg := by
  rw [DenseConstraintSystem.dedupN_eq]; exact DenseConstraintSystem.dedup_covered hc

end ApcOptimizer.Dense
