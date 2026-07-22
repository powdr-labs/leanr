import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate

set_option autoImplicit false

/-! # Dense domain-constant subexpression folding — shared foundation

Variable-free domain/assignment enumeration, the covered-set predicate/filter, the ordered inverted
covered-index and its completeness lemmas, the fold index (`DenseFoldIdx`), and the containment
soundness lemmas shared by the domain-fold pass (`DomainFoldRuntime.lean` / `DomainFoldProof.lean`)
and several other passes. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Small dense expression predicates -/

def DenseExpr.hasVar : DenseExpr p → Bool
  | .const _ => false
  | .var _ => true
  | .add a b => a.hasVar || b.hasVar
  | .mul a b => a.hasVar || b.hasVar

/-- Whether any variable of `xs` occurs in the expression. -/
def DenseExpr.anyVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.anyVarIn xs || b.anyVarIn xs
  | .mul a b => a.anyVarIn xs || b.anyVarIn xs

/-- Whether `e` has a variable-free node (a constant subexpression still to fold). -/
def DenseExpr.hasConstFoldableNode : DenseExpr p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b => !(DenseExpr.add a b).hasVar || a.hasConstFoldableNode || b.hasConstFoldableNode
  | .mul a b => !(DenseExpr.mul a b).hasVar || a.hasConstFoldableNode || b.hasConstFoldableNode

/-! ## Dense `findDomainAlg`, `coveredBy`, `coveredCsOf` -/

/-- Find `i`'s finite domain: the roots (`denseRootsIn`) of the first constraint mentioning `i`
    that yields any, skipping those that yield none. -/
def denseFindDomainAlg (all : List (DenseExpr p)) (i : VarId) : Option (List (ZMod p)) :=
  match all with
  | [] => none
  | c :: rest =>
    if c.mentions i then
      match denseRootsIn i c with
      | some d => some d
      | none => denseFindDomainAlg rest i
    else denseFindDomainAlg rest i

/-- Whether `c` mentions a variable, and every variable it mentions lies in `xs`. -/
def denseCoveredBy (xs : List VarId) (c : DenseExpr p) : Bool :=
  c.hasVar && c.varsInF xs

/-- The algebraic constraints covered by (contained wholly within) the variable set `xs`. -/
def denseCoveredCsOf (d : DenseConstraintSystem p) (xs : List VarId) : List (DenseExpr p) :=
  d.algebraicConstraints.filter (denseCoveredBy xs)

/-! ## Dense `groupDoms` -/

/-- Look up each variable's finite domain in `es`, all-or-nothing over the whole key list. -/
def denseGroupDoms (es : List (DenseExpr p)) :
    List VarId → Option (List (VarId × List (ZMod p)))
  | [] => some []
  | i :: rest =>
    match denseFindDomainAlg es i, denseGroupDoms es rest with
    | some d, some ds => some ((i, d) :: ds)
    | _, _ => none

/-! ## Dense enumeration of assignments -/

/-- The Cartesian product of a list of `(variable, domain)` pairs, as a list of full assignments. -/
def denseAssignments : List (VarId × List (ZMod p)) → List (List (VarId × ZMod p))
  | [] => [[]]
  | (i, d) :: rest => (denseAssignments rest).flatMap (fun a => d.map (fun v => (i, v) :: a))

/-! ## `denseGroupDoms` key structure -/

/-- `denseGroupDoms` yields the target keys, in order. -/
theorem denseGroupDoms_fst (es : List (DenseExpr p)) :
    ∀ (xs : List VarId) (doms : List (VarId × List (ZMod p))),
      denseGroupDoms es xs = some doms → doms.map Prod.fst = xs := by
  intro xs
  induction xs with
  | nil => intro doms h; simp only [denseGroupDoms, Option.some.injEq] at h; subst h; rfl
  | cons i rest ih =>
      intro doms h
      rw [denseGroupDoms] at h
      cases hd : denseFindDomainAlg es i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some d =>
          cases hr : denseGroupDoms es rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds =>
              rw [hd, hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp [ih ds hr]

/-! ## Ordered dense inverted index

`denseCoveredIdx` restores the covered items to original order and equals the plain filter whenever
every `Q`-item shares a variable with `xs`. The underlying index is from `DomainBatch.lean`. -/

variable {α : Type}

/-- Ordered covered items for target `xs`: the in-range, `Q`-satisfying elements at the index's
    candidate positions for `xs`, restored to original order. -/
def denseCoveredIdx (idx : DenseCovIndex) (arr : Array α) (Q : α → Bool) (xs : List VarId) :
    List α :=
  let uniq := ((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList
  (uniq.mergeSort (· ≤ ·)).filterMap (fun i =>
    if h : i < arr.size then (if Q arr[i] then some arr[i] else none) else none)

/-- Inserting a position into dense buckets never removes an existing membership. -/
theorem denseInner_getD_mono (i : Nat) (vs : List VarId) (w : VarId) (j : Nat) :
    ∀ (m : Std.HashMap VarId (List Nat)), j ∈ m.getD w [] →
    j ∈ (vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m).getD w [] := by
  induction vs with
  | nil => intro m hj; simpa using hj
  | cons v0 rest ih =>
    intro m hj
    simp only [List.foldl_cons]
    apply ih
    rw [Std.HashMap.getD_insert]
    by_cases h : (v0 == w) = true
    · rw [if_pos h]
      have hvw : v0 = w := eq_of_beq h
      subst hvw
      exact List.mem_cons_of_mem _ hj
    · rw [if_neg h]; exact hj

/-- After inserting `i` into every dense bucket of `vs`, `i` is in the bucket of each `v ∈ vs`. -/
theorem denseInner_getD_self (i : Nat) (vs : List VarId) (v : VarId) :
    ∀ (m : Std.HashMap VarId (List Nat)), v ∈ vs →
    i ∈ (vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m).getD v [] := by
  induction vs with
  | nil => intro m hv; simp at hv
  | cons v0 rest ih =>
    intro m hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · apply denseInner_getD_mono
      rw [Std.HashMap.getD_insert, if_pos (by simp)]
      exact List.mem_cons_self
    · exact ih _ hv

/-- **Index completeness (buckets).** Every item at position `i` with variable `v` is bucketed
    under `v`. -/
theorem denseBuildStep_bucket_complete (varsOf : α → List VarId) :
    ∀ (l : List (α × Nat)) (a : α) (i : Nat), (a, i) ∈ l → ∀ (v : VarId), v ∈ varsOf a →
      i ∈ (l.foldr (denseBuildStep varsOf) ⟨∅, []⟩).buckets.getD v [] := by
  intro l
  induction l with
  | nil => intro a i hai; simp at hai
  | cons ai0 rest ih =>
    intro a i hai v hv
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hai with heq | hmem
    · rw [← heq]
      cases hvs : varsOf a with
      | nil => rw [hvs] at hv; simp at hv
      | cons w0 ws =>
        rw [denseBuildStep_buckets_cons varsOf (a, i) _ w0 ws hvs]
        exact denseInner_getD_self i (w0 :: ws) v _ (by rw [← hvs]; exact hv)
    · have hrec : i ∈ (rest.foldr (denseBuildStep varsOf) ⟨∅, []⟩).buckets.getD v [] := ih a i hmem v hv
      cases hvs : varsOf ai0.1 with
      | nil => rw [denseBuildStep_buckets_nil varsOf ai0 _ hvs]; exact hrec
      | cons w0 ws =>
        rw [denseBuildStep_buckets_cons varsOf ai0 _ w0 ws hvs]
        exact denseInner_getD_mono ai0.2 (w0 :: ws) v i _ hrec

/-- A position bucketed under a variable of `xs` is a dense candidate. -/
theorem denseMem_candidates (idx : DenseCovIndex) (xs : List VarId) (v : VarId) (i : Nat)
    (hv : v ∈ xs) (hi : i ∈ idx.buckets.getD v []) : i ∈ denseCandidates idx xs :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨v, hv, hi⟩)

/-- `denseCoveredIdx` equals the plain filter for any index whose candidate set is complete (every
    in-range `Q`-position is a candidate of `xs`); extra candidate positions are harmless, being
    re-checked against the in-range bound and `Q`. -/
theorem denseCoveredIdx_eq_filter_of_complete (idx : DenseCovIndex) (items : List α)
    (Q : α → Bool) (xs : List VarId)
    (hcomplete : ∀ (i : Nat) (hi : i < items.length),
      Q items[i] = true → i ∈ denseCandidates idx xs) :
    denseCoveredIdx idx items.toArray Q xs = items.filter Q := by
  rw [denseCoveredIdx]
  simp only [List.size_toArray, List.getElem_toArray]
  set cand := denseCandidates idx xs with hcand
  set gI : Nat → Option α :=
    (fun i => if h : i < items.length then (if Q items[i] then some items[i] else none) else none)
    with hgI
  set sortedL := ((cand.foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).mergeSort (· ≤ ·)
    with hsortedL
  have F1 : ∀ i, i ∈ sortedL ↔ i ∈ cand := by
    intro i
    rw [hsortedL, List.mem_mergeSort, Std.HashSet.mem_toList, mem_foldl_insert]
    simp [Std.HashSet.not_mem_empty]
  have hnodupUniq : ((cand.foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).Nodup :=
    Std.HashSet.distinct_toList.imp (fun {a b} h => by simpa using h)
  have F2 : sortedL.Nodup := by
    rw [hsortedL]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hnodupUniq
  have F3 : sortedL.Pairwise (· ≤ ·) := by
    rw [hsortedL]; exact List.sortedLE_mergeSort.pairwise
  have F4 : ∀ (i : Nat) (hi : i < items.length), Q items[i] = true → i ∈ cand := hcomplete
  set keepB : Nat → Bool := (fun i => (gI i).isSome) with hkeepB
  have hkeep_lt : ∀ i, keepB i = true → i < items.length := by
    intro i hk
    by_contra hcon
    simp only [hkeepB, hgI, dif_neg hcon, Option.isSome_none, Bool.false_eq_true] at hk
  have hkeep_Q : ∀ i, keepB i = true → ∃ (_ : i < items.length), Q items[i] = true := by
    intro i hk
    have hlt := hkeep_lt i hk
    refine ⟨hlt, ?_⟩
    by_contra hQc
    simp only [hkeepB, hgI, dif_pos hlt, if_neg hQc, Option.isSome_none, Bool.false_eq_true] at hk
  have L1 : ∀ (l : List Nat), l.filterMap gI = (l.filter keepB).filterMap gI := by
    intro l
    induction l with
    | nil => rfl
    | cons a rest ih =>
      by_cases hk : keepB a = true
      · rw [List.filter_cons_of_pos hk]
        cases hga : gI a with
        | none => rw [hkeepB] at hk; simp [hga] at hk
        | some b => rw [List.filterMap_cons_some hga, List.filterMap_cons_some hga, ih]
      · rw [List.filter_cons_of_neg hk]
        have hga : gI a = none := by
          by_contra hne
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hne
          exact hk (by simp [hkeepB, hb])
        rw [List.filterMap_cons_none hga, ih]
  have claim1 : (List.range items.length).filterMap gI = items.filter Q := by
    have hrange : List.range items.length = items.zipIdx.map Prod.snd := by
      rw [List.zipIdx_map_snd, List.range_eq_range']
    rw [hrange, List.filterMap_map]
    rw [filterMap_congr' items.zipIdx
      (f := gI ∘ Prod.snd) (g := fun q => if Q q.1 then some q.1 else none)
      (by
        rintro ⟨a, j⟩ hp
        obtain ⟨_, hlt, heq⟩ := List.mem_zipIdx (k := 0) hp
        have hlt' : j < items.length := by simpa using hlt
        have heq' : items[j]'hlt' = a := by simpa using heq.symm
        simp only [Function.comp_apply, hgI, dif_pos hlt', heq'])]
    rw [filterMap_if_some]
    show ((items.zipIdx.filter (Q ∘ Prod.fst)).map Prod.fst) = items.filter Q
    rw [← List.filter_map, List.zipIdx_map_fst]
  have L2 : sortedL.filter keepB = (List.range items.length).filter keepB := by
    refine List.Perm.eq_of_sortedLE
      (List.Pairwise.sublist List.filter_sublist F3).sortedLE
      (List.Pairwise.sublist List.filter_sublist List.pairwise_le_range).sortedLE
      ((List.perm_ext_iff_of_nodup
        (List.Nodup.sublist List.filter_sublist F2)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)).mpr ?_)
    intro i
    rw [List.mem_filter, List.mem_filter, F1 i, List.mem_range]
    constructor
    · rintro ⟨hcandi, hk⟩; exact ⟨hkeep_lt i hk, hk⟩
    · rintro ⟨_, hk⟩
      obtain ⟨hlt', hQ⟩ := hkeep_Q i hk
      exact ⟨F4 i hlt' hQ, hk⟩
  calc sortedL.filterMap gI
      = (sortedL.filter keepB).filterMap gI := L1 sortedL
    _ = ((List.range items.length).filter keepB).filterMap gI := by rw [L2]
    _ = (List.range items.length).filterMap gI := (L1 _).symm
    _ = items.filter Q := claim1

/-- Completeness of a fresh dense build: every item position is bucketed under each variable
    `varsOf` yields for it. -/
theorem denseBuild_complete (varsOf : α → List VarId) (items : List α)
    (i : Nat) (hi : i < items.length) (v : VarId) (hv : v ∈ varsOf items[i]) :
    i ∈ (denseCovBuild varsOf items).buckets.getD v [] := by
  have hz : (items.zipIdx)[i]? = some (items[i], i) := by
    rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hi]; simp
  exact denseBuildStep_bucket_complete varsOf items.zipIdx items[i] i (List.mem_of_getElem? hz) v hv

/-! ## The dense fold index -/

/-- The dense fold index (plain data — no proof fields; completeness is threaded externally
    through the correctness proofs). -/
structure DenseFoldIdx (p : ℕ) where
  idx : DenseCovIndex
  arr : Array (DenseExpr p)
  bisIdx : DenseCovIndex
  arrBis : Array (BusInteraction (DenseExpr p))

/-- Per-item variable list, deduplicated: one bucket entry per distinct variable, not per
    occurrence. Same membership, so bucket completeness is unchanged. -/
def denseDedupVarsOf (c : DenseExpr p) : List VarId :=
  HashedDedup.hashedEraseDups (hash ·) c.vars

/-- `denseDedupVarsOf` for interactions (multiplicity + payload occurrences). -/
def denseDedupBiVarsOf (bi : BusInteraction (DenseExpr p)) : List VarId :=
  HashedDedup.hashedEraseDups (hash ·) (denseBIVars bi)

/-- Build the dense fold index for a system; buckets by the per-item deduped variable list, one
    entry per *distinct* variable. -/
def DenseFoldIdx.mk' (d : DenseConstraintSystem p) : DenseFoldIdx p where
  idx := denseCovBuild denseDedupVarsOf d.algebraicConstraints
  arr := d.algebraicConstraints.toArray
  bisIdx := denseCovBuild denseDedupBiVarsOf d.busInteractions
  arrBis := d.busInteractions.toArray

/-- Refresh after an accepted fold with no rebuild: the in-place fold is order- and
    length-preserving and only shrinks variable sets, so both bucket maps stay complete; only the
    item arrays are re-materialized. -/
def DenseFoldIdx.refresh (old : DenseFoldIdx p) (ro : DenseConstraintSystem p) : DenseFoldIdx p where
  idx := old.idx
  arr := ro.algebraicConstraints.toArray
  bisIdx := old.bisIdx
  arrBis := ro.busInteractions.toArray

/-! ## Foundational soundness lemmas -/

/-- A dense expression with a variable has a nonempty `vars` list. -/
theorem denseExpr_hasVar_vars_ne_nil (c : DenseExpr p) (h : c.hasVar = true) : c.vars ≠ [] := by
  induction c with
  | const n => simp [DenseExpr.hasVar] at h
  | var y => simp [DenseExpr.vars]
  | add a b iha ihb =>
    intro hnil
    rw [DenseExpr.vars, List.append_eq_nil_iff] at hnil
    simp only [DenseExpr.hasVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact iha h hnil.1
    · exact ihb h hnil.2
  | mul a b iha ihb =>
    intro hnil
    rw [DenseExpr.vars, List.append_eq_nil_iff] at hnil
    simp only [DenseExpr.hasVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact iha h hnil.1
    · exact ihb h hnil.2

/-- `denseContainsFast` soundness. -/
theorem denseContainsFast_sound (xs : List VarId) (v : VarId) (h : denseContainsFast xs v = true) :
    v ∈ xs := by
  induction xs with
  | nil => simp [denseContainsFast] at h
  | cons x rest ih =>
    simp only [denseContainsFast, Bool.or_eq_true] at h
    rcases h with h | h
    · exact List.mem_cons.2 (Or.inl (eq_of_beq h))
    · exact List.mem_cons.2 (Or.inr (ih h))

/-- `DenseExpr.varsInF` soundness (every variable lies in `xs`). -/
theorem denseVarsInF_sound (xs : List VarId) :
    ∀ (c : DenseExpr p), c.varsInF xs = true → ∀ v ∈ c.vars, v ∈ xs := by
  intro c
  induction c with
  | const n => intro _ v hv; simp [DenseExpr.vars] at hv
  | var y =>
      intro h v hv
      simp only [DenseExpr.vars, List.mem_singleton] at hv; subst hv
      exact denseContainsFast_sound xs v h
  | add a b iha ihb =>
      intro h v hv
      simp only [DenseExpr.varsInF, Bool.and_eq_true] at h
      simp only [DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv
  | mul a b iha ihb =>
      intro h v hv
      simp only [DenseExpr.varsInF, Bool.and_eq_true] at h
      simp only [DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha h.1 v hv
      · exact ihb h.2 v hv

/-- A `denseCoveredBy`-item shares a variable with the target `xs`. -/
theorem denseCoveredBy_shares_var (xs : List VarId) (c : DenseExpr p) (h : denseCoveredBy xs c = true) :
    ∃ v ∈ c.vars, v ∈ xs := by
  rw [denseCoveredBy, Bool.and_eq_true] at h
  obtain ⟨hhv, hvin⟩ := h
  obtain ⟨v, hmem⟩ := List.exists_mem_of_ne_nil c.vars (denseExpr_hasVar_vars_ne_nil c hhv)
  exact ⟨v, hmem, denseVarsInF_sound xs c hvin v hmem⟩

/-! ## Dense `svSet` -/

/-- The single-variable-constraint set: variables occurring in exactly one algebraic constraint
    (as their constraint's sole occurring variable). -/
def denseSvSet (d : DenseConstraintSystem p) : Std.HashSet VarId :=
  d.algebraicConstraints.foldl (init := ∅) fun s c =>
    match c.vars.dedup with
    | [x] => s.insert x
    | _ => s
