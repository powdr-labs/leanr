import ApcOptimizer.Implementation.OptimizerPasses.DomainProp

set_option autoImplicit false

/-! # Inverted index for covered-set scans

The finite-domain passes (`domainBatch`, `domainFold`, `reencode`) repeatedly ask, for a *target*
variable set `xs`, which items (algebraic constraints / bus interactions) have **all** their
variables in `xs` — the "covered" items, filtered by a boolean predicate `Q` (e.g.
`Expression.varsInF xs`, or `coveredBy xs`). Done naively (`items.filter Q`) this is a full-system
scan **per target**, and the passes run one target per constraint and per interaction, so the cost
is O(#targets × #system) — the dominant runtime term on large circuits.

This module builds, once per pass invocation, a variable→positions inverted index. A target's
covered items are then found by gathering only the items that share a variable with `xs` (plus the
variable-less items, covered by every `xs`) and re-checking `Q` on those few candidates — turning
the per-target cost from O(#system) into O(local). Correctness of the passes never depends on the
index being *complete*: `coveredIdx` re-applies the exact predicate `Q`, so every returned item
genuinely satisfies `Q` (`coveredIdx_mem`), which is all the enumeration soundness proofs consume.
This mirrors the candidate-then-reverify pattern already used by `busPairCancel`'s `recvIndex`.

Purely `List`/`Nat`/`Std.HashMap` combinatorics — no field theory, generic over the item type. -/

namespace CoveredIndex

universe u

variable {α : Type u}

/-- Inverted index over a list of items: `buckets v` is the positions (indices into the item list)
    of the items whose variable set contains `v`; `varless` is the positions of the items with no
    variables (covered by every target `xs`). -/
structure CovIndex where
  buckets : Std.HashMap Variable (List Nat)
  varless : List Nat

/-- One step of the index build for an item paired with its position: insert the position into
    every bucket of the variables the item mentions (or into `varless` when it mentions none).
    Split out of `build` so the completeness lemmas below can induct on it. -/
def buildStep (varsOf : α → List Variable) (ai : α × Nat) (idx : CovIndex) : CovIndex :=
  match varsOf ai.1 with
  | [] => ⟨idx.buckets, ai.2 :: idx.varless⟩
  | vs => ⟨vs.foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets, idx.varless⟩

/-- Build the inverted index in one pass over `items` paired with their positions. Mirrors
    `busPairCancel`'s `recvIndex`: a right fold inserting each position into every bucket of the
    variables it mentions (or into `varless` when it mentions none). -/
def build (varsOf : α → List Variable) (items : List α) : CovIndex :=
  items.zipIdx.foldr (buildStep varsOf) ⟨∅, []⟩

/-- The candidate positions for target `xs`: every position bucketed under a variable of `xs`,
    plus the variable-less positions. -/
def candidates (idx : CovIndex) (xs : List Variable) : List Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])) ++ idx.varless

/-- The covered items for target `xs`: gather the candidate positions, deduplicate them in **linear
    time** through a `HashSet` (a position appears once per variable of `xs` it carries; the naive
    `List.dedup` is quadratic and blows up on widely-shared variables), sort ascending (so the
    result keeps the items' original relative order), then keep the in-range ones whose item passes
    `Q`. `arr` is the item list as an `Array` (O(1) positional access). -/
def coveredIdx (idx : CovIndex) (arr : Array α) (Q : α → Bool) (xs : List Variable) : List α :=
  let uniq := ((candidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList
  (uniq.mergeSort (· ≤ ·)).filterMap (fun i =>
    if h : i < arr.size then (if Q arr[i] then some arr[i] else none) else none)

/-- `coveredIdx` without the order-restoring sort — for consumers whose result is independent of
    the covered list's *order* (`domainBatch`: the covered items only ever feed `all`/`any`
    filters and length counts). Same membership soundness (`coveredIdxUnord_mem_of_eq`). -/
def coveredIdxUnord (idx : CovIndex) (arr : Array α) (Q : α → Bool) (xs : List Variable) :
    List α :=
  let uniq := ((candidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList
  uniq.filterMap (fun i =>
    if h : i < arr.size then (if Q arr[i] then some arr[i] else none) else none)

/-- **Soundness.** Every item `coveredIdx` returns is a genuine item of `arr` (hence of the
    underlying list) that satisfies `Q`. This is all the enumeration proofs need; the index need
    not be complete for correctness (completeness only affects effectiveness, checked empirically). -/
theorem coveredIdx_mem (idx : CovIndex) (arr : Array α) (Q : α → Bool) (xs : List Variable)
    {e : α} (he : e ∈ coveredIdx idx arr Q xs) :
    ∃ i, ∃ _h : i < arr.size, arr[i] = e ∧ Q e = true := by
  rw [coveredIdx, List.mem_filterMap] at he
  obtain ⟨i, _hi, hfe⟩ := he
  by_cases h : i < arr.size
  · rw [dif_pos h] at hfe
    by_cases hq : Q arr[i]
    · rw [if_pos hq] at hfe
      have hei : arr[i] = e := Option.some.inj hfe
      exact ⟨i, h, hei, by rw [← hei]; exact hq⟩
    · rw [if_neg hq] at hfe; exact absurd hfe (by simp)
  · rw [dif_neg h] at hfe; exact absurd hfe (by simp)

theorem coveredIdxUnord_mem (idx : CovIndex) (arr : Array α) (Q : α → Bool) (xs : List Variable)
    {e : α} (he : e ∈ coveredIdxUnord idx arr Q xs) :
    ∃ i, ∃ _h : i < arr.size, arr[i] = e ∧ Q e = true := by
  rw [coveredIdxUnord, List.mem_filterMap] at he
  obtain ⟨i, _hi, hfe⟩ := he
  by_cases h : i < arr.size
  · rw [dif_pos h] at hfe
    by_cases hq : Q arr[i]
    · rw [if_pos hq] at hfe
      have hei : arr[i] = e := Option.some.inj hfe
      exact ⟨i, h, hei, by rw [← hei]; exact hq⟩
    · rw [if_neg hq] at hfe; exact absurd hfe (by simp)
  · rw [dif_neg h] at hfe; exact absurd hfe (by simp)

/-- Soundness of the unordered variant for an array threaded with its list equation. -/
theorem coveredIdxUnord_mem_of_eq (idx : CovIndex) (l : List α) (arr : Array α)
    (harr : arr = l.toArray) (Q : α → Bool) (xs : List Variable)
    {e : α} (he : e ∈ coveredIdxUnord idx arr Q xs) : e ∈ l ∧ Q e = true := by
  subst harr
  obtain ⟨i, hi, hei, hq⟩ := coveredIdxUnord_mem idx l.toArray Q xs he
  subst hei
  have hi' : i < l.length := by simpa using hi
  exact ⟨by simp [l.getElem_mem hi'], hq⟩

/-- Soundness, specialized to the array being a list's `toArray` (what the passes pass in): every
    returned item is a genuine member of the list and satisfies `Q`. -/
theorem coveredIdx_mem_list (idx : CovIndex) (l : List α) (Q : α → Bool) (xs : List Variable)
    {e : α} (he : e ∈ coveredIdx idx l.toArray Q xs) : e ∈ l ∧ Q e = true := by
  obtain ⟨i, hi, hei, hq⟩ := coveredIdx_mem idx l.toArray Q xs he
  subst hei
  have hi' : i < l.length := by simpa using hi
  have hmem : l.toArray[i] ∈ l := by simp [l.getElem_mem hi']
  exact ⟨hmem, hq⟩

/-- Soundness for an array threaded as a value together with the proof it is `l.toArray` (what the
    passes carry, so the array is built once rather than per target): the same conclusion. -/
theorem coveredIdx_mem_of_eq (idx : CovIndex) (l : List α) (arr : Array α)
    (harr : arr = l.toArray) (Q : α → Bool) (xs : List Variable)
    {e : α} (he : e ∈ coveredIdx idx arr Q xs) : e ∈ l ∧ Q e = true := by
  subst harr; exact coveredIdx_mem_list idx l Q xs he

/-! ## Completeness: `coveredIdx` equals the plain filter (for the exact-covered-set passes)

`domainBatch` / `reencode` consume only `coveredIdx_mem` (each returned item genuinely satisfies
`Q`) — index *completeness* only affects their effectiveness and is checked empirically. The
domain-**fold** pass, however, threads the covered set into `groupDoms` / `foldOut_correct`, whose
statements pin it to `cs.algebraicConstraints.filter (coveredBy xs)` *exactly*; substituting the
index there needs a genuine `coveredIdx … = items.filter Q` equality. It holds whenever every
`Q`-item shares a variable with the target `xs` (so the index gathers it) — the case for
`coveredBy`, whose `hasVar` guarantees at least one variable and whose `varsInF` puts every one in
`xs`. The proof is generic over the item type. -/

/-- Membership in the fold of a list into a `Std.HashSet` (used for the candidate-position dedup). -/
theorem mem_foldl_insert (l : List Nat) (s : Std.HashSet Nat) (i : Nat) :
    i ∈ l.foldl (·.insert ·) s ↔ i ∈ s ∨ i ∈ l := by
  induction l generalizing s with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih (s.insert a), Std.HashSet.mem_insert, List.mem_cons]
    simp only [beq_iff_eq]
    constructor
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact (Or.inl (Or.inl rfl))
      · exact Or.inr h

/-- Inserting a position into buckets never removes an existing membership. -/
theorem inner_getD_mono (i : Nat) (vs : List Variable) (w : Variable) (j : Nat) :
    ∀ (m : Std.HashMap Variable (List Nat)), j ∈ m.getD w [] →
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

/-- After inserting `i` into every bucket of `vs`, `i` is in the bucket of each `v ∈ vs`. -/
theorem inner_getD_self (i : Nat) (vs : List Variable) (v : Variable) :
    ∀ (m : Std.HashMap Variable (List Nat)), v ∈ vs →
    i ∈ (vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m).getD v [] := by
  induction vs with
  | nil => intro m hv; simp at hv
  | cons v0 rest ih =>
    intro m hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · apply inner_getD_mono
      rw [Std.HashMap.getD_insert, if_pos (by simp)]
      exact List.mem_cons_self
    · exact ih _ hv

/-- The `.buckets` of one `buildStep` when the item has no variables (unchanged). -/
theorem buildStep_buckets_nil (varsOf : α → List Variable) (ai : α × Nat) (idx : CovIndex)
    (h : varsOf ai.1 = []) : (buildStep varsOf ai idx).buckets = idx.buckets := by
  simp only [buildStep, h]

/-- The `.buckets` of one `buildStep` when the item has variables (the inner insert fold). -/
theorem buildStep_buckets_cons (varsOf : α → List Variable) (ai : α × Nat) (idx : CovIndex)
    (w0 : Variable) (ws : List Variable) (h : varsOf ai.1 = w0 :: ws) :
    (buildStep varsOf ai idx).buckets
      = (w0 :: ws).foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets := by
  simp only [buildStep, h]

/-- **Index completeness (buckets).** Every item at position `i` with variable `v` bucketed under
    `v`: the fold inserts `i` into `v`'s bucket and later steps never remove it. -/
theorem buildStep_bucket_complete (varsOf : α → List Variable) :
    ∀ (l : List (α × Nat)) (a : α) (i : Nat), (a, i) ∈ l → ∀ (v : Variable), v ∈ varsOf a →
      i ∈ (l.foldr (buildStep varsOf) ⟨∅, []⟩).buckets.getD v [] := by
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
        rw [buildStep_buckets_cons varsOf (a, i) _ w0 ws hvs]
        exact inner_getD_self i (w0 :: ws) v _ (by rw [← hvs]; exact hv)
    · have hrec : i ∈ (rest.foldr (buildStep varsOf) ⟨∅, []⟩).buckets.getD v [] := ih a i hmem v hv
      cases hvs : varsOf ai0.1 with
      | nil => rw [buildStep_buckets_nil varsOf ai0 _ hvs]; exact hrec
      | cons w0 ws =>
        rw [buildStep_buckets_cons varsOf ai0 _ w0 ws hvs]
        exact inner_getD_mono ai0.2 (w0 :: ws) v i _ hrec

/-- A position bucketed under a variable of `xs` is a candidate. -/
theorem mem_candidates (idx : CovIndex) (xs : List Variable) (v : Variable) (i : Nat)
    (hv : v ∈ xs) (hi : i ∈ idx.buckets.getD v []) : i ∈ candidates idx xs :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨v, hv, hi⟩)

/-- `filterMap` of a guarded `some` is the plain filter-then-map. -/
theorem filterMap_if_some {β γ : Type _} (P : β → Bool) (f : β → γ) (l : List β) :
    l.filterMap (fun x => if P x then some (f x) else none) = (l.filter P).map f := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : P a
    · rw [List.filterMap_cons_some (by rw [if_pos h]), List.filter_cons_of_pos h, List.map_cons, ih]
    · rw [List.filterMap_cons_none (by rw [if_neg h]), List.filter_cons_of_neg (by simpa using h), ih]

/-- `filterMap` respects pointwise equality of its function on the list. -/
theorem filterMap_congr' {β γ : Type _} {f g : β → Option γ} (l : List β)
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have ha := h a (List.mem_cons_self)
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hfa : f a with
    | none => rw [List.filterMap_cons_none hfa, List.filterMap_cons_none (ha ▸ hfa), hr]
    | some b => rw [List.filterMap_cons_some hfa, List.filterMap_cons_some (ha ▸ hfa), hr]

/-- **`coveredIdx` equals the plain filter** whenever every `Q`-item shares a variable with `xs`.
    All the fold/sort machinery collapses: the index gathers every `Q`-position (completeness), the
    `HashSet` dedup and `mergeSort` reorder them into ascending (i.e. original list) order, and the
    per-position `Q` re-check reproduces `items.filter Q` exactly. -/
theorem coveredIdx_eq_filter (varsOf : α → List Variable) (items : List α)
    (Q : α → Bool) (xs : List Variable)
    (hcomplete : ∀ (i : Nat) (hi : i < items.length),
      Q items[i] = true → ∃ v ∈ varsOf items[i], v ∈ xs) :
    coveredIdx (build varsOf items) items.toArray Q xs = items.filter Q := by
  rw [coveredIdx]
  simp only [List.size_toArray, List.getElem_toArray]
  set cand := candidates (build varsOf items) xs with hcand
  set gI : Nat → Option α :=
    (fun i => if h : i < items.length then (if Q items[i] then some items[i] else none) else none)
    with hgI
  set sortedL := ((cand.foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).mergeSort (· ≤ ·)
    with hsortedL
  -- (F1) membership in the sorted candidate list is membership in `cand`
  have F1 : ∀ i, i ∈ sortedL ↔ i ∈ cand := by
    intro i
    rw [hsortedL, List.mem_mergeSort, Std.HashSet.mem_toList, mem_foldl_insert]
    simp [Std.HashSet.not_mem_empty]
  -- (F2) the sorted list is duplicate-free
  have hnodupUniq : ((cand.foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).Nodup :=
    Std.HashSet.distinct_toList.imp (fun {a b} h => by simpa using h)
  have F2 : sortedL.Nodup := by
    rw [hsortedL]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hnodupUniq
  -- (F3) the sorted list is `≤`-sorted
  have F3 : sortedL.Pairwise (· ≤ ·) := by
    rw [hsortedL]; exact List.sortedLE_mergeSort.pairwise
  -- (F4) completeness: every in-range `Q`-position is a candidate
  have F4 : ∀ (i : Nat) (hi : i < items.length), Q items[i] = true → i ∈ cand := by
    intro i hi hQ
    obtain ⟨v, hvvars, hvxs⟩ := hcomplete i hi hQ
    have hz : (items.zipIdx)[i]? = some (items[i], i) := by
      rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hi]; simp
    have hmem : (items[i], i) ∈ items.zipIdx := List.mem_of_getElem? hz
    have hbucket := buildStep_bucket_complete varsOf items.zipIdx items[i] i hmem v hvvars
    rw [hcand]
    exact mem_candidates (build varsOf items) xs v i hvxs hbucket
  -- the keep-predicate coincides with `gI`'s definedness
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
  -- (L1) dropping the `none`-mapping positions before `filterMap` changes nothing
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
  -- (Claim1) the filter equals the filterMap over `[0, n)`
  have claim1 : (List.range items.length).filterMap gI = items.filter Q := by
    have hrange : List.range items.length = items.zipIdx.map Prod.snd := by
      rw [List.zipIdx_map_snd, List.range_eq_range']
    rw [hrange, List.filterMap_map]
    rw [filterMap_congr' items.zipIdx
      (f := gI ∘ Prod.snd) (g := fun p => if Q p.1 then some p.1 else none)
      (by
        rintro ⟨a, j⟩ hp
        obtain ⟨_, hlt, heq⟩ := List.mem_zipIdx (k := 0) hp
        have hlt' : j < items.length := by simpa using hlt
        have heq' : items[j]'hlt' = a := by simpa using heq.symm
        simp only [Function.comp_apply, hgI, dif_pos hlt', heq'])]
    rw [filterMap_if_some]
    show ((items.zipIdx.filter (Q ∘ Prod.fst)).map Prod.fst) = items.filter Q
    rw [← List.filter_map, List.zipIdx_map_fst]
  -- (L2) the kept positions of the sorted list coincide with those of `[0, n)`
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

end CoveredIndex
