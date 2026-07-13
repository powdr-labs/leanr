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

/-- Build the inverted index in one pass over `items` paired with their positions. Mirrors
    `busPairCancel`'s `recvIndex`: a right fold inserting each position into every bucket of the
    variables it mentions (or into `varless` when it mentions none). -/
def build (varsOf : α → List Variable) (items : List α) : CovIndex :=
  items.zipIdx.foldr (fun ai idx =>
    match varsOf ai.1 with
    | [] => ⟨idx.buckets, ai.2 :: idx.varless⟩
    | vs => ⟨vs.foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets, idx.varless⟩)
    ⟨∅, []⟩

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

end CoveredIndex
