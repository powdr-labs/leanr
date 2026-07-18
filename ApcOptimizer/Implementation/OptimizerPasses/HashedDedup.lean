import ApcOptimizer.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false

/-! # Hash-bucketed `eraseDups`

`List.eraseDups` keeps the first occurrence of each element, testing each new element against the
whole kept-so-far list — O(n²) structural comparisons. `hashedEraseDups` carries the kept set
bucketed by a caller-supplied structural hash, so each test scans one bucket;
`hashedEraseDups_eq` proves the output is the **identical list**, so callers keep their proofs
(and their byte-identical behavior) by rewriting along it. Generic in the element type; with
`LawfulBEq` the hash needs no congruence side condition. -/

namespace HashedDedup

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable UInt64]

/-- `List.eraseDupsBy.loop (· == ·)` with the kept-so-far list `bs` mirrored as hash buckets:
    the membership test scans only the bucket of the candidate's hash. -/
def loop (hf : α → UInt64) : List α → List α → Std.HashMap UInt64 (List α) → List α
  | [], bs, _ => bs.reverse
  | a :: as, bs, m =>
    if a ∈ m.getD (hf a) [] then loop hf as bs m
    else loop hf as (a :: bs) (m.insert (hf a) (a :: m.getD (hf a) []))

theorem loop_eq (hf : α → UInt64) :
    ∀ (as bs : List α) (m : Std.HashMap UInt64 (List α)),
      (∀ x : α, x ∈ bs ↔ x ∈ m.getD (hf x) []) →
      loop hf as bs m = List.eraseDupsBy.loop (· == ·) as bs := by
  intro as
  induction as with
  | nil => intro bs m _; rfl
  | cons a rest ih =>
    intro bs m h
    rw [loop, List.eraseDupsBy.loop]
    have hany : bs.any (a == ·) = decide (a ∈ bs) := by
      by_cases hmem : a ∈ bs
      · rw [decide_eq_true hmem, List.any_eq_true]
        exact ⟨a, hmem, beq_self_eq_true a⟩
      · rw [decide_eq_false hmem, List.any_eq_false]
        intro x hx hax
        exact hmem ((eq_of_beq hax).symm ▸ hx)
    by_cases hmem : a ∈ bs
    · rw [if_pos ((h a).mp hmem), hany, decide_eq_true hmem]
      exact ih bs m h
    · rw [if_neg (fun hc => hmem ((h a).mpr hc)), hany, decide_eq_false hmem]
      show _ = List.eraseDupsBy.loop (· == ·) rest (a :: bs)
      exact ih (a :: bs) (m.insert (hf a) (a :: m.getD (hf a) []))
        (by
          intro x
          rw [Std.HashMap.getD_insert]
          by_cases hbh : hf a = hf x
          · rw [if_pos (by simpa using hbh), List.mem_cons, List.mem_cons]
            have hx := h x
            rw [← hbh] at hx
            exact or_congr_right hx
          · have hxne : x ≠ a := fun he => hbh (by rw [he])
            rw [if_neg (by simpa using hbh), List.mem_cons]
            exact (or_iff_right hxne).trans (h x))

/-- Hash-bucketed `List.eraseDups`: identical output, one-bucket membership tests. -/
def hashedEraseDups (hf : α → UInt64) (l : List α) : List α :=
  loop hf l [] ∅

theorem hashedEraseDups_eq (hf : α → UInt64) (l : List α) :
    hashedEraseDups hf l = l.eraseDups :=
  loop_eq hf l [] ∅ (by intro x; simp [Std.HashMap.getD_empty])

/-! ## Hash-bucketed `List.dedup`

`List.dedup` keeps the **last** occurrence of each duplicate (`dedup (a :: l)` drops `a` when
`a ∈ l`), testing each head against its tail — O(n²). The bucketed twin walks the list carrying
the *remaining-tail multiset* as hash buckets: the head is kept exactly when it no longer occurs
in its bucket, which is `a ∈ l` by the count invariant — so `hashedDedup_eq` proves the output is
the identical list. Requires `DecidableEq` (like `List.dedup`). -/

section Dedup

/-- The multiset of a list, bucketed by hash (buckets keep every occurrence). -/
def bucketCounts (hf : α → UInt64) : List α → Std.HashMap UInt64 (List α)
  | [] => ∅
  | a :: rest => let m := bucketCounts hf rest; m.insert (hf a) (a :: m.getD (hf a) [])

theorem bucketCounts_count (hf : α → UInt64) (l : List α) (x : α) :
    ((bucketCounts hf l).getD (hf x) []).count x = l.count x := by
  induction l with
  | nil => simp [bucketCounts, Std.HashMap.getD_empty]
  | cons a rest ih =>
    simp only [bucketCounts, Std.HashMap.getD_insert]
    by_cases hbh : hf a = hf x
    · rw [if_pos (by simpa using hbh), hbh, List.count_cons, List.count_cons, ih]
    · have hxne : x ≠ a := fun he => hbh (by rw [he])
      rw [if_neg (by simpa using hbh), List.count_cons, ih,
        if_neg (by simpa using Ne.symm hxne), Nat.add_zero]

/-- One occurrence of `a` removed from its bucket: the multiset of `a :: rest` becomes the
    multiset of `rest`. -/
def bucketErase (hf : α → UInt64) (m : Std.HashMap UInt64 (List α)) (a : α) :
    Std.HashMap UInt64 (List α) :=
  m.insert (hf a) ((m.getD (hf a) []).erase a)

theorem bucketErase_count (hf : α → UInt64) {m : Std.HashMap UInt64 (List α)}
    {a : α} {rest : List α}
    (h : ∀ x : α, (m.getD (hf x) []).count x = (a :: rest).count x)
    (x : α) : ((bucketErase hf m a).getD (hf x) []).count x = rest.count x := by
  simp only [bucketErase, Std.HashMap.getD_insert]
  by_cases hbh : hf a = hf x
  · rw [if_pos (by simpa using hbh), List.count_erase, hbh, h x, List.count_cons,
      Nat.add_sub_cancel]
  · have hxne : x ≠ a := fun he => hbh (by rw [he])
    rw [if_neg (by simpa using hbh), h x, List.count_cons, if_neg (by simpa using Ne.symm hxne),
      Nat.add_zero]

variable [DecidableEq α]

/-- `List.dedup` with the remaining-tail multiset carried as hash buckets. -/
def dedupGo (hf : α → UInt64) : Std.HashMap UInt64 (List α) → List α → List α
  | _, [] => []
  | m, a :: rest =>
    let m' := bucketErase hf m a
    if a ∈ m'.getD (hf a) [] then dedupGo hf m' rest
    else a :: dedupGo hf m' rest

theorem dedupGo_eq (hf : α → UInt64) :
    ∀ (l : List α) (m : Std.HashMap UInt64 (List α)),
      (∀ x : α, (m.getD (hf x) []).count x = l.count x) →
      dedupGo hf m l = l.dedup := by
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons a rest ih =>
    intro m h
    rw [dedupGo]
    have h' := fun x => bucketErase_count hf h x
    have hmem : (a ∈ (bucketErase hf m a).getD (hf a) []) ↔ a ∈ rest := by
      rw [← List.count_pos_iff, ← List.count_pos_iff, h' a]
    by_cases hin : a ∈ rest
    · rw [if_pos (hmem.mpr hin), List.dedup_cons_of_mem hin, ih _ h']
    · rw [if_neg (fun hc => hin (hmem.mp hc)), List.dedup_cons_of_notMem hin, ih _ h']

/-- Hash-bucketed `List.dedup`: identical output, one-bucket membership tests. -/
def hashedDedup (hf : α → UInt64) (l : List α) : List α :=
  dedupGo hf (bucketCounts hf l) l

theorem hashedDedup_eq (hf : α → UInt64) (l : List α) : hashedDedup hf l = l.dedup :=
  dedupGo_eq hf l (bucketCounts hf l) (bucketCounts_count hf l)

end Dedup

end HashedDedup
