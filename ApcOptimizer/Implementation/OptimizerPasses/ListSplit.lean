import ApcOptimizer.Implementation.OptimizerPasses.Basic

set_option autoImplicit false

/-! # The split equation, by construction

A pass that scans the interaction *array* and certifies a swap/drop needs the list-level split
`cs.busInteractions = A ++ S :: B ++ R :: C`. Deciding that equation at runtime is an
O(#interactions) deep structural comparison per accepted change; instead it follows by
construction from the way `A`/`B`/`C` are extracted. Shared by `BusPairCancel` and
`TupleRange`. -/

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

/-! ### Generic `argmin` / `filterMap` list lemmas

Representation-independent list machinery re-homed here from `OldVariableBased/Gauss.lean` so the
dense Gauss pass can consume them without importing the reference pass; the reference pass imports
them back. -/

/-- `argmin` commutes with a key-preserving map: when `g` carries the key (`kγ (g a) = kα a`), the
    winner of the mapped list is the mapped winner. This lets us score cheap descriptors in place
    of built candidates. -/
theorem argmin_map_key {α γ : Type*} (g : α → γ) (kα : α → Nat) (kγ : γ → Nat)
    (h : ∀ a, kγ (g a) = kα a) : ∀ l : List α, (l.map g).argmin kγ = (l.argmin kα).map g := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.argmin_cons, List.argmin_cons, ih]
      cases t.argmin kα with
      | none => simp
      | some c =>
          simp only [Option.map_some, h]
          by_cases hlt : kα c < kα a <;> simp [hlt]

theorem map_filterMap {α β γ : Type*} (f : α → Option β) (g : β → γ) (l : List α) :
    (l.filterMap f).map g = l.filterMap (fun a => (f a).map g) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.filterMap_cons]
      cases f a with
      | none => simpa using ih
      | some b => simp [ih]

/-! ### Linear-time dedup

Re-homed here from `OldVariableBased/Reencode.lean` (generic list machinery); the reference passes
import it back. -/

/-- `List.dedup` computed in linear time via a hash set, with the **identical** result: an element
    is kept at its last-occurrence position (exactly `List.dedup`'s order), so swapping this in is a
    pure speedup — `reencodeLoop`'s correctness is independent of the target list, and its
    (order-sensitive, greedy) behaviour is unchanged because the list itself is unchanged. -/
def dedupHash {α : Type} [BEq α] [Hashable α] (l : List α) : List α :=
  (l.reverse.foldl (fun (st : List α × Std.HashSet α) t =>
    if st.2.contains t then st else (t :: st.1, st.2.insert t))
    (([], ∅) : List α × Std.HashSet α)).1

/-! ### `foldl max` bounds

Re-homed here from `OldVariableBased/RootPairUnify.lean` (generic `Nat`/`List` machinery); the
reference pass and the dense two-root bounds proof both consume them. -/

/-- The seed is at most the `foldl max` accumulation. -/
theorem init_le_foldl_max (l : List Nat) : ∀ b : Nat, b ≤ l.foldl max b := by
  induction l with
  | nil => intro b; simp
  | cons c rest ih => intro b; exact le_trans (le_max_left b c) (ih (max b c))

/-- Everything in a list is at most its `foldl max` accumulation. -/
theorem le_foldl_max (l : List Nat) : ∀ (b : Nat), ∀ a ∈ l, a ≤ l.foldl max b := by
  induction l with
  | nil => intro b a ha; simp at ha
  | cons c rest ih =>
    intro b a ha
    rcases List.mem_cons.1 ha with rfl | h
    · exact le_trans (le_max_right b a) (init_le_foldl_max rest (max b a))
    · exact ih (max b c) a h

/-! ### Early-exit list fold

Re-homed here from `OldVariableBased/DomainBatch.lean` (generic list machinery); the finite-domain
enumeration engine (`EnumEngine.lean`) and the reference passes both consume it. -/

/-- Left fold with an early exit: once `stop acc` holds, the remaining elements are skipped. -/
def foldlStop {α β : Type} (f : β → α → β) (stop : β → Bool) : List α → β → β
  | [], acc => acc
  | a :: rest, acc => if stop acc then acc else foldlStop f stop rest (f acc a)

theorem foldlStop_stopped {α β : Type} (f : β → α → β) (stop : β → Bool) (l : List α) (acc : β)
    (h : stop acc = true) : foldlStop f stop l acc = acc := by
  cases l with
  | nil => rfl
  | cons a rest => rw [foldlStop, if_pos h]

theorem foldlStop_append {α β : Type} (f : β → α → β) (stop : β → Bool)
    (xs ys : List α) (acc : β) :
    foldlStop f stop (xs ++ ys) acc = foldlStop f stop ys (foldlStop f stop xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    rw [List.cons_append, foldlStop, foldlStop]
    by_cases h : stop acc = true
    · rw [if_pos h, if_pos h, foldlStop_stopped f stop ys acc h]
    · rw [if_neg h, if_neg h, ih]

theorem foldlStop_map {α β γ : Type} (f : β → γ → β) (stop : β → Bool) (k : α → γ)
    (l : List α) (acc : β) :
    foldlStop f stop (l.map k) acc = foldlStop (fun acc a => f acc (k a)) stop l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a rest ih =>
    rw [List.map_cons, foldlStop, foldlStop]
    by_cases h : stop acc = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, ih]

theorem foldlStop_flatMap {α β γ : Type} (f : β → γ → β) (stop : β → Bool) (h : α → List γ)
    (l : List α) (acc : β) :
    foldlStop (fun acc a => foldlStop f stop (h a) acc) stop l acc
      = foldlStop f stop (l.flatMap h) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, foldlStop, foldlStop_append]
    by_cases hs : stop acc = true
    · rw [if_pos hs, foldlStop_stopped f stop (h a) acc hs,
        foldlStop_stopped f stop (rest.flatMap h) acc hs]
    · rw [if_neg hs, ih]

theorem foldlStop_congr {α β : Type} (f g : β → α → β) (stop : β → Bool) (l : List α) (acc : β)
    (h : ∀ acc a, f acc a = g acc a) : foldlStop f stop l acc = foldlStop g stop l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a rest ih =>
    rw [foldlStop, foldlStop]
    by_cases hs : stop acc = true
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs, h acc a, ih]

theorem foldlStop_all {α : Type} (pred : α → Bool) (l : List α) (acc : Bool) :
    foldlStop (fun acc a => acc && pred a) (fun acc => !acc) l acc = (acc && l.all pred) := by
  induction l generalizing acc with
  | nil => simp [foldlStop]
  | cons a rest ih =>
    rw [foldlStop, List.all_cons]
    by_cases hacc : acc = true
    · subst hacc; rw [ih]; simp
    · simp only [Bool.not_eq_true] at hacc; subst hacc; simp

/-! ### Sparse positional map and self-zip membership

Re-homed here from `OldVariableBased/DomainFold.lean` (`zipIdx_map_sparse`) and
`OldVariableBased/Reencode.lean` (`zip_map_self_mem`) — generic list machinery; the reference passes
and their dense correspondence proofs both consume them. -/

/-- The positional pass-through map equals the plain map when the function fixes the item at
    every position outside `mem`. -/
theorem zipIdx_map_sparse {α : Type _} (l : List α) (f : α → α) (mem : Nat → Bool)
    (hfix : ∀ (i : Nat) (hi : i < l.length), mem i = false → f l[i] = l[i]) :
    l.zipIdx.map (fun ai => if mem ai.2 then f ai.1 else ai.1) = l.map f := by
  rw [show l.map f = l.zipIdx.map (f ∘ Prod.fst) by rw [← List.map_map, List.zipIdx_map_fst]]
  refine List.map_congr_left ?_
  rintro ⟨a, i⟩ hp
  obtain ⟨_, hlt, heq⟩ := List.mem_zipIdx (k := 0) hp
  have hlt' : i < l.length := by simpa using hlt
  have heq' : l[i]'hlt' = a := by simpa using heq.symm
  dsimp only [Function.comp_apply]
  by_cases hm : mem i = true
  · rw [if_pos hm]
  · rw [if_neg hm]
    have := hfix i hlt' (by simpa using hm)
    rw [heq'] at this
    exact this.symm

/-- Membership of the graph pairs in the zip of a list with its image. -/
theorem zip_map_self_mem {α β : Type} (f : α → β) (l : List α) (a : α) (ha : a ∈ l) :
    (a, f a) ∈ l.zip (l.map f) := by
  induction l with
  | nil => simp at ha
  | cons x rest ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · simp
    · simp only [List.map_cons, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ (ih ha)

/-- Every element of a two-point split other than the two distinguished ones lies in the
    remaining region. -/
theorem mem_core_of_ne {α : Type _} {l A B C : List α} {S R x : α}
    (hsplit : l = A ++ S :: B ++ R :: C) (hx : x ∈ l) (hxS : x ≠ S) (hxR : x ≠ R) :
    x ∈ A ++ B ++ C := by
  subst hsplit
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  tauto

/-- Net multiplicity (over the representation-independent `BusState p`) is additive over
    concatenation of bus states. -/
theorem multiplicitySum_append {p : ℕ} (msg : BusMessage p) (s t : BusState p) :
    multiplicitySum msg (s ++ t) = multiplicitySum msg s + multiplicitySum msg t := by
  induction s with
  | nil => simp [multiplicitySum]
  | cons hd tl ih =>
      simp only [List.cons_append, multiplicitySum, ih]
      rw [← add_assoc]
