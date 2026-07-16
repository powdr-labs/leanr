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
