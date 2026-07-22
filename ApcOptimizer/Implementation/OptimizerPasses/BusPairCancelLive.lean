import ApcOptimizer.Implementation.OptimizerPasses.Encoding

set_option autoImplicit false

/-! # Dense stable live projection / tombstone machinery

The liveness-array (`alive : Array Bool`) tombstone machinery: `denseLiveSeg` (the live-entries
projection) and its algebra, `denseLiveCount` (the termination measure), the tail-recursive runtime
builder `denseLiveArr` (= `denseLiveSeg` via `denseLiveArr_eq`), and the projection `denseMkCs`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! `denseLiveSeg arr alive lo n` is the live entries of `arr` at positions `[lo, lo+n)`, skipping
tombstoned ones (structural recursion on the count `n`, so equation lemmas unfold cleanly). -/
def denseLiveSeg (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool) :
    Nat → Nat → List (BusInteraction (DenseExpr p))
  | _, 0 => []
  | lo, (n + 1) =>
    (if alive[lo]?.getD false then (arr[lo]?).elim [] (fun a => [a]) else [])
      ++ denseLiveSeg arr alive (lo + 1) n

/-- Additivity: scanning `m + n` positions from `lo` is the first `m` then the next `n`. -/
theorem denseLiveSeg_add (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (lo m n : Nat) :
    denseLiveSeg arr alive lo (m + n)
      = denseLiveSeg arr alive lo m ++ denseLiveSeg arr alive (lo + m) n := by
  induction m generalizing lo with
  | zero => simp [denseLiveSeg]
  | succ m ih =>
    have h1 : denseLiveSeg arr alive lo (m + 1)
        = (if alive[lo]?.getD false then (arr[lo]?).elim [] (fun a => [a]) else [])
            ++ denseLiveSeg arr alive (lo + 1) m := by rw [denseLiveSeg]
    have h2 : denseLiveSeg arr alive lo (m + 1 + n)
        = (if alive[lo]?.getD false then (arr[lo]?).elim [] (fun a => [a]) else [])
            ++ denseLiveSeg arr alive (lo + 1) (m + n) := by
      rw [show m + 1 + n = (m + n) + 1 from by omega, denseLiveSeg]
    rw [h1, h2, ih (lo + 1), ← List.append_assoc, show lo + 1 + m = lo + (m + 1) from by omega]

/-- Peel a live head off the front of a nonempty scan. -/
theorem denseLiveSeg_peel (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (lo n : Nat) (a : BusInteraction (DenseExpr p))
    (halive : alive[lo]?.getD false = true) (hget : arr[lo]? = some a) :
    denseLiveSeg arr alive lo (n + 1) = a :: denseLiveSeg arr alive (lo + 1) n := by
  rw [denseLiveSeg, halive, if_pos rfl, hget]; rfl

/-- Peel a dead head off the front of a nonempty scan. -/
theorem denseLiveSeg_skip (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (lo n : Nat) (halive : alive[lo]?.getD false = false) :
    denseLiveSeg arr alive lo (n + 1) = denseLiveSeg arr alive (lo + 1) n := by
  rw [denseLiveSeg, halive, if_neg (by simp)]; rfl

/-- The projection depends only on the liveness bits it reads: two liveness arrays that agree on
    every position of the scanned range give the same live projection. -/
theorem denseLiveSeg_congr (arr : Array (BusInteraction (DenseExpr p))) (alive alive' : Array Bool)
    (lo n : Nat) (h : ∀ j, lo ≤ j → j < lo + n → alive'[j]? = alive[j]?) :
    denseLiveSeg arr alive' lo n = denseLiveSeg arr alive lo n := by
  induction n generalizing lo with
  | zero => simp [denseLiveSeg]
  | succ n ih =>
    rw [denseLiveSeg, denseLiveSeg, h lo (Nat.le_refl _) (by omega),
      ih (lo + 1) (fun j hj1 hj2 => h j (by omega) (by omega))]

/-- A live position's entry is a member of the projection over any enclosing range. -/
theorem denseLiveSeg_mem (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (lo n k : Nat) (a : BusInteraction (DenseExpr p))
    (hlo : lo ≤ k) (hk : k < lo + n)
    (halive : alive[k]?.getD false = true) (hget : arr[k]? = some a) :
    a ∈ denseLiveSeg arr alive lo n := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hlo
  obtain ⟨e, rfl⟩ : ∃ e, n = d + (e + 1) := ⟨n - d - 1, by omega⟩
  rw [denseLiveSeg_add]
  refine List.mem_append_right _ ?_
  rw [denseLiveSeg_peel arr alive (lo + d) e a halive hget]
  exact List.mem_cons.2 (Or.inl rfl)

/-! On accepting a pair `(iP, jP)`, the live projection factors as `A ++ S :: B ++ R :: C'`
(`denseLiveSeg_split`); tombstoning the two positions changes it to `A ++ B ++ C'`
(`denseLiveSeg_drop`) — the shape `denseDropPair_correct` produces. -/

/-- The live projection factors around two live positions `iP < jP`. -/
theorem denseLiveSeg_split (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (iP jP size : Nat) (S R : BusInteraction (DenseExpr p))
    (hij : iP < jP) (hj : jP < size)
    (hSget : arr[iP]? = some S) (hRget : arr[jP]? = some R)
    (hSalive : alive[iP]?.getD false = true) (hRalive : alive[jP]?.getD false = true) :
    denseLiveSeg arr alive 0 size
      = denseLiveSeg arr alive 0 iP ++ S :: denseLiveSeg arr alive (iP + 1) (jP - iP - 1)
          ++ R :: denseLiveSeg arr alive (jP + 1) (size - jP - 1) := by
  have peelS : denseLiveSeg arr alive iP (size - iP)
      = S :: denseLiveSeg arr alive (iP + 1) (size - iP - 1) := by
    conv_lhs => rw [show size - iP = (size - iP - 1) + 1 from by omega]
    exact denseLiveSeg_peel arr alive iP (size - iP - 1) S hSalive hSget
  have peelR : denseLiveSeg arr alive jP (size - jP)
      = R :: denseLiveSeg arr alive (jP + 1) (size - jP - 1) := by
    conv_lhs => rw [show size - jP = (size - jP - 1) + 1 from by omega]
    exact denseLiveSeg_peel arr alive jP (size - jP - 1) R hRalive hRget
  have splitJ : denseLiveSeg arr alive (iP + 1) (size - iP - 1)
      = denseLiveSeg arr alive (iP + 1) (jP - iP - 1) ++ denseLiveSeg arr alive jP (size - jP) := by
    conv_lhs => rw [show size - iP - 1 = (jP - iP - 1) + (size - jP) from by omega]
    rw [denseLiveSeg_add, show iP + 1 + (jP - iP - 1) = jP from by omega]
  conv_lhs => rw [show size = iP + (size - iP) from by omega]
  rw [denseLiveSeg_add, Nat.zero_add, peelS, splitJ, peelR]
  simp only [List.append_assoc, List.cons_append]

/-- Tombstoning two live positions `iP < jP` deletes exactly those two entries from the projection,
    leaving every other position in place. -/
theorem denseLiveSeg_drop (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (iP jP size : Nat) (hij : iP < jP) (hj : jP < size)
    (hisz : iP < alive.size) (hjsz : jP < alive.size)
    (alive' : Array Bool)
    (halive' : alive' = (alive.setIfInBounds iP false).setIfInBounds jP false) :
    denseLiveSeg arr alive' 0 size
      = denseLiveSeg arr alive 0 iP ++ denseLiveSeg arr alive (iP + 1) (jP - iP - 1)
          ++ denseLiveSeg arr alive (jP + 1) (size - jP - 1) := by
  have hgetIP : alive'[iP]?.getD false = false := by
    rw [halive', Array.getElem?_setIfInBounds_ne (show jP ≠ iP from by omega),
      Array.getElem?_setIfInBounds_self_of_lt hisz]; rfl
  have hgetJP : alive'[jP]?.getD false = false := by
    rw [halive', Array.getElem?_setIfInBounds_self_of_lt
      (by rw [Array.size_setIfInBounds]; exact hjsz)]; rfl
  have hne : ∀ (lo n : Nat), (iP < lo ∨ lo + n ≤ iP) → (jP < lo ∨ lo + n ≤ jP) →
      denseLiveSeg arr alive' lo n = denseLiveSeg arr alive lo n := by
    intro lo n hI hJ
    rw [halive']
    refine denseLiveSeg_congr arr _ _ lo n (fun j hj1 hj2 => ?_)
    rw [Array.getElem?_setIfInBounds_ne (show jP ≠ j from by omega),
      Array.getElem?_setIfInBounds_ne (show iP ≠ j from by omega)]
  have step1 : denseLiveSeg arr alive' iP (size - iP)
      = denseLiveSeg arr alive' (iP + 1) (size - iP - 1) := by
    conv_lhs => rw [show size - iP = (size - iP - 1) + 1 from by omega]
    exact denseLiveSeg_skip arr alive' iP (size - iP - 1) hgetIP
  have step2 : denseLiveSeg arr alive' (iP + 1) (size - iP - 1)
      = denseLiveSeg arr alive' (iP + 1) (jP - iP - 1) ++ denseLiveSeg arr alive' jP (size - jP) := by
    conv_lhs => rw [show size - iP - 1 = (jP - iP - 1) + (size - jP) from by omega]
    rw [denseLiveSeg_add, show iP + 1 + (jP - iP - 1) = jP from by omega]
  have step3 : denseLiveSeg arr alive' jP (size - jP)
      = denseLiveSeg arr alive' (jP + 1) (size - jP - 1) := by
    conv_lhs => rw [show size - jP = (size - jP - 1) + 1 from by omega]
    exact denseLiveSeg_skip arr alive' jP (size - jP - 1) hgetJP
  conv_lhs => rw [show size = iP + (size - iP) from by omega]
  rw [denseLiveSeg_add, Nat.zero_add, step1, step2, step3,
    hne 0 iP (by omega) (by omega),
    hne (iP + 1) (jP - iP - 1) (by omega) (by omega),
    hne (jP + 1) (size - jP - 1) (by omega) (by omega),
    ← List.append_assoc]

/-- The number of live interactions — the loop's termination measure (each drop removes two, so it
    strictly decreases). -/
def denseLiveCount (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool) : Nat :=
  (denseLiveSeg arr alive 0 arr.size).length

/-! `denseLiveArr` is the tail-recursive runtime array-builder (accumulate reversed, reverse once);
`denseLiveArr_eq` proves it equal to the spec `denseLiveSeg`, so proofs reason about `denseLiveSeg`
exclusively. -/
def denseLiveArrGo (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (halive : alive.size = arr.size) :
    (lo n : Nat) → lo + n ≤ arr.size → List (BusInteraction (DenseExpr p)) →
      List (BusInteraction (DenseExpr p))
  | _, 0, _, acc => acc.reverse
  | lo, n + 1, hb, acc =>
    have hlo : lo < arr.size := by omega
    denseLiveArrGo arr alive halive (lo + 1) n (by omega)
      (if alive[lo]'(by rw [halive]; exact hlo) then arr[lo]'hlo :: acc else acc)

/-- Tail-recursive live projection of `[lo, lo+n)`. Equal to `denseLiveSeg` (`denseLiveArr_eq`). -/
def denseLiveArr (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (halive : alive.size = arr.size) (lo n : Nat) (hb : lo + n ≤ arr.size) :
    List (BusInteraction (DenseExpr p)) :=
  denseLiveArrGo arr alive halive lo n hb []

theorem denseLiveArrGo_eq (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (halive : alive.size = arr.size) :
    ∀ (lo n : Nat) (hb : lo + n ≤ arr.size) (acc : List (BusInteraction (DenseExpr p))),
      denseLiveArrGo arr alive halive lo n hb acc = acc.reverse ++ denseLiveSeg arr alive lo n := by
  intro lo n
  induction n generalizing lo with
  | zero => intro hb acc; simp [denseLiveArrGo, denseLiveSeg]
  | succ n ih =>
    intro hb acc
    have hlo : lo < arr.size := by omega
    have hla : lo < alive.size := by rw [halive]; exact hlo
    have halo : alive[lo]?.getD false = alive[lo]'hla := by
      rw [Array.getElem?_eq_getElem hla]; rfl
    have haro : arr[lo]? = some (arr[lo]'hlo) := Array.getElem?_eq_getElem hlo
    rw [denseLiveArrGo, ih (lo + 1) (by omega)]
    split
    · rename_i hal
      rw [denseLiveSeg_peel arr alive lo n (arr[lo]'hlo) (by rw [halo]; exact hal) haro]
      simp [List.reverse_cons]
    · rename_i hal
      rw [denseLiveSeg_skip arr alive lo n (by rw [halo]; simpa using hal)]

theorem denseLiveArr_eq (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (halive : alive.size = arr.size) (lo n : Nat) (hb : lo + n ≤ arr.size) :
    denseLiveArr arr alive halive lo n hb = denseLiveSeg arr alive lo n := by
  rw [denseLiveArr, denseLiveArrGo_eq]; simp

/-- The logical constraint system at a point in the loop: the original system with its interactions
    replaced by the live projection followed by the checks emitted so far. -/
def denseMkCs (cs0 : DenseConstraintSystem p) (arr : Array (BusInteraction (DenseExpr p)))
    (alive : Array Bool) (checks : List (BusInteraction (DenseExpr p))) : DenseConstraintSystem p :=
  { cs0 with busInteractions := denseLiveSeg arr alive 0 arr.size ++ checks }

/-- With every bit live, the projection is the whole array. -/
theorem denseLiveSeg_all (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (halive : ∀ k, k < arr.size → alive[k]?.getD false = true) :
    ∀ (lo n : Nat), lo + n = arr.size → denseLiveSeg arr alive lo n = arr.toList.drop lo := by
  intro lo n
  induction n generalizing lo with
  | zero =>
    intro h
    exact (List.drop_eq_nil_iff.2 (by rw [Array.length_toList]; omega)).symm
  | succ n ih =>
    intro h
    have hlo : lo < arr.size := by omega
    have hcons : arr.toList.drop lo = arr.toList[lo] :: arr.toList.drop (lo + 1) :=
      List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact hlo)
    rw [denseLiveSeg_peel arr alive lo n arr[lo] (halive lo hlo) (Array.getElem?_eq_getElem hlo),
      ih (lo + 1) (by omega), hcons, Array.getElem_toList]

/-- The initial logical system (all live, no checks) is the original system. -/
theorem denseMkCs_all (cs0 : DenseConstraintSystem p) (arr : Array (BusInteraction (DenseExpr p)))
    (harr : arr = cs0.busInteractions.toArray) (alive : Array Bool)
    (halive : ∀ k, k < arr.size → alive[k]?.getD false = true) :
    denseMkCs cs0 arr alive [] = cs0 := by
  unfold denseMkCs
  rw [denseLiveSeg_all arr alive halive 0 arr.size (by omega), List.drop_zero, List.append_nil, harr]

end ApcOptimizer.Dense
