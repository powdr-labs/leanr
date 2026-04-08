import Leanr.RangeConstraint

-- ===== Bitwise helper lemmas =====

theorem nat_and_two_pow_sub_one (n k : Nat) (h : n < 2^k) : n &&& (2^k - 1) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < k
  · simp [hi]
  · have := Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega : k ≤ i)))
    simp [show ¬(i < k) from hi, this]

/-- If n ≤ max and max > 0, then n fits in maskFromBits (numBits max). -/
theorem fits_maskFromBits (n max : Nat) (h : n ≤ max) (hmax : 0 < max) :
    n &&& maskFromBits (numBits max) = n := by
  have hne : max ≠ 0 := by omega
  have hnb : numBits max = Nat.log2 max + 1 := by
    unfold numBits; simp [show (max == 0) = false from beq_false_of_ne hne]
  have hmfb : maskFromBits (numBits max) = 2 ^ (Nat.log2 max + 1) - 1 := by
    unfold maskFromBits; rw [hnb]
    simp [show (Nat.log2 max + 1 == 0) = false from beq_false_of_ne (by omega)]
  rw [hmfb]
  apply nat_and_two_pow_sub_one
  exact lt_of_le_of_lt h ((Nat.log2_lt hne).mp (Nat.lt_add_one _))

/-- Conjunction of bitmasks: if n passes both masks, it passes their AND. -/
theorem nat_and_conj (n m1 m2 : Nat) (h1 : n &&& m1 = n) (h2 : n &&& m2 = n) :
    n &&& (m1 &&& m2) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_and]
  have h1i := congr_arg (·.testBit i) h1
  have h2i := congr_arg (·.testBit i) h2
  simp [Nat.testBit_and] at h1i h2i
  cases hn : n.testBit i <;> simp_all

/-- n passes a weaker mask (mask OR extra bits). -/
theorem nat_and_or_weaken (n m1 m2 : Nat) (h : n &&& m1 = n) :
    n &&& (m1 ||| m2) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_or]
  have hi := congr_arg (·.testBit i) h
  simp [Nat.testBit_and] at hi
  cases hn : n.testBit i <;> simp_all

-- ===== allowsValue decomposition =====

/-- Decompose allowsValue into range and mask conditions. -/
theorem RangeConstraint.allowsValue_iff {p : ℕ} (rc : RangeConstraint p) (v : ZMod p) :
    rc.allowsValue v = true ↔
    (if rc.min.val ≤ rc.max.val then
      rc.min.val ≤ v.val ∧ v.val ≤ rc.max.val
    else
      rc.min.val ≤ v.val ∨ v.val ≤ rc.max.val) ∧
    (v.val &&& rc.mask = v.val) := by
  unfold allowsValue
  simp only [Bool.and_eq_true_iff, beq_iff_eq]
  split <;> simp [decide_eq_true_iff]

-- ===== unconstrained allows any value =====

/-- `unconstrained` allows any value. -/
theorem RangeConstraint.unconstrained_allows_any {p : ℕ} [NeZero p] (v : ZMod p) :
    (RangeConstraint.unconstrained (p := p)).allowsValue v = true := by
  have hp : 0 < p := NeZero.pos p
  have hv : v.val < p := ZMod.val_lt v
  have hmask : v.val &&& (2 ^ (Nat.log 2 p + 1) - 1) = v.val := by
    apply nat_and_two_pow_sub_one
    exact lt_of_lt_of_le hv (Nat.lt_pow_succ_log_self (by omega) p).le
  unfold RangeConstraint.unconstrained RangeConstraint.allowsValue
  simp only [ZMod.val_zero, Nat.zero_le, ite_true]
  have hmax : ((p - 1 : Nat) : ZMod p).val = p - 1 := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
  rw [hmax, hmask, beq_self_eq_true]
  simp only [Bool.and_true, decide_true, Bool.true_and, decide_eq_true_eq]
  omega

-- ===== Soundness of fromRange =====

/-- fromRange allows values in a non-wrapping range [lo, hi]. -/
theorem RangeConstraint.fromRange_allows_nonwrap {p : ℕ} [NeZero p]
    (lo hi v : ZMod p) (hle : lo.val ≤ hi.val)
    (hlo : lo.val ≤ v.val) (hhi : v.val ≤ hi.val) :
    (RangeConstraint.fromRange lo hi).allowsValue v = true := by
  rw [allowsValue_iff]; unfold fromRange
  simp only [hle, ite_true]
  exact ⟨⟨hlo, hhi⟩, by
    by_cases hhi0 : hi.val = 0
    · have hv0 : v.val = 0 := by omega
      rw [hv0]; exact Nat.zero_and _
    · exact fits_maskFromBits v.val hi.val hhi (by omega)⟩

/-- fromRange allows values in a wrapping range [lo, hi]. -/
theorem RangeConstraint.fromRange_allows_wrap {p : ℕ} [NeZero p]
    (lo hi v : ZMod p) (hwrap : hi.val < lo.val)
    (hrange : lo.val ≤ v.val ∨ v.val ≤ hi.val) :
    (RangeConstraint.fromRange lo hi).allowsValue v = true := by
  rw [allowsValue_iff]; unfold fromRange
  simp only [show ¬(lo.val ≤ hi.val) from by omega, ite_false]
  constructor
  · exact hrange
  · show v.val &&& (RangeConstraint.unconstrained (p := p)).mask = v.val
    unfold RangeConstraint.unconstrained; simp only
    apply nat_and_two_pow_sub_one
    exact lt_of_lt_of_le (ZMod.val_lt v) (Nat.lt_pow_succ_log_self (by omega) p).le

-- ===== Range-only predicate and soundness =====

/-- Whether a value falls in the range [min, max] (wrapping supported). -/
def RangeConstraint.inRange {p : ℕ} (rc : RangeConstraint p) (v : ZMod p) : Prop :=
  if rc.min.val ≤ rc.max.val then
    rc.min.val ≤ v.val ∧ v.val ≤ rc.max.val
  else
    rc.min.val ≤ v.val ∨ v.val ≤ rc.max.val

/-- allowsValue implies inRange. -/
theorem RangeConstraint.allowsValue_inRange {p : ℕ} (rc : RangeConstraint p) (v : ZMod p)
    (h : rc.allowsValue v = true) : rc.inRange v := by
  rw [allowsValue_iff] at h; exact h.1

/-- Negation preserves range: if x ∈ [min, max] then -x ∈ [-max, -min]. -/
theorem RangeConstraint.neg_inRange {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (x : ZMod p)
    (h : rc.inRange x) :
    (rc.neg).inRange (-x) := by
  -- rc.neg = fromRange (-rc.max) (-rc.min), so neg.min = -rc.max, neg.max = -rc.min
  -- Key: ZMod.neg_val: (-a).val = if a = 0 then 0 else p - a.val
  -- If x ∈ [min, max] (non-wrapping): min.val ≤ x.val ≤ max.val
  --   When all nonzero: p - max.val ≤ p - x.val ≤ p - min.val → -x ∈ [-max, -min] non-wrapping
  --   Zero cases need care but fromRange handles wrapping
  -- If x ∈ [min, max] (wrapping): min.val ≤ x.val ∨ x.val ≤ max.val → similar reversal
  sorry

/-- Addition preserves range: if x1 ∈ rc1's range and x2 ∈ rc2's range,
    then x1 + x2 ∈ (rc1.add rc2)'s range. -/
theorem RangeConstraint.add_inRange {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.inRange x1) (h2 : rc2.inRange x2) :
    (rc1.add rc2).inRange (x1 + x2) := by
  -- The add range is either (min1+min2, max1+max2) when widths don't overflow,
  -- or (0, p-1) (unconstrained) when they do.
  -- Unconstrained case is trivial.
  -- Non-overflow case: the key insight is that if widths sum ≤ p,
  -- then the sum range [min1+min2, max1+max2] contains x1+x2 in ZMod.
  sorry

/-- Subtraction preserves range (follows from add + neg). -/
theorem RangeConstraint.sub_inRange {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.inRange x1) (h2 : rc2.inRange x2) :
    (rc1.sub rc2).inRange (x1 - x2) := by
  unfold RangeConstraint.sub
  rw [show x1 - x2 = x1 + (-x2) from sub_eq_add_neg x1 x2]
  exact add_inRange rc1 rc2.neg x1 (-x2) h1 (neg_inRange rc2 x2 h2)

/-- Scalar multiplication preserves range. -/
theorem RangeConstraint.multiple_inRange {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (f x : ZMod p)
    (h : rc.inRange x) :
    (rc.multiple f).inRange (f * x) := by
  sorry

/-- Multiplication preserves range. -/
theorem RangeConstraint.mul_inRange {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.inRange x1) (h2 : rc2.inRange x2) :
    (rc1.mul rc2).inRange (x1 * x2) := by
  sorry

/-- Conjunction preserves range. -/
theorem RangeConstraint.conjunction_inRange {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x : ZMod p)
    (h1 : rc1.inRange x) (h2 : rc2.inRange x) :
    (rc1.conjunction rc2).inRange x := by
  sorry

-- ===== Main soundness theorems =====

/-- Negation is sound: if rc allows x, then rc.neg allows -x. -/
theorem RangeConstraint.neg_sound {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (x : ZMod p)
    (h : rc.allowsValue x = true) :
    rc.neg.allowsValue (-x) = true := by
  -- rc.neg = fromRange (-rc.max) (-rc.min)
  -- Need: (-x) in range [-max, -min] with proper mask.
  -- Key: ZMod.neg_val gives (-a).val = if a = 0 then 0 else p - a.val
  -- Negation reverses range membership in ZMod.
  -- The mask from fromRange is either maskFromBits (non-wrapping) or unconstrained (wrapping),
  -- both sufficient since (-x).val < p.
  unfold RangeConstraint.neg; sorry

/-- Addition is sound: if rc1 allows x1 and rc2 allows x2,
    then (rc1.add rc2) allows (x1 + x2). -/
theorem RangeConstraint.add_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.add rc2).allowsValue (x1 + x2) = true := by
  -- Overflow cases return unconstrained (trivially sound).
  -- Non-overflow: range widths don't exceed p, so [min1+min2, max1+max2] is sound;
  -- mask (m1+m2) ||| m1 ||| m2 covers all bits of (x1+x2) since val(x1+x2) ≤ val(x1)+val(x2).
  unfold RangeConstraint.add; simp; sorry

/-- Subtraction is sound: follows from add_sound and neg_sound. -/
theorem RangeConstraint.sub_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.sub rc2).allowsValue (x1 - x2) = true := by
  unfold RangeConstraint.sub
  show (rc1.add rc2.neg).allowsValue (x1 - x2) = true
  have hneg : rc2.neg.allowsValue (-x2) = true := neg_sound rc2 x2 h2
  rw [show x1 - x2 = x1 + (-x2) from sub_eq_add_neg x1 x2]
  exact add_sound rc1 rc2.neg x1 (-x2) h1 hneg

/-- Scalar multiplication is sound. -/
theorem RangeConstraint.multiple_sound {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (f x : ZMod p)
    (h : rc.allowsValue x = true) :
    (rc.multiple f).allowsValue (f * x) = true := by
  unfold RangeConstraint.multiple; sorry

/-- Multiplication is sound. -/
theorem RangeConstraint.mul_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.mul rc2).allowsValue (x1 * x2) = true := by
  unfold RangeConstraint.mul; sorry

/-- Conjunction is sound. -/
theorem RangeConstraint.conjunction_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x : ZMod p)
    (h1 : rc1.allowsValue x = true) (h2 : rc2.allowsValue x = true) :
    (rc1.conjunction rc2).allowsValue x = true := by
  unfold RangeConstraint.conjunction; sorry
