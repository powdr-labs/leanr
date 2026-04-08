import Leanr.RangeConstraint
import Mathlib.Tactic.Ring

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

-- ===== ZMod val arithmetic helpers =====

/-- val of a ZMod subtraction, with wrapping. -/
theorem ZMod_val_sub {p : ℕ} [NeZero p] (a b : ZMod p) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else a.val + p - b.val := by
  split
  case isTrue h => exact ZMod.val_sub h
  case isFalse h =>
    push Not at h
    rw [show a - b = a + (-b) from sub_eq_add_neg a b, ZMod.val_add, ZMod.neg_val']
    have hb : b.val < p := ZMod.val_lt b
    by_cases hb0 : b.val = 0
    · omega
    · rw [Nat.mod_eq_of_lt (by omega : p - b.val < p),
          Nat.mod_eq_of_lt (by omega : a.val + (p - b.val) < p)]
      omega

-- ===== Range-only predicate and soundness =====

/-- Whether a value falls in the range [min, max] (wrapping supported). -/
def RangeConstraint.inRange {p : ℕ} (rc : RangeConstraint p) (v : ZMod p) : Prop :=
  if rc.min.val ≤ rc.max.val then
    rc.min.val ≤ v.val ∧ v.val ≤ rc.max.val
  else
    rc.min.val ≤ v.val ∨ v.val ≤ rc.max.val

/-- inRange is equivalent to (v - min).val ≤ (max - min).val (offset form). -/
theorem RangeConstraint.inRange_iff_offset {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (v : ZMod p) :
    rc.inRange v ↔ (v - rc.min).val ≤ (rc.max - rc.min).val := by
  have hp : 0 < p := NeZero.pos p
  have hv : v.val < p := ZMod.val_lt v
  have hmin : rc.min.val < p := ZMod.val_lt rc.min
  have hmax : rc.max.val < p := ZMod.val_lt rc.max
  unfold inRange
  rw [ZMod_val_sub v rc.min, ZMod_val_sub rc.max rc.min]
  by_cases hle : rc.min.val ≤ rc.max.val
  · by_cases hvm : rc.min.val ≤ v.val
    · simp only [if_pos hle, if_pos hvm]; constructor <;> omega
    · push Not at hvm
      simp only [if_pos hle, if_neg (show ¬(rc.min.val ≤ v.val) from by omega)]
      constructor
      · intro ⟨h1, _⟩; omega
      · intro h; exfalso; omega
  · push Not at hle
    by_cases hvm : rc.min.val ≤ v.val
    · simp only [if_neg (show ¬(rc.min.val ≤ rc.max.val) from by omega), if_pos hvm]
      constructor
      · intro _; omega
      · intro _; exact Or.inl hvm
    · push Not at hvm
      simp only [if_neg (show ¬(rc.min.val ≤ rc.max.val) from by omega),
                  if_neg (show ¬(rc.min.val ≤ v.val) from by omega)]
      constructor
      · intro h; cases h with
        | inl h => omega
        | inr h => omega
      · intro h; exact Or.inr (by omega)

/-- The unconstrained range contains every value. -/
theorem RangeConstraint.unconstrained_inRange {p : ℕ} [NeZero p] (v : ZMod p) :
    (RangeConstraint.unconstrained (p := p)).inRange v := by
  have hp : 0 < p := NeZero.pos p
  have hv : v.val < p := ZMod.val_lt v
  unfold unconstrained inRange
  simp only [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
  split <;> omega

/-- The width of unconstrained is p. -/
theorem RangeConstraint.unconstrained_rangeWidth {p : ℕ} [NeZero p] :
    (RangeConstraint.unconstrained (p := p)).rangeWidth = p := by
  have hp : 0 < p := NeZero.pos p
  unfold unconstrained rangeWidth
  simp only
  have hcast : ((p - 1 : ℕ) : ZMod p) + 1 = (0 : ZMod p) := by
    rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) from Nat.cast_one.symm,
        ← Nat.cast_add, show p - 1 + 1 = p from by omega, ZMod.natCast_self]
  rw [show (((p - 1 : ℕ) : ZMod p) + 1 == (0 : ZMod p)) = true from beq_iff_eq.mpr hcast]
  simp

/-- The span (max - min).val is strictly less than rangeWidth. -/
theorem RangeConstraint.span_lt_rangeWidth {p : ℕ} [NeZero p] (rc : RangeConstraint p) :
    (rc.max - rc.min).val < rc.rangeWidth := by
  have hp : 0 < p := NeZero.pos p
  unfold rangeWidth
  by_cases hfull : (rc.max + 1 == rc.min) = true
  · simp [hfull]; exact ZMod.val_lt _
  · simp [hfull]
    have hne : ¬(rc.max + 1 = rc.min) := fun h => hfull (beq_iff_eq.mpr h)
    have hp2 : 2 ≤ p := by
      by_contra hlt
      push Not at hlt
      have hp1 : p = 1 := by omega
      subst hp1
      exact hne (Subsingleton.elim _ _)
    have hspan_lt : (rc.max - rc.min).val < p - 1 := by
      by_contra hge
      push Not at hge
      have hval : (rc.max - rc.min).val = p - 1 := by
        have := ZMod.val_lt (rc.max - rc.min); omega
      have hd1_val : (rc.max - rc.min + 1).val = 0 := by
        conv => lhs; rw [show rc.max - rc.min + 1 = rc.max - rc.min + ((1 : ℕ) : ZMod p) from by norm_cast]
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < p), hval,
            show p - 1 + 1 = p from by omega, Nat.mod_self]
      have hd1_zero : rc.max - rc.min + 1 = 0 := (ZMod.val_eq_zero _).mp hd1_val
      have : rc.max + 1 = rc.min := by
        have h1 : rc.max + 1 = (rc.max - rc.min + 1) + rc.min := by ring
        rw [hd1_zero, zero_add] at h1
        exact h1
      exact hne this
    suffices h : (rc.max - rc.min + 1).val = (rc.max - rc.min).val + 1 by omega
    conv => lhs; rw [show rc.max - rc.min + 1 = rc.max - rc.min + ((1 : ℕ) : ZMod p) from by norm_cast]
    rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < p),
        Nat.mod_eq_of_lt (by omega)]

/-- allowsValue implies inRange. -/
theorem RangeConstraint.allowsValue_inRange {p : ℕ} (rc : RangeConstraint p) (v : ZMod p)
    (h : rc.allowsValue v = true) : rc.inRange v := by
  rw [allowsValue_iff] at h; exact h.1

/-- fromRange always generates a valid allowsValue for values in its range. -/
theorem RangeConstraint.fromRange_allowsValue_of_inRange {p : ℕ} [NeZero p]
    (lo hi v : ZMod p)
    (h : (RangeConstraint.fromRange lo hi).inRange v) :
    (RangeConstraint.fromRange lo hi).allowsValue v = true := by
  unfold RangeConstraint.inRange at h
  simp only [show (fromRange lo hi).min = lo from rfl,
             show (fromRange lo hi).max = hi from rfl] at h
  by_cases hle : lo.val ≤ hi.val
  · rw [if_pos hle] at h
    exact fromRange_allows_nonwrap lo hi v hle h.1 h.2
  · push Not at hle
    rw [if_neg (show ¬(lo.val ≤ hi.val) from by omega)] at h
    exact fromRange_allows_wrap lo hi v (by omega) h

/-- Negation preserves range: if x ∈ [min, max] then -x ∈ [-max, -min]. -/
theorem RangeConstraint.neg_inRange {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (x : ZMod p)
    (h : rc.inRange x) :
    (rc.neg).inRange (-x) := by
  unfold RangeConstraint.neg RangeConstraint.fromRange
  rw [inRange_iff_offset]
  simp only
  rw [show -x - -rc.max = rc.max - x from by ring,
      show -rc.min - -rc.max = rc.max - rc.min from by ring]
  rw [inRange_iff_offset] at h
  have hp : 0 < p := NeZero.pos p
  have hx : x.val < p := ZMod.val_lt x
  have hmin : rc.min.val < p := ZMod.val_lt rc.min
  have hmax : rc.max.val < p := ZMod.val_lt rc.max
  by_cases hle : rc.min.val ≤ rc.max.val
  · -- Non-wrapping
    have hspan : (rc.max - rc.min).val = rc.max.val - rc.min.val := ZMod.val_sub hle
    rw [hspan] at h ⊢
    have hxmin : rc.min.val ≤ x.val := by
      rw [ZMod_val_sub] at h; split_ifs at h <;> omega
    have hxmax : x.val ≤ rc.max.val := by
      rw [ZMod_val_sub] at h; split_ifs at h <;> omega
    rw [ZMod.val_sub hxmax]; omega
  · -- Wrapping
    push Not at hle
    have hspan : (rc.max - rc.min).val = rc.max.val + p - rc.min.val := by
      rw [ZMod_val_sub]; simp [show ¬(rc.min.val ≤ rc.max.val) from by omega]
    rw [hspan] at h ⊢
    rw [ZMod_val_sub x rc.min] at h
    by_cases hxmin : rc.min.val ≤ x.val
    · simp only [if_pos hxmin] at h
      rw [ZMod_val_sub]; simp [show ¬(x.val ≤ rc.max.val) from by omega]; omega
    · push Not at hxmin
      simp only [if_neg (show ¬(rc.min.val ≤ x.val) from by omega)] at h
      have hxmax : x.val ≤ rc.max.val := by omega
      rw [ZMod.val_sub hxmax]; omega

/-- Addition preserves range: if x1 ∈ rc1's range and x2 ∈ rc2's range,
    then x1 + x2 ∈ (rc1.add rc2)'s range. -/
theorem RangeConstraint.add_inRange {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.inRange x1) (h2 : rc2.inRange x2) :
    (rc1.add rc2).inRange (x1 + x2) := by
  have hp : 0 < p := NeZero.pos p
  unfold RangeConstraint.add
  simp only
  by_cases hwidth : rc1.rangeWidth + rc2.rangeWidth ≤ (RangeConstraint.unconstrained (p := p)).rangeWidth
  · -- Non-overflow: result is [min1+min2, max1+max2]
    simp only [hwidth, ite_true]
    rw [inRange_iff_offset] at h1 h2 ⊢
    have heq1 : x1 + x2 - (rc1.min + rc2.min) = (x1 - rc1.min) + (x2 - rc2.min) := by ring
    have heq2 : rc1.max + rc2.max - (rc1.min + rc2.min) = (rc1.max - rc1.min) + (rc2.max - rc2.min) := by ring
    rw [heq1, heq2, unconstrained_rangeWidth] at *
    have hs1 := span_lt_rangeWidth rc1
    have hs2 := span_lt_rangeWidth rc2
    rw [ZMod.val_add, ZMod.val_add,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · -- Overflow: result is unconstrained
    push Not at hwidth
    simp only [show ¬(rc1.rangeWidth + rc2.rangeWidth ≤ (RangeConstraint.unconstrained (p := p)).rangeWidth) from by omega, ite_false]
    exact unconstrained_inRange _

/-- Subtraction preserves range (follows from add + neg). -/
theorem RangeConstraint.sub_inRange {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.inRange x1) (h2 : rc2.inRange x2) :
    (rc1.sub rc2).inRange (x1 - x2) := by
  unfold RangeConstraint.sub
  rw [show x1 - x2 = x1 + (-x2) from sub_eq_add_neg x1 x2]
  exact add_inRange rc1 rc2.neg x1 (-x2) h1 (neg_inRange rc2 x2 h2)

/-- val of a ZMod product when the Nat product doesn't overflow. -/
theorem ZMod_val_mul {p : ℕ} [NeZero p] (a b : ZMod p)
    (h : a.val * b.val < p) :
    (a * b).val = a.val * b.val := by
  rw [show a * b = ((a.val * b.val : ℕ) : ZMod p) from by push_cast; simp [ZMod.natCast_val]]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

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
  unfold RangeConstraint.mul
  split
  · -- b.toSingleValue? = some v → multiple
    sorry
  · split
    · -- a.toSingleValue? = some v → multiple
      sorry
    · -- Neither is single value
      split
      · -- fromRange case: non-wrapping and max1*max2 < p
        rename_i hb ha hcond
        simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hcond
        obtain ⟨⟨hle1, hle2⟩, hmul⟩ := hcond
        unfold inRange at h1 h2
        rw [if_pos hle1] at h1; rw [if_pos hle2] at h2
        obtain ⟨hx1lo, hx1hi⟩ := h1; obtain ⟨hx2lo, hx2hi⟩ := h2
        have hmulx : x1.val * x2.val < p := by
          calc x1.val * x2.val ≤ rc1.max.val * rc2.max.val := Nat.mul_le_mul hx1hi hx2hi
          _ < p := hmul
        have hval_lo : (rc1.min * rc2.min).val = rc1.min.val * rc2.min.val :=
          ZMod_val_mul rc1.min rc2.min (by
            calc rc1.min.val * rc2.min.val ≤ rc1.max.val * rc2.max.val :=
                  Nat.mul_le_mul (by omega) (by omega)
            _ < p := hmul)
        have hval_hi : (rc1.max * rc2.max).val = rc1.max.val * rc2.max.val :=
          ZMod_val_mul rc1.max rc2.max hmul
        have hle_range : (rc1.min * rc2.min).val ≤ (rc1.max * rc2.max).val := by
          rw [hval_lo, hval_hi]; exact Nat.mul_le_mul (by omega) (by omega)
        unfold inRange fromRange
        simp only [hle_range, ite_true]
        rw [ZMod_val_mul x1 x2 hmulx, hval_lo, hval_hi]
        exact ⟨Nat.mul_le_mul hx1lo hx2lo, Nat.mul_le_mul hx1hi hx2hi⟩
      · -- Unconstrained fallback
        exact unconstrained_inRange _

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
  rw [allowsValue_iff] at h ⊢
  have hir : rc.inRange x := allowsValue_inRange rc x (by rw [allowsValue_iff]; exact h)
  have hnir := neg_inRange rc x hir
  unfold neg fromRange at hnir ⊢
  simp only at hnir ⊢
  constructor
  · unfold inRange at hnir; exact hnir
  · by_cases hle : (-rc.max).val ≤ (-rc.min).val
    · simp only [hle, ite_true]
      by_cases hmin0 : (-rc.min).val = 0
      · unfold inRange at hnir
        simp only [hle, ite_true] at hnir
        have : (-x).val = 0 := by omega
        rw [this]; exact Nat.zero_and _
      · exact fits_maskFromBits (-x).val (-rc.min).val
          (by unfold inRange at hnir; simp [hle] at hnir; exact hnir.2) (by omega)
    · push Not at hle
      simp only [show ¬((-rc.max).val ≤ (-rc.min).val) from by omega, ite_false]
      show (-x).val &&& (RangeConstraint.unconstrained (p := p)).mask = (-x).val
      unfold RangeConstraint.unconstrained; simp only
      apply nat_and_two_pow_sub_one
      exact lt_of_lt_of_le (ZMod.val_lt (-x)) (Nat.lt_pow_succ_log_self (by omega) p).le

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
