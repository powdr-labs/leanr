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

/-- The overflow range [1, 0] contains all values. -/
theorem overflow_range_inRange {p : ℕ} [NeZero p] (v : ZMod p) :
    RangeConstraint.inRange { mask := 0, min := (1 : ZMod p), max := (0 : ZMod p) } v := by
  unfold RangeConstraint.inRange; simp only
  have hp : 0 < p := NeZero.pos p
  by_cases hp1 : p = 1
  · subst hp1; simp [show (1 : ZMod 1).val = 0 from by decide,
      show (0 : ZMod 1).val = 0 from by decide, Subsingleton.elim v 0]
  · rw [show (1 : ZMod p).val = 1 from by
        rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) from Nat.cast_one.symm,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)],
      ZMod.val_zero, if_neg (by omega)]
    cases Nat.eq_zero_or_pos v.val with
    | inl h => right; omega
    | inr h => left; omega

/-- inRange doesn't depend on the mask field. -/
theorem RangeConstraint.inRange_mask_irrelevant {p : ℕ}
    (m1 m2 : Nat) (lo hi : ZMod p) (v : ZMod p) :
    RangeConstraint.inRange { mask := m1, min := lo, max := hi } v ↔
    RangeConstraint.inRange { mask := m2, min := lo, max := hi } v := by
  unfold inRange; simp

/-- rangeMultiple preserves range membership. -/
theorem rangeMultiple_inRange {p : ℕ} [NeZero p]
    (lo hi factor x : ZMod p)
    (h : RangeConstraint.inRange { mask := 0, min := lo, max := hi } x) :
    RangeConstraint.inRange { mask := 0, min := (rangeMultiple lo hi factor).1,
                               max := (rangeMultiple lo hi factor).2 } (factor * x) := by
  have hp : 0 < p := NeZero.pos p
  unfold rangeMultiple; simp only
  set w := if hi + 1 == lo then p else (hi - lo + 1).val
  by_cases hle : w * factor.val ≤ p
  · simp only [hle, ite_true]
    rw [RangeConstraint.inRange_iff_offset] at h ⊢; simp only at h ⊢
    rw [show factor * x - lo * factor = factor * (x - lo) from by ring,
        show hi * factor - lo * factor = factor * (hi - lo) from by ring]
    have hspan : (hi - lo).val < w :=
      RangeConstraint.span_lt_rangeWidth ({ mask := 0, min := lo, max := hi } : RangeConstraint p)
    by_cases hf0 : factor.val = 0
    · rw [show factor = 0 from by rwa [ZMod.val_eq_zero] at hf0]; simp
    · have hfs : factor.val * (hi - lo).val < p := by
        have h1 : factor.val * (hi - lo).val < factor.val * w :=
          (Nat.mul_lt_mul_left (by omega)).mpr hspan
        have h2 : factor.val * w = w * factor.val := Nat.mul_comm _ _; omega
      have hfd : factor.val * (x - lo).val < p := by
        have := Nat.mul_le_mul_left factor.val h; omega
      rw [show factor * (x - lo) = ((factor.val * (x - lo).val : ℕ) : ZMod p) from by
            push_cast; simp [ZMod.natCast_val],
          show factor * (hi - lo) = ((factor.val * (hi - lo).val : ℕ) : ZMod p) from by
            push_cast; simp [ZMod.natCast_val],
          ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hfd, Nat.mod_eq_of_lt hfs]
      exact Nat.mul_le_mul_left _ h
  · push Not at hle
    simp only [show ¬(w * factor.val ≤ p) from by omega, ite_false]
    exact overflow_range_inRange _

/-- Scalar multiplication preserves range. -/
theorem RangeConstraint.multiple_inRange {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (f x : ZMod p)
    (h : rc.inRange x) :
    (rc.multiple f).inRange (f * x) := by
  unfold RangeConstraint.multiple; simp only
  by_cases hlh : f.val ≤ p / 2
  · simp only [hlh, ite_true]
    rw [inRange_mask_irrelevant _ 0]
    exact rangeMultiple_inRange rc.min rc.max f x
      ((inRange_mask_irrelevant rc.mask 0 rc.min rc.max x).mp h)
  · push Not at hlh
    simp only [show ¬(f.val ≤ p / 2) from by omega, ite_false]
    rw [inRange_mask_irrelevant _ 0, show f * x = (-f) * (-x) from by ring]
    have hnir := neg_inRange rc x h
    unfold neg fromRange at hnir
    exact rangeMultiple_inRange (-rc.max) (-rc.min) (-f) (-x)
      ((inRange_mask_irrelevant _ 0 _ _ _).mp hnir)

/-- If toSingleValue? returns some v and x is in range, then x = v. -/
theorem toSingleValue_eq {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (v x : ZMod p)
    (hsv : rc.toSingleValue? = some v) (h : rc.inRange x) : x = v := by
  unfold RangeConstraint.toSingleValue? at hsv
  split at hsv
  · rename_i hcond
    injection hsv with hsv; subst hsv
    simp only [Bool.and_eq_true_iff] at hcond
    rw [beq_iff_eq] at hcond
    unfold RangeConstraint.inRange at h
    have : rc.min.val = rc.max.val := congr_arg ZMod.val hcond.1
    rw [if_pos (by omega : rc.min.val ≤ rc.max.val)] at h
    exact ZMod.val_injective p (by omega)
  · contradiction

/-- Multiplication preserves range. -/
theorem RangeConstraint.mul_inRange {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.inRange x1) (h2 : rc2.inRange x2) :
    (rc1.mul rc2).inRange (x1 * x2) := by
  unfold RangeConstraint.mul
  split
  · -- b.toSingleValue? = some v
    next v hv =>
    have hx2v : x2 = v := toSingleValue_eq rc2 v x2 hv h2
    subst hx2v
    rw [show x1 * x2 = x2 * x1 from mul_comm x1 x2]
    exact multiple_inRange rc1 x2 x1 h1
  · split
    · -- a.toSingleValue? = some v
      next hb v hv =>
      have hx1v : x1 = v := toSingleValue_eq rc1 v x1 hv h1
      subst hx1v
      exact multiple_inRange rc2 x1 x2 h2
    · split
      · -- fromRange case
        next hb ha hcond =>
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
      · exact unconstrained_inRange _

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

/-- x &&& m = x implies x ≤ m. -/
theorem nat_and_eq_implies_le (x m : Nat) (h : x &&& m = x) : x ≤ m := by
  have := @Nat.and_le_right x m; omega

-- ===== Bitwise addition carry theory =====

/-- Carry function for binary addition. -/
def addCarry (x y : Nat) : Nat → Bool
  | 0 => false
  | i + 1 => (x.testBit i && y.testBit i) ||
              (x.testBit i && addCarry x y i) ||
              (y.testBit i && addCarry x y i)

/-- Generalized carry with initial carry bit. -/
def genCarry (x y : Nat) (c : Bool) : Nat → Bool
  | 0 => c
  | i + 1 => (x.testBit i && y.testBit i) ||
              (x.testBit i && genCarry x y c i) ||
              (y.testBit i && genCarry x y c i)

theorem addCarry_eq_genCarry (x y i : Nat) : addCarry x y i = genCarry x y false i := by
  induction i with
  | zero => rfl
  | succ n ih => unfold addCarry genCarry; rw [ih]

/-- Carry shifts: genCarry at (i+1) equals genCarry of halved inputs at i. -/
theorem genCarry_succ_shift (x y : Nat) (c : Bool) (i : Nat) :
    genCarry x y c (i + 1) = genCarry (x / 2) (y / 2) (genCarry x y c 1) i := by
  induction i with
  | zero => unfold genCarry; rfl
  | succ n ih =>
    show (x.testBit (n + 1) && y.testBit (n + 1) ||
          x.testBit (n + 1) && genCarry x y c (n + 1) ||
          y.testBit (n + 1) && genCarry x y c (n + 1)) =
         ((x / 2).testBit n && (y / 2).testBit n ||
          (x / 2).testBit n && genCarry (x / 2) (y / 2) (genCarry x y c 1) n ||
          (y / 2).testBit n && genCarry (x / 2) (y / 2) (genCarry x y c 1) n)
    rw [Nat.testBit_succ, Nat.testBit_succ, ih]

/-- Parity of sum with carry. -/
theorem testBit_zero_add (x y : Nat) (c : Bool) :
    (x + y + c.toNat).testBit 0 = (x.testBit 0).xor ((y.testBit 0).xor c) := by
  simp only [Nat.testBit_zero]
  have hx : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
  have hy : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;> simp [hx, hy, Bool.xor]
  all_goals omega

/-- Division by 2 of sum distributes with carry. -/
theorem add_div2_eq (x y : Nat) (c : Bool) :
    (x + y + c.toNat) / 2 = x / 2 + y / 2 + (genCarry x y c 1).toNat := by
  unfold genCarry
  simp only [genCarry, Nat.testBit_zero]
  have hx : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
  have hy : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
  have hxd := Nat.div_add_mod x 2
  have hyd := Nat.div_add_mod y 2
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;> simp [hx, hy] <;> omega

/-- testBit of sum equals XOR with carry (generalized). -/
theorem testBit_add_gen (x y : Nat) (c : Bool) (i : Nat) :
    (x + y + c.toNat).testBit i = (x.testBit i).xor ((y.testBit i).xor (genCarry x y c i)) := by
  induction i generalizing x y c with
  | zero => exact testBit_zero_add x y c
  | succ n ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    rw [genCarry_succ_shift, add_div2_eq]
    exact ih (x / 2) (y / 2) (genCarry x y c 1)

/-- testBit of sum equals XOR with carry. -/
theorem testBit_add (x y i : Nat) :
    (x + y).testBit i = (x.testBit i).xor ((y.testBit i).xor (addCarry x y i)) := by
  rw [addCarry_eq_genCarry]; have := testBit_add_gen x y false i; simp at this; exact this

/-- If x's bits are subset of m's, then x.testBit i → m.testBit i. -/
theorem and_eq_self_testBit (x m : Nat) (h : x &&& m = x) (i : Nat)
    (hxi : x.testBit i = true) : m.testBit i = true := by
  have hi := congr_arg (·.testBit i) h
  simp only [Nat.testBit_and] at hi
  rw [hxi, Bool.true_and] at hi; exact hi

/-- Carry monotonicity: if x ⊆ m and y ⊆ n bitwise, carry(x,y) ≤ carry(m,n). -/
theorem carry_monotone (x1 x2 m1 m2 : Nat) (i : Nat)
    (h1 : x1 &&& m1 = x1) (h2 : x2 &&& m2 = x2)
    (hc : addCarry x1 x2 i = true) : addCarry m1 m2 i = true := by
  induction i with
  | zero => simp [addCarry] at hc
  | succ n ih =>
    unfold addCarry at hc ⊢
    have hx1m := and_eq_self_testBit x1 m1 h1 n
    have hx2m := and_eq_self_testBit x2 m2 h2 n
    cases hx1n : x1.testBit n <;> cases hx2n : x2.testBit n
    · simp [hx1n, hx2n] at hc
    · simp [hx1n, hx2n] at hc; simp [hx2m hx2n, ih hc]
    · simp [hx1n, hx2n] at hc; simp [hx1m hx1n, ih hc]
    · simp [hx1m hx1n, hx2m hx2n]

/-- Core mask lemma for addition: if x1 ⊆ m1 and x2 ⊆ m2 bitwise,
    then (x1+x2) ⊆ (m1+m2) ||| m1 ||| m2 bitwise. -/
theorem add_mask_preservation (x1 x2 m1 m2 : Nat)
    (h1 : x1 &&& m1 = x1) (h2 : x2 &&& m2 = x2) :
    (x1 + x2) &&& ((m1 + m2) ||| m1 ||| m2) = x1 + x2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  by_cases hb : (x1 + x2).testBit i
  · rw [hb]; simp
    rw [testBit_add] at hb
    by_cases hx1 : x1.testBit i <;> by_cases hx2 : x2.testBit i
    · left; right; exact and_eq_self_testBit x1 m1 h1 i hx1
    · left; right; exact and_eq_self_testBit x1 m1 h1 i hx1
    · right; exact and_eq_self_testBit x2 m2 h2 i hx2
    · -- Both false, carry must be true
      simp [hx1, hx2, Bool.xor] at hb
      have hcm := carry_monotone x1 x2 m1 m2 i h1 h2 hb
      rw [testBit_add m1 m2 i]
      by_cases hm1 : m1.testBit i <;> by_cases hm2 : m2.testBit i
      · left; left; simp [hm1, hm2, Bool.xor, hcm]
      · left; right; exact hm1
      · right; exact hm2
      · left; left; simp [hm1, hm2, Bool.xor, hcm]
  · simp [show (x1 + x2).testBit i = false by simp_all]

/-- Extract inRange bound from add result in range-ok nonwrap case. -/
private theorem add_inRange_val_le_max {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (v : ZMod p)
    (hir : (rc1.add rc2).inRange v)
    (hrange : rc1.rangeWidth + rc2.rangeWidth ≤
      (RangeConstraint.unconstrained (p := p)).rangeWidth)
    (hnonwrap : (rc1.min + rc2.min).val ≤ (rc1.max + rc2.max).val) :
    v.val ≤ (rc1.max + rc2.max).val := by
  unfold RangeConstraint.add RangeConstraint.inRange at hir
  simp only [] at hir; rw [if_pos hrange] at hir
  simp only [] at hir; rw [if_pos hnonwrap] at hir
  exact hir.2

/-- unc.mask covers any value in ZMod p. -/
private theorem unc_mask_covers_val {p : ℕ} [NeZero p] (v : ZMod p) :
    v.val &&& (RangeConstraint.unconstrained (p := p)).mask = v.val := by
  have hp : 0 < p := NeZero.pos p
  exact nat_and_two_pow_sub_one _ _
    (lt_of_lt_of_le (ZMod.val_lt v) (Nat.lt_pow_succ_log_self (by omega) p).le)

/-- val < p → val fits maskFromBits(numBits (p-1)). -/
private theorem fits_maskFromBits_p_minus_1 {p : ℕ} [NeZero p] (n : Nat) (h : n < p) :
    n &&& maskFromBits (numBits ((p - 1 : Nat) : ZMod p).val) = n := by
  have hp : 0 < p := NeZero.pos p
  rw [show ((p - 1 : Nat) : ZMod p).val = p - 1 from by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)]
  rcases Nat.eq_zero_or_pos (p - 1) with hp1 | hp1
  · have : p = 1 := by omega
    subst this; simp at h; subst h; simp [Nat.zero_and]
  · exact fits_maskFromBits _ _ (by omega) hp1

/-- fits_maskFromBits extended to handle max=0. -/
private theorem fits_maskFromBits' (n m : Nat) (h : n ≤ m) :
    n &&& maskFromBits (numBits m) = n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp at h; subst h; simp [Nat.zero_and]
  · exact fits_maskFromBits n m h hm

/-- When mask sum < p, val of ZMod sum equals Nat sum. -/
private theorem val_add_of_masks_lt {p : ℕ} [NeZero p]
    (x1 x2 : ZMod p) (m1 m2 : Nat)
    (hm1 : x1.val &&& m1 = x1.val) (hm2 : x2.val &&& m2 = x2.val)
    (hmov : ¬(m1 + m2 ≥ p)) :
    (x1 + x2).val = x1.val + x2.val := by
  push Not at hmov
  have : x1.val + x2.val < p := by
    have := nat_and_eq_implies_le _ _ hm1
    have := nat_and_eq_implies_le _ _ hm2; omega
  rw [ZMod.val_add]; exact Nat.mod_eq_of_lt this

set_option maxHeartbeats 800000 in
/-- Addition is sound: if rc1 allows x1 and rc2 allows x2,
    then (rc1.add rc2) allows (x1 + x2).
    Range part proved by add_inRange. Mask part uses add_mask_preservation. -/
theorem RangeConstraint.add_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.add rc2).allowsValue (x1 + x2) = true := by
  have hm1 := ((rc1.allowsValue_iff x1).mp h1).2
  have hm2 := ((rc2.allowsValue_iff x2).mp h2).2
  have hir_add := RangeConstraint.add_inRange rc1 rc2 _ _
    (rc1.allowsValue_inRange x1 h1) (rc2.allowsValue_inRange x2 h2)
  have hv_lt := ZMod.val_lt (x1 + x2)
  rw [RangeConstraint.allowsValue_iff]
  refine ⟨hir_add, ?_⟩
  unfold RangeConstraint.add; simp only []
  -- 8 branches from: range overflow × non-wrapping × mask overflow
  split <;> split <;> split
  -- range_ok, nonwrap, mask_ov: unc.mask &&& maskFromBits
  · next hrange hnonwrap _ =>
    apply nat_and_conj
    · exact unc_mask_covers_val _
    · exact fits_maskFromBits' _ _
        (add_inRange_val_le_max rc1 rc2 (x1+x2) hir_add hrange hnonwrap)
  -- range_ok, nonwrap, no mask_ov: maskSum &&& maskFromBits
  · next hrange hnonwrap hmov =>
    rw [val_add_of_masks_lt x1 x2 _ _ hm1 hm2 hmov]
    apply nat_and_conj
    · exact add_mask_preservation x1.val x2.val rc1.mask rc2.mask hm1 hm2
    · have hb := add_inRange_val_le_max rc1 rc2 (x1+x2) hir_add hrange hnonwrap
      rw [val_add_of_masks_lt x1 x2 _ _ hm1 hm2 hmov] at hb
      exact fits_maskFromBits' _ _ hb
  -- range_ok, wrap, mask_ov: unc.mask
  · exact unc_mask_covers_val _
  -- range_ok, wrap, no mask_ov: maskSum
  · next _ _ hmov =>
    rw [val_add_of_masks_lt x1 x2 _ _ hm1 hm2 hmov]
    exact add_mask_preservation x1.val x2.val rc1.mask rc2.mask hm1 hm2
  -- range_ov, nonwrap, mask_ov: unc.mask &&& maskFromBits(numBits unc.max.val)
  · apply nat_and_conj
    · exact unc_mask_covers_val _
    · exact fits_maskFromBits_p_minus_1 _ hv_lt
  -- range_ov, nonwrap, no mask_ov: maskSum &&& maskFromBits
  · next _ _ hmov =>
    rw [val_add_of_masks_lt x1 x2 _ _ hm1 hm2 hmov]
    apply nat_and_conj
    · exact add_mask_preservation x1.val x2.val rc1.mask rc2.mask hm1 hm2
    · exact fits_maskFromBits_p_minus_1 _ (by
        have := nat_and_eq_implies_le _ _ hm1
        have := nat_and_eq_implies_le _ _ hm2
        push Not at hmov; omega)
  -- range_ov, wrap, mask_ov: unc.mask
  · exact unc_mask_covers_val _
  -- range_ov, wrap, no mask_ov: maskSum
  · next _ _ hmov =>
    rw [val_add_of_masks_lt x1 x2 _ _ hm1 hm2 hmov]
    exact add_mask_preservation x1.val x2.val rc1.mask rc2.mask hm1 hm2

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

-- ===== Helpers for multiple_sound =====

/-- Shift preserves bitwise AND: (a <<< n) &&& (b <<< n) = (a &&& b) <<< n. -/
theorem and_shiftLeft (a b n : Nat) : (a <<< n) &&& (b <<< n) = (a &&& b) <<< n := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_and, Nat.testBit_shiftLeft]
  cases (decide (i ≥ n)) <;> simp

/-- A nonzero value with n &&& (n-1) = 0 is 2^(log2 n). -/
theorem pow2_eq_of_and_pred (n : Nat) (hn : n ≠ 0) (hpow : n &&& (n-1) = 0) :
    n = 2^n.log2 := by
  have h := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hn).mp hpow
  obtain ⟨k, hk⟩ := h; subst hk; rw [Nat.log2_two_pow]

/-- When factor is a power of 2, the shifted mask covers the product value. -/
theorem shift_mask_covers {p : Nat} [NeZero p]
    (x : ZMod p) (mask : Nat) (f : ZMod p)
    (hmask : x.val &&& mask = x.val)
    (hfv_ne : f.val ≠ 0)
    (hpow2 : f.val &&& (f.val - 1) = 0)
    (hshift_lt : mask <<< Nat.log2 f.val < p) :
    (f * x).val &&& (mask <<< Nat.log2 f.val) = (f * x).val := by
  have hle := nat_and_eq_implies_le _ _ hmask
  have hlog := pow2_eq_of_and_pred f.val hfv_ne hpow2
  have hval_prod : f.val * x.val < p := by
    calc f.val * x.val
      _ ≤ f.val * mask := Nat.mul_le_mul_left f.val hle
      _ = 2^f.val.log2 * mask := by rw [← hlog]
      _ = mask * 2^f.val.log2 := Nat.mul_comm _ _
      _ = mask <<< f.val.log2 := (Nat.shiftLeft_eq mask f.val.log2).symm
      _ < p := hshift_lt
  have hval_eq : (f * x).val = f.val * x.val := by
    rw [show f * x = ((f.val * x.val : Nat) : ZMod p) from by push_cast; simp [ZMod.natCast_val]]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hval_prod]
  rw [hval_eq, show f.val * x.val = x.val * f.val from Nat.mul_comm _ _,
      show x.val * f.val = x.val * 2^f.val.log2 from by rw [← hlog],
      ← Nat.shiftLeft_eq, and_shiftLeft, hmask]

/-- Extract the mask condition from fromRange when inRange holds. -/
private theorem fromRange_mask_of_inRange {p : Nat} [NeZero p]
    (lo hi v : ZMod p)
    (h : (RangeConstraint.fromRange lo hi).inRange v) :
    v.val &&& (RangeConstraint.fromRange lo hi).mask = v.val :=
  ((RangeConstraint.allowsValue_iff _ _).mp
    (RangeConstraint.fromRange_allowsValue_of_inRange lo hi v h)).2

set_option maxHeartbeats 1600000 in
/-- Scalar multiplication is sound. -/
theorem RangeConstraint.multiple_sound {p : Nat} [NeZero p]
    (rc : RangeConstraint p) (f x : ZMod p)
    (h : rc.allowsValue x = true) :
    (rc.multiple f).allowsValue (f * x) = true := by
  have hir := RangeConstraint.multiple_inRange rc f x (RangeConstraint.allowsValue_inRange rc x h)
  have hmask := ((RangeConstraint.allowsValue_iff rc x).mp h).2
  rw [RangeConstraint.allowsValue_iff]; refine ⟨hir, ?_⟩
  show (f * x).val &&& (RangeConstraint.multiple rc f).mask = (f * x).val
  unfold RangeConstraint.multiple; simp only []
  split
  · -- f.val == 0: maskOpt = some 0
    rename_i hf0
    dsimp only [bind, pure, Bind.bind, Pure.pure, Option.bind]
    simp only [Option.getD_some]
    have : f.val = 0 := by simpa using hf0
    have : f = 0 := (ZMod.val_eq_zero f).mp this
    rw [this, zero_mul, ZMod.val_zero, Nat.zero_and]
  · -- f.val ≠ 0
    rename_i hf0
    have hfne : f.val ≠ 0 := by simpa using hf0
    simp only [guard]
    split
    · -- power of 2 factor
      rename_i hpow
      split
      · -- shifted mask fits in p
        rename_i hshift
        dsimp only [bind, pure, Bind.bind, Pure.pure, Option.bind]
        simp only [Option.getD_some]
        rw [beq_iff_eq] at hpow
        exact shift_mask_covers x rc.mask f hmask hfne hpow hshift
      · -- shifted too large, fallback to fromRange mask
        dsimp only [bind, pure, failure, Bind.bind, Pure.pure, Alternative.failure, Option.bind]
        simp only [Option.getD_none]
        exact fromRange_mask_of_inRange _ _ _
          ((RangeConstraint.inRange_mask_irrelevant _ _ _ _ _).mp hir)
    · -- not power of 2, fallback to fromRange mask
      dsimp only [bind, pure, failure, Bind.bind, Pure.pure, Alternative.failure, Option.bind]
      simp only [Option.getD_none]
      exact fromRange_mask_of_inRange _ _ _
        ((RangeConstraint.inRange_mask_irrelevant _ _ _ _ _).mp hir)

set_option maxHeartbeats 800000 in
/-- Multiplication is sound. -/
theorem RangeConstraint.mul_sound {p : Nat} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.mul rc2).allowsValue (x1 * x2) = true := by
  unfold RangeConstraint.mul
  split
  · -- b.toSingleValue? = some v
    next v hv =>
    have hx2v := toSingleValue_eq rc2 v x2 hv (allowsValue_inRange rc2 x2 h2)
    subst hx2v; rw [mul_comm]
    exact multiple_sound rc1 x2 x1 h1
  · split
    · -- a.toSingleValue? = some v
      next _ v hv =>
      have hx1v := toSingleValue_eq rc1 v x1 hv (allowsValue_inRange rc1 x1 h1)
      subst hx1v
      exact multiple_sound rc2 x1 x2 h2
    · split
      · -- fromRange case
        next _ _ hcond =>
        simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hcond
        obtain ⟨⟨hle1, hle2⟩, hmul⟩ := hcond
        have h1r := allowsValue_inRange rc1 x1 h1
        have h2r := allowsValue_inRange rc2 x2 h2
        unfold inRange at h1r h2r
        rw [if_pos hle1] at h1r; rw [if_pos hle2] at h2r
        obtain ⟨hx1lo, hx1hi⟩ := h1r; obtain ⟨hx2lo, hx2hi⟩ := h2r
        have hmulx : x1.val * x2.val < p := by
          calc x1.val * x2.val ≤ rc1.max.val * rc2.max.val := Nat.mul_le_mul hx1hi hx2hi
          _ < p := hmul
        exact fromRange_allowsValue_of_inRange _ _ _ (by
          unfold inRange fromRange; simp only
          have hval_lo : (rc1.min * rc2.min).val = rc1.min.val * rc2.min.val :=
            ZMod_val_mul rc1.min rc2.min (by
              calc rc1.min.val * rc2.min.val ≤ rc1.max.val * rc2.max.val :=
                    Nat.mul_le_mul (by omega) (by omega)
              _ < p := hmul)
          have hval_hi : (rc1.max * rc2.max).val = rc1.max.val * rc2.max.val :=
            ZMod_val_mul rc1.max rc2.max hmul
          rw [if_pos (by rw [hval_lo, hval_hi]; exact Nat.mul_le_mul (by omega) (by omega)),
              ZMod_val_mul x1 x2 hmulx, hval_lo, hval_hi]
          exact ⟨Nat.mul_le_mul hx1lo hx2lo, Nat.mul_le_mul hx1hi hx2hi⟩)
      · -- unconstrained fallback
        exact unconstrained_allows_any _

/-- Conjunction is sound. -/
theorem RangeConstraint.conjunction_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x : ZMod p)
    (h1 : rc1.allowsValue x = true) (h2 : rc2.allowsValue x = true) :
    (rc1.conjunction rc2).allowsValue x = true := by
  unfold RangeConstraint.conjunction; sorry
