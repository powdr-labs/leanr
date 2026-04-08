import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise

structure RangeConstraint (p : ℕ) where
  mask : Nat
  min : ZMod p
  max : ZMod p

/-- Check whether a value is allowed by this range constraint. -/
def RangeConstraint.allowsValue {p : ℕ} (rc : RangeConstraint p) (v : ZMod p) : Bool :=
  let inRange :=
    if rc.min.val ≤ rc.max.val then
      rc.min.val ≤ v.val && v.val ≤ rc.max.val
    else
      rc.min.val ≤ v.val || v.val ≤ rc.max.val
  let inMask := v.val &&& rc.mask == v.val
  inRange && inMask

/-- If `min == max` and the value is consistent with the mask, return the single value. -/
def RangeConstraint.toSingleValue? {p : ℕ} (rc : RangeConstraint p) : Option (ZMod p) :=
  if rc.min == rc.max && rc.min.val &&& rc.mask == rc.min.val then
    some rc.min
  else
    none

/-- Coerce a single value into a range constraint. -/
instance {p : ℕ} : Coe (ZMod p) (RangeConstraint p) where
  coe v := { mask := v.val, min := v, max := v }

/-- Number of bits needed to represent n. -/
private def numBits (n : Nat) : Nat :=
  if n == 0 then 0 else Nat.log2 n + 1

/-- Bit mask with the lowest `bits` bits set. -/
private def maskFromBits (bits : Nat) : Nat :=
  if bits == 0 then 0 else 2 ^ bits - 1

-- TODO: `unconstrained` recomputes the mask on every call via Nat.log.
-- If this becomes a performance bottleneck, precompute the mask as a constant
-- for specific field sizes (e.g. `def babyBearMask : Nat := 0x7FFFFFFF`).

/-- The unconstrained range constraint (any value). -/
def RangeConstraint.unconstrained {p : ℕ} : RangeConstraint p :=
  { mask := 2 ^ (Nat.log 2 p + 1) - 1, min := 0, max := (p - 1 : Nat) }

instance {p : ℕ} : ToString (RangeConstraint p) where
  toString rc :=
    if rc.min == rc.max then s!"{rc.min.val}"
    else s!"[{rc.min.val}, {rc.max.val}] & 0x{Nat.toDigits 16 rc.mask |>.asString}"

/-- A range constraint representing all values whose bits fit the given mask. -/
def RangeConstraint.fromMask {p : ℕ} (m : Nat) : RangeConstraint p :=
  { mask := m, min := 0, max := (Nat.min m (p - 1) : Nat) }

/-- Constraint that allows no higher bits set than the one given (counting from zero). -/
def RangeConstraint.fromMaxBit {p : ℕ} (maxBit : Nat) : RangeConstraint p :=
  RangeConstraint.fromMask (maskFromBits (maxBit + 1))

/-- A range constraint representing values in [lo, hi]. Wrapping ranges are supported. -/
def RangeConstraint.fromRange {p : ℕ} (lo hi : ZMod p) : RangeConstraint p :=
  let mask := if lo.val ≤ hi.val then
    maskFromBits (numBits hi.val)
  else
    RangeConstraint.unconstrained (p := p) |>.mask
  { mask := mask, min := lo, max := hi }

/-- A byte constraint: values in [0, 255]. -/
def RangeConstraint.byte {p : ℕ} : RangeConstraint p :=
  RangeConstraint.fromMask 0xFF

/-- The number of elements in the range [min, max] (inclusive, wrapping). -/
def RangeConstraint.rangeWidth {p : ℕ} (rc : RangeConstraint p) : Nat :=
  if rc.max.val + 1 == rc.min.val then p
  else (rc.max - rc.min + 1).val

/-- Intersect two range constraints (conjunction).
    Follows the Rust implementation: intersects masks, ranges, and cross-refines. -/
def RangeConstraint.conjunction {p : ℕ}
    (a b : RangeConstraint p) : RangeConstraint p :=
  let mask := a.mask &&& b.mask
  -- Interval intersection: shift both intervals to try to make them non-wrapping
  let (min, max) : ZMod p × ZMod p := Id.run do
    -- Try shifting by a.min, then b.min
    for shift in [a.min, b.min] do
      let aLo := (a.min - shift).val
      let aHi := (a.max - shift).val
      let bLo := (b.min - shift).val
      let bHi := (b.max - shift).val
      if aLo ≤ aHi && bLo ≤ bHi then
        let lo := Nat.max aLo bLo
        let hi := Nat.min aHi bHi
        if lo ≤ hi then
          let rMin : ZMod p := (lo + shift.val : Nat)
          let rMax : ZMod p := (hi + shift.val : Nat)
          return (rMin, rMax)
        else
          return ((0 : ZMod p), (0 : ZMod p))
    -- Could not make both non-wrapping: return the smaller interval
    if a.rangeWidth ≤ b.rangeWidth then (a.min, a.max) else (b.min, b.max)
  -- Cross-refine mask from range
  let mask := if min.val ≤ max.val then
    mask &&& maskFromBits (numBits max.val)
  else mask
  -- Cross-refine range from mask
  let (min, max) : ZMod p × ZMod p :=
    if mask < p then
      if min.val ≤ max.val then
        ((Nat.min mask min.val : Nat), (Nat.min mask max.val : Nat))
      else if min.val > mask then
        ((0 : ZMod p), (Nat.min mask max.val : Nat))
      else
        (min, max)
    else (min, max)
  { mask := mask, min := min, max := max }

/-- Range constraint of `-a` (additive inverse). -/
def RangeConstraint.neg {p : ℕ}
    (a : RangeConstraint p) : RangeConstraint p :=
  RangeConstraint.fromRange (-a.max) (-a.min)

/-- Compute [min, max] of factor * [lo, hi], or the full range if it overflows. -/
private def rangeMultiple {p : ℕ} (lo hi factor : ZMod p) : ZMod p × ZMod p :=
  let width := if hi.val + 1 == lo.val then p
               else (hi - lo + 1).val
  if width * factor.val ≤ p then
    (lo * factor, hi * factor)
  else
    ((1 : ZMod p), (0 : ZMod p))  -- full range

/-- The constraint of an integer multiple of an expression.
    If `r` is valid for `e`, then `r.multiple(factor)` is valid for `factor * e`. -/
def RangeConstraint.multiple {p : ℕ}
    (rc : RangeConstraint p) (factor : ZMod p) : RangeConstraint p :=
  -- Try to compute mask via bit shift if factor is a power of 2
  let maskOpt : Option Nat := do
    let fv := factor.val
    if fv == 0 then return 0
    -- Check if fv is a power of 2
    guard (fv &&& (fv - 1) == 0)
    let exponent := Nat.log2 fv
    let shifted := rc.mask <<< exponent
    guard (shifted < p)
    return shifted
  let isLowerHalf := factor.val ≤ p / 2
  let (min, max) := if isLowerHalf then
    rangeMultiple rc.min rc.max factor
  else
    rangeMultiple (-rc.max) (-rc.min) (-factor)
  let mask := maskOpt.getD (RangeConstraint.fromRange min max |>.mask)
  { mask := mask, min := min, max := max }

/-- Range constraint of `a + b` (combine_sum from Rust). -/
def RangeConstraint.add {p : ℕ}
    (a b : RangeConstraint p) : RangeConstraint p :=
  let unc := RangeConstraint.unconstrained (p := p)
  -- Mask: if sum of masks overflows, use unconstrained mask
  let maskSum := if a.mask + b.mask ≥ p then
    unc.mask
  else
    (a.mask + b.mask) ||| a.mask ||| b.mask
  -- Range: if sum of range widths overflows, use unconstrained range
  let (min, max) := if a.rangeWidth + b.rangeWidth ≤ unc.rangeWidth then
    (a.min + b.min, a.max + b.max)
  else
    (unc.min, unc.max)
  -- Cross-refine mask from range
  let mask := if min.val ≤ max.val then
    maskSum &&& maskFromBits (numBits max.val)
  else maskSum
  { mask := mask, min := min, max := max }

/-- Range constraint of `a - b` (i.e. `a + (-b)`). -/
def RangeConstraint.sub {p : ℕ}
    (a b : RangeConstraint p) : RangeConstraint p :=
  a.add b.neg

/-- Range constraint of `a * b` (combine_product from Rust). -/
def RangeConstraint.mul {p : ℕ}
    (a b : RangeConstraint p) : RangeConstraint p :=
  if let some v := b.toSingleValue? then
    a.multiple v
  else if let some v := a.toSingleValue? then
    b.multiple v
  else if a.min.val ≤ a.max.val && b.min.val ≤ b.max.val
       && a.max.val * b.max.val < p then
    RangeConstraint.fromRange (a.min * b.min) (a.max * b.max)
  else
    RangeConstraint.unconstrained

instance {p : ℕ} : Add (RangeConstraint p) where add := RangeConstraint.add
instance {p : ℕ} : Sub (RangeConstraint p) where sub := RangeConstraint.sub
instance {p : ℕ} : Mul (RangeConstraint p) where mul := RangeConstraint.mul
instance {p : ℕ} : Neg (RangeConstraint p) where neg := RangeConstraint.neg

private theorem nat_and_two_pow_sub_one (n k : Nat) (h : n < 2^k) : n &&& (2^k - 1) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < k
  · simp [hi]
  · have := Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega : k ≤ i)))
    simp [show ¬(i < k) from hi, this]

/-- `unconstrained` allows any value. -/
theorem RangeConstraint.unconstrained_allows_any {p : ℕ} [NeZero p] (v : ZMod p) :
    (RangeConstraint.unconstrained (p := p)).allowsValue v = true := by
  have hp : 0 < p := NeZero.pos p
  have hv : v.val < p := ZMod.val_lt v
  have hmask : v.val &&& (2 ^ (Nat.log 2 p + 1) - 1) = v.val := by
    apply nat_and_two_pow_sub_one
    exact lt_of_lt_of_le hv (Nat.lt_pow_succ_log_self (by omega) p).le
  unfold unconstrained allowsValue
  simp only [ZMod.val_zero, Nat.zero_le, ite_true]
  have hmax : ((p - 1 : Nat) : ZMod p).val = p - 1 := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
  rw [hmax, hmask, beq_self_eq_true]
  simp only [Bool.and_true, decide_true, Bool.true_and, decide_eq_true_eq]
  omega

-- ===== Helper lemmas for soundness proofs =====

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

/-- If n ≤ max and max > 0, then n fits in maskFromBits (numBits max). -/
private theorem fits_maskFromBits (n max : Nat) (h : n ≤ max) (hmax : 0 < max) :
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
private theorem nat_and_conj (n m1 m2 : Nat) (h1 : n &&& m1 = n) (h2 : n &&& m2 = n) :
    n &&& (m1 &&& m2) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_and]
  have h1i := congr_arg (·.testBit i) h1
  have h2i := congr_arg (·.testBit i) h2
  simp [Nat.testBit_and] at h1i h2i
  cases hn : n.testBit i <;> simp_all

/-- n passes a weaker mask (mask OR extra bits). -/
private theorem nat_and_or_weaken (n m1 m2 : Nat) (h : n &&& m1 = n) :
    n &&& (m1 ||| m2) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_or]
  have hi := congr_arg (·.testBit i) h
  simp [Nat.testBit_and] at hi
  cases hn : n.testBit i <;> simp_all

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
  · -- Mask is unconstrained, so it allows any value < p
    show v.val &&& (unconstrained (p := p)).mask = v.val
    unfold unconstrained; simp only
    apply nat_and_two_pow_sub_one
    exact lt_of_lt_of_le (ZMod.val_lt v) (Nat.lt_pow_succ_log_self (by omega) p).le

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
  unfold neg; sorry

/-- Addition is sound: if rc1 allows x1 and rc2 allows x2,
    then (rc1.add rc2) allows (x1 + x2). -/
theorem RangeConstraint.add_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.add rc2).allowsValue (x1 + x2) = true := by
  -- Overflow cases return unconstrained (trivially sound).
  -- Non-overflow: range widths don't exceed p, so [min1+min2, max1+max2] is sound;
  -- mask (m1+m2) ||| m1 ||| m2 covers all bits of (x1+x2) since val(x1+x2) ≤ val(x1)+val(x2).
  unfold add; sorry

/-- Subtraction is sound: follows from add_sound and neg_sound. -/
theorem RangeConstraint.sub_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.sub rc2).allowsValue (x1 - x2) = true := by
  unfold sub
  show (rc1.add rc2.neg).allowsValue (x1 - x2) = true
  have hneg : rc2.neg.allowsValue (-x2) = true := neg_sound rc2 x2 h2
  rw [show x1 - x2 = x1 + (-x2) from sub_eq_add_neg x1 x2]
  exact add_sound rc1 rc2.neg x1 (-x2) h1 hneg

/-- Scalar multiplication is sound. -/
theorem RangeConstraint.multiple_sound {p : ℕ} [NeZero p]
    (rc : RangeConstraint p) (f x : ZMod p)
    (h : rc.allowsValue x = true) :
    (rc.multiple f).allowsValue (f * x) = true := by
  unfold multiple; sorry

/-- Multiplication is sound. -/
theorem RangeConstraint.mul_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x1 x2 : ZMod p)
    (h1 : rc1.allowsValue x1 = true) (h2 : rc2.allowsValue x2 = true) :
    (rc1.mul rc2).allowsValue (x1 * x2) = true := by
  unfold mul; sorry

/-- Conjunction is sound. -/
theorem RangeConstraint.conjunction_sound {p : ℕ} [NeZero p]
    (rc1 rc2 : RangeConstraint p) (x : ZMod p)
    (h1 : rc1.allowsValue x = true) (h2 : rc2.allowsValue x = true) :
    (rc1.conjunction rc2).allowsValue x = true := by
  unfold conjunction; sorry
