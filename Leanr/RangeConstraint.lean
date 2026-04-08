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
