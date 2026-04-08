import Mathlib.Data.ZMod.Basic

structure RangeConstraint (p : ℕ) where
  mask : Nat
  min : ZMod p
  max : ZMod p

/-- If `min == max` and the value is consistent with the mask, return the single value. -/
def RangeConstraint.toSingleValue? {p : ℕ} (rc : RangeConstraint p) : Option (ZMod p) :=
  if rc.min == rc.max && rc.min.val &&& rc.mask == rc.min.val then
    some rc.min
  else
    none

/-- Coerce a single value into a range constraint. -/
instance {p : ℕ} : Coe (ZMod p) (RangeConstraint p) where
  coe v := { mask := v.val, min := v, max := v }

/-- A range constraint representing all values whose bits fit the given mask. -/
def RangeConstraint.fromMask {p : ℕ} (m : Nat) : RangeConstraint p :=
  { mask := m, min := 0, max := (m : ZMod p) }

/-- A range constraint representing values in [lo, hi]. -/
def RangeConstraint.fromRange {p : ℕ} (lo hi : ZMod p) : RangeConstraint p :=
  { mask := hi.val, min := lo, max := hi }

/-- A byte constraint: values in [0, 255]. -/
def RangeConstraint.byte {p : ℕ} : RangeConstraint p :=
  RangeConstraint.fromMask 0xFF

/-- Intersect two range constraints (conjunction). -/
def RangeConstraint.conjunction {p : ℕ}
    (a b : RangeConstraint p) : RangeConstraint p :=
  { mask := a.mask &&& b.mask
    min := if a.min.val ≥ b.min.val then a.min else b.min
    max := if a.max.val ≤ b.max.val then a.max else b.max }
