import ApcOptimizer.Implementation.OptimizerPasses.ListSplit

set_option autoImplicit false

/-! # Finite-domain enumeration engine (value-only core)

The variable-free core of the finite-domain enumeration used by the domain-propagation passes: the
symbolic `FiniteDomain` with its `Nat`-loop element fold, and the index-compiled expression /
bus-interaction types `IExpr` / `CBi` (leaves are positions, not `VarId`s). -/

variable {p : ℕ}

/-! ## Symbolic finite domains

A domain is either an explicit element list (roots of a product-of-affine-factors constraint) or a
range `[0, bound)` (a fact-bounded payload slot). `size` is O(1) and the scan uses a `Nat` loop
(`foldElts`); `toList` is proof-specification only and never runs. -/

/-- A finite domain, kept symbolically: an explicit element list, or the range `[0, bound)`. -/
inductive FiniteDomain (p : ℕ) where
  | explicit (values : List (ZMod p))
  | range (bound : Nat)

/-- The element list a finite domain denotes — proof specification only; the range cast is
    materialized only here, never on the runtime path. -/
def FiniteDomain.toList : FiniteDomain p → List (ZMod p)
  | .explicit vs => vs
  | .range b => (List.range b).map (Nat.cast : Nat → ZMod p)

/-- The domain's cardinality — O(1) for a range. -/
@[inline] def FiniteDomain.size : FiniteDomain p → Nat
  | .explicit vs => vs.length
  | .range b => b

/-! ## The `Nat`-loop element fold

`foldElts` folds over a domain's elements with early exit: a list fold for `explicit`, a field-
incrementing loop (`rangeFoldFrom`, building no element list) for `range`. Both equal
`foldlStop f stop d.toList` (`foldElts_eq`), so eager soundness results carry over. -/

/-- Ascending field loop, advancing with a caller-hoisted successor and allocating no element list. -/
def rangeFoldFrom {β : Type} (f : β → ZMod p → β) (stop : β → Bool)
    (next : ZMod p → ZMod p) (current : ZMod p) :
    Nat → β → β
  | 0, acc => acc
  | n + 1, acc =>
    if stop acc then acc else rangeFoldFrom f stop next (next current) n (f acc current)

theorem rangeFoldFrom_eq {β : Type} (f : β → ZMod p → β) (stop : β → Bool)
    (next : ZMod p → ZMod p) (hnext : ∀ v, next v = v + 1)
    (start count : Nat) (current : ZMod p) (hcurrent : current = (start : ZMod p)) (acc : β) :
    rangeFoldFrom f stop next current count acc
      = foldlStop f stop ((List.range' start count).map (Nat.cast : Nat → ZMod p)) acc := by
  induction count generalizing start current acc with
  | zero => rfl
  | succ n ih =>
    rw [rangeFoldFrom, List.range'_succ, List.map_cons, foldlStop]
    by_cases h : stop acc = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, hcurrent]
      apply ih (start + 1) (next (start : ZMod p)) _ (f acc (start : ZMod p))
      rw [hnext]
      simp

/-- Fold over a domain's elements with early exit; equal to `foldlStop f stop d.toList`. -/
def FiniteDomain.foldElts {β : Type} (zero : ZMod p) (next : ZMod p → ZMod p)
    (f : β → ZMod p → β) (stop : β → Bool) :
    FiniteDomain p → β → β
  | .explicit vs, acc => foldlStop f stop vs acc
  | .range b, acc => rangeFoldFrom f stop next zero b acc

theorem FiniteDomain.foldElts_eq {β : Type} (zero : ZMod p) (next : ZMod p → ZMod p)
    (hzero : zero = 0) (hnext : ∀ v, next v = v + 1)
    (f : β → ZMod p → β) (stop : β → Bool)
    (d : FiniteDomain p) (acc : β) :
    d.foldElts zero next f stop acc = foldlStop f stop d.toList acc := by
  cases d with
  | explicit vs => rfl
  | range b =>
    rw [FiniteDomain.foldElts, FiniteDomain.toList,
      rangeFoldFrom_eq f stop next hnext 0 b zero (by simpa using hzero), List.range_eq_range']

/-! ## Interned, index-compiled items

`IExpr` compiles variable leaves to positions (`ix`); `CBi` is a bus interaction over `IExpr`. Both
are variable-free, shared by every consumer of the domain-propagation passes. -/

/-- An expression with variable leaves compiled to positions. -/
inductive IExpr (p : ℕ) where
  | const (n : ZMod p)
  | ix (i : Nat)
  | add (a b : IExpr p)
  | mul (a b : IExpr p)

/-- A bus interaction with compiled multiplicity and payload. -/
structure CBi (p : ℕ) where
  busId : Nat
  mult : IExpr p
  payload : List (IExpr p)
