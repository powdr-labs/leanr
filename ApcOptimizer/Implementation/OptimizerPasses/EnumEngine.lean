import ApcOptimizer.Implementation.OptimizerPasses.ListSplit

set_option autoImplicit false

/-! # Finite-domain enumeration engine (value-only core)

The value-only, variable-free core of the finite-domain enumeration used by the domain-propagation
passes: the symbolic `FiniteDomain` and its `Nat`-loop element fold, and the interned, index-compiled
expression / bus-interaction types `IExpr` / `CBi`. None of these mentions a `VarId` — their leaves
are positions (`IExpr.ix`) and their domains carry only `ZMod p` values — so the same compiled term
and enumerated element stream serve every consumer, differing only in the key type of the point it
evaluates against. The generic early-exit list fold `foldlStop` it builds on lives in
`ListSplit.lean`.

Collected here:

* the symbolic finite domain `FiniteDomain` with `toList` / `size` / `size_eq`, and its `Nat`-loop
  element fold `rangeFoldFrom` / `FiniteDomain.foldElts` (with `rangeFoldFrom_eq` / `foldElts_eq`
  proving them equal to the eager `foldlStop … toList`);
* the index-compiled expression type `IExpr` and bus-interaction type `CBi`. -/

variable {p : ℕ}

/-! ## Symbolic finite domains

A variable's finite domain is either an **explicit** list of field elements (the roots of a
product-of-affine-factors constraint) or the **range** `[0, bound)` (a fact-bounded raw payload
slot), which keeps only its `Nat` bound. Its `size` is read in O(1), and the box scan enumerates it
with a `Nat` loop (`FiniteDomain.foldElts`) that never builds an element list — a range recasts one
`Nat` per point it actually visits, so an early-aborting scan touches only a handful.
`toList` — `(List.range bound).map Nat.cast`, the `2^16`-element list a 16-bit limb would have
materialized eagerly — is the **specification only**: it appears in the equivalence/soundness proofs
(`foldElts_eq` and the enumeration bridge) and never on the runtime path. Every table/box decision
that would otherwise use `List.length` on the eagerly-materialized list instead reads `size`;
`size_eq` proves them equal. -/

/-- A finite domain, kept symbolically: an explicit element list, or the range `[0, bound)`. -/
inductive FiniteDomain (p : ℕ) where
  | explicit (values : List (ZMod p))
  | range (bound : Nat)

/-- The element list a finite domain denotes — the **proof specification** for `size` and
    `foldElts` (the range cast is materialized only here, in proofs). The runtime enumeration never
    calls this; it streams the domain with the `Nat`-loop `FiniteDomain.foldElts`. -/
def FiniteDomain.toList : FiniteDomain p → List (ZMod p)
  | .explicit vs => vs
  | .range b => (List.range b).map (Nat.cast : Nat → ZMod p)

/-- The domain's cardinality — O(1) for a range (no materialization). On the runtime path. -/
@[inline] def FiniteDomain.size : FiniteDomain p → Nat
  | .explicit vs => vs.length
  | .range b => b

/-! ## The `Nat`-loop element fold

`rangeFoldFrom` streams a `range` domain by a `Nat` loop (no element list is ever built) and stops the
moment `stop` holds, so an aborted scan over a `2^16` range costs a handful of iterations, not 65536.
`FiniteDomain.foldElts` is a plain list fold for `explicit` and this `Nat` loop for `range`; both are
proved equal to the eager `foldlStop f stop d.toList` (`foldElts_eq`), so eager soundness results
carry over verbatim. -/

/-- Ascending `Nat` loop `start, start+1, …, start+count-1`, casting each into `ZMod p` and folding
    with an early exit — the `range` case of a domain fold, allocating no element list. -/
def rangeFoldFrom {β : Type} (f : β → ZMod p → β) (stop : β → Bool) (start : Nat) :
    Nat → β → β
  | 0, acc => acc
  | n + 1, acc =>
    if stop acc then acc else rangeFoldFrom f stop (start + 1) n (f acc ((start : ℕ) : ZMod p))

theorem rangeFoldFrom_eq {β : Type} (f : β → ZMod p → β) (stop : β → Bool)
    (start count : Nat) (acc : β) :
    rangeFoldFrom f stop start count acc
      = foldlStop f stop ((List.range' start count).map (Nat.cast : Nat → ZMod p)) acc := by
  induction count generalizing start acc with
  | zero => rfl
  | succ n ih =>
    rw [rangeFoldFrom, List.range'_succ, List.map_cons, foldlStop]
    by_cases h : stop acc = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, ih]

/-- Fold a function over a domain's elements with an early exit: a plain list fold for `explicit`,
    a `Nat` loop for `range` (no `toList`). Equal to `foldlStop f stop d.toList` (`foldElts_eq`). -/
def FiniteDomain.foldElts {β : Type} (f : β → ZMod p → β) (stop : β → Bool) :
    FiniteDomain p → β → β
  | .explicit vs, acc => foldlStop f stop vs acc
  | .range b, acc => rangeFoldFrom f stop 0 b acc

theorem FiniteDomain.foldElts_eq {β : Type} (f : β → ZMod p → β) (stop : β → Bool)
    (d : FiniteDomain p) (acc : β) : d.foldElts f stop acc = foldlStop f stop d.toList acc := by
  cases d with
  | explicit vs => rfl
  | range b =>
    rw [FiniteDomain.foldElts, FiniteDomain.toList, rangeFoldFrom_eq, List.range_eq_range']

/-! ## Interned, index-compiled items

`IExpr` is an expression with variable leaves compiled to positions (`ix`); `CBi` is a bus
interaction with compiled multiplicity and payload. Both are variable-free — the *same* compiled term
is produced whatever the source key type — so they are shared by every consumer of the
domain-propagation passes. -/

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
