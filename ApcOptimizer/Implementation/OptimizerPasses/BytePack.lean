import ApcOptimizer.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false

/-! # Canonical byte-check message shapes

On a bitwise-style lookup bus (OpenVM's `BitwiseLookup`) a single value is byte-range-checked by the
self-XOR message `[e, e, 0, 1]` (op = 1: it asserts `e ⊕ e = 0`, forcing both operands — here the
same `e` — to be bytes), and two such checks pack into one pair check `[e₁, e₂, 0, 0]` (op = 0:
range-check both operands as bytes). These two message shapes are used across passes:

* `ByteCheckPack.lean` recognizes single-value byte checks (in any of their equivalent encodings)
  and packs two into one pair check `byteCheck2` (a bus-interaction win);
* `TupleRange.lean` reuses `byteCheck1` when repacking a byte obligation together with an
  exact-width range check.

This module just provides the two canonical constructors and their evaluation lemmas. -/

variable {p : ℕ}

/-- Canonical single-value byte check `[e, e, 0, 1]` (multiplicity `1`). Constants are written with
    `Expression.const` rather than numeral sugar so the file needs no numeral-notation import. -/
def byteCheck1 (busId : Nat) (e : Expression p) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1, payload := [e, e, .const 0, .const 1] }

/-- Canonical packed pair byte check `[e₁, e₂, 0, 0]` (multiplicity `1`). -/
def byteCheck2 (busId : Nat) (e₁ e₂ : Expression p) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := .const 1, payload := [e₁, e₂, .const 0, .const 0] }

theorem byteCheck1_eval (busId : Nat) (e : Expression p) (env : Variable → ZMod p) :
    (byteCheck1 busId e).eval env
      = { busId := busId, multiplicity := 1, payload := [e.eval env, e.eval env, 0, 1] } := rfl

theorem byteCheck2_eval (busId : Nat) (e₁ e₂ : Expression p) (env : Variable → ZMod p) :
    (byteCheck2 busId e₁ e₂).eval env
      = { busId := busId, multiplicity := 1, payload := [e₁.eval env, e₂.eval env, 0, 0] } := rfl
