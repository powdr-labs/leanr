import Leanr.Spec

/-!
# A small DSL and renderer for spec-level constraint systems

Reusable helpers for *writing* and *pretty-printing* `Expression` / `ConstraintSystem` values
(see `Leanr/Spec.lean`). Not tied to any particular zkVM — used e.g. by the OpenVM snapshot
test in `Leanr/OpenVM/Snapshot.lean`.

`Expression` only has `const/var/add/mul`; subtraction and negation are provided here as sugar
that lowers to multiplication by `-1`.
-/

set_option autoImplicit false

namespace Leanr.Spec.Dsl

variable {p : ℕ}

/-! ## Building expressions -/

instance : Add (Expression p) := ⟨Expression.add⟩
instance : Mul (Expression p) := ⟨Expression.mul⟩
instance : Neg (Expression p) := ⟨fun e => Expression.mul (Expression.const (-1)) e⟩
instance : Sub (Expression p) := ⟨fun a b => a + (-b)⟩

/-- Numeric literals: `(5 : Expression p)` is the constant `5` in the field. -/
instance {n : ℕ} : OfNat (Expression p) n := ⟨Expression.const (OfNat.ofNat n)⟩

/-- A variable, referenced by name. -/
def V (x : String) : Expression p := .var x

/-! ## Rendering -/

private def parenIf : Bool → String → String
  | true, s => s!"({s})"
  | false, s => s

/-- Render an expression, parenthesizing only where precedence requires it
    (`*` binds tighter than `+`). `ctx` is the precedence of the surrounding context:
    `0` top-level, `1` inside `+`, `2`/`3` inside `*`. -/
def renderExprPrec (ctx : Nat) : Expression p → String
  | .const n => toString n.val
  | .var x => x
  | .add a b => parenIf (decide (1 < ctx)) s!"{renderExprPrec 1 a} + {renderExprPrec 2 b}"
  | .mul a b => parenIf (decide (2 < ctx)) s!"{renderExprPrec 2 a} * {renderExprPrec 3 b}"

/-- Render an expression with minimal parenthesization. -/
def renderExpr (e : Expression p) : String := renderExprPrec 0 e

/-- Render a list of bus interactions, emitting a `// Bus N:` header whenever the bus id
    changes (the list is assumed to be grouped by bus, as powdr renders it). -/
def renderBusInteractions (bis : List (BusInteraction (Expression p))) : String :=
  let step : (Option Nat × List String) → BusInteraction (Expression p) → (Option Nat × List String) :=
    fun (prev, acc) bi =>
      let header := if prev = some bi.busId then [] else [s!"// Bus {bi.busId}:"]
      let args := String.intercalate ", " (bi.payload.map renderExpr)
      let line := s!"mult={renderExpr bi.multiplicity}, args=[{args}]"
      (some bi.busId, acc ++ header ++ [line])
  String.intercalate "\n" (bis.foldl step (none, [])).2

/-- Render a whole constraint system in a canonical, powdr-like format. -/
def render (cs : ConstraintSystem p) : String :=
  let cons := String.intercalate "\n" (cs.algebraicConstraints.map (fun e => s!"{renderExpr e} = 0"))
  s!"{renderBusInteractions cs.busInteractions}\n\n// Algebraic constraints:\n{cons}"

/-- Convenience predicate for snapshot `#guard`s: does `cs` render to `expected`? -/
def matchesSnapshot (cs : ConstraintSystem p) (expected : String) : Bool :=
  render cs == expected

end Leanr.Spec.Dsl
