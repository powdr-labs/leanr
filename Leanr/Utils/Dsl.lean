import Leanr.Spec

/-!
# A small DSL and renderer for spec-level constraint systems

Reusable helpers for *writing* and *pretty-printing* `Expression` / `ConstraintSystem` values
(see `Leanr/Spec.lean`). Not tied to any particular zkVM — used e.g. by the CLI's `render`
command (`Main.lean`).

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

/-! ## Rendering

The renderer simplifies the *display* of an expression (it never rewrites the expression itself):
constant folding of numeric factors, dropping `+ 0` / `* 1` / `* 0`, and showing constants in the
upper half of `[0, p)` as negatives — so `x + (p-1) * y` prints as `x - y` and `(p-1) * 2` as `-2`.
Parentheses are emitted only around sum factors of a product, where precedence requires them.

Variable names carry a trailing `@<id>` witness-column disambiguator (e.g. `opcode_add_flag_0@31`)
that is stripped for display by `displayVar`; within a single circuit the names are already unique
without it. -/

/-- Strip a trailing `@<id>` suffix from a variable name for display, e.g. `opcode_add_flag_0@31`
    renders as `opcode_add_flag_0`. The suffix is a witness-column disambiguator and the names are
    already unique without it within a single circuit, so this loses no information. A name without
    such a suffix (no `@`, or a non-numeric one) is returned unchanged. -/
def displayVar (name : String) : String :=
  match name.splitOn "@" with
  | [base, id] => if id ≠ "" && id.all Char.isDigit then base else name
  | _ => name

/-- Split a field constant into a sign and magnitude: constants in the upper half of `[0, p)`
    are shown as negatives (e.g. `p - 1` renders as `-1`, `p - 2` as `-2`). -/
private def signMag (n : ZMod p) : Bool × ℕ :=
  if 0 < p ∧ p < 2 * n.val then (true, p - n.val) else (false, n.val)

mutual
  /-- Fold a product tree into a single field coefficient and the list of already-rendered
      non-constant factors. Numeric factors are multiplied together (so `(p-1) * 2` collapses to
      the coefficient `-2`); an additive factor is rendered and parenthesized. -/
  private partial def prodFold : Expression p → ZMod p × List String
    | .mul a b => let (ca, fa) := prodFold a; let (cb, fb) := prodFold b; (ca * cb, fa ++ fb)
    | .const n => (n, [])
    | .var x => (1, [displayVar x])
    | e =>                                                 -- an additive factor
      match collectSummands e with
      | [(neg, body)] => (if neg then -1 else 1, [body])   -- single term: splice in, no parens
      | ss => (1, [s!"({joinSummands ss})"])

  /-- Flatten an addition tree into summands, dropping zero terms and pulling each term's sign out
      so it can be joined with `+`/`-`. Returns `(isNegative, body)` per surviving summand. -/
  private partial def collectSummands : Expression p → List (Bool × String)
    | .add a b => collectSummands a ++ collectSummands b
    | e =>
      let (c, facs) := prodFold e
      let (neg, mag) := signMag c
      if mag == 0 then []                                 -- `… * 0` or the constant `0`: drop it
      else match facs with
        | [] => [(neg, toString mag)]                     -- a pure constant
        | _ =>
          let body := String.intercalate " * " facs
          [(neg, if mag == 1 then body else s!"{mag} * {body}")]  -- drop the coefficient `1`

  /-- Join summands with `+`/`-`, using a leading `-` for a negative first term. -/
  private partial def joinSummands : List (Bool × String) → String
    | [] => "0"
    | (s0, b0) :: rest =>
      let head := if s0 then "-" ++ b0 else b0
      rest.foldl (fun acc (s, b) => acc ++ (if s then " - " else " + ") ++ b) head

  /-- Render an expression with the simplifications described above. -/
  partial def renderExpr : Expression p → String
    | e => joinSummands (collectSummands e)
end

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
