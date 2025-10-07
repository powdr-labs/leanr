import Leanr.Solver
import Leanr.Expression

import Init.Data.ToString.Basic


/--
Parse strings of the form:
// Bus 0 (EXECUTION_BRIDGE):
mult=is_valid * -1, args=[0, from_state__timestamp_0]
mult=is_valid * 1, args=[4, from_state__timestamp_0 + 3]

// Bus 1 (MEMORY):
mult=is_valid * -1, args=[1, 0, 0, 0, 0, 0, reads_aux__0__base__prev_timestamp_0]
mult=is_valid * 1, args=[1, 0, 0, 0, 0, 0, from_state__timestamp_0]
mult=is_valid * -1, args=[1, 8, writes_aux__prev_data__0_0, writes_aux__prev_data__1_0, writes_aux__prev_data__2_0, writes_aux__prev_data__3_0, writes_aux__base__prev_timestamp_0]
mult=is_valid * 1, args=[1, 8, 0, 0, 0, 0, from_state__timestamp_0 + 2]

// Bus 3 (VARIABLE_RANGE_CHECKER):
mult=is_valid * 1, args=[reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0, 17]
mult=is_valid * 1, args=[15360 * reads_aux__0__base__prev_timestamp_0 + 15360 * reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0 + 15360 - 15360 * from_state__timestamp_0, 12]
mult=is_valid * 1, args=[writes_aux__base__timestamp_lt_aux__lower_decomp__0_0, 17]
mult=is_valid * 1, args=[15360 * writes_aux__base__prev_timestamp_0 + 15360 * writes_aux__base__timestamp_lt_aux__lower_decomp__0_0 - (15360 * from_state__timestamp_0 + 15360), 12]

// Algebraic constraints:
is_valid * (is_valid - 1) = 0
-/

structure PState where
  s : String
  i : String.Pos := 0

namespace P

def eof (st : PState) : Bool := st.i ≥ st.s.endPos

def peek (st : PState) : Option Char := st.s.get? st.i

def step (st : PState) : PState := { st with i := st.s.next st.i }

partial def skipSpaces (st : PState) : PState :=
  match peek st with
  | some c =>
    if c.isWhitespace then skipSpaces (step st) else st
  | none => st

def expect (c : Char) (st : PState) : Except String PState := do
  let st := skipSpaces st
  match peek st with
  | some d =>
    if d = c then
      return step st
    else
      throw s!"expected '{c}', found '{d}' at {st.i.byteIdx}"
  | none => throw s!"expected '{c}', found end of input"

partial def expectString (expected : String) (st : PState) : Except String PState := do
  let st := skipSpaces st
  let rec loop (i : Nat) (st : PState) : Except String PState := do
    if i = expected.length then
      return st
    else
      let some c := expected.get? ⟨i⟩
        | throw "internal error in expectString"
      match peek st with
      | some d =>
        if d = c then
          loop (i + 1) (step st)
        else
          throw s!"expected '{expected}', found '{d}' at {st.i.byteIdx}"
      | none => throw s!"expected '{expected}', found end of input"
  loop 0 st

/-- Parse one or more decimal digits, return the natural number. -/
partial def nat (st : PState) : Except String (Nat × PState) := do
  let st := skipSpaces st
  let some c := peek st
    | throw s!"expected digit, found end of input"
  if !c.isDigit then
    throw s!"expected digit, found '{c}' at {st.i.byteIdx}"
  let rec loop (acc : Nat) (st : PState) : (Nat × PState) :=
    match peek st with
    | some d =>
      if d.isDigit then
        loop (acc * 10 + (d.toNat - '0'.toNat)) (step st)
      else
        (acc, st)
    | none => (acc, st)
  pure (loop (c.toNat - '0'.toNat) (step st))

/-- identifier: letter or '_' followed by letters/digits/'_'/'\'' -/
partial def ident (st : PState) : Except String (String × PState) := do
  let st := skipSpaces st
  let some c := peek st
    | throw s!"expected identifier, found end of input"
  let isStart := c.isAlpha || c = '_'
  if !isStart then
    throw s!"expected identifier, found '{c}' at {st.i.byteIdx}"
  let rec loop (buf : String) (st : PState) : (String × PState) :=
    match peek st with
    | some d =>
      if d.isAlphanum || d = '_' || d = '\'' then
        loop (buf.push d) (step st)
      else
        (buf, st)
    | none => (buf, st)
  pure (loop (String.singleton c) (step st))

end P

open P

mutual
  /-- atom := number | ident | '(' expr ')' -/
  partial def parseAtom {p : ℕ} (st : PState) : Except String (Expression p × PState) := do
    let st := skipSpaces st
    match peek st with
    | some c =>
      if c = '(' then
        let st ← expect '(' st
        let (e, st) ← parseExpr st
        let st ← expect ')' st
        pure (e, st)
      else if c.isDigit then
        let (n, st) ← nat st
        pure (Expression.const (n : ZMod p), st)
      else if c = '-' then
        let st ← expect '-' st
        let (e, st) ← parseExpr st
        pure (Expression.mul (Expression.const (-1)) e, st)
      else
        -- treat any identifier as a variable
        let (x, st) ← ident st
        pure (Expression.var x, st)
    | none => throw "expected expression, found end of input"

  /-- term := atom ('*' atom)*   (left-assoc) -/
  partial def parseTerm {p : ℕ} (st : PState) : Except String (Expression p × PState) := do
    let (e, st) ← parseAtom st
    let rec loop (e : Expression p) (st : PState) :
        Except String (Expression p × PState) := do
      let st1 := skipSpaces st
      match peek st1 with
      | some '*' =>
        let st2 := step st1
        let (e2, st3) ← parseAtom st2
        loop (Expression.mul e e2) st3
      | _ => pure (e, st1)
    loop e st

  /-- expr := term ('+' term)*   (left-assoc) -/
  partial def parseExpr {p : ℕ} (st : PState) : Except String (Expression p × PState) := do
    let (e, st) ← parseTerm st
    let rec parseLoop (e : Expression p) (st : PState) :
        Except String (Expression p × PState) := do
      let st1 := skipSpaces st
      match peek st1 with
      | some '+' =>
        let st2 := step st1
        let (e2, st3) ← parseTerm st2
        parseLoop (Expression.add e e2) st3
      | some '-' =>
        let st2 := step st1
        let (e2, st3) ← parseTerm st2
        parseLoop (Expression.add e (Expression.mul (Expression.const (-1)) e2)) st3
      | _ => pure (e, st1)
    parseLoop e st
end

/-- Parse a comma-separated list of expressions. No trailing comma allowed. -/
partial def parseExpressionList {p : ℕ} (st : PState) : Except String (List (Expression p) × PState) := do
  let rec loop (acc : List (Expression p)) (st : PState)
      : Except String (List (Expression p) × PState) := do
    let st := skipSpaces st
    if eof st then
      pure (acc.reverse, st)
    else
      let (e, st) ← parseExpr st
      let st := skipSpaces st
      match peek st with
      | some ',' =>
          -- consume the comma and continue
          loop (e :: acc) (step st)
      | _ =>
          -- end of input, finish
          pure (List.reverse (e :: acc), st)
  loop [] st

def parseAlgebraicConstraint {p : ℕ} (s : String) : Except String (AlgebraicConstraint p) := do
  let (lhs, st) ← parseExpr { s }
  let st ← expect '=' st
  let (rhs, st) ← parseExpr st
  let st := skipSpaces st
  if eof st then
    pure (AlgebraicConstraint.assertZero (lhs + (Expression.mul (Expression.const (-1)) rhs)))
  else
    throw s!"unexpected trailing input at {st.i.byteIdx}"

/-- Trim ASCII whitespace both ends. -/
def trim (s : String) : String :=
  s.dropWhile Char.isWhitespace |>.dropRightWhile Char.isWhitespace

/-- Parse a `mult=..., args=[...]` line. -/
def parseBusInteraction {p : ℕ}
    (busId : Expression p)
    (line : String) : Except String (BusInteraction (Expression p)) := do
  -- Expect `mult=<expr>, args=[...]`
  let line := trim line
  if !line.startsWith "mult=" then
    throw "expected line starting with `mult=`"
  let st : PState := { s := line.drop 5 }
  let (multiplicity, st) ← parseExpr (p := p) st
  let st ← expect ',' st
  let st ← expectString "args" st
  let st ← expect '=' st
  let st ← expect '[' st
  let (payload, st) ← parseExpressionList (p := p) st
  let st ← expect ']' st
  let st := skipSpaces st
  if !eof st then
    throw s!"unexpected trailing input at {st.i.byteIdx}"
  pure { busId := busId, multiplicity := multiplicity, payload := payload }


/-- Main entry: parse a whole document into (bus interactions, loose expressions). -/
def parseSystem {p : ℕ}
  (s : String) : Except String (List (BusInteraction (Expression p)) × List (AlgebraicConstraint p)) := do
  let lines := s.splitOn "\n"
  let mut currentBusId : Option (Expression p) := none
  let mut busInteractions : List (BusInteraction (Expression p)) := []
  let mut algebraicConstraints : List (AlgebraicConstraint p) := []
  for rawLine in lines do
    let line := trim rawLine
    if line.isEmpty then
      continue
    else if line.startsWith "//" then
      let rest := trim (line.drop 2)
      if rest.startsWith "Bus" then
        -- try to parse bus ID
        let rest := trim (rest.drop 3)
        let idDigits := rest.takeWhile (fun c => c.isDigit)
        match idDigits.toNat? with
        | some n => currentBusId := some (Expression.const (n : ZMod p))
        | none => currentBusId := none
    else
      if line.startsWith "mult=" then
        match currentBusId with
        | none => throw "found `mult=` line outside of a `// Bus <id>` section"
        | some busId =>
          let busInteraction ← parseBusInteraction (p := p) busId line
          busInteractions := busInteraction :: busInteractions
      else
        -- an algebraic constraint
        let c ← parseAlgebraicConstraint (p := p) line
        algebraicConstraints := c :: algebraicConstraints
  pure (busInteractions.reverse, algebraicConstraints.reverse)

/-- Public entry point: parse whole string (must consume all non-space input). -/
def parse {p : ℕ} (s : String) : Except String (Expression p) := do
  let (e, st) ← parseExpr { s }
  let st := skipSpaces st
  if eof st then
    pure e
  else
    throw s!"unexpected trailing input at {st.i.byteIdx}"


/-- info: "(((x * 3) + (y * (z + 2))) + 5)" -/
#guard_msgs in
#eval
  match (parse (p := 101) "x*3 + y* (z + 2) + 5") with
  | .ok e    => ToString.toString e
  | .error e => "error: " ++ e

/-- info: "((((a * b) * c) + d) + (5 * (e + f)))" -/
#guard_msgs in
#eval
  match (parse (p := 7) "a*b*c + d + 12*(e+f)") with
  | .ok e    => ToString.toString e
  | .error e => "error: " ++ e

/-- info: "((a + (6 * b)) + (6 * (c * 5)))" -/
#guard_msgs in
#eval
  match (parse (p := 7) "a - b - c * 5") with
  | .ok e    => ToString.toString e
  | .error e => "error: " ++ e

/-- info: Assignments:

Constraints:
((is_valid * (is_valid + (1966078 * 1))) + (1966078 * 0))
Bus Interactions:
BusInteraction { bus_id: 0, multiplicity: (is_valid * (1966078 * 1)), payload: [0, from_state__timestamp_0] }
BusInteraction { bus_id: 0, multiplicity: (is_valid * 1), payload: [4, (from_state__timestamp_0 + 3)] }
BusInteraction { bus_id: 1, multiplicity: (is_valid * (1966078 * 1)), payload: [1, 0, 0, 0, 0, 0, reads_aux__0__base__prev_timestamp_0] }
BusInteraction { bus_id: 1, multiplicity: (is_valid * 1), payload: [1, 0, 0, 0, 0, 0, from_state__timestamp_0] }
BusInteraction { bus_id: 1, multiplicity: (is_valid * (1966078 * 1)), payload: [1, 8, writes_aux__prev_data__0_0, writes_aux__prev_data__1_0, writes_aux__prev_data__2_0, writes_aux__prev_data__3_0, writes_aux__base__prev_timestamp_0] }
BusInteraction { bus_id: 1, multiplicity: (is_valid * 1), payload: [1, 8, 0, 0, 0, 0, (from_state__timestamp_0 + 2)] }
BusInteraction { bus_id: 3, multiplicity: (is_valid * 1), payload: [reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0, 17] }
BusInteraction { bus_id: 3, multiplicity: (is_valid * 1), payload: [((((15360 * reads_aux__0__base__prev_timestamp_0) + (15360 * reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0)) + 15360) + (1966078 * (15360 * from_state__timestamp_0))), 12] }
BusInteraction { bus_id: 3, multiplicity: (is_valid * 1), payload: [writes_aux__base__timestamp_lt_aux__lower_decomp__0_0, 17] }
BusInteraction { bus_id: 3, multiplicity: (is_valid * 1), payload: [(((15360 * writes_aux__base__prev_timestamp_0) + (15360 * writes_aux__base__timestamp_lt_aux__lower_decomp__0_0)) + (1966078 * ((15360 * from_state__timestamp_0) + 15360))), 12] }-/
#guard_msgs in
#eval
  let input :=
    "// Bus 0 (EXECUTION_BRIDGE):
    mult=is_valid * -1, args=[0, from_state__timestamp_0]
    mult=is_valid * 1, args=[4, from_state__timestamp_0 + 3]
    // Bus 1 (MEMORY):
    mult=is_valid * -1, args=[1, 0, 0, 0, 0, 0, reads_aux__0__base__prev_timestamp_0]
    mult=is_valid * 1, args=[1, 0, 0, 0, 0, 0, from_state__timestamp_0]
    mult=is_valid * -1, args=[1, 8, writes_aux__prev_data__0_0, writes_aux__prev_data__1_0, writes_aux__prev_data__2_0, writes_aux__prev_data__3_0, writes_aux__base__prev_timestamp_0]
    mult=is_valid * 1, args=[1, 8, 0, 0, 0, 0, from_state__timestamp_0 + 2]
    // Bus 3 (VARIABLE_RANGE_CHECKER):
    mult=is_valid * 1, args=[reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0, 17]
    mult=is_valid * 1, args=[15360 * reads_aux__0__base__prev_timestamp_0 + 15360 * reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0 + 15360 - 15360 * from_state__timestamp_0, 12]
    mult=is_valid * 1, args=[writes_aux__base__timestamp_lt_aux__lower_decomp__0_0, 17]
    mult=is_valid * 1, args=[15360 * writes_aux__base__prev_timestamp_0 + 15360 * writes_aux__base__timestamp_lt_aux__lower_decomp__0_0 - (15360 * from_state__timestamp_0 + 15360), 12]
    // Algebraic constraints:
    is_valid * (is_valid - 1) = 0"
  match parseSystem (p := 0x1dffff) input with
  | .ok (busInteractions, constraints) =>
    let system : System 0x1dffff := {
      constraints := constraints,
      bus_interactions := busInteractions,
      assignments := []
    }
    system
  | .error _ => System.fromConstraints []
