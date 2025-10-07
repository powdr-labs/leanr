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

def step (st : PState) : PState :=
  { st with i := st.s.next st.i }

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
        let (e, st) ← parseExpr (skipSpaces st)
        let st ← expect ')' st
        pure (e, st)
      else if c.isDigit then
        let (n, st) ← nat st
        pure (Expression.const (n : ZMod p), st)
      else
        -- treat any identifier as a variable
        let (x, st) ← ident st
        pure (Expression.var x, st)
    | none => throw "expected expression, found end of input"

  /-- term := atom ('*' atom)*   (left-assoc) -/
  partial def parseTerm {p : ℕ} (st : PState) : Except String (Expression p × PState) := do
    let (e, st) ← parseAtom (skipSpaces st)
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
    let (e, st) ← parseTerm (skipSpaces st)
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
