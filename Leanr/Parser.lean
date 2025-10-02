import Init.Data.ToString

import Leanr.Expression

declare_syntax_cat expr

syntax:65 expr:65  "+" expr:66 : expr
syntax:70 expr:70 "*" expr:71 : expr
syntax "(" expr ")" : expr
syntax num : expr
syntax ident : expr

syntax "expr" "{" expr "}" : term

macro_rules
  | `(expr {$x + $y}) => `(Expression.add (expr {$x}) (expr {$y}))
  | `(expr {$x * $y}) => `(Expression.mul (expr {$x}) (expr {$y}))
  | `(expr {($x)}) => `(expr {$x})
  | `(expr {$n:num}) => `(.const (OfNat.ofNat $n))
  | `(expr {$x:ident}) => `(.var $(Lean.quote x.getId.toString))

/-- info: ((2 * x) + 0) -/
#guard_msgs in
#eval (expr { 2 * x + 0 } : Expression 9)

/-- info: (((2 * x) + (3 * y)) + 4) -/
#guard_msgs in
#eval ((expr { 2 * x + 3 * y + 4 }) : Expression 9)

/-- info: (((2 * x) + (3 * y)) + 0) -/
#guard_msgs in
#eval ((expr { 2 * x + 3 * y + 4 }) : Expression 4)
