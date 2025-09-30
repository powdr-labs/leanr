import Mathlib.Data.ZMod.Basic

-- TODO could use generic Field instead of ZMod p

inductive Expression (p : ℕ) where
  | const (n : ZMod p)
  | var (x : String)
  | add (e1 e2 : Expression p)
  | mul (e1 e2 : Expression p)

def Expression.eval {p : ℕ} (e : Expression p) (env : String → ZMod p): ZMod p :=
  match e with
  | .const n => n
  | .var x => env x
  | .add e1 e2 => e1.eval env + e2.eval env
  | .mul e1 e2 => e1.eval env * e2.eval env

def Expression.substitute {p : ℕ} (e : Expression p) (x : String) (v : ZMod p) : Expression p :=
  match e with
  | .const n => .const n
  | .var y => if x = y then .const v else e
  | .add e1 e2 => .add (e1.substitute x v) (e2.substitute x v)
  | .mul e1 e2 => .mul (e1.substitute x v) (e2.substitute x v)

