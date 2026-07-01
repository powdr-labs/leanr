import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

-- `p` is the field characteristic; a prime, so `ZMod p` is a field.
variable {p : ℕ} [Fact p.Prime]

/-- An arithmetic expression over variables (identified by `String`) and field constants. -/
inductive Expression (p : ℕ) where
  | const (n : ZMod p)
  | var (x : String)
  | add (e1 e2 : Expression p)
  | mul (e1 e2 : Expression p)

/-- Evaluate an expression under an assignment `env` of variables to field elements. -/
def Expression.eval (e : Expression p) (env : String → ZMod p) : ZMod p :=
  match e with
  | .const n => n
  | .var x => env x
  | .add e1 e2 => e1.eval env + e2.eval env
  | .mul e1 e2 => e1.eval env * e2.eval env

/-- A bus interaction, consisting of a bus ID, a multiplicity, and a payload. -/
structure BusInteraction (α : Type) where
  busId : Nat
  multiplicity : α
  payload : List α

/-- Evaluates a bus interaction under an assignment `env` of variables to a bus interaction message. -/
def BusInteraction.eval (bi : BusInteraction (Expression p)) (env : String → ZMod p) : BusInteraction (ZMod p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.eval env,
    payload := bi.payload.map (fun e => e.eval env) }

/-- A constraint system. -/
structure ConstraintSystem (p : ℕ) where
  algebraicConstraints : List (Expression p)
  busInteractions : List (BusInteraction (Expression p))

/-- `env` satisfies all constraints in `s` -/
def ConstraintSystem.satisfies (s : ConstraintSystem p) (env : String → ZMod p) : Prop :=
  ∀ c ∈ s.algebraicConstraints, c.eval env = 0

/-- The satisfiability of `self` implies the satisfiability of `other` -/
def ConstraintSystem.impliesSatisfiabilityOf (self other : ConstraintSystem p) : Prop :=
  ∀ env, (self.satisfies env → ∃ env', other.satisfies env')

/-- `self` and `other` are equivalent if they imply each other's satisfiability -/
def ConstraintSystem.equivalentTo (self other : ConstraintSystem p) : Prop :=
  self.impliesSatisfiabilityOf other ∧ other.impliesSatisfiabilityOf self

def optimizerMaintainsCircuitEquivalence (optimizer : ConstraintSystem p → ConstraintSystem p) : Prop :=
  ∀ s, (optimizer s).equivalentTo s
