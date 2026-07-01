import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Basic

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

structure BusInteraction (α : Type) where
  busId : Nat
  multiplicity : α
  payload : List α

def BusInteraction.eval (bi : BusInteraction (Expression p)) (env : String → ZMod p) :
    BusInteraction (ZMod p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.eval env,
    payload := bi.payload.map (fun e => e.eval env) }

structure BusSemantics (p : ℕ) where
  isStateful : Nat → Bool
  accepts : BusInteraction (ZMod p) → Bool

structure ConstraintSystem (p : ℕ) where
  algebraicConstraints : List (Expression p)
  busInteractions : List (BusInteraction (Expression p))

noncomputable def ConstraintSystem.sideEffects (cs : ConstraintSystem p)
    (busSemantics : BusSemantics p) (env : String → ZMod p) : (Nat × List (ZMod p)) →₀ ZMod p :=
  (cs.busInteractions.filter (fun bi => busSemantics.isStateful bi.busId) |>.map (fun bi =>
    let m := bi.eval env
    Finsupp.single (m.busId, m.payload) m.multiplicity)).sum

def ConstraintSystem.satisfies (s : ConstraintSystem p) (busSemantics : BusSemantics p)
    (env : String → ZMod p) : Prop :=
  (∀ c ∈ s.algebraicConstraints, c.eval env = 0) ∧
  (∀ bi ∈ s.busInteractions, busSemantics.accepts (bi.eval env))

def ConstraintSystem.implies (self other : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  ∀ env, self.satisfies busSemantics env →
    ∃ env', other.satisfies busSemantics env' ∧
      self.sideEffects busSemantics env = other.sideEffects busSemantics env'

def ConstraintSystem.equivalentTo (self other : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  self.implies other busSemantics ∧ other.implies self busSemantics

def optimizerMaintainsCircuitEquivalence (optimizer : ConstraintSystem p → ConstraintSystem p) :
    Prop :=
  ∀ constraintSystem busSemantics,
    (optimizer constraintSystem).equivalentTo constraintSystem busSemantics
