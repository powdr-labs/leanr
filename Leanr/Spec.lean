import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Basic

set_option autoImplicit false

-- `p` is the field characteristic; a prime, so `ZMod p` is a field.
variable {p : ℕ} [Fact p.Prime]

--------- Expressions ---------

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

--------- Bus Interactions ---------

/-- A bus interaction. Typically, α is
    - an expression (=> symbolic bus interaction), or
    - a field element (=> bus interaction message). -/
structure BusInteraction (α : Type) where
  busId : Nat
  multiplicity : α
  payload : List α

/-- Evaluate a bus interaction under an assignment `env`, turning a symbolic bus
    interaction into a bus interaction message. -/
def BusInteraction.eval (bi : BusInteraction (Expression p)) (env : String → ZMod p) :
    BusInteraction (ZMod p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.eval env,
    payload := bi.payload.map (fun e => e.eval env) }

/-- The bus semantics of the zkVM. -/
structure BusSemantics (p : ℕ) where
  /-- Whether the bus of the given ID changes the state of the VM.
      Stateless bus interactions are typically lookups. -/
  isStateful (busId : Nat) : Bool
  /-- Whether sending this bus interaction message violates a constraint in *another* chip.
      An example of this is sending a message that conflicts with a lookup table entry. -/
  violatesConstraint (busInteractionMessage : BusInteraction (ZMod p)) : Bool
  /-- Whether sending this bus interaction message breaks an invariant on which soundness
      of the system depends.
      For example, a memory bus might have the invariant that all sent values must be in
      a certain range. -/
  breaksInvariant (busInteractionMessage : BusInteraction (ZMod p)) : Bool

/-- A concrete bus interaction message: which bus, and the tuple sent. -/
abbrev BusMessage (p : ℕ) := Nat × List (ZMod p)

/-- Net effect on the stateful buses: each message mapped to its summed multiplicity. -/
abbrev BusEffect (p : ℕ) := BusMessage p →₀ ZMod p

--------- Constraint System ---------

/-- A constraint system representing a single zkVM chip. -/
structure ConstraintSystem (p : ℕ) where
  algebraicConstraints : List (Expression p)
  busInteractions : List (BusInteraction (Expression p))

/-- The side effects of a constraint system under a given environment and bus semantics.
    The side effects are the tuples sent to the *stateful* buses.-/
noncomputable def ConstraintSystem.sideEffects (cs : ConstraintSystem p)
    (busSemantics : BusSemantics p) (env : String → ZMod p) : BusEffect p :=
  (cs.busInteractions.filter (fun bi => busSemantics.isStateful bi.busId)
    |>.map (fun bi =>
      let m := bi.eval env
      Finsupp.single (m.busId, m.payload) m.multiplicity)
  ).sum

/-- Whether a constraint system is satisfied under a given environment and bus semantics. -/
def ConstraintSystem.satisfies (s : ConstraintSystem p) (busSemantics : BusSemantics p)
    (env : String → ZMod p) : Prop :=
  (∀ c ∈ s.algebraicConstraints, c.eval env = 0) ∧
  (∀ bi ∈ s.busInteractions,
    let message := bi.eval env
    message.multiplicity ≠ 0 → busSemantics.violatesConstraint message = false)

/-- Whether a constraint system guarantees that all invariants are maintained under a given bus semantics. -/
def ConstraintSystem.guaranteesInvariants (s : ConstraintSystem p) (busSemantics : BusSemantics p) : Prop :=
  ∀ env, s.satisfies busSemantics env → ∀ bi ∈ s.busInteractions,
    let message := bi.eval env
    message.multiplicity ≠ 0 → busSemantics.breaksInvariant message = false

/-- Whether a constraint system implies another under a given bus semantics.
    Informally, a constraint system `self` implies a system `other` if for every
    satisfying assignment of `self`:
    1. There exists a satisfying assignment of `other`
    2. The side effects of `self` under the given environment and bus semantics
       are equal to the side effects of `other` under the corresponding environment. -/
def ConstraintSystem.implies (self other : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  ∀ env, self.satisfies busSemantics env →
    ∃ env', other.satisfies busSemantics env' ∧
      self.sideEffects busSemantics env = other.sideEffects busSemantics env'

/-- Whether two constraint systems are equivalent under a given bus semantics.
    Two constraint systems are equivalent if each implies the other. -/
def ConstraintSystem.equivalentTo (self other : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  self.implies other busSemantics ∧ other.implies self busSemantics

/-- Whether an optimizer maintains correctness. This means that, for all constraint systems
    and bus semantics:
    1. The optimized constraint system is equivalent to the original, i.e. it has a satisfying
       witness iff the original does.
    2. Assuming the original constraint system guarantees invariants, so does the optimized one. -/
def optimizerMaintainsCorrectness (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p) :
    Prop :=
  ∀ constraintSystem busSemantics,
    ((optimizer constraintSystem busSemantics).equivalentTo constraintSystem busSemantics) ∧
    (constraintSystem.guaranteesInvariants busSemantics →
      (optimizer constraintSystem busSemantics).guaranteesInvariants busSemantics)
