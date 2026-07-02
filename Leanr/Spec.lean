import Mathlib.Data.ZMod.Basic

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

/-- Shape declaration of a *last-write-wins memory bus* (offline memory checking, Blum et al.):
    each access receives the previous cell content (multiplicity `-1`) and sends the new one
    (multiplicity `1`). Payload slots listed in `addressFields` form the access key; `tsField`
    holds the timestamp (a send carries its write time, a receive the time of the write it
    observes); all remaining slots are the value.

    Declaring a bus with this shape is an **audited assumption** about the surrounding VM (see
    `BusSemantics.memoryBus` and `ConstraintSystem.memoryDiscipline`). -/
structure MemoryBusShape where
  /-- Payload positions forming the access key (e.g. OpenVM's two-limb address:
      address space and pointer). -/
  addressFields : List Nat
  /-- Payload position of the timestamp. -/
  tsField : Nat
  /-- Upper bound on timestamp values on this bus (e.g. `2^29` for OpenVM). -/
  tsBound : Nat

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
  /-- Declares a stateful bus to follow last-write-wins memory discipline
      (`ConstraintSystem.memoryDiscipline`); `none` (the default case) for buses without it.
      **Audited assumption** for `some`: the surrounding VM implements offline memory checking
      on this bus (every receive tuple equals some send tuple, timestamps unique per address
      and globally range-checked below `tsBound`), and grants a fragment an exclusive
      timestamp window, so that between two of a fragment's own accesses to an address no
      other chip can access it. -/
  memoryBus (busId : Nat) : Option MemoryBusShape

/-- A concrete bus interaction message: which bus, and the tuple sent. -/
abbrev BusMessage (p : ℕ) := Nat × List (ZMod p)

/-- The effect on the stateful buses: the messages sent, each with a multiplicity. -/
abbrev BusState (p : ℕ) := List (BusMessage p × ZMod p)

/-- The net multiplicity with which `message` is sent in `state`. -/
def multiplicitySum (message : BusMessage p) (state : BusState p) : ZMod p :=
  match state with
  | [] => 0
  | (msg, mult) :: tl => (if msg = message then mult else 0) + multiplicitySum message tl

/-- Two bus states are equal when every message is sent with the same net multiplicity. -/
instance : HasEquiv (BusState p) :=
  ⟨fun s t => ∀ message, multiplicitySum message s = multiplicitySum message t⟩

--------- Constraint System ---------

/-- A constraint system representing a single zkVM chip. -/
structure ConstraintSystem (p : ℕ) where
  algebraicConstraints : List (Expression p)
  busInteractions : List (BusInteraction (Expression p))

/-- The side effects of a constraint system under a given environment and bus semantics.
    The side effects are the tuples sent to the *stateful* buses.-/
def ConstraintSystem.sideEffects (cs : ConstraintSystem p)
    (busSemantics : BusSemantics p) (env : String → ZMod p) : BusState p :=
  cs.busInteractions.filter (fun bi => busSemantics.isStateful bi.busId)
    |>.map (fun bi =>
      let m := bi.eval env
      ((m.busId, m.payload), m.multiplicity))

/-- The address projection of an evaluated message, per a memory-bus shape. -/
def MemoryBusShape.address (shape : MemoryBusShape) (m : BusInteraction (ZMod p)) :
    List (Option (ZMod p)) :=
  shape.addressFields.map (fun (slot : Nat) => m.payload[slot]?)

/-- The timestamp value of an evaluated message, per a memory-bus shape. -/
def MemoryBusShape.tsVal (shape : MemoryBusShape) (m : BusInteraction (ZMod p)) : Nat :=
  ((m.payload[shape.tsField]?).getD 0).val

/-- The last-write-wins discipline over a list of evaluated messages ("active" means nonzero
    multiplicity; sends have multiplicity `1`, receives `-1`):
    1. **matching** — an active send and an active receive with the same address and timestamp
       carry the same payload (offline memory checking: a receive's tuple equals some send's
       tuple, and `(address, timestamp)` identifies a send uniquely across the system);
    2. **in-window consumption** — of two active sends to the same address with no active send
       to it strictly between (by timestamp value), the earlier one's tuple is received within
       the fragment (window exclusivity: no other chip can access the address in between, so
       the earlier send's consumer is one of the fragment's own receives);
    3. **timestamp range** — active messages carry timestamps below the declared bound (the
       VM's global timestamp range-checking). -/
def MemoryBusShape.disciplineOn (shape : MemoryBusShape)
    (msgs : List (BusInteraction (ZMod p))) : Prop :=
  (∀ S ∈ msgs, ∀ R ∈ msgs, S.multiplicity = 1 → R.multiplicity = -1 →
    shape.address S = shape.address R → shape.tsVal S = shape.tsVal R →
    S.payload = R.payload) ∧
  (∀ S ∈ msgs, ∀ S' ∈ msgs, S.multiplicity = 1 → S'.multiplicity = 1 →
    shape.address S = shape.address S' → shape.tsVal S < shape.tsVal S' →
    (∀ S'' ∈ msgs, S''.multiplicity = 1 → shape.address S'' = shape.address S →
      ¬(shape.tsVal S < shape.tsVal S'' ∧ shape.tsVal S'' < shape.tsVal S')) →
    ∃ R ∈ msgs, R.multiplicity = -1 ∧ R.payload = S.payload) ∧
  (∀ m ∈ msgs, m.multiplicity ≠ 0 → shape.tsVal m < shape.tsBound)

/-- The memory discipline of a constraint system: every declared memory bus's discipline holds
    for the system's evaluated interactions on that bus. -/
def ConstraintSystem.memoryDiscipline (s : ConstraintSystem p) (busSemantics : BusSemantics p)
    (env : String → ZMod p) : Prop :=
  ∀ (busId : Nat) (shape : MemoryBusShape), busSemantics.memoryBus busId = some shape →
    shape.disciplineOn
      ((s.busInteractions.filter (fun bi => bi.busId = busId)).map (fun bi => bi.eval env))

/-- Whether a constraint system is satisfied under a given environment and bus semantics. -/
def ConstraintSystem.satisfies (s : ConstraintSystem p) (busSemantics : BusSemantics p)
    (env : String → ZMod p) : Prop :=
  (∀ c ∈ s.algebraicConstraints, c.eval env = 0) ∧
  (∀ bi ∈ s.busInteractions,
    let message := bi.eval env
    message.multiplicity ≠ 0 → busSemantics.violatesConstraint message = false) ∧
  s.memoryDiscipline busSemantics env

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
      self.sideEffects busSemantics env ≈ other.sideEffects busSemantics env'

/-- Whether two constraint systems are equivalent under a given bus semantics.
    Two constraint systems are equivalent if each implies the other. -/
def ConstraintSystem.equivalentTo (self other : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  self.implies other busSemantics ∧ other.implies self busSemantics

/-- Whether an optimizer maintains correctness. This means that, for all constraint systems
    and bus semantics:
    1. The optimized constraint system is equivalent to the original, i.e. it has a satisfying
       witness iff the original does **and** the side effects are the same.
    2. Assuming the original constraint system guarantees invariants, so does the optimized one. -/
def optimizerMaintainsCorrectness (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p) :
    Prop :=
  ∀ constraintSystem busSemantics,
    ((optimizer constraintSystem busSemantics).equivalentTo constraintSystem busSemantics) ∧
    (constraintSystem.guaranteesInvariants busSemantics →
      (optimizer constraintSystem busSemantics).guaranteesInvariants busSemantics)
