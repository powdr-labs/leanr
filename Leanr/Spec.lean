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

/-- The multiplicative degree of an expression (an upper bound on the total degree of the
    polynomial it denotes): constants are degree `0`, variables `1`, addition takes the
    maximum, multiplication the sum. -/
def Expression.degree : Expression p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add e1 e2 => max e1.degree e2.degree
  | .mul e1 e2 => e1.degree + e2.degree

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

/-- Per-zkVM bound on the multiplicative degree of a circuit's expressions: the proving
    backend fixes how large the degree of algebraic constraints (`identities`) and of bus
    interaction fields — multiplicities and payload entries — may become. An optimizer must
    never exceed it (`optimizerRespectsDegree`). -/
structure DegreeBound where
  identities : Nat
  busInteractions : Nat

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
      other chip can access it.

      The shape also covers *linear-consumption* buses with `addressFields := []` — a single
      global cell, e.g. an execution bridge whose tuples are `(pc, timestamp)` states: each
      state is produced once and consumed once, at most one per timestamp, and window
      exclusivity means a state produced strictly before another of the fragment's own
      productions is consumed by the fragment itself. -/
  memoryBus (busId : Nat) : Option MemoryBusShape
  /-- The zkVM's degree bound (see `DegreeBound`): what the proving backend supports. -/
  degreeBound : DegreeBound

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
       VM's global timestamp range-checking);
    4. **timestamp uniqueness** — two active sends (dually, two active receives) to the same
       address with the same timestamp value carry the same payload (`(address, timestamp)`
       identifies at most one send and at most one receive across the system — the same
       global-uniqueness assumption clause 1 relies on, stated send-to-send and
       receive-to-receive);
    5. **program-order timestamp monotonicity** — active messages are listed in
       non-decreasing timestamp order: for any two active messages with the earlier one first
       in the interaction list, the earlier one's timestamp is `≤` the later one's
       (`List.Pairwise`). **Audited assumption** (with Georg's sign-off): the APC generator
       emits a fragment's bus interactions in execution order and the VM's timestamps advance
       monotonically along that execution, so list order is time order within the fragment's
       exclusive timestamp window. Unlike clauses 1–4, this makes list order load-bearing for
       the *soundness* of the optimizations it enables (e.g. it identifies the last active
       send as the timestamp maximum, the anchor an execution-bridge chain needs when a
       block ends in a computed jump). -/
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
  (∀ m ∈ msgs, m.multiplicity ≠ 0 → shape.tsVal m < shape.tsBound) ∧
  (∀ S ∈ msgs, ∀ S' ∈ msgs, S.multiplicity = 1 → S'.multiplicity = 1 →
    shape.address S = shape.address S' → shape.tsVal S = shape.tsVal S' →
    S.payload = S'.payload) ∧
  (∀ R ∈ msgs, ∀ R' ∈ msgs, R.multiplicity = -1 → R'.multiplicity = -1 →
    shape.address R = shape.address R' → shape.tsVal R = shape.tsVal R' →
    R.payload = R'.payload) ∧
  (msgs.Pairwise (fun a b => a.multiplicity ≠ 0 → b.multiplicity ≠ 0 →
    shape.tsVal a ≤ shape.tsVal b))

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

/-- Whether a constraint system stays within a degree bound: every algebraic constraint has
    degree at most `b.identities`, and every bus interaction field — the multiplicity and
    each payload entry — has degree at most `b.busInteractions`. -/
def ConstraintSystem.withinDegree (s : ConstraintSystem p) (b : DegreeBound) : Prop :=
  (∀ c ∈ s.algebraicConstraints, c.degree ≤ b.identities) ∧
  (∀ bi ∈ s.busInteractions, bi.multiplicity.degree ≤ b.busInteractions ∧
    ∀ e ∈ bi.payload, e.degree ≤ b.busInteractions)

/-- Decidable twin of `withinDegree`. -/
def ConstraintSystem.withinDegreeB (s : ConstraintSystem p) (b : DegreeBound) : Bool :=
  s.algebraicConstraints.all (fun c => c.degree ≤ b.identities) &&
  s.busInteractions.all (fun bi =>
    decide (bi.multiplicity.degree ≤ b.busInteractions) &&
      bi.payload.all (fun e => e.degree ≤ b.busInteractions))

omit [Fact p.Prime] in
theorem ConstraintSystem.withinDegreeB_iff (s : ConstraintSystem p) (b : DegreeBound) :
    s.withinDegreeB b = true ↔ s.withinDegree b := by
  unfold ConstraintSystem.withinDegreeB ConstraintSystem.withinDegree
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hcm => by simpa using hc c hcm, fun bi hbm => ?_⟩
    have := hb bi hbm
    rw [Bool.and_eq_true, List.all_eq_true] at this
    exact ⟨by simpa using this.1, fun e he => by simpa using this.2 e he⟩
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hcm => by simpa using hc c hcm, fun bi hbm => ?_⟩
    rw [Bool.and_eq_true, List.all_eq_true]
    exact ⟨by simpa using (hb bi hbm).1, fun e he => by simpa using (hb bi hbm).2 e he⟩

/-- Whether an optimizer respects the zkVM's degree bound: it never pushes a circuit that is
    within the bound past it. -/
def optimizerRespectsDegree
    (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p) : Prop :=
  ∀ (constraintSystem : ConstraintSystem p) (busSemantics : BusSemantics p),
    constraintSystem.withinDegree busSemantics.degreeBound →
    (optimizer constraintSystem busSemantics).withinDegree busSemantics.degreeBound

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
