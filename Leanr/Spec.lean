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

/-- The multiplicative degree of an expression. -/
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

/-- Per-zkVM bound on the multiplicative degree of a circuit's expressions: the proving
    backend fixes how large the degree of algebraic constraints (`identities`) and of bus
    interaction fields — multiplicities and payload entries — may become. An optimizer must
    never exceed it (`optimizerRespectsDegreeBound`). -/
structure DegreeBound where
  identities : Nat
  busInteractions : Nat

/-- The bus semantics of the zkVM. -/
-- TODO: Rename to VmSemantics
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
  /-- Audited, VM-supplied predicate on the evaluated messages of the *stateful* buses: holds
      exactly for the message lists that correspond to a real VM trace (offline memory checking /
      program-ordered execution). The optimizer must preserve completeness only for assignments
      whose stateful messages are `admissible` — never for every satisfying assignment (see
      `ConstraintSystem.admissible`, `impliesAdmissible`, `refines`). Concrete memory/exec
      discipline lives in the integration (`Leanr/MemoryBus.lean`, `Leanr/OpenVM/`), not here. -/
  admissible : List (BusInteraction (ZMod p)) → Prop
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

/-- The **admissible** (real-trace) assignments of a constraint system: those whose evaluated
    messages on the *stateful* buses form a real VM trace, per the VM's `BusSemantics.admissible`
    predicate. Pre-filtered to active (nonzero-multiplicity) stateful messages, so it is
    insensitive to inactive and stateless interactions — which is what lets it transfer through
    every pass generically (substitution/rewrites preserve the evaluated messages; zero-mult and
    tautology removal drop only messages this filter already excludes).

    This is an **audited assumption** about the surrounding VM. It is deliberately *not* part of
    `satisfies`: the optimizer must preserve completeness only for admissible assignments, never
    for every satisfying assignment (see `impliesAdmissible`/`refines`). Whether a real trace is
    additionally *forced* to be the unique satisfying assignment — as it is for memory, by offline
    memory checking — is out of scope; we only assume real traces are admissible. -/
def ConstraintSystem.admissible (s : ConstraintSystem p) (busSemantics : BusSemantics p)
    (env : String → ZMod p) : Prop :=
  busSemantics.admissible ((s.busInteractions.map (fun bi => bi.eval env)).filter
    (fun m => decide (m.multiplicity ≠ 0) && busSemantics.isStateful m.busId))

/-- Whether a constraint system is satisfied under a given environment and bus semantics.
    Minimal by design (algebraic constraints + bus-message obligations only); the memory
    discipline lives separately in `isIntended` and gates the completeness direction of
    `refines`, not satisfaction. -/
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
      self.sideEffects busSemantics env ≈ other.sideEffects busSemantics env'

/-- Like `implies`, but the obligation is only required for `self`'s **admissible** (real-trace)
    assignments, and the produced witness is itself admissible. This is the *completeness*
    direction of an optimization: the optimizer must reproduce every real trace, but may drop
    spurious (non-trace) satisfying assignments. Delivering an admissible witness is what makes
    `refines` composable (see `impliesAdmissible_trans`). -/
def ConstraintSystem.impliesAdmissible (self other : ConstraintSystem p)
    (busSemantics : BusSemantics p) : Prop :=
  ∀ env, self.admissible busSemantics env → self.satisfies busSemantics env →
    ∃ env', other.satisfies busSemantics env' ∧ other.admissible busSemantics env' ∧
      self.sideEffects busSemantics env ≈ other.sideEffects busSemantics env'

/-- Whether `self` is a valid **optimization** of `other` under a given bus semantics:
    * **sound** — `self.implies other`: every satisfying assignment of `self` is one of `other`
      (unconditional; this is what keeps the proof system honest);
    * **complete for admissible executions** — `other.impliesAdmissible self`: every *admissible*
      (real-trace) satisfying assignment of `other` is reproduced by `self`.

    Replaces the old symmetric `equivalentTo`; it is deliberately **not** symmetric — an
    optimizer may drop non-trace witnesses, so `refines` does not entail its converse. -/
def ConstraintSystem.refines (self other : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  self.implies other busSemantics ∧ other.impliesAdmissible self busSemantics

/-- Whether a constraint system stays within a degree bound. -/
def ConstraintSystem.withinDegree (s : ConstraintSystem p) (b : DegreeBound) : Prop :=
  (∀ c ∈ s.algebraicConstraints, c.degree ≤ b.identities) ∧
  (∀ bi ∈ s.busInteractions, bi.multiplicity.degree ≤ b.busInteractions ∧
    ∀ e ∈ bi.payload, e.degree ≤ b.busInteractions)

/-- Whether an optimizer respects the zkVM's degree bound: it never pushes a circuit that is
    within the bound past it. -/
def optimizerRespectsDegreeBound
    (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p) : Prop :=
  ∀ (constraintSystem : ConstraintSystem p) (busSemantics : BusSemantics p),
    constraintSystem.withinDegree busSemantics.degreeBound →
    (optimizer constraintSystem busSemantics).withinDegree busSemantics.degreeBound

/-- Whether an optimizer maintains correctness. This means that, for all constraint systems
    and bus semantics:
    1. The optimized constraint system `refines` the original: it is sound (every satisfying
       witness of the output is one of the input, with the same side effects) and complete for
       the input's intended (real-trace) executions.
    2. Assuming the original constraint system guarantees invariants, so does the optimized one.
    3. The optimizer respects the zkVM's degree bound. -/
def optimizerMaintainsCorrectness (optimizer : ConstraintSystem p → BusSemantics p → ConstraintSystem p) :
    Prop :=
  (∀ constraintSystem busSemantics,
    ((optimizer constraintSystem busSemantics).refines constraintSystem busSemantics) ∧
    (constraintSystem.guaranteesInvariants busSemantics →
      (optimizer constraintSystem busSemantics).guaranteesInvariants busSemantics))
  ∧ optimizerRespectsDegreeBound optimizer
