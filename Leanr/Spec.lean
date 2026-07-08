import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

-- `p` is the field characteristic; a prime, so `ZMod p` is a field.
variable {p : ℕ} [Fact p.Prime]

--------- Expressions ---------

/-- A circuit variable: a display `name` plus an optional powdr witness-column ID. -/
structure Variable where
  name : String
  powdrId? : Option Nat := none
  deriving DecidableEq, Repr

instance : BEq Variable := ⟨fun a b => decide (a = b)⟩
/-- An arithmetic expression over structured variables and field constants. -/
inductive Expression (p : ℕ) where
  | const (n : ZMod p)
  | var (x : Variable)
  | add (e1 e2 : Expression p)
  | mul (e1 e2 : Expression p)

/-- Evaluate an expression under an assignment `env` of variables to field elements. -/
def Expression.eval (e : Expression p) (env : Variable → ZMod p) : ZMod p :=
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

/-- The variables occurring in an expression. -/
def Expression.vars : Expression p → List Variable
  | .const _ => []
  | .var x => [x]
  | .add e1 e2 => e1.vars ++ e2.vars
  | .mul e1 e2 => e1.vars ++ e2.vars

--------- Computation Methods ---------

/-- A method for computing a *derived* variable's value from other variables, mirroring powdr's
    `ComputationMethod`. For newly introduced variables, this is interpreted by powdr's witness
    generator.
    `quotientOrZero num den` is `num / den` in the field, or `0` when
    `den = 0`; `ifEqZero cond thenM elseM` picks `thenM` when `cond` evaluates to `0`, else `elseM`. -/
inductive ComputationMethod (p : ℕ) where
  | const (c : ZMod p)
  | quotientOrZero (num den : Expression p)
  | ifEqZero (cond : Expression p) (thenM elseM : ComputationMethod p)

/-- Evaluate a computation method under an assignment (cf. powdr's `evaluate_computation_method`). -/
def ComputationMethod.eval : ComputationMethod p → (Variable → ZMod p) → ZMod p
  | .const c, _ => c
  | .quotientOrZero num den, env =>
      if den.eval env = 0 then 0 else (den.eval env)⁻¹ * num.eval env
  | .ifEqZero cond thenM elseM, env =>
      if cond.eval env = 0 then thenM.eval env else elseM.eval env

/-- The variables a computation method may read. -/
def ComputationMethod.vars : ComputationMethod p → List Variable
  | .const _ => []
  | .quotientOrZero num den => num.vars ++ den.vars
  | .ifEqZero cond thenM elseM => cond.vars ++ thenM.vars ++ elseM.vars

/-- A list of derived variables paired with how to compute each, in order — the extra output of
    the optimizer, consumed by witness generation. -/
abbrev Derivations (p : ℕ) := List (Variable × ComputationMethod p)

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
def BusInteraction.eval (bi : BusInteraction (Expression p)) (env : Variable → ZMod p) :
    BusInteraction (ZMod p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.eval env,
    payload := bi.payload.map (fun e => e.eval env) }

/-- Per-zkVM bound on the multiplicative degree of a circuit's expressions. -/
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
  /-- A property on *stateful* bus messages with nonzero multiplicity. Completeness is only
      required for assignments whose stateful messages are `admissible`.
      One useful way to use this is to describe the semantics of memory buses, see
      ``Leanr/MemoryBus.lean``. -/
  admissible (statefulBusMessages: List (BusInteraction (ZMod p))): Prop
  /-- The zkVM's degree bound. -/
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

/-- The variables occurring anywhere in a constraint system. -/
def ConstraintSystem.vars (cs : ConstraintSystem p) : List Variable :=
  cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap
      (fun bi => bi.multiplicity.vars ++ bi.payload.flatMap Expression.vars)

/-- The side effects of a constraint system under a given environment and bus semantics.
    The side effects are the tuples sent to the *stateful* buses.-/
def ConstraintSystem.sideEffects (cs : ConstraintSystem p)
    (busSemantics : BusSemantics p) (env : Variable → ZMod p) : BusState p :=
  cs.busInteractions.filter (fun bi => busSemantics.isStateful bi.busId)
    |>.map (fun bi =>
      let m := bi.eval env
      ((m.busId, m.payload), m.multiplicity))

--------- Derived variables ---------

/-- The `ComputationMethod` witness generation uses for `v`: the **last** one `ds` lists for it
    (later derivations override earlier ones), or `none` if `v` is not derived. -/
def Derivations.methodFor : Derivations p → Variable → Option (ComputationMethod p)
  | [], _ => none
  | (u, cm) :: rest, v =>
      (Derivations.methodFor rest v).orElse (fun _ => if u = v then some cm else none)

/-- The provided output circuit assignment can be derived from the provided input circuit assignment
    by the following algorithm:
    - If the variable has a powdr ID, it must be present in the input circuit and have the same value.
    - If the variable does not have a powdr ID, it must be derivable using the provided derivations.

    ASSUMPTION: all variables in the input circuit have a powdr ID. -/
def ConstraintSystem.witnessDerivableFrom (outputCS inputCS : ConstraintSystem p) (ds : Derivations p)
    (outputEnv inputEnv : Variable → ZMod p) : Prop :=
  (∀ v ∈ inputCS.vars, v.powdrId?.isSome) →
  ∀ v ∈ outputCS.vars,
    match v.powdrId? with
    | some _ => v ∈ inputCS.vars ∧ inputEnv v = outputEnv v
    | none => ∃ cm, Derivations.methodFor ds v = some cm ∧
        (∀ x ∈ cm.vars, x.powdrId?.isSome) ∧ cm.eval inputEnv = inputEnv v

--------- Constraint system implications ---------

/-- Whether a given assignment is admissible under the bus semantics. -/
def ConstraintSystem.admissible (s : ConstraintSystem p) (busSemantics : BusSemantics p)
    (env : Variable → ZMod p) : Prop :=
  busSemantics.admissible ((s.busInteractions.map (fun bi => bi.eval env)).filter
    (fun m => decide (m.multiplicity ≠ 0) && busSemantics.isStateful m.busId))

/-- Whether a constraint system is satisfied under a given environment and bus semantics,
    i.e., whether it satisfies all algebraic constraints and does not violate any bus constraints. -/
def ConstraintSystem.satisfies (s : ConstraintSystem p) (busSemantics : BusSemantics p)
    (env : Variable → ZMod p) : Prop :=
  (∀ c ∈ s.algebraicConstraints, c.eval env = 0) ∧
  (∀ bi ∈ s.busInteractions,
    let message := bi.eval env
    message.multiplicity ≠ 0 → busSemantics.violatesConstraint message = false)

/-- Whether a constraint system guarantees that all invariants are maintained under a given bus semantics. -/
def ConstraintSystem.guaranteesInvariants (s : ConstraintSystem p) (busSemantics : BusSemantics p) : Prop :=
  ∀ env, s.satisfies busSemantics env → ∀ bi ∈ s.busInteractions,
    let message := bi.eval env
    message.multiplicity ≠ 0 → busSemantics.breaksInvariant message = false

/-- Whether an optimized constraint system is a sound replacement for an original constraint system.
    Informally, for any satisfying assignment of the optimized system, there exists a corresponding
    satisfying assignment of the original system *with equivalent side effects*. Also, the optimized
    system must maintain all invariants guaranteed by the original system. -/
def ConstraintSystem.isSoundReplacementOf (optimizedCS originalCS : ConstraintSystem p) (busSemantics : BusSemantics p) :
    Prop :=
  (∀ env, optimizedCS.satisfies busSemantics env →
    ∃ env', originalCS.satisfies busSemantics env' ∧
      optimizedCS.sideEffects busSemantics env ≈ originalCS.sideEffects busSemantics env') ∧
  (originalCS.guaranteesInvariants busSemantics → optimizedCS.guaranteesInvariants busSemantics)

/-- Whether an optimized constraint system is a complete replacement for an original constraint system.
    Informally, for any admissible and satisfying assignment of the original system, there exists a
    corresponding admissible and satisfying assignment of the optimized system *with equivalent side effects*.
    Also, it should be possible to derive a witness for the optimized system from a valid witness of the
    original system. -/
def ConstraintSystem.isCompleteReplacementOf (optimizedCS originalCS : ConstraintSystem p)
    (busSemantics : BusSemantics p) (ds : Derivations p) : Prop :=
  ∀ env, originalCS.admissible busSemantics env → originalCS.satisfies busSemantics env →
    ∃ env', optimizedCS.satisfies busSemantics env' ∧ optimizedCS.admissible busSemantics env' ∧
      originalCS.sideEffects busSemantics env ≈ optimizedCS.sideEffects busSemantics env' ∧
      (optimizedCS.witnessDerivableFrom originalCS ds env env')

--------- Degree bound ---------

/-- Whether a constraint system stays within a degree bound. -/
def ConstraintSystem.withinDegree (s : ConstraintSystem p) (b : DegreeBound) : Prop :=
  (∀ c ∈ s.algebraicConstraints, c.degree ≤ b.identities) ∧
  (∀ bi ∈ s.busInteractions, bi.multiplicity.degree ≤ b.busInteractions ∧
    ∀ e ∈ bi.payload, e.degree ≤ b.busInteractions)

/-- Whether an optimizer for the fixed `busSemantics` respects the zkVM's degree bound: a
    within-bound input always yields a within-bound output. -/
def optimizerRespectsDegreeBound (busSemantics : BusSemantics p)
    (optimizer : ConstraintSystem p → ConstraintSystem p × Derivations p) : Prop :=
  ∀ constraintSystem : ConstraintSystem p,
    constraintSystem.withinDegree busSemantics.degreeBound →
    (optimizer constraintSystem).1.withinDegree busSemantics.degreeBound

--------- Optimizer correctness ---------

abbrev Optimizer (p : ℕ) := ConstraintSystem p → ConstraintSystem p × Derivations p

/-- An optimizer is correct, for all possible input constraint systems, replacing it
    by the optimized constraint system is sound and complete. Also, it has to respect
    the degree bound. -/
def Optimizer.isCorrect (optimizer : Optimizer p) (busSemantics : BusSemantics p) : Prop :=
  (∀ originalCS : ConstraintSystem p,
    let (optimizedCS, derivations) := optimizer originalCS
    (optimizedCS.isSoundReplacementOf originalCS busSemantics) ∧
    (optimizedCS.isCompleteReplacementOf originalCS busSemantics derivations))
  ∧ optimizerRespectsDegreeBound busSemantics optimizer
