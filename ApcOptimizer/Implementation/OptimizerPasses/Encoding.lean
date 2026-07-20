import ApcOptimizer.Implementation.OptimizerPasses.Registry
import ApcOptimizer.Utils.Size

set_option autoImplicit false

/-! # Dense data model and encode/decode (Task 3, WP-B)

Implementation-only dense counterparts of the spec's recursive circuit values, with `VarId` leaves.
`decode` resolves IDs through a registry to recover the spec value; `encode` threads a registry
left-to-right, registering each variable occurrence and emitting dense leaves in one traversal.

The correspondence results (`decode ∘ encode = id`, extension agreement, degree/eval/vars
preservation) are the bridge every dense pass proof rides on: a pass is proved correct by showing
its dense transform *decodes to* the existing spec pass's output. All evidence is `Prop` (erases);
no proof wrapper is stored at expression nodes — a single coverage invariant is threaded and local
validity derived when needed.

Dense bus interactions reuse the spec's polymorphic `BusInteraction` at `DenseExpr p`, so the
generic `BusInteraction` machinery composes directly. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense types -/

/-- A dense arithmetic expression: the spec `Expression` with `VarId` leaves. -/
inductive DenseExpr (p : ℕ) where
  | const (n : ZMod p)
  | var (i : VarId)
  | add (a b : DenseExpr p)
  | mul (a b : DenseExpr p)
deriving Repr, DecidableEq

/-- A dense computation method: the spec `ComputationMethod` over `DenseExpr`. -/
inductive DenseComputationMethod (p : ℕ) where
  | const (c : ZMod p)
  | quotientOrZero (num den : DenseExpr p)
  | ifEqZero (cond : DenseExpr p) (thenM elseM : DenseComputationMethod p)

/-- A dense derivation list: `VarId`-keyed computation methods, in order (last-entry-wins on decode,
    mirroring `Derivations.methodFor`). -/
abbrev DenseDerivations (p : ℕ) := List (VarId × DenseComputationMethod p)

/-- A dense constraint system: algebraic constraints and bus interactions over `DenseExpr`. -/
structure DenseConstraintSystem (p : ℕ) where
  algebraicConstraints : List (DenseExpr p)
  busInteractions : List (BusInteraction (DenseExpr p))

/-! ## Dense expression operations (runtime; specified against decode below) -/

/-- Multiplicative degree, mirroring `Expression.degree`. -/
def DenseExpr.degree : DenseExpr p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree

/-- Evaluation under a dense environment. -/
def DenseExpr.eval (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  match e with
  | .const n => n
  | .var i => denv i
  | .add a b => a.eval denv + b.eval denv
  | .mul a b => a.eval denv * b.eval denv

/-- The `VarId`s occurring in a dense expression, in left-to-right order. -/
def DenseExpr.vars : DenseExpr p → List VarId
  | .const _ => []
  | .var i => [i]
  | .add a b => a.vars ++ b.vars
  | .mul a b => a.vars ++ b.vars

/-- All `VarId`s of a dense bus interaction (multiplicity then payload). -/
def denseBIVars (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.multiplicity.vars ++ bi.payload.flatMap DenseExpr.vars

/-! ## Coverage: every leaf ID is valid in the registry -/

/-- Every `VarId` leaf of `e` is valid in `r`. Threaded as a single invariant; local validity of a
    particular leaf is derived from it. -/
def DenseExpr.CoveredBy (r : VarRegistry) (e : DenseExpr p) : Prop :=
  ∀ i ∈ e.vars, r.Valid i

theorem DenseExpr.coveredBy_const (r : VarRegistry) (n : ZMod p) :
    (DenseExpr.const n).CoveredBy r := by intro i hi; simp [DenseExpr.vars] at hi

theorem DenseExpr.coveredBy_var {r : VarRegistry} {i : VarId} (h : r.Valid i) :
    (DenseExpr.var i : DenseExpr p).CoveredBy r := by
  intro j hj; simp [DenseExpr.vars] at hj; exact hj ▸ h

theorem DenseExpr.coveredBy_add {r : VarRegistry} {a b : DenseExpr p} :
    (a.add b).CoveredBy r ↔ a.CoveredBy r ∧ b.CoveredBy r := by
  simp only [CoveredBy, DenseExpr.vars, List.mem_append]
  constructor
  · exact fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · exact fun ⟨ha, hb⟩ i hi => hi.elim (ha i) (hb i)

theorem DenseExpr.coveredBy_mul {r : VarRegistry} {a b : DenseExpr p} :
    (a.mul b).CoveredBy r ↔ a.CoveredBy r ∧ b.CoveredBy r := by
  simp only [CoveredBy, DenseExpr.vars, List.mem_append]
  constructor
  · exact fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · exact fun ⟨ha, hb⟩ i hi => hi.elim (ha i) (hb i)

/-! ## Decoding -/

/-- Decode a dense expression: resolve each `VarId` leaf through the registry. -/
def VarRegistry.decodeExpr (r : VarRegistry) : DenseExpr p → Expression p
  | .const n => .const n
  | .var i => .var (r.resolve i)
  | .add a b => .add (r.decodeExpr a) (r.decodeExpr b)
  | .mul a b => .mul (r.decodeExpr a) (r.decodeExpr b)

/-- Decode a dense computation method. -/
def VarRegistry.decodeCM (r : VarRegistry) : DenseComputationMethod p → ComputationMethod p
  | .const c => .const c
  | .quotientOrZero num den => .quotientOrZero (r.decodeExpr num) (r.decodeExpr den)
  | .ifEqZero cond thenM elseM => .ifEqZero (r.decodeExpr cond) (r.decodeCM thenM) (r.decodeCM elseM)

/-- Decode a dense bus interaction. -/
def VarRegistry.decodeBI (r : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    BusInteraction (Expression p) :=
  { busId := bi.busId,
    multiplicity := r.decodeExpr bi.multiplicity,
    payload := bi.payload.map r.decodeExpr }

/-- Decode a dense constraint system. -/
def VarRegistry.decodeCS (r : VarRegistry) (d : DenseConstraintSystem p) : ConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map r.decodeExpr,
    busInteractions := d.busInteractions.map r.decodeBI }

/-- Decode dense derivations. -/
def VarRegistry.decodeDerivs (r : VarRegistry) (dd : DenseDerivations p) : Derivations p :=
  dd.map (fun d => (r.resolve d.1, r.decodeCM d.2))

/-! ## Decode correspondence: degree, eval, vars -/

/-- Decoding preserves multiplicative degree. -/
theorem VarRegistry.decodeExpr_degree (r : VarRegistry) (e : DenseExpr p) :
    (r.decodeExpr e).degree = e.degree := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [decodeExpr, Expression.degree, DenseExpr.degree, iha, ihb]
  | mul a b iha ihb => simp [decodeExpr, Expression.degree, DenseExpr.degree, iha, ihb]

/-- Decoding commutes with evaluation: evaluating the decoded expression under `env` equals
    evaluating the dense expression under `env ∘ resolve`. -/
theorem VarRegistry.decodeExpr_eval (r : VarRegistry) (e : DenseExpr p) (env : Variable → ZMod p) :
    (r.decodeExpr e).eval env = e.eval (fun i => env (r.resolve i)) := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [decodeExpr, Expression.eval, DenseExpr.eval, iha, ihb]
  | mul a b iha ihb => simp [decodeExpr, Expression.eval, DenseExpr.eval, iha, ihb]

/-- The variables of a decoded expression are the resolved dense variables, in order. -/
theorem VarRegistry.decodeExpr_vars (r : VarRegistry) (e : DenseExpr p) :
    (r.decodeExpr e).vars = e.vars.map r.resolve := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [decodeExpr, Expression.vars, DenseExpr.vars, iha, ihb]
  | mul a b iha ihb => simp [decodeExpr, Expression.vars, DenseExpr.vars, iha, ihb]

/-! ## Decode stability under registry extension -/

/-- Decoding a covered dense expression is unchanged by extending the registry. -/
theorem VarRegistry.Extends.decodeExpr_eq {r r' : VarRegistry} (h : r.Extends r') {e : DenseExpr p}
    (hc : e.CoveredBy r) : r'.decodeExpr e = r.decodeExpr e := by
  induction e with
  | const n => rfl
  | var i =>
      have : r.Valid i := hc i (by simp [DenseExpr.vars])
      simp [decodeExpr, h.resolve_eq this]
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      simp [decodeExpr, iha ha, ihb hb]
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      simp [decodeExpr, iha ha, ihb hb]

/-- Coverage is preserved by extension. -/
theorem DenseExpr.CoveredBy.mono {r r' : VarRegistry} (h : r.Extends r') {e : DenseExpr p}
    (hc : e.CoveredBy r) : e.CoveredBy r' := fun i hi => h.valid (hc i hi)

/-! ## Encoding (state-threaded registration + dense emission) -/

/-- Encode a spec expression into a dense one, threading the registry (registering each variable
    occurrence). One `Variable → VarId` lookup per source occurrence — the allowed entry-edge cost. -/
def VarRegistry.encodeExpr (r : VarRegistry) : Expression p → VarRegistry × DenseExpr p
  | .const n => (r, .const n)
  | .var x => let (r', i) := r.register x; (r', .var i)
  | .add a b =>
      let (r1, a') := r.encodeExpr a
      let (r2, b') := r1.encodeExpr b
      (r2, .add a' b')
  | .mul a b =>
      let (r1, a') := r.encodeExpr a
      let (r2, b') := r1.encodeExpr b
      (r2, .mul a' b')

/-- State-threaded encode of a list of expressions (linear, cons-built — no quadratic append). -/
def VarRegistry.encodeExprs (r : VarRegistry) :
    List (Expression p) → VarRegistry × List (DenseExpr p)
  | [] => (r, [])
  | e :: rest =>
      let (r1, e') := r.encodeExpr e
      let (r2, rest') := r1.encodeExprs rest
      (r2, e' :: rest')

/-- Encode a spec bus interaction, threading the registry through multiplicity then payload. -/
def VarRegistry.encodeBI (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    VarRegistry × BusInteraction (DenseExpr p) :=
  let (r1, m) := r.encodeExpr bi.multiplicity
  let (r2, ps) := r1.encodeExprs bi.payload
  (r2, { busId := bi.busId, multiplicity := m, payload := ps })

/-- State-threaded encode of a list of bus interactions. -/
def VarRegistry.encodeBIs (r : VarRegistry) :
    List (BusInteraction (Expression p)) → VarRegistry × List (BusInteraction (DenseExpr p))
  | [] => (r, [])
  | bi :: rest =>
      let (r1, bi') := r.encodeBI bi
      let (r2, rest') := r1.encodeBIs rest
      (r2, bi' :: rest')

/-- Encode a spec constraint system, threading the registry through constraints then interactions.
    Left-to-right, single traversal; the registry it returns covers the dense system it returns. -/
def VarRegistry.encodeCS (r : VarRegistry) (cs : ConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p :=
  let (r1, acs) := r.encodeExprs cs.algebraicConstraints
  let (r2, bis) := r1.encodeBIs cs.busInteractions
  (r2, { algebraicConstraints := acs, busInteractions := bis })

/-! ## Encode: extension, coverage, round trip (expression level) -/

/-- Encoding extends the registry. -/
theorem VarRegistry.encodeExpr_extends (r : VarRegistry) (e : Expression p) :
    r.Extends (r.encodeExpr e).1 := by
  induction e generalizing r with
  | const n => exact VarRegistry.Extends.refl r
  | var x => exact r.register_extends x
  | add a b iha ihb =>
      exact (iha r).trans (ihb (r.encodeExpr a).1)
  | mul a b iha ihb =>
      exact (iha r).trans (ihb (r.encodeExpr a).1)

/-- The dense expression `encode` returns is covered by the registry it returns. -/
theorem VarRegistry.encodeExpr_covered (r : VarRegistry) (e : Expression p) :
    (r.encodeExpr e).2.CoveredBy (r.encodeExpr e).1 := by
  induction e generalizing r with
  | const n => exact DenseExpr.coveredBy_const _ n
  | var x => exact DenseExpr.coveredBy_var (r.register_valid x)
  | add a b iha ihb =>
      show (DenseExpr.add (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2).CoveredBy _
      rw [DenseExpr.coveredBy_add]
      refine ⟨?_, ihb (r.encodeExpr a).1⟩
      exact (iha r).mono ((r.encodeExpr a).1.encodeExpr_extends b)
  | mul a b iha ihb =>
      show (DenseExpr.mul (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2).CoveredBy _
      rw [DenseExpr.coveredBy_mul]
      refine ⟨?_, ihb (r.encodeExpr a).1⟩
      exact (iha r).mono ((r.encodeExpr a).1.encodeExpr_extends b)

/-- Round trip: decoding an encoded expression (under the resulting registry) is the identity. -/
theorem VarRegistry.decodeExpr_encodeExpr (r : VarRegistry) (e : Expression p) :
    (r.encodeExpr e).1.decodeExpr (r.encodeExpr e).2 = e := by
  induction e generalizing r with
  | const n => rfl
  | var x =>
      show (r.register x).1.decodeExpr (.var (r.register x).2) = .var x
      simp [decodeExpr, r.register_resolve x]
  | add a b iha ihb =>
      show ((r.encodeExpr a).1.encodeExpr b).1.decodeExpr
        (.add (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2) = .add a b
      rw [decodeExpr]
      congr 1
      · rw [((r.encodeExpr a).1.encodeExpr_extends b).decodeExpr_eq (r.encodeExpr_covered a)]
        exact iha r
      · exact ihb (r.encodeExpr a).1
  | mul a b iha ihb =>
      show ((r.encodeExpr a).1.encodeExpr b).1.decodeExpr
        (.mul (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2) = .mul a b
      rw [decodeExpr]
      congr 1
      · rw [((r.encodeExpr a).1.encodeExpr_extends b).decodeExpr_eq (r.encodeExpr_covered a)]
        exact iha r
      · exact ihb (r.encodeExpr a).1

/-! ## Encode: extension, coverage, round trip (list / bus-interaction / system levels) -/

/-- Structural unfolding of `encodeExprs` on a cons (holds by `rfl` via `Prod` eta). -/
theorem VarRegistry.encodeExprs_cons (r : VarRegistry) (e : Expression p)
    (rest : List (Expression p)) :
    r.encodeExprs (e :: rest) =
      (((r.encodeExpr e).1.encodeExprs rest).1,
        (r.encodeExpr e).2 :: ((r.encodeExpr e).1.encodeExprs rest).2) := rfl

theorem VarRegistry.encodeBIs_cons (r : VarRegistry) (bi : BusInteraction (Expression p))
    (rest : List (BusInteraction (Expression p))) :
    r.encodeBIs (bi :: rest) =
      (((r.encodeBI bi).1.encodeBIs rest).1,
        (r.encodeBI bi).2 :: ((r.encodeBI bi).1.encodeBIs rest).2) := rfl

/-- List-level decode stability under extension. -/
theorem VarRegistry.Extends.decodeExprs_eq {r r' : VarRegistry} (h : r.Extends r')
    {es : List (DenseExpr p)} (hc : ∀ e ∈ es, e.CoveredBy r) :
    es.map r'.decodeExpr = es.map r.decodeExpr :=
  List.map_congr_left (fun e he => h.decodeExpr_eq (hc e he))

theorem VarRegistry.encodeExprs_extends (r : VarRegistry) (es : List (Expression p)) :
    r.Extends (r.encodeExprs es).1 := by
  induction es generalizing r with
  | nil => exact Extends.refl r
  | cons e rest ih =>
      rw [encodeExprs_cons]
      exact (r.encodeExpr_extends e).trans (ih (r.encodeExpr e).1)

theorem VarRegistry.encodeExprs_covered (r : VarRegistry) (es : List (Expression p)) :
    ∀ e ∈ (r.encodeExprs es).2, e.CoveredBy (r.encodeExprs es).1 := by
  induction es generalizing r with
  | nil => intro e he; simp [encodeExprs] at he
  | cons e rest ih =>
      rw [encodeExprs_cons]
      intro e' he'
      rcases List.mem_cons.mp he' with heq | hmem
      · subst heq
        exact (r.encodeExpr_covered e).mono ((r.encodeExpr e).1.encodeExprs_extends rest)
      · exact ih (r.encodeExpr e).1 e' hmem

theorem VarRegistry.decodeExprs_encodeExprs (r : VarRegistry) (es : List (Expression p)) :
    ((r.encodeExprs es).2).map (r.encodeExprs es).1.decodeExpr = es := by
  induction es generalizing r with
  | nil => rfl
  | cons e rest ih =>
      rw [encodeExprs_cons]
      simp only [List.map_cons]
      congr 1
      · rw [((r.encodeExpr e).1.encodeExprs_extends rest).decodeExpr_eq (r.encodeExpr_covered e)]
        exact r.decodeExpr_encodeExpr e
      · exact ih (r.encodeExpr e).1

/-- Coverage of a dense bus interaction: multiplicity and every payload expression are covered. -/
def denseBICovered (r : VarRegistry) (bi : BusInteraction (DenseExpr p)) : Prop :=
  bi.multiplicity.CoveredBy r ∧ ∀ e ∈ bi.payload, e.CoveredBy r

/-- Structural projections of `encodeBI` (each holds by `rfl` via `Prod` eta). -/
theorem VarRegistry.encodeBI_fst (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    (r.encodeBI bi).1 = ((r.encodeExpr bi.multiplicity).1.encodeExprs bi.payload).1 := rfl

theorem VarRegistry.encodeBI_busId (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    (r.encodeBI bi).2.busId = bi.busId := rfl

theorem VarRegistry.encodeBI_mult (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    (r.encodeBI bi).2.multiplicity = (r.encodeExpr bi.multiplicity).2 := rfl

theorem VarRegistry.encodeBI_payload (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    (r.encodeBI bi).2.payload = ((r.encodeExpr bi.multiplicity).1.encodeExprs bi.payload).2 := rfl

/-- Bus-interaction decode stability under extension. -/
theorem VarRegistry.Extends.decodeBI_eq {r r' : VarRegistry} (h : r.Extends r')
    {bi : BusInteraction (DenseExpr p)} (hc : denseBICovered r bi) :
    r'.decodeBI bi = r.decodeBI bi := by
  obtain ⟨hm, hp⟩ := hc
  simp only [VarRegistry.decodeBI, h.decodeExpr_eq hm, h.decodeExprs_eq hp]

theorem VarRegistry.encodeBI_extends (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    r.Extends (r.encodeBI bi).1 :=
  (r.encodeExpr_extends bi.multiplicity).trans
    ((r.encodeExpr bi.multiplicity).1.encodeExprs_extends bi.payload)

theorem VarRegistry.encodeBI_covered (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    denseBICovered (r.encodeBI bi).1 (r.encodeBI bi).2 := by
  rw [denseBICovered, encodeBI_mult, encodeBI_payload, encodeBI_fst]
  refine ⟨?_, ?_⟩
  · exact (r.encodeExpr_covered bi.multiplicity).mono
      ((r.encodeExpr bi.multiplicity).1.encodeExprs_extends bi.payload)
  · exact (r.encodeExpr bi.multiplicity).1.encodeExprs_covered bi.payload

theorem VarRegistry.decodeBI_encodeBI (r : VarRegistry) (bi : BusInteraction (Expression p)) :
    (r.encodeBI bi).1.decodeBI (r.encodeBI bi).2 = bi := by
  simp only [VarRegistry.decodeBI, encodeBI_fst, encodeBI_busId, encodeBI_mult, encodeBI_payload]
  obtain ⟨busId, mult, payload⟩ := bi
  congr 1
  · rw [((r.encodeExpr mult).1.encodeExprs_extends payload).decodeExpr_eq
        (r.encodeExpr_covered mult)]
    exact r.decodeExpr_encodeExpr mult
  · exact (r.encodeExpr mult).1.decodeExprs_encodeExprs payload

theorem VarRegistry.encodeBIs_extends (r : VarRegistry)
    (bis : List (BusInteraction (Expression p))) : r.Extends (r.encodeBIs bis).1 := by
  induction bis generalizing r with
  | nil => exact Extends.refl r
  | cons bi rest ih =>
      rw [encodeBIs_cons]
      exact (r.encodeBI_extends bi).trans (ih (r.encodeBI bi).1)

theorem VarRegistry.decodeBIs_encodeBIs (r : VarRegistry)
    (bis : List (BusInteraction (Expression p))) :
    ((r.encodeBIs bis).2).map (r.encodeBIs bis).1.decodeBI = bis := by
  induction bis generalizing r with
  | nil => rfl
  | cons bi rest ih =>
      rw [encodeBIs_cons]
      simp only [List.map_cons]
      congr 1
      · rw [((r.encodeBI bi).1.encodeBIs_extends rest).decodeBI_eq (r.encodeBI_covered bi)]
        exact r.decodeBI_encodeBI bi
      · exact ih (r.encodeBI bi).1

/-- Structural projections of `encodeCS` (each holds by `rfl` via `Prod` eta). -/
theorem VarRegistry.encodeCS_fst (r : VarRegistry) (cs : ConstraintSystem p) :
    (r.encodeCS cs).1
      = ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs cs.busInteractions).1 := rfl

theorem VarRegistry.encodeCS_acs (r : VarRegistry) (cs : ConstraintSystem p) :
    (r.encodeCS cs).2.algebraicConstraints = (r.encodeExprs cs.algebraicConstraints).2 := rfl

theorem VarRegistry.encodeCS_bis (r : VarRegistry) (cs : ConstraintSystem p) :
    (r.encodeCS cs).2.busInteractions
      = ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs cs.busInteractions).2 := rfl

/-- **Round trip at the system level.** Decoding an encoded constraint system (under the resulting
    registry) recovers the original — the identity the Checkpoint-1 encode/decode adapter rides on. -/
theorem VarRegistry.decodeCS_encodeCS (r : VarRegistry) (cs : ConstraintSystem p) :
    (r.encodeCS cs).1.decodeCS (r.encodeCS cs).2 = cs := by
  obtain ⟨acs, bis⟩ := cs
  simp only [VarRegistry.decodeCS, encodeCS_fst, encodeCS_acs, encodeCS_bis]
  congr 1
  · rw [((r.encodeExprs acs).1.encodeBIs_extends bis).decodeExprs_eq
        (r.encodeExprs_covered acs)]
    exact r.decodeExprs_encodeExprs acs
  · exact (r.encodeExprs acs).1.decodeBIs_encodeBIs bis

end ApcOptimizer.Dense
