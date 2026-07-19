import ApcOptimizer.Implementation.Dense.BusPairCancelJustifyProof

set_option autoImplicit false

/-! # Native dense drop-pair core (Task 3, chunk C2)

The single-drop correctness step of `busPairCancel`, ported natively to the dense `VarId`
representation. This mirrors the spec chain `sideEffects_dropPair_equiv` (:905) and
`dropPair_correct` (:1008) in `OptimizerPasses/BusPairCancel.lean`, re-derived over dense
environments (`VarId → ZMod p`) with no decode dependency: every semantic notion is the dense one
from `Dense/Bridge.lean` (`DenseConstraintSystem.satisfies`/`admissible`/`sideEffects`/
`guaranteesInvariants`/`implies`, `denseBIEval`), every `BusFacts` field is applied at the *value*
level over `denseBIEval`, and the byte obligation is discharged from C1's
`denseRecvSlotsJustified_sound`.

## Statement shape (mirrors spec exactly)

`dropPair_correct`/`denseDropPair_correct` are stated over a **plain** constraint system with the
split hypothesis `d.busInteractions = A ++ S :: B ++ R :: C`, concluding
`DensePassCorrect isInput d { d with busInteractions := A ++ B ++ C ++ checks } [] bs` — assembled
via `DensePassCorrect.ofEnvEq`, exactly as spec assembles `PassCorrect cs
{ cs with busInteractions := A ++ B ++ C ++ checks } [] bs` via `PassCorrect.ofEnvEq`. The `mkCs`
projection is *not* part of this statement: in the spec, `dropPair_correct`/`checkCancel_sound` are
over a plain `cs`, and the `mkCs`-shaped intermediate systems are threaded only later, in the
`cancelLoop` (C7), which instantiates this lemma's `cs`/`d` with `mkCs cs0 arr alive checks` and
recognises the output via `liveSeg_split`/`liveSeg_drop`. So C7 composes the single steps this file
provides through `DensePassCorrect.andThen`, and C5 (`checkCancel`) feeds this lemma its
hypotheses. The hypothesis list is the exact dense mirror of spec `dropPair_correct`'s: payload
equality (`hpayEval`, discharged by C5 via `denseConsecutivePayloadEq`-style entailment), the
between-region refutation (`hmidEval`) and before-region shield (`hpreEval`) as hypotheses
(discharged by C5 via `midRefuted`/`shieldOk`), and the byte obligation (`hbyte`, from C1).

## Runtime vs proof classification of `toBusState`/`activeStatefulMsgs`

Both are **proof-only** in the spec: they occur *only* inside the `dropPair_correct` proof (no pass
transform — `busPairCancelPass`/`cancelLoop`/`checkCancel`/`firstMatchAt` — ever calls them; the
runtime produces the output constraint system directly). Their dense analogues
(`denseToBusState`/`denseActiveStatefulMsgs`) are therefore free-form proof-side helpers here, and
they equal `DenseConstraintSystem.sideEffects`/`admissible` (from `Dense/Bridge.lean`) definitionally
on `d.busInteractions`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Net-multiplicity bookkeeping (dense side-effect state)

`denseToBusState` is the dense mirror of the spec's proof-only `toBusState`: the stateful-bus
side-effect state of a raw dense interaction list, which is exactly what
`DenseConstraintSystem.sideEffects` computes on `d.busInteractions`. `multiplicitySum` and its
additivity `multiplicitySum_append` live over the representation-independent `BusState p`, so they
are reused unchanged from the spec. -/

/-- The stateful side-effect state of a raw dense interaction list under `denv` (what dense
    `sideEffects` computes). -/
def denseToBusState (bs : BusSemantics p) (denv : VarId → ZMod p)
    (L : List (BusInteraction (DenseExpr p))) : BusState p :=
  (L.filter (fun bi => bs.isStateful bi.busId)).map
    (fun bi => let m := denseBIEval bi denv; ((m.busId, m.payload), m.multiplicity))

theorem denseToBusState_append (bs : BusSemantics p) (denv : VarId → ZMod p)
    (L1 L2 : List (BusInteraction (DenseExpr p))) :
    denseToBusState bs denv (L1 ++ L2) = denseToBusState bs denv L1 ++ denseToBusState bs denv L2 := by
  simp only [denseToBusState, List.filter_append, List.map_append]

theorem denseToBusState_cons_stateful (bs : BusSemantics p) (denv : VarId → ZMod p)
    (bi : BusInteraction (DenseExpr p)) (L : List (BusInteraction (DenseExpr p)))
    (h : bs.isStateful bi.busId = true) :
    denseToBusState bs denv (bi :: L)
    = (let m := denseBIEval bi denv; ((m.busId, m.payload), m.multiplicity))
        :: denseToBusState bs denv L := by
  simp only [denseToBusState]
  rw [List.filter_cons_of_pos (p := fun b : BusInteraction (DenseExpr p) => bs.isStateful b.busId) h,
    List.map_cons]

/-- A list of stateless interactions contributes nothing to the dense bus state. -/
theorem denseToBusState_stateless (bs : BusSemantics p) (denv : VarId → ZMod p)
    (L : List (BusInteraction (DenseExpr p)))
    (h : ∀ bi ∈ L, bs.isStateful bi.busId = false) :
    denseToBusState bs denv L = [] := by
  unfold denseToBusState
  rw [List.filter_eq_nil_iff.mpr (fun bi hbi => by simp [h bi hbi])]
  rfl

/-- Dropping a matched send/receive pair (equal evaluated message, opposite multiplicities) leaves
    every message's net multiplicity unchanged: the `+shape.setNewMult` and `-shape.setNewMult`
    contributions cancel. Native mirror of `sideEffects_dropPair_equiv`. -/
theorem denseSideEffects_dropPair_equiv (bs : BusSemantics p) (denv : VarId → ZMod p)
    (A B C : List (BusInteraction (DenseExpr p))) (S R : BusInteraction (DenseExpr p))
    (hSstate : bs.isStateful S.busId = true) (hRstate : bs.isStateful R.busId = true)
    (hRm : (denseBIEval R denv).multiplicity = -(denseBIEval S denv).multiplicity)
    (hbusEq : (denseBIEval S denv).busId = (denseBIEval R denv).busId)
    (hpay : (denseBIEval S denv).payload = (denseBIEval R denv).payload) :
    denseToBusState bs denv (A ++ S :: B ++ R :: C) ≈ denseToBusState bs denv (A ++ B ++ C) := by
  intro msg
  have hstructFull : A ++ S :: B ++ R :: C = (A ++ S :: B) ++ (R :: C) := by
    simp only [List.append_assoc, List.cons_append]
  have hstructOut : A ++ B ++ C = (A ++ B) ++ C := rfl
  rw [hstructFull, denseToBusState_append, denseToBusState_cons_stateful bs denv R C hRstate,
    denseToBusState_append, denseToBusState_cons_stateful bs denv S B hSstate]
  rw [hstructOut, denseToBusState_append, denseToBusState_append]
  have hmsgEq : ((denseBIEval S denv).busId, (denseBIEval S denv).payload)
      = ((denseBIEval R denv).busId, (denseBIEval R denv).payload) := by rw [hbusEq, hpay]
  simp only [multiplicitySum_append, multiplicitySum, hmsgEq, hRm]
  split_ifs <;> ring

/-! ## The active∧stateful evaluated messages (what dense `admissible` inspects)

`denseActiveStatefulMsgs` is the dense mirror of the spec's proof-only `activeStatefulMsgs`: the
active, stateful evaluated messages of a raw dense interaction list — the argument dense
`admissible` passes to `bs.admissible`. Proof-only; equals `DenseConstraintSystem.admissible`'s
argument on `d.busInteractions` definitionally. -/

/-- The active, stateful evaluated messages of a raw dense interaction list. -/
def denseActiveStatefulMsgs (bs : BusSemantics p) (denv : VarId → ZMod p)
    (L : List (BusInteraction (DenseExpr p))) : List (BusInteraction (ZMod p)) :=
  (L.map (fun bi => denseBIEval bi denv)).filter
    (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)

theorem denseActiveStatefulMsgs_append (bs : BusSemantics p) (denv : VarId → ZMod p)
    (L1 L2 : List (BusInteraction (DenseExpr p))) :
    denseActiveStatefulMsgs bs denv (L1 ++ L2)
    = denseActiveStatefulMsgs bs denv L1 ++ denseActiveStatefulMsgs bs denv L2 := by
  simp only [denseActiveStatefulMsgs, List.map_append, List.filter_append]

theorem denseActiveStatefulMsgs_cons_survive (bs : BusSemantics p) (denv : VarId → ZMod p)
    (bi : BusInteraction (DenseExpr p)) (L : List (BusInteraction (DenseExpr p)))
    (h : (decide ((denseBIEval bi denv).multiplicity ≠ 0)
      && bs.isStateful (denseBIEval bi denv).busId) = true) :
    denseActiveStatefulMsgs bs denv (bi :: L)
    = denseBIEval bi denv :: denseActiveStatefulMsgs bs denv L := by
  simp only [denseActiveStatefulMsgs, List.map_cons]
  rw [List.filter_cons_of_pos
    (p := fun m : BusInteraction (ZMod p) => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) h]

theorem denseMem_activeStatefulMsgs (bs : BusSemantics p) (denv : VarId → ZMod p)
    (L : List (BusInteraction (DenseExpr p))) (m : BusInteraction (ZMod p))
    (hm : m ∈ denseActiveStatefulMsgs bs denv L) :
    ∃ m0 ∈ L, denseBIEval m0 denv = m := by
  unfold denseActiveStatefulMsgs at hm
  obtain ⟨hmem, _⟩ := List.mem_filter.mp hm
  obtain ⟨m0, hm0, hev⟩ := List.mem_map.mp hmem
  exact ⟨m0, hm0, hev⟩

/-- A split of the active∧stateful evaluated messages of `A` lifts to a syntactic split of `A`
    whose evaluated tail is the split's tail (via `filter_split` + `map_split`, reused from the
    representation-independent `MemoryBusDrop`). Lets the pass's *syntactic* shield discharge the
    `admissible_dropPair` shield stated over `denseActiveStatefulMsgs`. Native mirror of
    `activeStatefulMsgs_split`. -/
theorem denseActiveStatefulMsgs_split (bs : BusSemantics p) (denv : VarId → ZMod p)
    (A : List (BusInteraction (DenseExpr p))) (A₁ A₂ : List (BusInteraction (ZMod p)))
    (Sx : BusInteraction (ZMod p)) (h : denseActiveStatefulMsgs bs denv A = A₁ ++ Sx :: A₂) :
    ∃ (A_pre : List (BusInteraction (DenseExpr p))) (m0 : BusInteraction (DenseExpr p))
      (A_suf : List (BusInteraction (DenseExpr p))),
      A = A_pre ++ m0 :: A_suf ∧ denseBIEval m0 denv = Sx
        ∧ denseActiveStatefulMsgs bs denv A_suf = A₂ := by
  have h' : (A.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) = A₁ ++ Sx :: A₂ := h
  have hfs := filter_split (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) Sx
      (A.map (fun bi => denseBIEval bi denv)) A₁ A₂ h'
  obtain ⟨M_pre, M_suf, hmapeq, _, hMsuf⟩ := hfs
  have hms := map_split (fun bi => denseBIEval bi denv) Sx A M_pre M_suf hmapeq
  obtain ⟨A_pre, m0, A_suf, hAeq, _, hm0, hAsuf⟩ := hms
  refine ⟨A_pre, m0, A_suf, hAeq, hm0, ?_⟩
  show (A_suf.map (fun bi => denseBIEval bi denv)).filter
    (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) = A₂
  rw [hAsuf]; exact hMsuf

/-- A list of stateless interactions contributes nothing to the dense active∧stateful messages. -/
theorem denseActiveStatefulMsgs_stateless (bs : BusSemantics p) (denv : VarId → ZMod p)
    (L : List (BusInteraction (DenseExpr p)))
    (h : ∀ bi ∈ L, bs.isStateful bi.busId = false) :
    denseActiveStatefulMsgs bs denv L = [] := by
  unfold denseActiveStatefulMsgs
  apply List.filter_eq_nil_iff.mpr
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
  simp [denseBIEval, h m0 hm0]

/-! ## The core correctness of dropping a matched pair (native) -/

/-- **Native correctness of dropping one matched consecutive send/receive pair, optionally emitting
    replacement byte checks.** The exact dense mirror of `dropPair_correct`: `S` (a send) and `R` (a
    later receive) carry the same evaluated payload (`hpayEval`), are on a bus `busId` with a
    declared `shape` and a `recvByteSlots` contract whose byte obligation for `R` is justified by the
    remaining interactions *including the emitted checks* (`hbyte`, discharged by C1's
    `denseRecvSlotsJustified_sound`), with no active same-address message between them (`hmidEval`)
    and every active same-address send before `S` shielded by a later active same-address receive
    (`hpreEval`). Each emitted check is stateless, implied by `R`'s own accepted receive,
    invariant-free, and adds no `VarId`s (`hchecks`). Dropping the pair and appending the checks is
    `DensePassCorrect`. Assembled via `DensePassCorrect.ofEnvEq`, so C7's `cancelLoop` composes the
    single steps through `DensePassCorrect.andThen`. -/
theorem denseDropPair_correct (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0)
    (A B C : List (BusInteraction (DenseExpr p))) (S R : BusInteraction (DenseExpr p))
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pattern : List (Option (ZMod p))) (slots : List Nat) (bound : Nat)
    (hslots : facts.recvByteSlots busId pattern = some (slots, bound))
    (hRmatch : ∀ denv, Matches (denseBIEval R denv).payload pattern)
    (checks : List (BusInteraction (DenseExpr p)))
    (hchecks : ∀ ck ∈ checks,
      bs.isStateful ck.busId = false ∧
      (∀ denv, bs.violatesConstraint (denseBIEval R denv) = false →
        bs.violatesConstraint (denseBIEval ck denv) = false) ∧
      (∀ denv, bs.breaksInvariant (denseBIEval ck denv) = false) ∧
      (∀ v ∈ denseBIVars ck, v ∈ denseBIVars R))
    (hbyte : ∀ (denv : VarId → ZMod p),
      (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) →
      (∀ bi ∈ A ++ B ++ C ++ checks, (denseBIEval bi denv).multiplicity ≠ 0 →
        bs.violatesConstraint (denseBIEval bi denv) = false) →
      ∀ slot ∈ slots, ∀ x : ZMod p, (denseBIEval R denv).payload[slot]? = some x → x.val < bound)
    (hsplit : d.busInteractions = A ++ S :: B ++ R :: C)
    (hSbus : S.busId = busId) (hRbus : R.busId = busId)
    (hSm : S.multiplicity.constValue? = some shape.setNewMult)
    (hRm : R.multiplicity.constValue? = some (-shape.setNewMult))
    (hpayEval : ∀ (denv : VarId → ZMod p), (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) →
      (denseBIEval S denv).payload = (denseBIEval R denv).payload)
    (hmidEval : ∀ (denv : VarId → ZMod p), (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) →
        ∀ m0 ∈ B, (denseBIEval m0 denv).busId = busId →
        (denseBIEval m0 denv).multiplicity ≠ 0 →
        shape.address (denseBIEval m0 denv) = shape.address (denseBIEval S denv) → False)
    (hpreEval : ∀ (denv : VarId → ZMod p), (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) →
        ∀ (A_pre : List (BusInteraction (DenseExpr p)))
        (m0 : BusInteraction (DenseExpr p)) (A_suf : List (BusInteraction (DenseExpr p))),
        A = A_pre ++ m0 :: A_suf → (denseBIEval m0 denv).busId = busId →
        (denseBIEval m0 denv).multiplicity ≠ 0 →
        shape.address (denseBIEval m0 denv) = shape.address (denseBIEval S denv) →
        (denseBIEval m0 denv).multiplicity = shape.setNewMult →
        ∃ Rp ∈ A_suf, (denseBIEval Rp denv).busId = busId ∧ (denseBIEval Rp denv).multiplicity ≠ 0 ∧
          shape.address (denseBIEval Rp denv) = shape.address (denseBIEval S denv) ∧
          (denseBIEval Rp denv).multiplicity = -shape.setNewMult) :
    DensePassCorrect isInput d { d with busInteractions := A ++ B ++ C ++ checks } [] bs := by
  set out : DenseConstraintSystem p := { d with busInteractions := A ++ B ++ C ++ checks } with hout
  have houtb : out.busInteractions = A ++ B ++ C ++ checks := rfl
  have hchecksStateless : ∀ bi ∈ checks, bs.isStateful bi.busId = false :=
    fun bi hbi => (hchecks bi hbi).1
  have hRmem : R ∈ d.busInteractions := by
    rw [hsplit]
    exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
  -- Common facts.
  have hStateful : bs.isStateful busId = true := facts.memShape_stateful busId shape hshape
  have hSstate : bs.isStateful S.busId = true := hSbus ▸ hStateful
  have hRstate : bs.isStateful R.busId = true := hRbus ▸ hStateful
  have hSmEv : ∀ denv, (denseBIEval S denv).multiplicity = shape.setNewMult :=
    fun denv => S.multiplicity.constValue?_sound shape.setNewMult hSm denv
  have hRmEv : ∀ denv, (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    fun denv => R.multiplicity.constValue?_sound (-shape.setNewMult) hRm denv
  have hSactive : ∀ denv, (denseBIEval S denv).multiplicity ≠ 0 :=
    fun denv => by rw [hSmEv denv]; exact shape.setNewMult_ne_zero hp1
  have hRactive : ∀ denv, (denseBIEval R denv).multiplicity ≠ 0 :=
    fun denv => by rw [hRmEv denv]; exact neg_ne_zero.mpr (shape.setNewMult_ne_zero hp1)
  have haddrEv : ∀ denv, (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) →
      shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv) := fun denv hcon => by
    simp only [MemoryBusShape.address, hpayEval denv hcon]
  -- Membership: the kept core `A ++ B ++ C` is among `d`'s interactions.
  have hmem_core : ∀ bi, bi ∈ A ++ B ++ C → bi ∈ d.busInteractions := by
    intro bi hbi
    rw [hsplit]
    simp only [List.mem_append, List.mem_cons] at hbi ⊢; tauto
  -- Re-adding the dropped pair imposes no obligation: the send never violates (the
  -- `recvByteSlots` contract), and the receive's byte slots are justified from the remaining
  -- interactions, whose obligations hold under any `out`-satisfying assignment.
  have hnvS : ∀ denv, bs.violatesConstraint (denseBIEval S denv) = false := fun denv =>
    (facts.recvByteSlots_sound busId shape hshape pattern slots bound hslots (denseBIEval S denv)
      (show (denseBIEval S denv).busId = busId from hSbus)).1 (hSmEv denv)
  have hnvR : ∀ denv, out.satisfies bs denv → bs.violatesConstraint (denseBIEval R denv) = false := by
    intro denv hsat
    have hbyteEnv : ∀ slot ∈ slots, ∀ x : ZMod p, (denseBIEval R denv).payload[slot]? = some x →
        x.val < bound := by
      refine hbyte denv (fun c hc => hsat.1 c hc) ?_
      intro bi hbi hne
      exact hsat.2 bi (by rw [houtb]; exact hbi) hne
    refine (facts.recvByteSlots_sound busId shape hshape pattern slots bound hslots (denseBIEval R denv)
      (show (denseBIEval R denv).busId = busId from hRbus)).2 (hRmEv denv) (hRmatch denv) hbyteEnv
  -- Side effects are `≈`-equal (the pair contributes `0` net; the checks are stateless). The
  -- evaluated-payload equality is discharged from the constraints, which hold in **both**
  -- refinement directions — a drop leaves `algebraicConstraints` untouched.
  have hSE : ∀ denv, (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) →
      d.sideEffects bs denv ≈ out.sideEffects bs denv := by
    intro denv hcon
    have e1 : d.sideEffects bs denv = denseToBusState bs denv (A ++ S :: B ++ R :: C) := by
      show denseToBusState bs denv d.busInteractions = denseToBusState bs denv (A ++ S :: B ++ R :: C)
      rw [hsplit]
    have e2 : out.sideEffects bs denv = denseToBusState bs denv (A ++ B ++ C) := by
      show denseToBusState bs denv (A ++ B ++ C ++ checks) = denseToBusState bs denv (A ++ B ++ C)
      rw [denseToBusState_append, denseToBusState_stateless bs denv checks hchecksStateless,
        List.append_nil]
    rw [e1, e2]
    exact denseSideEffects_dropPair_equiv bs denv A B C S R hSstate hRstate
      (by rw [hRmEv denv, hSmEv denv])
      (by rw [show (denseBIEval S denv).busId = busId from hSbus,
              show (denseBIEval R denv).busId = busId from hRbus])
      (hpayEval denv hcon)
  -- `d.satisfies` implies `out.satisfies` (the kept core has fewer obligations; each emitted
  -- check is implied by `R`'s own obligation, which `d.satisfies` includes).
  have hsat_cs_out : ∀ denv, d.satisfies bs denv → out.satisfies bs denv := by
    intro denv hsat
    refine ⟨hsat.1, ?_⟩
    intro bi hbi
    rw [houtb] at hbi
    rcases List.mem_append.1 hbi with hbi | hbi
    · exact hsat.2 bi (hmem_core bi hbi)
    · exact fun _ => (hchecks bi hbi).2.1 denv (hsat.2 R hRmem (hRactive denv))
  -- `out.satisfies` implies `d.satisfies` (the extra pair never violates).
  have hsat_out_cs : ∀ denv, out.satisfies bs denv → d.satisfies bs denv := by
    intro denv hsat
    refine ⟨hsat.1, ?_⟩
    intro bi hbi
    rw [hsplit] at hbi
    simp only [List.mem_append, List.mem_cons] at hbi
    rcases hbi with (hbi | rfl | hbi) | (rfl | hbi)
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
    · exact fun _ => hnvS denv
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
    · exact fun _ => hnvR denv hsat
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
  -- `admissible` is preserved (completeness; the constraint satisfaction feeds the two-root
  -- address-disequality certificates inside the region tests).
  have hadm_cs_out : ∀ denv, d.admissible bs denv →
      (∀ c ∈ d.algebraicConstraints, c.eval denv = 0) → out.admissible bs denv := by
    intro denv hadm hcon
    have hSsurv : (decide ((denseBIEval S denv).multiplicity ≠ 0)
        && bs.isStateful (denseBIEval S denv).busId) = true := by
      rw [show bs.isStateful (denseBIEval S denv).busId = true from hSstate, Bool.and_true,
        decide_eq_true_eq]
      exact hSactive denv
    have hRsurv : (decide ((denseBIEval R denv).multiplicity ≠ 0)
        && bs.isStateful (denseBIEval R denv).busId) = true := by
      rw [show bs.isStateful (denseBIEval R denv).busId = true from hRstate, Bool.and_true,
        decide_eq_true_eq]
      exact hRactive denv
    -- Rewrite both admissible arguments into split form.
    have hasmFull : denseActiveStatefulMsgs bs denv d.busInteractions
        = denseActiveStatefulMsgs bs denv A ++ (denseBIEval S denv)
          :: denseActiveStatefulMsgs bs denv B
          ++ (denseBIEval R denv) :: denseActiveStatefulMsgs bs denv C := by
      rw [hsplit, show A ++ S :: B ++ R :: C = (A ++ S :: B) ++ (R :: C) from by
            simp only [List.append_assoc, List.cons_append],
        denseActiveStatefulMsgs_append, denseActiveStatefulMsgs_cons_survive bs denv R C hRsurv,
        denseActiveStatefulMsgs_append, denseActiveStatefulMsgs_cons_survive bs denv S B hSsurv]
    have hasmOut : denseActiveStatefulMsgs bs denv out.busInteractions
        = denseActiveStatefulMsgs bs denv A ++ denseActiveStatefulMsgs bs denv B
          ++ denseActiveStatefulMsgs bs denv C := by
      show denseActiveStatefulMsgs bs denv (A ++ B ++ C ++ checks) = _
      rw [denseActiveStatefulMsgs_append,
        denseActiveStatefulMsgs_stateless bs denv checks hchecksStateless,
        List.append_nil, denseActiveStatefulMsgs_append, denseActiveStatefulMsgs_append]
    have hadm' : bs.admissible (denseActiveStatefulMsgs bs denv A ++ (denseBIEval S denv)
        :: denseActiveStatefulMsgs bs denv B ++ (denseBIEval R denv)
          :: denseActiveStatefulMsgs bs denv C) := by
      have : bs.admissible (denseActiveStatefulMsgs bs denv d.busInteractions) := hadm
      rwa [hasmFull] at this
    show bs.admissible (denseActiveStatefulMsgs bs denv out.busInteractions)
    rw [hasmOut]
    refine facts.admissible_dropPair hp1 busId shape hshape _ _ _
      (denseBIEval S denv) (denseBIEval R denv)
      hSbus hRbus (hSmEv denv) (hRmEv denv) (haddrEv denv hcon) ?_ ?_ hadm'
    · intro m hm hbid hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := denseMem_activeStatefulMsgs bs denv B m hm
      exact hmidEval denv hcon m0 hm0 hbid hmne hmaddr
    · -- shield: lift the split of `denseActiveStatefulMsgs A` to a syntactic split of `A`, apply the
      -- syntactic shield `hpreEval`, then push the resulting receive back into the filtered tail.
      intro A₁ Sx A₂ hAsplit hbid hne haddr hmult
      obtain ⟨A_pre, m0, A_suf, hAeq, hm0, hAsuf⟩ :=
        denseActiveStatefulMsgs_split bs denv A A₁ A₂ Sx hAsplit
      subst hm0
      obtain ⟨Rp, hRpmem, hRpbid, hRpne, hRpaddr, hRpmult⟩ :=
        hpreEval denv hcon A_pre m0 A_suf hAeq hbid hne haddr hmult
      refine ⟨denseBIEval Rp denv, ?_, hRpbid, hRpne, hRpaddr, hRpmult⟩
      rw [← hAsuf]
      unfold denseActiveStatefulMsgs
      refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨Rp, hRpmem, rfl⟩, ?_⟩
      rw [show bs.isStateful (denseBIEval Rp denv).busId = true from by rw [hRpbid]; exact hStateful]
      rw [Bool.and_true, decide_eq_true_eq]; exact hRpne
  -- Variables only shrink (the pair is dropped; each emitted check's variables come from `R`).
  have hsub : ∀ i ∈ out.occ, i ∈ d.occ := by
    intro i hi
    have hi2 : i ∈ d.algebraicConstraints.flatMap DenseExpr.vars
        ++ (A ++ B ++ C ++ checks).flatMap denseBIVars := hi
    rw [List.mem_append] at hi2
    rcases hi2 with hi2 | hi2
    · rw [List.mem_flatMap] at hi2
      obtain ⟨c, hc, hic⟩ := hi2
      exact DenseConstraintSystem.mem_occ_of_constraint hc hic
    · rw [List.mem_flatMap] at hi2
      obtain ⟨bi, hbi, hibi⟩ := hi2
      rcases List.mem_append.1 hbi with hbi' | hbi'
      · exact DenseConstraintSystem.mem_occ_of_bi (hmem_core bi hbi') hibi
      · exact DenseConstraintSystem.mem_occ_of_bi hRmem ((hchecks bi hbi').2.2.2 i hibi)
  -- Assemble via `ofEnvEq` (completeness witness is the input assignment; no derivations).
  exact DensePassCorrect.ofEnvEq
    (fun denv hsat => ⟨denv, hsat_out_cs denv hsat, BusState.equiv_symm (hSE denv hsat.1)⟩)
    (fun hinv denv hsat bi hbi => by
      rcases List.mem_append.1 (by rw [houtb] at hbi; exact hbi) with hbi' | hbi'
      · exact hinv denv (hsat_out_cs denv hsat) bi (hmem_core bi hbi')
      · exact fun _ => (hchecks bi hbi').2.2.1 denv)
    hsub
    (fun denv hadm hsat => ⟨hsat_cs_out denv hsat, hadm_cs_out denv hadm hsat.1, hSE denv hsat.1⟩)

end ApcOptimizer.Dense
