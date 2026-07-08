import Leanr.Implementation.OptimizerPasses.BusUnify
import Leanr.Implementation.MemoryBusDrop

set_option autoImplicit false

/-! # Cancelling matched send/receive pairs on a memory bus

After `busUnifyPass` and the affine/Gauss machinery, a memory access chain leaves the bus with a
*send* `S` (multiplicity `1`) and a later *receive* `R` (multiplicity `-1`) carrying the **same
payload** — the write of one access and the read of the next, unified to the same tuple. These two
messages have opposite multiplicity on the same tuple, so they contribute `0` to every message's
net multiplicity: dropping **both** leaves the bus state (`≈`) unchanged and shrinks the circuit.
It is exactly powdr's memory-interaction cancellation.

Under the frozen spec this is sound because:

* **soundness** (`out.implies cs`): the dropped pair is on a `neverViolates` bus, so re-adding it to
  reach a witness of `cs` imposes no obligation, and the pair's net side-effect contribution is `0`;
* **completeness** (`cs.impliesAdmissible out`): removing the pair preserves the VM's `admissible`
  predicate (`admissible_dropPair`), provided `S` is the *earliest* active send to its address —
  otherwise the removal could expose a fresh consecutive send→receive pair with mismatched payloads.
  This side condition holds for the standard receive-before-send access discipline. -/

variable {p : ℕ}

/-! ## Net-multiplicity bookkeeping -/

/-- Net multiplicity is additive over concatenation of bus states. -/
theorem multiplicitySum_append (msg : BusMessage p) (s t : BusState p) :
    multiplicitySum msg (s ++ t) = multiplicitySum msg s + multiplicitySum msg t := by
  induction s with
  | nil => simp [multiplicitySum]
  | cons hd tl ih =>
      simp only [List.cons_append, multiplicitySum, ih]
      ring

/-- The stateful side-effect state of a raw interaction list under `env` (what `sideEffects`
    computes). -/
def toBusState (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p))) : BusState p :=
  (L.filter (fun bi => bs.isStateful bi.busId)).map
    (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity))

theorem toBusState_append (bs : BusSemantics p) (env : Variable → ZMod p)
    (L1 L2 : List (BusInteraction (Expression p))) :
    toBusState bs env (L1 ++ L2) = toBusState bs env L1 ++ toBusState bs env L2 := by
  simp only [toBusState, List.filter_append, List.map_append]

theorem toBusState_cons_stateful (bs : BusSemantics p) (env : Variable → ZMod p)
    (bi : BusInteraction (Expression p)) (L : List (BusInteraction (Expression p)))
    (h : bs.isStateful bi.busId = true) :
    toBusState bs env (bi :: L)
    = (let m := bi.eval env; ((m.busId, m.payload), m.multiplicity)) :: toBusState bs env L := by
  simp only [toBusState]
  rw [List.filter_cons_of_pos (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) h,
    List.map_cons]

/-- Dropping a matched send/receive pair (equal evaluated message, opposite multiplicities) leaves
    every message's net multiplicity unchanged: the `+1` and `-1` contributions cancel. -/
theorem sideEffects_dropPair_equiv (bs : BusSemantics p) (env : Variable → ZMod p)
    (A B C : List (BusInteraction (Expression p))) (S R : BusInteraction (Expression p))
    (hSstate : bs.isStateful S.busId = true) (hRstate : bs.isStateful R.busId = true)
    (hSm : (S.eval env).multiplicity = 1) (hRm : (R.eval env).multiplicity = -1)
    (hbusEq : (S.eval env).busId = (R.eval env).busId)
    (hpay : (S.eval env).payload = (R.eval env).payload) :
    toBusState bs env (A ++ S :: B ++ R :: C) ≈ toBusState bs env (A ++ B ++ C) := by
  intro msg
  have hstructFull : A ++ S :: B ++ R :: C = (A ++ S :: B) ++ (R :: C) := by
    simp only [List.append_assoc, List.cons_append]
  have hstructOut : A ++ B ++ C = (A ++ B) ++ C := rfl
  rw [hstructFull, toBusState_append, toBusState_cons_stateful bs env R C hRstate,
    toBusState_append, toBusState_cons_stateful bs env S B hSstate]
  rw [hstructOut, toBusState_append, toBusState_append]
  have hmsgEq : ((S.eval env).busId, (S.eval env).payload)
      = ((R.eval env).busId, (R.eval env).payload) := by rw [hbusEq, hpay]
  simp only [multiplicitySum_append, multiplicitySum, hmsgEq, hSm, hRm]
  split_ifs <;> ring

/-! ## The active∧stateful evaluated messages (what `admissible` inspects) -/

/-- The active, stateful evaluated messages of a raw interaction list — the argument
    `ConstraintSystem.admissible` passes to `bs.admissible`. -/
def activeStatefulMsgs (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p))) : List (BusInteraction (ZMod p)) :=
  (L.map (fun bi => bi.eval env)).filter
    (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)

theorem activeStatefulMsgs_append (bs : BusSemantics p) (env : Variable → ZMod p)
    (L1 L2 : List (BusInteraction (Expression p))) :
    activeStatefulMsgs bs env (L1 ++ L2)
    = activeStatefulMsgs bs env L1 ++ activeStatefulMsgs bs env L2 := by
  simp only [activeStatefulMsgs, List.map_append, List.filter_append]

theorem activeStatefulMsgs_cons_survive (bs : BusSemantics p) (env : Variable → ZMod p)
    (bi : BusInteraction (Expression p)) (L : List (BusInteraction (Expression p)))
    (h : (decide ((bi.eval env).multiplicity ≠ 0) && bs.isStateful (bi.eval env).busId) = true) :
    activeStatefulMsgs bs env (bi :: L) = bi.eval env :: activeStatefulMsgs bs env L := by
  simp only [activeStatefulMsgs, List.map_cons]
  rw [List.filter_cons_of_pos
    (p := fun m : BusInteraction (ZMod p) => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) h]

theorem mem_activeStatefulMsgs (bs : BusSemantics p) (env : Variable → ZMod p)
    (L : List (BusInteraction (Expression p))) (m : BusInteraction (ZMod p))
    (hm : m ∈ activeStatefulMsgs bs env L) :
    ∃ m0 ∈ L, m0.eval env = m := by
  unfold activeStatefulMsgs at hm
  obtain ⟨hmem, _⟩ := List.mem_filter.mp hm
  obtain ⟨m0, hm0, hev⟩ := List.mem_map.mp hmem
  exact ⟨m0, hm0, hev⟩

/-! ## The core correctness of dropping a matched pair -/

/-- **Correctness of dropping one matched consecutive send/receive pair.** `S` (a send) and `R`
    (a later receive) carry the same payload (`hpay`), are on a `neverViolates` bus `busId` with a
    declared `shape`, with no active same-address message between them (`hmidEval`) and no active
    same-address send before `S` (`hpreEval`). Dropping both is `PassCorrect`. -/
theorem dropPair_correct (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0)
    (A B C : List (BusInteraction (Expression p))) (S R : BusInteraction (Expression p))
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (hnv : facts.neverViolates busId = true)
    (hsplit : cs.busInteractions = A ++ S :: B ++ R :: C)
    (hSbus : S.busId = busId) (hRbus : R.busId = busId)
    (hSm : S.multiplicity.constValue? = some 1) (hRm : R.multiplicity.constValue? = some (-1))
    (hpay : S.payload = R.payload)
    (hmidEval : ∀ (env : Variable → ZMod p), ∀ m0 ∈ B, (m0.eval env).busId = busId →
        (m0.eval env).multiplicity ≠ 0 →
        shape.address (m0.eval env) = shape.address (S.eval env) → False)
    (hpreEval : ∀ (env : Variable → ZMod p), ∀ m0 ∈ A, (m0.eval env).busId = busId →
        (m0.eval env).multiplicity ≠ 0 →
        shape.address (m0.eval env) = shape.address (S.eval env) → (m0.eval env).multiplicity ≠ 1) :
    PassCorrect cs { cs with busInteractions := A ++ B ++ C } [] bs := by
  set out : ConstraintSystem p := { cs with busInteractions := A ++ B ++ C } with hout
  have houtb : out.busInteractions = A ++ B ++ C := rfl
  -- Common facts.
  have hStateful : bs.isStateful busId = true := facts.memShape_stateful busId shape hshape
  have hSstate : bs.isStateful S.busId = true := hSbus ▸ hStateful
  have hRstate : bs.isStateful R.busId = true := hRbus ▸ hStateful
  have hSmEv : ∀ env, (S.eval env).multiplicity = 1 :=
    fun env => S.multiplicity.constValue?_sound 1 hSm env
  have hRmEv : ∀ env, (R.eval env).multiplicity = -1 :=
    fun env => R.multiplicity.constValue?_sound (-1) hRm env
  have hSactive : ∀ env, (S.eval env).multiplicity ≠ 0 := fun env => by rw [hSmEv env]; exact hp1
  have hRactive : ∀ env, (R.eval env).multiplicity ≠ 0 :=
    fun env => by rw [hRmEv env]; exact neg_ne_zero.mpr hp1
  have hpayEv : ∀ env, (S.eval env).payload = (R.eval env).payload := fun env => by
    show S.payload.map (fun e => e.eval env) = R.payload.map (fun e => e.eval env); rw [hpay]
  have haddrEv : ∀ env, shape.address (S.eval env) = shape.address (R.eval env) := fun env => by
    simp only [MemoryBusShape.address, hpayEv env]
  -- Membership: `out`'s interactions are among `cs`'s.
  have hmem_out_cs : ∀ bi, bi ∈ out.busInteractions → bi ∈ cs.busInteractions := by
    intro bi hbi
    rw [houtb] at hbi
    rw [hsplit]
    simp only [List.mem_append, List.mem_cons] at hbi ⊢; tauto
  -- The dropped pair never violates.
  have hnvS : ∀ env, bs.violatesConstraint (S.eval env) = false := fun env =>
    facts.neverViolates_sound (S.eval env) (by show facts.neverViolates S.busId = true; rw [hSbus]; exact hnv)
  have hnvR : ∀ env, bs.violatesConstraint (R.eval env) = false := fun env =>
    facts.neverViolates_sound (R.eval env) (by show facts.neverViolates R.busId = true; rw [hRbus]; exact hnv)
  -- Side effects are `≈`-equal (the pair contributes `0` net).
  have hSE : ∀ env, cs.sideEffects bs env ≈ out.sideEffects bs env := by
    intro env
    have e1 : cs.sideEffects bs env = toBusState bs env (A ++ S :: B ++ R :: C) := by
      show toBusState bs env cs.busInteractions = toBusState bs env (A ++ S :: B ++ R :: C)
      rw [hsplit]
    have e2 : out.sideEffects bs env = toBusState bs env (A ++ B ++ C) := rfl
    rw [e1, e2]
    exact sideEffects_dropPair_equiv bs env A B C S R hSstate hRstate (hSmEv env) (hRmEv env)
      (by rw [show (S.eval env).busId = busId from hSbus, show (R.eval env).busId = busId from hRbus])
      (hpayEv env)
  -- `cs.satisfies` implies `out.satisfies` (out has fewer obligations).
  have hsat_cs_out : ∀ env, cs.satisfies bs env → out.satisfies bs env := by
    intro env hsat
    refine ⟨hsat.1, fun bi hbi => hsat.2 bi (hmem_out_cs bi hbi)⟩
  -- `out.satisfies` implies `cs.satisfies` (the extra pair never violates).
  have hsat_out_cs : ∀ env, out.satisfies bs env → cs.satisfies bs env := by
    intro env hsat
    refine ⟨hsat.1, ?_⟩
    intro bi hbi
    rw [hsplit] at hbi
    simp only [List.mem_append, List.mem_cons] at hbi
    rcases hbi with (hbi | rfl | hbi) | (rfl | hbi)
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
    · exact fun _ => hnvS env
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
    · exact fun _ => hnvR env
    · exact hsat.2 bi (by rw [houtb]; simp only [List.mem_append]; tauto)
  -- `admissible` is preserved (completeness).
  have hadm_cs_out : ∀ env, cs.admissible bs env → out.admissible bs env := by
    intro env hadm
    have hSsurv : (decide ((S.eval env).multiplicity ≠ 0) && bs.isStateful (S.eval env).busId) = true := by
      rw [show bs.isStateful (S.eval env).busId = true from hSstate, Bool.and_true, decide_eq_true_eq]
      exact hSactive env
    have hRsurv : (decide ((R.eval env).multiplicity ≠ 0) && bs.isStateful (R.eval env).busId) = true := by
      rw [show bs.isStateful (R.eval env).busId = true from hRstate, Bool.and_true, decide_eq_true_eq]
      exact hRactive env
    -- Rewrite both admissible arguments into split form.
    have hasmFull : activeStatefulMsgs bs env cs.busInteractions
        = activeStatefulMsgs bs env A ++ (S.eval env) :: activeStatefulMsgs bs env B
          ++ (R.eval env) :: activeStatefulMsgs bs env C := by
      rw [hsplit, show A ++ S :: B ++ R :: C = (A ++ S :: B) ++ (R :: C) from by
            simp only [List.append_assoc, List.cons_append],
        activeStatefulMsgs_append, activeStatefulMsgs_cons_survive bs env R C hRsurv,
        activeStatefulMsgs_append, activeStatefulMsgs_cons_survive bs env S B hSsurv]
    have hasmOut : activeStatefulMsgs bs env out.busInteractions
        = activeStatefulMsgs bs env A ++ activeStatefulMsgs bs env B
          ++ activeStatefulMsgs bs env C := by
      show activeStatefulMsgs bs env (A ++ B ++ C) = _
      rw [show A ++ B ++ C = (A ++ B) ++ C from rfl, activeStatefulMsgs_append,
        activeStatefulMsgs_append]
    have hadm' : bs.admissible (activeStatefulMsgs bs env A ++ (S.eval env)
        :: activeStatefulMsgs bs env B ++ (R.eval env) :: activeStatefulMsgs bs env C) := by
      have : bs.admissible (activeStatefulMsgs bs env cs.busInteractions) := hadm
      rwa [hasmFull] at this
    show bs.admissible (activeStatefulMsgs bs env out.busInteractions)
    rw [hasmOut]
    refine facts.admissible_dropPair hp1 busId shape hshape _ _ _ (S.eval env) (R.eval env)
      hSbus hRbus (hSmEv env) (hRmEv env) (haddrEv env) ?_ ?_ hadm'
    · intro m hm hbid hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := mem_activeStatefulMsgs bs env B m hm
      exact hmidEval env m0 hm0 hbid hmne hmaddr
    · intro m hm hbid hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := mem_activeStatefulMsgs bs env A m hm
      exact hpreEval env m0 hm0 hbid hmne hmaddr
  -- Variables only shrink (the pair is dropped, no new variables introduced).
  have hsub : ∀ v ∈ out.vars, v ∈ cs.vars := by
    intro v hv
    rw [ConstraintSystem.mem_vars] at hv ⊢
    rcases hv with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hbiv⟩
    · exact Or.inl ⟨c, hc, hvc⟩
    · exact Or.inr ⟨bi, hmem_out_cs bi hbi, hbiv⟩
  -- Assemble via `ofEnvEq` (completeness witness is the input assignment; no derivations).
  exact PassCorrect.ofEnvEq
    (fun env hsat => ⟨env, hsat_out_cs env hsat, BusState.equiv_symm (hSE env)⟩)
    (fun hinv env hsat bi hbi => hinv env (hsat_out_cs env hsat) bi (hmem_out_cs bi hbi))
    hsub
    (fun env hadm hsat => ⟨hsat_cs_out env hsat, hadm_cs_out env hadm, hSE env⟩)

/-! ## The pass: detect and drop matched pairs -/

/-- Scan for the first matching receive `R` for a send `S`: constant `-1` multiplicity, on `busId`,
    carrying `S`'s payload. Returns `(B, R, C)` — the scanned prefix `B`, the receive `R`, and the
    remainder `C`. -/
def findMatchRecv (busId : Nat) (S : BusInteraction (Expression p)) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    Option (List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)))
  | _, [] => none
  | revB, R :: rest =>
      if decide (multConst R = some (-1)) && decide (R.busId = busId)
         && decide (S.payload = R.payload) then
        some (revB.reverse, R, rest)
      else findMatchRecv busId S (R :: revB) rest

/-- Refute `m` as an active same-address message on `busId` (the "between" region test). -/
def midRefuted (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p)) : Bool :=
  decide (m.busId ≠ busId) || decide (multConst m = some 0) || addrConstsNeq shape S m

/-- Refute `m` as an active same-address *send* on `busId` (the "before" region test: earliest-send). -/
def preRefuted (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p)) : Bool :=
  midRefuted shape busId S m ||
    (match multConst m with | some c => decide (c ≠ 1) | none => false)

theorem midRefuted_sound (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p))
    (h : midRefuted shape busId S m = true) (env : Variable → ZMod p)
    (hbid : (m.eval env).busId = busId) (hmne : (m.eval env).multiplicity ≠ 0)
    (hmaddr : shape.address (m.eval env) = shape.address (S.eval env)) : False := by
  unfold midRefuted at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact absurd hbid (of_decide_eq_true h)
  · exact hmne (m.multiplicity.constValue?_sound 0 (of_decide_eq_true h) env)
  · exact addrConstsNeq_sound shape S m h env hmaddr.symm

theorem preRefuted_sound (shape : MemoryBusShape) (busId : Nat) (S m : BusInteraction (Expression p))
    (h : preRefuted shape busId S m = true) (env : Variable → ZMod p)
    (hbid : (m.eval env).busId = busId) (hmne : (m.eval env).multiplicity ≠ 0)
    (hmaddr : shape.address (m.eval env) = shape.address (S.eval env)) :
    (m.eval env).multiplicity ≠ 1 := by
  unfold preRefuted at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact (midRefuted_sound shape busId S m h env hbid hmne hmaddr).elim
  · cases hc : multConst m with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      have heval : (m.eval env).multiplicity = c := m.multiplicity.constValue?_sound c hc env
      rw [heval]
      exact of_decide_eq_true h

/-- The per-candidate check (address/multiplicity/payload of the pair, plus the between/before
    region tests). The split equation `cs.busInteractions = A ++ S :: B ++ R :: C` is *not* checked
    here — it is supplied separately (decided once for the chosen candidate) to avoid an O(n)
    whole-list comparison per candidate. -/
def checkCancel (shape : MemoryBusShape) (busId : Nat)
    (A : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (B : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p)) : Bool :=
  decide (S.busId = busId) && decide (R.busId = busId) &&
  decide (multConst S = some 1) && decide (multConst R = some (-1)) &&
  decide (S.payload = R.payload) &&
  B.all (midRefuted shape busId S) &&
  A.all (preRefuted shape busId S)

/-- A passing `checkCancel` (with the split equation) yields `PassCorrect` via `dropPair_correct`. -/
theorem checkCancel_sound (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape) (hnv : facts.neverViolates busId = true)
    (A : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (B : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p))
    (C : List (BusInteraction (Expression p)))
    (hsplit : cs.busInteractions = A ++ S :: B ++ R :: C)
    (h : checkCancel shape busId A S B R = true) :
    PassCorrect cs { cs with busInteractions := A ++ B ++ C } [] bs := by
  unfold checkCancel at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hSb, hRb⟩, hSm⟩, hRm⟩, hpay⟩, hmid⟩, hpre⟩ := h
  refine dropPair_correct cs bs facts hp1 A B C S R busId shape hshape hnv hsplit
    (of_decide_eq_true hSb) (of_decide_eq_true hRb)
    (of_decide_eq_true hSm) (of_decide_eq_true hRm) (of_decide_eq_true hpay) ?_ ?_
  · intro env m0 hm0 hbid hmne hmaddr
    exact midRefuted_sound shape busId S m0 (List.all_eq_true.mp hmid m0 hm0) env hbid hmne hmaddr
  · intro env m0 hm0 hbid hmne hmaddr
    exact preRefuted_sound shape busId S m0 (List.all_eq_true.mp hpre m0 hm0) env hbid hmne hmaddr

/-- Fused left-to-right scan for the first droppable pair on `busId`: at each send `S` (accumulating
    the reversed prefix `revA`), find its matching receive and run the cheap `checkCancel`; the O(n)
    split-equation decide runs only when `checkCancel` passes. Stops at the first hit, so each pass
    invocation is linear (no eager materialization of all candidates). -/
def findCancelGo (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape) (hnv : facts.neverViolates busId = true)
    (revA : List (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) →
    Option (PassResult cs bs)
  | [] => none
  | S :: rest =>
    if decide (multConst S = some 1) && decide (S.busId = busId) then
      match findMatchRecv busId S [] rest with
      | some (B, R, C) =>
        if hchk : checkCancel shape busId revA.reverse S B R = true then
          if hsplit : cs.busInteractions = revA.reverse ++ S :: B ++ R :: C then
            some ⟨{ cs with busInteractions := revA.reverse ++ B ++ C }, [],
                  checkCancel_sound cs bs facts hp1 busId shape hshape hnv revA.reverse S B R C
                    hsplit hchk⟩
          else findCancelGo cs bs facts hp1 busId shape hshape hnv (S :: revA) rest
        else findCancelGo cs bs facts hp1 busId shape hshape hnv (S :: revA) rest
      | none => findCancelGo cs bs facts hp1 busId shape hshape hnv (S :: revA) rest
    else findCancelGo cs bs facts hp1 busId shape hshape hnv (S :: revA) rest

/-- Search one declared bus for a droppable pair. -/
def findCancelForBus (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape) (hnv : facts.neverViolates busId = true) :
    Option (PassResult cs bs) :=
  findCancelGo cs bs facts hp1 busId shape hshape hnv [] cs.busInteractions

/-- Search all declared buses. -/
def findCancel (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) :
    List Nat → Option (PassResult cs bs)
  | [] => none
  | busId :: rest =>
    match hshape : facts.memShape busId with
    | some shape =>
      if hnv : facts.neverViolates busId = true then
        match findCancelForBus cs bs facts hp1 busId shape hshape hnv with
        | some r => some r
        | none => findCancel cs bs facts hp1 rest
      else findCancel cs bs facts hp1 rest
    | none => findCancel cs bs facts hp1 rest

/-- Drop one matched consecutive send/receive pair on a declared, `neverViolates` memory bus. The
    cleanup loop iterates it to cancel a whole access chain. -/
def busPairCancelPass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    match findCancel cs bs facts hp1 ((cs.busInteractions.map (fun bi => bi.busId)).dedup) with
    | some r => r
    | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
