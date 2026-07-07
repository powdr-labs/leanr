import Leanr.Implementation.OptimizerPasses.MemoryUnify
import Leanr.MemoryBus

set_option autoImplicit false

/-! # Unified consecutive-match bus unification (one pass for memory *and* the execution bridge)

The abstract `admissible` spec — *consecutive same-address send→receive pairs match*
(`admissibleMemoryBus`) — collapses what used to be three passes (`memoryUnifyBatchPass`,
`execChainPass`, `chainUnifyPass`) into **one**. For every declared last-write-wins bus (memory,
or the empty-address execution bridge), each active send `S` and the next active same-address
message — a receive `R`, with no active same-address message between them — satisfy
`S.payload = R.payload` by `admissibleMemoryBus.consecutive`. This pass adds those slot equalities
(`memEqConstraints`), which the affine/domain machinery then propagates.

The execution bridge is the empty-address special case (its consecutive pairs are list-adjacent);
whole same-address chains are just "all consecutive pairs". Constant addresses/multiplicities are
required to certify the match positionally (same limitation as the old passes). -/

variable {p : ℕ}

/-! ## Address inequality (companion to `addrConstsEq`) -/

/-- Some address slot carries provably-different constants: the two interactions provably have
    different addresses. -/
def addrConstsNeq (shape : MemoryBusShape) (S bi : BusInteraction (Expression p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' =>
      (match e.constValue?, e'.constValue? with
       | some c, some c' => decide (c ≠ c')
       | _, _ => false)
    | _, _ => false)

theorem addrConstsNeq_sound (shape : MemoryBusShape) (S bi : BusInteraction (Expression p))
    (h : addrConstsNeq shape S bi = true) (env : String → ZMod p) :
    shape.address (S.eval env) ≠ shape.address (bi.eval env) := by
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  intro heq
  -- the address projections agree at `slot`'s position
  obtain ⟨j, hj⟩ : ∃ j, shape.addressFields[j]? = some slot := List.getElem?_of_mem hslot
  have key : (S.eval env).payload[slot]? = (bi.eval env).payload[slot]? := by
    have e1 : (shape.address (S.eval env))[j]? = some ((S.eval env).payload[slot]?) := by
      simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
    have e2 : (shape.address (bi.eval env))[j]? = some ((bi.eval env).payload[slot]?) := by
      simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
    rw [heq, e2] at e1; exact (Option.some.inj e1).symm
  have keyS : (S.eval env).payload[slot]? = (S.payload[slot]?).map (fun e => e.eval env) := by
    show (S.payload.map (fun e => e.eval env))[slot]? = _; rw [List.getElem?_map]
  have keyB : (bi.eval env).payload[slot]? = (bi.payload[slot]?).map (fun e => e.eval env) := by
    show (bi.payload.map (fun e => e.eval env))[slot]? = _; rw [List.getElem?_map]
  rw [keyS, keyB] at key
  -- unpack the differing constant slot and contradict `key`
  cases hSp : S.payload[slot]? with
  | none => simp [hSp] at hcond
  | some e =>
    cases hbp : bi.payload[slot]? with
    | none => simp [hSp, hbp] at hcond
    | some e' =>
      simp only [hSp, hbp, Option.map_some, Option.some.injEq] at key
      cases hc : e.constValue? with
      | none => simp [hSp, hbp, hc] at hcond
      | some c =>
        cases hc' : e'.constValue? with
        | none => simp [hSp, hbp, hc, hc'] at hcond
        | some c' =>
          simp only [hSp, hbp, hc, hc'] at hcond
          exact of_decide_eq_true hcond (by
            rw [← e.constValue?_sound c hc env, ← e'.constValue?_sound c' hc' env]; exact key)

/-! ## The `admissible` → payload-equality bridge -/

/-- Filtering evaluated messages by bus id equals evaluating the bus-filtered interactions
    (evaluation preserves the bus id). -/
theorem map_eval_filter_busId (l : List (BusInteraction (Expression p))) (busId : Nat)
    (env : String → ZMod p) :
    (l.map (fun bi => bi.eval env)).filter (fun m => m.busId = busId)
    = (l.filter (fun bi => bi.busId = busId)).map (fun bi => bi.eval env) := by
  induction l with
  | nil => rfl
  | cons bi rest ih =>
    have hbid : (bi.eval env).busId = bi.busId := rfl
    simp only [List.map_cons, List.filter_cons, hbid]
    by_cases h : bi.busId = busId
    · simp [h, ih]
    · simp [h, ih]

/-- From the VM's `admissible` predicate, a send `S` followed by a receive `R` to the same
    address in the bus's interaction list, with no active same-address message strictly between,
    have equal evaluated payloads (`admissibleMemoryBus.consecutive`). -/
theorem consecutivePayloadEq (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (env : String → ZMod p)
    (hadm : cs.admissible bs env)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre mid post : List (BusInteraction (Expression p)))
    (S R : BusInteraction (Expression p))
    (hsplit : cs.busInteractions.filter (fun bi => bi.busId = busId) = pre ++ S :: mid ++ R :: post)
    (hS : (S.eval env).multiplicity = 1) (hR : (R.eval env).multiplicity = -1)
    (haddr : shape.address (S.eval env) = shape.address (R.eval env))
    (hmid : ∀ m ∈ mid, (m.eval env).multiplicity ≠ 0 →
        shape.address (m.eval env) = shape.address (S.eval env) → False) :
    (S.eval env).payload = (R.eval env).payload := by
  have hadm' : bs.admissible ((cs.busInteractions.map (fun bi => bi.eval env)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
  have hb := facts.admissible_sound (cs.busInteractions.map (fun bi => bi.eval env)) hadm'
    busId shape hshape
  rw [map_eval_filter_busId, hsplit, List.map_append, List.map_cons, List.map_append,
    List.map_cons] at hb
  exact admissibleMemoryBus.consecutive shape _ hp1 hb
    (pre.map (fun bi => bi.eval env)) (mid.map (fun bi => bi.eval env))
    (post.map (fun bi => bi.eval env)) (S.eval env) (R.eval env) rfl hS hR haddr
    (by
      intro m hm hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
      exact hmid m0 hm0 hmne hmaddr)

/-! ## The checked pair and its entailment -/

/-- A checked consecutive send→receive pair on bus `busId`: `L` splits as `pre ++ S :: mid ++ R
    :: post`, `S` a constant send, `R` a constant receive, same constant address, and every `mid`
    message is provably inactive or of a different address. -/
def checkPair (shape : MemoryBusShape) (L : List (BusInteraction (Expression p)))
    (pre : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (mid : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p))
    (post : List (BusInteraction (Expression p))) : Bool :=
  decide (L = pre ++ S :: mid ++ R :: post) &&
  decide (multConst S = some 1) && decide (multConst R = some (-1)) &&
  addrConstsEq shape S R &&
  mid.all (fun m => addrConstsNeq shape S m || decide (multConst m = some 0))

theorem checkPair_sound (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (mid : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p))
    (post : List (BusInteraction (Expression p)))
    (hchk : checkPair shape (cs.busInteractions.filter (fun bi => bi.busId = busId))
      pre S mid R post = true)
    (env : String → ZMod p) (hadm : cs.admissible bs env) :
    ∀ c ∈ memEqConstraints shape S R, c.eval env = 0 := by
  unfold checkPair at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hspl, hSm⟩, hRm⟩, haddrEq⟩, hmidall⟩ := hchk
  have hsplit : cs.busInteractions.filter (fun bi => bi.busId = busId)
      = pre ++ S :: mid ++ R :: post := of_decide_eq_true hspl
  have hSm : multConst S = some 1 := of_decide_eq_true hSm
  have hRm : multConst R = some (-1) := of_decide_eq_true hRm
  have hSev : (S.eval env).multiplicity = 1 := by
    show S.multiplicity.eval env = 1; exact S.multiplicity.constValue?_sound 1 hSm env
  have hRev : (R.eval env).multiplicity = -1 := by
    show R.multiplicity.eval env = -1; exact R.multiplicity.constValue?_sound (-1) hRm env
  have haddr : shape.address (S.eval env) = shape.address (R.eval env) :=
    addrConstsEq_sound shape S R haddrEq env
  have hmid : ∀ m ∈ mid, (m.eval env).multiplicity ≠ 0 →
      shape.address (m.eval env) = shape.address (S.eval env) → False := by
    intro m hm hmne hmaddr
    rcases (Bool.or_eq_true _ _).mp (List.all_eq_true.mp hmidall m hm) with hneq | hz
    · exact addrConstsNeq_sound shape S m hneq env (hmaddr.symm)
    · have : (m.eval env).multiplicity = 0 := by
        show m.multiplicity.eval env = 0
        exact m.multiplicity.constValue?_sound 0 (of_decide_eq_true hz) env
      exact hmne this
  have hpay : (S.eval env).payload = (R.eval env).payload :=
    consecutivePayloadEq cs bs facts hp1 env hadm busId shape hshape pre mid post S R
      hsplit hSev hRev haddr hmid
  intro c hc
  unfold memEqConstraints at hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
  rw [eqExpr_eval]
  have hPQ : R.payload.map (fun e => e.eval env) = S.payload.map (fun e => e.eval env) := by
    have h1 : (R.eval env).payload = R.payload.map (fun e => e.eval env) := rfl
    have h2 : (S.eval env).payload = S.payload.map (fun e => e.eval env) := rfl
    rw [← h1, ← h2, hpay]
  rw [payloadSlot_eval_eq R.payload S.payload env hPQ i, sub_self]

/-! ## The pass -/

/-- Scan forward from a send `S` for its consumer: the first same-address receive, with every
    message before it excludable (different address, or inactive). Returns `(mid, R, post)` on
    success; `none` if a possibly-same-address active non-receive blocks the window. -/
def findConsumer (shape : MemoryBusShape) (S : BusInteraction (Expression p)) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    Option (List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)))
  | _, [] => none
  | revMid, r :: rest =>
      if decide (multConst r = some (-1)) && addrConstsEq shape S r then
        some (revMid.reverse, r, rest)
      else if addrConstsNeq shape S r || decide (multConst r = some 0) then
        findConsumer shape S (r :: revMid) rest
      else none

/-- One candidate `(pre, S, mid, R, post)` per active send `S`, pairing it with its consumer
    receive (`findConsumer`). Linear in the number of sends × scan length, so no O(n²) blow-up
    on large buses. `checkPair` re-verifies each candidate. -/
def candidateSplits (shape : MemoryBusShape) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    List (List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)))
  | _, [] => []
  | revPre, S :: rest =>
      (if decide (multConst S = some 1) then
        match findConsumer shape S [] rest with
        | some (mid, R, post) => [(revPre.reverse, S, mid, R, post)]
        | none => []
       else []) ++ candidateSplits shape (S :: revPre) rest

/-- Collect the entailed equalities for one bus, with proof. -/
def collectForBus (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape) :
    List (List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p))) →
    { out : List (Expression p) //
        ∀ env, cs.admissible bs env → cs.satisfies bs env → ∀ c ∈ out, c.eval env = 0 }
  | [] => ⟨[], fun _ _ _ _ h => absurd h (by simp)⟩
  | (pre, S, mid, R, post) :: rest =>
    let ⟨acc, hacc⟩ := collectForBus cs bs facts hp1 busId shape hshape rest
    if hchk : checkPair shape (cs.busInteractions.filter (fun bi => bi.busId = busId))
        pre S mid R post = true then
      ⟨memEqConstraints shape S R ++ acc, by
        intro env hadm hsat c hc
        rcases List.mem_append.1 hc with h | h
        · exact checkPair_sound cs bs facts hp1 busId shape hshape pre S mid R post hchk env hadm c h
        · exact hacc env hadm hsat c h⟩
    else ⟨acc, hacc⟩

/-- Collect over every declared bus, with proof. -/
def collectAllBuses (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) :
    List Nat →
    { out : List (Expression p) //
        ∀ env, cs.admissible bs env → cs.satisfies bs env → ∀ c ∈ out, c.eval env = 0 }
  | [] => ⟨[], fun _ _ _ _ h => absurd h (by simp)⟩
  | busId :: rest =>
    let ⟨acc, hacc⟩ := collectAllBuses cs bs facts hp1 rest
    match hshape : facts.memShape busId with
    | some shape =>
      let ⟨eqs, heqs⟩ := collectForBus cs bs facts hp1 busId shape hshape
        (candidateSplits shape [] (cs.busInteractions.filter (fun bi => bi.busId = busId)))
      ⟨eqs ++ acc, by
        intro env hadm hsat c hc
        rcases List.mem_append.1 hc with h | h
        · exact heqs env hadm hsat c h
        · exact hacc env hadm hsat c h⟩
    | none => ⟨acc, hacc⟩

/-- The unified bus-unification pass: add the entailed consecutive send→receive slot equalities
    for every declared memory / execution-bridge bus (skipping equations already present or
    trivially zero). Replaces `memoryUnifyBatchPass`, `execChainPass`, and `chainUnifyPass`. -/
def busUnifyPass : VerifiedPassW p := fun cs bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    let ⟨eqs, heqs⟩ := collectAllBuses cs bs facts hp1
      ((cs.busInteractions.map (fun bi => bi.busId)).dedup)
    let new := eqs.filter
      (fun c => !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c)
    if new.isEmpty then ⟨cs, cs.refines_refl bs, _root_.id⟩
    else
      ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new },
       cs.addConstraints_correct bs new (fun env hadm hsat c hc =>
         heqs env hadm hsat c (List.mem_of_mem_filter hc))⟩
  else ⟨cs, cs.refines_refl bs, _root_.id⟩
