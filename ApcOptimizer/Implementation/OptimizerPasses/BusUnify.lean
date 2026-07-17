import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify
import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.MemoryBusDrop
import ApcOptimizer.MemoryBus

set_option autoImplicit false

variable {p : ℕ}

/-- Structural hash of an expression (order-sensitive) — the shared prefilter key for
    "is this exact expression already present" tests (`busUnifyPass`'s already-present filter,
    `busPairCancel`'s payload match, …). Hash inequality proves structural inequality; hits are
    re-verified structurally, so a collision can only cost time. -/
def Expression.structHash : Expression p → UInt64
  | .const n => mixHash 11 (UInt64.ofNat n.val)
  | .var y => mixHash 13 (mixHash (hash y.name) (hash y.powdrId?))
  | .add a b => mixHash 17 (mixHash a.structHash b.structHash)
  | .mul a b => mixHash 19 (mixHash a.structHash b.structHash)

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
    (h : addrConstsNeq shape S bi = true) (env : Variable → ZMod p) :
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
    (env : Variable → ZMod p) :
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
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (env : Variable → ZMod p)
    (hadm : cs.admissible bs env)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre mid post : List (BusInteraction (Expression p)))
    (S R : BusInteraction (Expression p))
    (hsplit : cs.busInteractions.filter (fun bi => bi.busId = busId) = pre ++ S :: mid ++ R :: post)
    (hS : (S.eval env).multiplicity = shape.setNewMult)
    (hR : (R.eval env).multiplicity = -shape.setNewMult)
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

/-- A checked consecutive send→receive pair on bus `busId`: `S` a constant send, `R` a constant
    receive, same constant address, and every `mid` message provably inactive or of a different
    address. The split equation `L = pre ++ S :: mid ++ R :: post` is *not* re-decided here —
    the enumerator (`candidateSplits`) produces it by construction, and it reaches
    `checkPair_sound` as a hypothesis (the old per-candidate O(#interactions) structural
    comparison dominated this pass). -/
def checkPair (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : TwoRootMap p constraints) (nw : NonzeroWits p constraints)
    (S : BusInteraction (Expression p))
    (mid : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p)) : Bool :=
  decide (multConst S = some shape.setNewMult) && decide (multConst R = some (-shape.setNewMult)) &&
  addrConstsEq shape S R &&
  mid.all (fun m => addrConstsNeq shape S m || addrAffineNeq shape S m
    || addrTwoRootNeq shape T S m || addrNonzeroNeq shape nw S m || decide (multConst m = some 0))

theorem checkPair_sound (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre : List (BusInteraction (Expression p))) (S : BusInteraction (Expression p))
    (mid : List (BusInteraction (Expression p))) (R : BusInteraction (Expression p))
    (post : List (BusInteraction (Expression p)))
    (T : TwoRootMap p cs.algebraicConstraints) (nw : NonzeroWits p cs.algebraicConstraints)
    (hsplit : cs.busInteractions.filter (fun bi => bi.busId = busId)
      = pre ++ S :: mid ++ R :: post)
    (hchk : checkPair shape T nw S mid R = true)
    (env : Variable → ZMod p) (hadm : cs.admissible bs env) (hsat : cs.satisfies bs env) :
    ∀ c ∈ memEqConstraints shape S R, c.eval env = 0 := by
  unfold checkPair at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨hSm, hRm⟩, haddrEq⟩, hmidall⟩ := hchk
  have hSm : multConst S = some shape.setNewMult := of_decide_eq_true hSm
  have hRm : multConst R = some (-shape.setNewMult) := of_decide_eq_true hRm
  have hSev : (S.eval env).multiplicity = shape.setNewMult := by
    show S.multiplicity.eval env = shape.setNewMult
    exact S.multiplicity.constValue?_sound shape.setNewMult hSm env
  have hRev : (R.eval env).multiplicity = -shape.setNewMult := by
    show R.multiplicity.eval env = -shape.setNewMult
    exact R.multiplicity.constValue?_sound (-shape.setNewMult) hRm env
  have haddr : shape.address (S.eval env) = shape.address (R.eval env) :=
    addrConstsEq_sound shape S R haddrEq env
  have hcon : ∀ c ∈ cs.algebraicConstraints, c.eval env = 0 := hsat.1
  have hmid : ∀ m ∈ mid, (m.eval env).multiplicity ≠ 0 →
      shape.address (m.eval env) = shape.address (S.eval env) → False := by
    intro m hm hmne hmaddr
    rcases (Bool.or_eq_true _ _).mp (List.all_eq_true.mp hmidall m hm) with hcond | hz
    · rcases (Bool.or_eq_true _ _).mp hcond with hcond_a | hnz
      · rcases (Bool.or_eq_true _ _).mp hcond_a with hcond2 | h2r
        · rcases (Bool.or_eq_true _ _).mp hcond2 with hneq | haff
          · exact addrConstsNeq_sound shape S m hneq env (hmaddr.symm)
          · exact addrAffineNeq_sound shape S m haff env (hmaddr.symm)
        · exact addrTwoRootNeq_sound shape T S m h2r env hcon (hmaddr.symm)
      · exact addrNonzeroNeq_sound shape nw S m hnz env hcon (hmaddr.symm)
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

/-- One `(pre, S, mid, R, post)` candidate, carrying the split equation it was constructed
    from. -/
def SplitCand (p : ℕ) (L : List (BusInteraction (Expression p))) :=
  { c : List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)) //
    L = c.1 ++ c.2.1 :: c.2.2.1 ++ c.2.2.2.1 :: c.2.2.2.2 }

/-- Scan forward from a send `S` for its consumer: the first same-address receive, with every
    message before it excludable (different address, or inactive). Returns `(mid, R, post)` on
    success — together with the recomposition proof `revMid.reverse ++ rest = mid ++ R :: post`
    — or `none` if a possibly-same-address active non-receive blocks the window. -/
def findConsumer (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : TwoRootMap p constraints) (nw : NonzeroWits p constraints)
    (S : BusInteraction (Expression p)) :
    (revMid rest : List (BusInteraction (Expression p))) →
    Option ({ mrp : List (BusInteraction (Expression p)) × BusInteraction (Expression p)
      × List (BusInteraction (Expression p)) //
      revMid.reverse ++ rest = mrp.1 ++ mrp.2.1 :: mrp.2.2 })
  | _, [] => none
  | revMid, r :: rest =>
      if decide (multConst r = some (-shape.setNewMult)) && addrConstsEq shape S r then
        some ⟨(revMid.reverse, r, rest), rfl⟩
      else if addrConstsNeq shape S r || addrAffineNeq shape S r || addrTwoRootNeq shape T S r
          || addrNonzeroNeq shape nw S r || decide (multConst r = some 0) then
        (findConsumer shape T nw S (r :: revMid) rest).map (fun ⟨mrp, hmrp⟩ =>
          ⟨mrp, by
            rw [← hmrp, List.reverse_cons, List.append_assoc]
            rfl⟩)
      else none

/-- One candidate per active send `S`, pairing it with its consumer receive (`findConsumer`),
    each carrying its split equation by construction. Linear in the number of sends × scan
    length, so no O(n²) blow-up on large buses. `checkPair` re-verifies the pair conditions. -/
def candidateSplits (shape : MemoryBusShape) {constraints : List (Expression p)}
    (T : TwoRootMap p constraints) (nw : NonzeroWits p constraints)
    (L : List (BusInteraction (Expression p))) :
    (revPre rest : List (BusInteraction (Expression p))) →
    (hinv : L = revPre.reverse ++ rest) →
    List (SplitCand p L)
  | _, [], _ => []
  | revPre, S :: rest, hinv =>
      (if decide (multConst S = some shape.setNewMult) then
        match findConsumer shape T nw S [] rest with
        | some ⟨(mid, R, post), hmrp⟩ =>
          [⟨(revPre.reverse, S, mid, R, post), by
            rw [hinv]
            have h : rest = mid ++ R :: post := hmrp
            rw [h]
            simp⟩]
        | none => []
       else []) ++ candidateSplits shape T nw L (S :: revPre) rest
        (by rw [hinv, List.reverse_cons, List.append_assoc]; rfl)

/-- Collect the entailed equalities for one bus, with proof. -/
def collectForBus (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (T : TwoRootMap p cs.algebraicConstraints)
    (nw : NonzeroWits p cs.algebraicConstraints)
    (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape) :
    List (SplitCand p (cs.busInteractions.filter (fun bi => bi.busId = busId))) →
    { out : List (Expression p) //
        ∀ env, cs.admissible bs env → cs.satisfies bs env → ∀ c ∈ out, c.eval env = 0 }
  | [] => ⟨[], fun _ _ _ _ h => absurd h (by simp)⟩
  | ⟨(pre, S, mid, R, post), hsplit⟩ :: rest =>
    let ⟨acc, hacc⟩ := collectForBus cs bs facts hp1 T nw busId shape hshape rest
    if hchk : checkPair shape T nw S mid R = true then
      ⟨memEqConstraints shape S R ++ acc, by
        intro env hadm hsat c hc
        rcases List.mem_append.1 hc with h | h
        · exact checkPair_sound cs bs facts hp1 busId shape hshape pre S mid R post T nw hsplit
            hchk env hadm hsat c h
        · exact hacc env hadm hsat c h⟩
    else ⟨acc, hacc⟩

/-- Collect over every declared bus, with proof. -/
def collectAllBuses (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (T : TwoRootMap p cs.algebraicConstraints)
    (nw : NonzeroWits p cs.algebraicConstraints) :
    List Nat →
    { out : List (Expression p) //
        ∀ env, cs.admissible bs env → cs.satisfies bs env → ∀ c ∈ out, c.eval env = 0 }
  | [] => ⟨[], fun _ _ _ _ h => absurd h (by simp)⟩
  | busId :: rest =>
    let ⟨acc, hacc⟩ := collectAllBuses cs bs facts hp1 T nw rest
    match hshape : facts.memShape busId with
    | some shape =>
      let ⟨eqs, heqs⟩ := collectForBus cs bs facts hp1 T nw busId shape hshape
        (candidateSplits shape T nw _ []
          (cs.busInteractions.filter (fun bi => bi.busId = busId)) rfl)
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
    -- precompute the per-variable two-root data once (memoized `twoRootOf?`), so the
    -- address-disequality certificate is a constant-time hash lookup per candidate pair
    let T := TwoRootMap.build cs.algebraicConstraints
    -- reciprocal (nonzero-witness) forms, for the register-vs-RAM address-disequality certificate
    let nw := NonzeroWits.build cs.algebraicConstraints
    let ⟨eqs, heqs⟩ := collectAllBuses cs bs facts hp1 T nw
      ((cs.busInteractions.map (fun bi => bi.busId)).dedup)
    -- keep only equalities over existing columns, so the pass introduces no new variable
    -- (the real slot equalities are built from `cs`'s payloads, so none are dropped).
    -- The membership test `z ∈ cs.vars` is the load-bearing "no new variable" check, run for
    -- every variable of every candidate equality. `cs.vars` is the whole occurrence list (~10⁴
    -- entries on large blocks), so the per-`z` **linear** list scan dominated this filter. Build a
    -- `Std.HashSet` of it once and test membership in O(1); `Std.HashSet.contains_ofList` transports
    -- the check back to genuine list membership `z ∈ cs.vars` (all the correctness proof needs).
    let csVarSet := Std.HashSet.ofList cs.vars
    -- The already-present test (`cs.algebraicConstraints.contains c`) is likewise a per-equality
    -- O(#constraints) deep structural scan — most equalities *are* already present from the
    -- previous cycle. Bucket the constraints by structural hash once and compare within the
    -- bucket; the result is the identical Bool (hash inequality proves inequality).
    let csHashes : Std.HashMap UInt64 (List (Expression p)) :=
      cs.algebraicConstraints.foldl (fun m c =>
        let h := c.structHash
        m.insert h (c :: m.getD h [])) ∅
    let containsC : Expression p → Bool := fun c =>
      (csHashes.getD c.structHash []).any (fun c' => c' == c)
    let new := eqs.filter
      (fun c => !c.normalize.fold.isConstZero && !containsC c
        && c.vars.all (fun z => csVarSet.contains z))
    if new.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
    else
      ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
       cs.addConstraints_correct bs new
         (fun env hadm hsat c hc => heqs env hadm hsat c (List.mem_of_mem_filter hc))
         (fun c hc z hz => by
           have hp := (List.mem_filter.1 hc).2
           simp only [Bool.and_eq_true, List.all_eq_true] at hp
           have hz' : csVarSet.contains z = true := hp.2 z hz
           rw [Std.HashSet.contains_ofList] at hz'
           exact List.contains_iff_mem.mp hz')⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
