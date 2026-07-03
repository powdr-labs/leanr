import Leanr.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Generalized memory send/receive unification

`memoryUnifyPass` (entry 18) handles a bus with *exactly two* active sends — enough for the
single-instruction snapshot, never applicable to real blocks with dozens of memory accesses.
This pass generalizes the certificate: for a pair of sends `(S, S')` to the same constant
address, **every** other interaction on the bus must be individually excluded as an
in-between send by one of

* being `S` or `S'` itself,
* a constant multiplicity ≠ 1 (not an active send),
* a provably different constant address (some address slot where both payloads are constants
  that differ), or
* a constant timestamp offset placing it outside the open window `(ts S, ts S')`: either
  `ts S = ts bi + e` with `tsBound + e.val ≤ p` (so `tsVal bi ≤ tsVal S`), or
  `ts bi = ts S + d` with `gap ≤ d.val` and `tsBound + d.val ≤ p` (so `tsVal S' ≤ tsVal bi`) —
  both via the discipline's timestamp-range clause, which keeps `ZMod.val` arithmetic exact.

The receive identification is as before (all other receives refuted by constant multiplicity
or a never-zero timestamp difference), extended by the different-constant-address refutation
(the consumer's payload equals `S`'s, so its address equals `S`'s address). With chained
accesses (`a₁ … aₙ` to one address), the *latest* pair certifies immediately; each earlier
pair certifies one cycle later, after the previous unification's equalities are substituted
and turn the matched receive's timestamp into a constant offset — so chains of length `n`
resolve in `n` cycles of the pipeline.

All matches found in one invocation are collected and their entailed slot-wise equalities
added at once (`addConstraints_correct`); the affine/domain machinery eliminates the
variables. -/

variable {p : ℕ}

/-! ## New exclusion certificates -/

/-- Some address slot where both payloads carry *different* constants — the evaluated
    addresses then provably differ. -/
def addrConstsNeq (shape : MemoryBusShape) (S S' : BusInteraction (Expression p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, S'.payload[slot]? with
    | some e, some e' =>
      match e.constValue?, e'.constValue? with
      | some c, some c' => decide (c ≠ c')
      | _, _ => false
    | _, _ => false)

theorem addrConstsNeq_sound (shape : MemoryBusShape) (S S' : BusInteraction (Expression p))
    (h : addrConstsNeq shape S S' = true) (env : String → ZMod p) :
    shape.address (S.eval env) ≠ shape.address (S'.eval env) := by
  intro heq
  obtain ⟨slot, hslot, hs⟩ := List.any_eq_true.1 h
  -- extract the differing constants
  split at hs
  · rename_i e e' hP hQ
    split at hs
    · rename_i c c' he he'
      have hcc : c ≠ c' := of_decide_eq_true hs
      -- the address lists agree at the position of `slot`
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hslot
      have h1 : (shape.address (S.eval env))[i]? = some ((S.eval env).payload[slot]?) := by
        unfold MemoryBusShape.address
        rw [List.getElem?_map, hi]
        rfl
      have h2 : (shape.address (S'.eval env))[i]? = some ((S'.eval env).payload[slot]?) := by
        unfold MemoryBusShape.address
        rw [List.getElem?_map, hi]
        rfl
      rw [heq, h2] at h1
      have hpay : (S.eval env).payload[slot]? = (S'.eval env).payload[slot]? := by
        simpa using h1.symm
      -- but the evaluated payload entries are the distinct constants
      have hSs : (S.eval env).payload[slot]? = some (c : ZMod p) := by
        show (S.payload.map (fun e : Expression p => e.eval env))[slot]? = _
        rw [List.getElem?_map, hP]
        simp [e.constValue?_sound c he env]
      have hS's : (S'.eval env).payload[slot]? = some (c' : ZMod p) := by
        show (S'.payload.map (fun e : Expression p => e.eval env))[slot]? = _
        rw [List.getElem?_map, hQ]
        simp [e'.constValue?_sound c' he' env]
      rw [hSs, hS's] at hpay
      exact hcc (by simpa using hpay)
    · exact absurd hs (by simp)
  · exact absurd hs (by simp)

/-- Timestamp exclusion: a constant offset placing `bi` outside the open window
    `(ts S, ts S + k)`. `low`: `ts S = ts bi + e` with `e` small enough that values add
    exactly; `high`: `ts bi = ts S + d` with `d` at least the gap. -/
def notBetweenTs (shape : MemoryBusShape) (S : BusInteraction (Expression p)) (k : ZMod p)
    (bi : BusInteraction (Expression p)) : Bool :=
  (match constDiff (tsExprOf shape bi) (tsExprOf shape S) with
   | some e => decide (shape.tsBound + e.val ≤ p)
   | none => false) ||
  (match constDiff (tsExprOf shape S) (tsExprOf shape bi) with
   | some d => decide (k.val ≤ d.val) && decide (shape.tsBound + d.val ≤ p)
   | none => false)

/-- One interaction excluded as an in-between send for the pair `(S, S')` with gap `k`. -/
def sendExcluded (shape : MemoryBusShape) (S S' : BusInteraction (Expression p)) (k : ZMod p)
    (bi : BusInteraction (Expression p)) : Bool :=
  decide (bi = S) || decide (bi = S') || notSend bi ||
    addrConstsNeq shape S bi || notBetweenTs shape S k bi

/-- Receive refutation, extended by the different-address certificate. -/
def notMatchG (B : Std.HashMap String Nat) (shape : MemoryBusShape)
    (S bi : BusInteraction (Expression p)) : Bool :=
  (match multConst bi with
   | some m => decide (m ≠ -1)
   | none => false) || tsRefuted B shape S bi || addrConstsNeq shape S bi

/-! ## The generalized checked match -/

/-- All checked side conditions for a memory match `(S, S', Rt)` on `busId`: `S`/`S'` active
    constant-multiplicity sends to the same constant address with a constant in-range
    timestamp gap; every interaction on the bus is excluded as an in-between send; every
    interaction except `Rt` is provably not the matching receive. -/
def checkMemMatchG (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (busId : Nat) (shape : MemoryBusShape) (S S' Rt : BusInteraction (Expression p)) : Bool :=
  let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
  decide ((1 : ZMod p) ≠ 0) &&
  decide (1 ≤ shape.tsBound) &&
  decide (S ∈ L) && decide (S' ∈ L) && decide (Rt ∈ L) &&
  decide (multConst S = some 1) && decide (multConst S' = some 1) &&
  decide (multConst Rt = some (-1)) &&
  addrConstsEq shape S S' &&
  (match constDiff (tsExprOf shape S) (tsExprOf shape S') with
   | some k =>
     decide (0 < k.val) && decide (shape.tsBound + k.val ≤ p) &&
       L.all (sendExcluded shape S S' k)
   | none => false) &&
  L.all (fun bi => decide (bi = Rt) || notMatchG B shape S bi)

theorem checkMemMatchG_sound (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (hB : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, B[x]? = some b → (env x).val < b)
    (busId : Nat) (shape : MemoryBusShape)
    (S S' Rt : BusInteraction (Expression p)) (hdecl : bs.memoryBus busId = some shape)
    (hchk : checkMemMatchG cs bs B busId shape S S' Rt = true)
    (env : String → ZMod p) (hsat : cs.satisfies bs env) :
    ∀ c ∈ memEqConstraints shape S Rt, c.eval env = 0 := by
  -- unpack the certificate
  unfold checkMemMatchG at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1ne, htsb⟩, hSmem⟩, hS'mem⟩, hRtmem⟩, hSm⟩, hS'm⟩, hRtm⟩,
    haddrc⟩, hgapblock⟩, hmatch⟩ := hchk
  have h1ne := of_decide_eq_true h1ne
  have htsb := of_decide_eq_true htsb
  have hSmem := of_decide_eq_true hSmem
  have hS'mem := of_decide_eq_true hS'mem
  have hRtmem := of_decide_eq_true hRtmem
  have hSm := of_decide_eq_true hSm
  have hS'm := of_decide_eq_true hS'm
  have hRtm := of_decide_eq_true hRtm
  -- the timestamp gap and the send-exclusion certificate
  obtain ⟨k, hk, hkpos, hkrange, hsends⟩ :
      ∃ k, constDiff (tsExprOf shape S) (tsExprOf shape S') = some k ∧
        0 < k.val ∧ shape.tsBound + k.val ≤ p ∧
        (cs.busInteractions.filter (fun bi => bi.busId = busId)).all
          (sendExcluded shape S S' k) = true := by
    split at hgapblock
    · rename_i k hk
      rw [Bool.and_eq_true, Bool.and_eq_true] at hgapblock
      exact ⟨k, hk, of_decide_eq_true hgapblock.1.1, of_decide_eq_true hgapblock.1.2,
        hgapblock.2⟩
    · exact absurd hgapblock (by simp)
  have hp : 0 < p := by omega
  -- the discipline for this bus
  obtain ⟨hc, hb, hd⟩ := hsat
  obtain ⟨c1, c2, c3, c4, c5⟩ := hd busId shape hdecl
  have hbus : ∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false := fun bi hbi => hb bi hbi
  -- evaluated multiplicities
  have hSev : (S.eval env).multiplicity = 1 := S.multiplicity.constValue?_sound 1 hSm env
  have hS'ev : (S'.eval env).multiplicity = 1 := S'.multiplicity.constValue?_sound 1 hS'm env
  -- membership of the evaluated messages
  have hmem : ∀ bi ∈ cs.busInteractions.filter (fun bi => bi.busId = busId),
      bi.eval env ∈ (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
        (fun bi => bi.eval env) := fun bi hbi => List.mem_map.2 ⟨bi, hbi, rfl⟩
  -- timestamp values
  have htsS : shape.tsVal (S.eval env) < shape.tsBound :=
    c3 (S.eval env) (hmem S hSmem) (by rw [hSev]; exact h1ne)
  have htsS' : shape.tsVal (S'.eval env) = shape.tsVal (S.eval env) + k.val := by
    rw [tsVal_eval, tsVal_eval, constDiff_sound _ _ k hk env]
    exact ZMod.val_add_of_lt (by
      rw [← tsVal_eval]
      omega)
  have hlt : shape.tsVal (S.eval env) < shape.tsVal (S'.eval env) := by omega
  -- addresses agree
  have haddr := addrConstsEq_sound shape S S' haddrc env
  -- no active send strictly between
  have hnobetween : ∀ S'' ∈ (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => bi.eval env), S''.multiplicity = 1 →
      shape.address S'' = shape.address (S.eval env) →
      ¬(shape.tsVal (S.eval env) < shape.tsVal S'' ∧
        shape.tsVal S'' < shape.tsVal (S'.eval env)) := by
    intro S'' hS''mem hS''mult haddr''
    obtain ⟨bi, hbi, rfl⟩ := List.mem_map.1 hS''mem
    have hcase := List.all_eq_true.mp hsends bi hbi
    simp only [sendExcluded, Bool.or_eq_true] at hcase
    rcases hcase with ((((hcase | hcase) | hcase) | hcase) | hcase)
    · have : bi = S := of_decide_eq_true hcase
      subst this
      omega
    · have : bi = S' := of_decide_eq_true hcase
      subst this
      omega
    · -- not a send: constant multiplicity ≠ 1
      unfold notSend at hcase
      split at hcase
      · rename_i m hm
        have : (bi.eval env).multiplicity = m := bi.multiplicity.constValue?_sound m hm env
        rw [this] at hS''mult
        exact absurd hS''mult (of_decide_eq_true hcase)
      · exact absurd hcase (by simp)
    · -- provably different address
      exact absurd haddr''.symm (addrConstsNeq_sound shape S bi hcase env)
    · -- outside the timestamp window
      have hbiactive : (bi.eval env).multiplicity ≠ 0 := by rw [hS''mult]; exact h1ne
      have htsbi : shape.tsVal (bi.eval env) < shape.tsBound :=
        c3 (bi.eval env) (hmem bi hbi) hbiactive
      unfold notBetweenTs at hcase
      rw [Bool.or_eq_true] at hcase
      rcases hcase with hlow | hhigh
      · -- ts S = ts bi + e : bi is at or before S
        split at hlow
        · rename_i e he
          have herange := of_decide_eq_true hlow
          have hSval : shape.tsVal (S.eval env)
              = shape.tsVal (bi.eval env) + e.val := by
            rw [tsVal_eval, tsVal_eval, constDiff_sound _ _ e he env]
            exact ZMod.val_add_of_lt (by rw [← tsVal_eval]; omega)
          omega
        · exact absurd hlow (by simp)
      · -- ts bi = ts S + d with d ≥ k : bi is at or after S'
        split at hhigh
        · rename_i d hd'
          rw [Bool.and_eq_true] at hhigh
          have hdk := of_decide_eq_true hhigh.1
          have hdrange := of_decide_eq_true hhigh.2
          have hbival : shape.tsVal (bi.eval env)
              = shape.tsVal (S.eval env) + d.val := by
            rw [tsVal_eval, tsVal_eval, constDiff_sound _ _ d hd' env]
            exact ZMod.val_add_of_lt (by rw [← tsVal_eval]; omega)
          omega
        · exact absurd hhigh (by simp)
  -- the discipline's in-window consumption clause
  obtain ⟨Rcv, hRcvMem, hRcvMult, hRcvPay⟩ :=
    c2 (S.eval env) (hmem S hSmem) (S'.eval env) (hmem S' hS'mem)
      hSev hS'ev haddr hlt hnobetween
  -- identify the receive: everything except `Rt` is refuted
  obtain ⟨bi, hbi, hbieq⟩ := List.mem_map.1 hRcvMem
  have hbiRt : bi = Rt := by
    have hcase := List.all_eq_true.mp hmatch bi hbi
    rcases (Bool.or_eq_true _ _).mp hcase with hcase | hcase
    · exact of_decide_eq_true hcase
    · exfalso
      unfold notMatchG at hcase
      rw [Bool.or_eq_true, Bool.or_eq_true] at hcase
      have hpay : bi.payload.map (fun e => e.eval env)
          = S.payload.map (fun e => e.eval env) := by
        have := hRcvPay
        rw [← hbieq] at this
        exact this
      rcases hcase with (hcase | href) | haddrne
      · split at hcase
        · rename_i m hm
          have hmne : m ≠ -1 := of_decide_eq_true hcase
          have hme : (bi.eval env).multiplicity = m := bi.multiplicity.constValue?_sound m hm env
          apply hmne
          rw [← hme, hbieq]
          exact hRcvMult
        · exact absurd hcase (by simp)
      · -- payload equality forces timestamp equality, contradicting the refutation
        have := payloadSlot_eval_eq bi.payload S.payload env hpay shape.tsField
        exact tsRefuted_sound B shape S bi hp href env (hB env hbus) this
      · -- payload equality forces address equality, contradicting the refutation
        have haddreq : shape.address (S.eval env) = shape.address (bi.eval env) := by
          unfold MemoryBusShape.address
          apply List.map_congr_left
          intro slot _
          show (S.payload.map (fun e : Expression p => e.eval env))[slot]?
            = (bi.payload.map (fun e : Expression p => e.eval env))[slot]?
          rw [hpay]
        exact addrConstsNeq_sound shape S bi haddrne env haddreq
  -- the payload equality, slot by slot, gives the conclusions
  have hpay : Rt.payload.map (fun e => e.eval env) = S.payload.map (fun e => e.eval env) := by
    have h' := hRcvPay
    rw [← hbieq, hbiRt] at h'
    exact h'
  intro c hcmem
  unfold memEqConstraints at hcmem
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hcmem
  rw [eqExpr_eval, payloadSlot_eval_eq Rt.payload S.payload env hpay i]
  ring

/-! ## The search (proof-free) and the batch pass -/

/-- The closest later send to the same constant address, by constant timestamp gap. -/
def bestSuccessor (shape : MemoryBusShape) (sends : List (BusInteraction (Expression p)))
    (S : BusInteraction (Expression p)) : Option (BusInteraction (Expression p)) :=
  (sends.filterMap (fun S' =>
      if S' = S then none
      else if addrConstsEq shape S S' then
        match constDiff (tsExprOf shape S) (tsExprOf shape S') with
        | some k => if 0 < k.val then some (S', k.val) else none
        | none => none
      else none)).argmin Prod.snd |>.map Prod.fst

/-- All checked memory matches: for each declared bus, each active constant send with a
    successor to the same address, and the first receive passing the full certificate. -/
def findMemMatchesG (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat) :
    List (Nat × BusInteraction (Expression p) × BusInteraction (Expression p)
      × BusInteraction (Expression p)) :=
  ((cs.busInteractions.map (fun bi => bi.busId)).dedup).flatMap (fun busId =>
    match bs.memoryBus busId with
    | none => []
    | some shape =>
      let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
      let sends := L.filter (fun bi => multConst bi = some 1)
      let receives := L.filter (fun bi => multConst bi = some (-1))
      sends.filterMap (fun S =>
        (bestSuccessor shape sends S).bind (fun S' =>
          -- cheap pre-filter: only unrefuted receives are candidates (usually exactly one)
          match receives.filter (fun r => !notMatchG B shape S r) with
          | [Rt] =>
            if checkMemMatchG cs bs B busId shape S S' Rt then some (busId, S, S', Rt)
            else none
          | _ => none)))

/-- Re-check every found match and collect the entailed equality constraints, with proof. -/
def collectMemEqs (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (hB : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, B[x]? = some b → (env x).val < b) :
    List (Nat × BusInteraction (Expression p) × BusInteraction (Expression p)
      × BusInteraction (Expression p)) →
    { out : List (Expression p) //
        ∀ env, cs.satisfies bs env → ∀ c ∈ out, c.eval env = 0 }
  | [] => ⟨[], fun _ _ _ hc => absurd hc (by simp)⟩
  | (busId, S, S', Rt) :: rest =>
    let ⟨acc, hacc⟩ := collectMemEqs cs bs B hB rest
    match hdecl : bs.memoryBus busId with
    | none => ⟨acc, hacc⟩
    | some shape =>
      if hchk : checkMemMatchG cs bs B busId shape S S' Rt = true then
        ⟨memEqConstraints shape S Rt ++ acc, by
          intro env hsat c hc
          rcases List.mem_append.1 hc with h | h
          · exact checkMemMatchG_sound cs bs B hB busId shape S S' Rt hdecl hchk env hsat c h
          · exact hacc env hsat c h⟩
      else ⟨acc, hacc⟩

/-- The batch memory-unification pass: add the entailed receive-equals-send equations for
    every checked match (skipping equations already present or trivially zero, so the pass is
    idempotent). The affine/domain passes then eliminate the receives' witness variables. -/
def memoryUnifyBatchPass : VerifiedPassW p := fun cs bs facts =>
  let Bm : BoundsMap p cs bs := BoundsMap.build facts
  let ⟨eqs, heqs⟩ := collectMemEqs cs bs Bm.map Bm.sound (findMemMatchesG cs bs Bm.map)
  let new := eqs.filter
    (fun c => !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c)
  if new.isEmpty then ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
  else
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new },
     cs.addConstraints_correct bs new (fun env hsat c hc =>
       heqs env hsat c (List.mem_of_mem_filter hc))⟩
