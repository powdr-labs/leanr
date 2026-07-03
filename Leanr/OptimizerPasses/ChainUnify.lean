import Leanr.OptimizerPasses.MemoryUnifyBatch

set_option autoImplicit false

/-! # Whole-chain memory unification

`memoryUnifyBatchPass` certifies one send/receive link per address per cycle: the receive of
an *earlier* pair can only be identified after the *later* pair's equalities have been
substituted (its timestamp expression must become a refutable constant offset). On an
unrolled loop where one register is accessed a hundred times that means a hundred full
pipeline cycles. This pass certifies the **entire chain in one invocation**, processing the
same-address sends from the *top* (latest) down and carrying the already-established claims
as an accumulator: the receive claimed for send `S` is identified by refuting all others —
receives *below* by the usual never-zero timestamp difference (`notMatchG`), and receives
already claimed *above* by their accumulated payload equality together with the constant,
in-range timestamp gap between their send and `S` (equal payloads would force equal
timestamp values).

Link adjacency ("no active send strictly between `S` and its successor `S'`") reuses
`sendExcluded` verbatim — chain sends below/above are excluded by the constant-offset
low/high routes, so no ordering accumulator is needed for it. The conclusions are the
slot-wise payload equalities of every link, added at once; Gauss then collapses the whole
chain in the next cycle. -/

variable {p : ℕ}

/-- Constant, positive, in-range timestamp gap from `S` up to `X`. -/
def gapOkTo (shape : MemoryBusShape) (S X : BusInteraction (Expression p)) : Bool :=
  match constDiff (tsExprOf shape S) (tsExprOf shape X) with
  | some d => decide (0 < d.val) && decide (shape.tsBound + d.val ≤ p)
  | none => false

theorem gapOkTo_sound (shape : MemoryBusShape) (S X : BusInteraction (Expression p))
    (h : gapOkTo shape S X = true) :
    ∃ d : ZMod p, constDiff (tsExprOf shape S) (tsExprOf shape X) = some d ∧
      0 < d.val ∧ shape.tsBound + d.val ≤ p := by
  unfold gapOkTo at h
  split at h
  · rename_i d hd
    rw [Bool.and_eq_true] at h
    exact ⟨d, hd, of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  · exact absurd h (by simp)

/-- One chain link: `S'` is the next send above `S`, `R` the claimed receive, `higher` the
    (receive, send) pairs already claimed above. -/
def linkCheck (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (busId : Nat) (shape : MemoryBusShape) (S' S R : BusInteraction (Expression p))
    (higher : List (BusInteraction (Expression p) × BusInteraction (Expression p))) : Bool :=
  let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
  decide (S ∈ L) && decide (R ∈ L) &&
  decide (multConst S = some 1) && decide (multConst R = some (-1)) &&
  addrConstsEq shape S S' &&
  (match constDiff (tsExprOf shape S) (tsExprOf shape S') with
   | some k =>
     decide (0 < k.val) && decide (shape.tsBound + k.val ≤ p) &&
       L.all (sendExcluded shape S S' k)
   | none => false) &&
  higher.all (fun hr =>
    decide (hr.2 ∈ L) && decide (multConst hr.2 = some 1) && gapOkTo shape S hr.2) &&
  L.all (fun bi => decide (bi = R) ||
    notMatchG B shape S bi ||
    higher.any (fun hr => decide (bi = hr.1)))

/-- Check a chain given top-down: `sendsDesc = [S_top, …, S_0]`,
    `recvsDesc = [R_top, …, R_1]` (one claimed receive per send except the top one). -/
def checkChainRev (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (busId : Nat) (shape : MemoryBusShape) :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    List (BusInteraction (Expression p) × BusInteraction (Expression p)) → Bool
  | [_], [], _ => true
  | S' :: S :: sends, R :: recvs, higher =>
      linkCheck cs bs B busId shape S' S R higher &&
      checkChainRev cs bs B busId shape (S :: sends) recvs ((R, S) :: higher)
  | _, _, _ => false

/-- The claimed `(send, receive)` pairs of a top-down chain. -/
def chainPairs :
    List (BusInteraction (Expression p)) → List (BusInteraction (Expression p)) →
    List (BusInteraction (Expression p) × BusInteraction (Expression p))
  | _ :: S :: sends, R :: recvs => (S, R) :: chainPairs (S :: sends) recvs
  | _, _ => []

/-- Full chain certificate: global side conditions plus the top-down recursion. -/
def checkMemChainG (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (busId : Nat) (shape : MemoryBusShape)
    (sendsDesc recvsDesc : List (BusInteraction (Expression p))) : Bool :=
  decide ((1 : ZMod p) ≠ 0) && decide (1 ≤ shape.tsBound) &&
  (match sendsDesc.head? with
   | some Stop =>
     decide (Stop ∈ cs.busInteractions.filter (fun bi => bi.busId = busId)) &&
       decide (multConst Stop = some 1)
   | none => false) &&
  checkChainRev cs bs B busId shape sendsDesc recvsDesc []

/-- The entailed equalities of every chain link. -/
def chainEqs (shape : MemoryBusShape)
    (sendsDesc recvsDesc : List (BusInteraction (Expression p))) : List (Expression p) :=
  (chainPairs sendsDesc recvsDesc).flatMap (fun SR => memEqConstraints shape SR.1 SR.2)

theorem checkChainRev_sound (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (hB : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, B[x]? = some b → (env x).val < b)
    (busId : Nat) (shape : MemoryBusShape)
    (hdecl : bs.memoryBus busId = some shape) (h1ne : (1 : ZMod p) ≠ 0)
    (htsb : 1 ≤ shape.tsBound) (env : String → ZMod p) (hsat : cs.satisfies bs env) :
    ∀ (sendsDesc recvsDesc : List (BusInteraction (Expression p)))
      (higher : List (BusInteraction (Expression p) × BusInteraction (Expression p))),
    (∀ X, sendsDesc.head? = some X →
      X ∈ cs.busInteractions.filter (fun bi => bi.busId = busId) ∧ multConst X = some 1) →
    (∀ hr ∈ higher, (hr.1.eval env).payload = (hr.2.eval env).payload) →
    checkChainRev cs bs B busId shape sendsDesc recvsDesc higher = true →
    ∀ SR ∈ chainPairs sendsDesc recvsDesc,
      (SR.2.eval env).payload = (SR.1.eval env).payload := by
  obtain ⟨hcon, hob, hd⟩ := hsat
  obtain ⟨c1, c2, c3, c4, c5, cmono⟩ := hd busId shape hdecl
  have hsat' : cs.satisfies bs env := ⟨hcon, hob, hd⟩
  have hbus : ∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false := fun bi hbi => hob bi hbi
  have hmem : ∀ bi ∈ cs.busInteractions.filter (fun bi => bi.busId = busId),
      bi.eval env ∈ (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
        (fun bi => bi.eval env) := fun bi hbi => List.mem_map.2 ⟨bi, hbi, rfl⟩
  intro sendsDesc
  induction sendsDesc with
  | nil =>
      intro recvsDesc higher _ _ hchk
      simp [checkChainRev] at hchk
  | cons S' rest ih =>
    intro recvsDesc higher hhead hacc hchk
    rcases rest with _ | ⟨S, sends⟩
    · rcases recvsDesc with _ | ⟨R, recvs⟩
      · intro SR hSR
        simp [chainPairs] at hSR
      · simp [checkChainRev] at hchk
    rcases recvsDesc with _ | ⟨R, recvs⟩
    · simp [checkChainRev] at hchk
    simp only [checkChainRev, Bool.and_eq_true] at hchk
    obtain ⟨hlink, hrest⟩ := hchk
    unfold linkCheck at hlink
    simp only [Bool.and_eq_true] at hlink
    obtain ⟨⟨⟨⟨⟨⟨⟨hSmem, hRmem⟩, hSm⟩, hRm⟩, haddrc⟩, hgapblock⟩, hhigher⟩, hident⟩ := hlink
    have hSmem := of_decide_eq_true hSmem
    have hRmem := of_decide_eq_true hRmem
    have hSm := of_decide_eq_true hSm
    have hRm := of_decide_eq_true hRm
    obtain ⟨hS'mem, hS'm⟩ := hhead S' rfl
    -- the gap to the successor
    obtain ⟨k, hk, hkpos, hkrange, hexcl⟩ :
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
    -- evaluated multiplicities and timestamp facts
    have hSev : (S.eval env).multiplicity = 1 := S.multiplicity.constValue?_sound 1 hSm env
    have hS'ev : (S'.eval env).multiplicity = 1 :=
      S'.multiplicity.constValue?_sound 1 hS'm env
    have htsS : shape.tsVal (S.eval env) < shape.tsBound :=
      c3 (S.eval env) (hmem S hSmem) (by rw [hSev]; exact h1ne)
    have htsS' : shape.tsVal (S'.eval env) = shape.tsVal (S.eval env) + k.val := by
      rw [tsVal_eval, tsVal_eval, constDiff_sound _ _ k hk env]
      exact ZMod.val_add_of_lt (by rw [← tsVal_eval]; omega)
    have hlt : shape.tsVal (S.eval env) < shape.tsVal (S'.eval env) := by omega
    have haddr := addrConstsEq_sound shape S S' haddrc env
    -- no active send strictly between (same argument as `checkMemMatchG_sound`)
    have hnobetween : ∀ S'' ∈ (cs.busInteractions.filter (fun bi => bi.busId = busId)).map
        (fun bi => bi.eval env), S''.multiplicity = 1 →
        shape.address S'' = shape.address (S.eval env) →
        ¬(shape.tsVal (S.eval env) < shape.tsVal S'' ∧
          shape.tsVal S'' < shape.tsVal (S'.eval env)) := by
      intro S'' hS''mem hS''mult haddr''
      obtain ⟨bi, hbi, rfl⟩ := List.mem_map.1 hS''mem
      have hcase := List.all_eq_true.mp hexcl bi hbi
      simp only [sendExcluded, Bool.or_eq_true] at hcase
      rcases hcase with ((((hcase | hcase) | hcase) | hcase) | hcase)
      · have : bi = S := of_decide_eq_true hcase
        subst this
        omega
      · have : bi = S' := of_decide_eq_true hcase
        subst this
        omega
      · unfold notSend at hcase
        split at hcase
        · rename_i m hm
          have heq : (bi.eval env).multiplicity = m :=
            bi.multiplicity.constValue?_sound m hm env
          rw [heq] at hS''mult
          exact absurd hS''mult (of_decide_eq_true hcase)
        · exact absurd hcase (by simp)
      · exact absurd haddr''.symm (addrConstsNeq_sound shape S bi hcase env)
      · have hbiactive : (bi.eval env).multiplicity ≠ 0 := by
          rw [hS''mult]; exact h1ne
        have htsbi : shape.tsVal (bi.eval env) < shape.tsBound :=
          c3 (bi.eval env) (hmem bi hbi) hbiactive
        unfold notBetweenTs at hcase
        rw [Bool.or_eq_true] at hcase
        rcases hcase with hlow | hhigh
        · split at hlow
          · rename_i e he
            have herange := of_decide_eq_true hlow
            have hSval : shape.tsVal (S.eval env)
                = shape.tsVal (bi.eval env) + e.val := by
              rw [tsVal_eval, tsVal_eval, constDiff_sound _ _ e he env]
              exact ZMod.val_add_of_lt (by rw [← tsVal_eval]; omega)
            omega
          · exact absurd hlow (by simp)
        · split at hhigh
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
    -- the in-window consumer of S
    obtain ⟨Rcv, hRcvMem, hRcvMult, hRcvPay⟩ :=
      c2 (S.eval env) (hmem S hSmem) (S'.eval env) (hmem S' hS'mem)
        hSev hS'ev haddr hlt hnobetween
    -- identify the consumer as R
    obtain ⟨bi, hbi, hbieq⟩ := List.mem_map.1 hRcvMem
    have hpayS : (bi.eval env).payload = (S.eval env).payload := by
      rw [hbieq]; exact hRcvPay
    have hbiR : bi = R := by
      rcases (Bool.or_eq_true _ _).mp (List.all_eq_true.mp hident bi hbi) with hcase | hhi
      · rcases (Bool.or_eq_true _ _).mp hcase with hcase | hcase
        · exact of_decide_eq_true hcase
        · exfalso
          unfold notMatchG at hcase
          rw [Bool.or_eq_true, Bool.or_eq_true] at hcase
          have hpay : bi.payload.map (fun e => e.eval env)
              = S.payload.map (fun e => e.eval env) := hpayS
          rcases hcase with (hcase | href) | haddrne
          · split at hcase
            · rename_i m hm
              have hmne : m ≠ -1 := of_decide_eq_true hcase
              have hme : (bi.eval env).multiplicity = m :=
                bi.multiplicity.constValue?_sound m hm env
              apply hmne
              rw [← hme, hbieq]
              exact hRcvMult
            · exact absurd hcase (by simp)
          · have := payloadSlot_eval_eq bi.payload S.payload env hpay shape.tsField
            exact tsRefuted_sound B shape S bi hp href env (hB env hbus) this
          · have haddreq : shape.address (S.eval env) = shape.address (bi.eval env) := by
              unfold MemoryBusShape.address
              apply List.map_congr_left
              intro slot _
              show (S.payload.map (fun e : Expression p => e.eval env))[slot]?
                = (bi.payload.map (fun e : Expression p => e.eval env))[slot]?
              rw [hpay]
            exact addrConstsNeq_sound shape S bi haddrne env haddreq
      · -- an already-claimed receive above: its send's timestamp differs from S's
        exfalso
        obtain ⟨hr, hhrmem, hbihr⟩ := List.any_eq_true.1 hhi
        have hbihr : bi = hr.1 := of_decide_eq_true hbihr
        have hpayhr : (bi.eval env).payload = (hr.2.eval env).payload := by
          rw [hbihr]; exact hacc hr hhrmem
        have hhr := List.all_eq_true.mp hhigher hr hhrmem
        rw [Bool.and_eq_true, Bool.and_eq_true] at hhr
        obtain ⟨⟨hhrL, hhrm⟩, hgap⟩ := hhr
        have hhrL := of_decide_eq_true hhrL
        have hhrm := of_decide_eq_true hhrm
        obtain ⟨d, hd, hdpos, hdrange⟩ := gapOkTo_sound shape S hr.2 hgap
        have hhrev : (hr.2.eval env).multiplicity = 1 :=
          hr.2.multiplicity.constValue?_sound 1 hhrm env
        have htshr : shape.tsVal (hr.2.eval env) = shape.tsVal (S.eval env) + d.val := by
          rw [tsVal_eval, tsVal_eval, constDiff_sound _ _ d hd env]
          exact ZMod.val_add_of_lt (by rw [← tsVal_eval]; omega)
        have h1 : shape.tsVal (bi.eval env) = shape.tsVal (S.eval env) := by
          unfold MemoryBusShape.tsVal
          rw [hpayS]
        have h2 : shape.tsVal (bi.eval env) = shape.tsVal (hr.2.eval env) := by
          unfold MemoryBusShape.tsVal
          rw [hpayhr]
        omega
    have hlinkeq : (R.eval env).payload = (S.eval env).payload := by
      rw [← hbiR]
      exact hpayS
    -- assemble: this link plus the recursion
    intro SR hSR
    simp only [chainPairs, List.mem_cons] at hSR
    rcases hSR with rfl | hSR
    · exact hlinkeq
    · exact ih recvs ((R, S) :: higher)
        (fun X hX => by
          simp only [List.head?_cons, Option.some.injEq] at hX
          subst hX
          exact ⟨hSmem, hSm⟩)
        (fun hr hhr => by
          rcases List.mem_cons.1 hhr with rfl | hhr
          · exact hlinkeq
          · exact hacc hr hhr)
        hrest SR hSR

theorem checkMemChainG_sound (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (hB : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, B[x]? = some b → (env x).val < b)
    (busId : Nat) (shape : MemoryBusShape)
    (sendsDesc recvsDesc : List (BusInteraction (Expression p)))
    (hdecl : bs.memoryBus busId = some shape)
    (hchk : checkMemChainG cs bs B busId shape sendsDesc recvsDesc = true)
    (env : String → ZMod p) (hsat : cs.satisfies bs env) :
    ∀ c ∈ chainEqs shape sendsDesc recvsDesc, c.eval env = 0 := by
  unfold checkMemChainG at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨h1ne, htsb⟩, hheadblock⟩, hrev⟩ := hchk
  have h1ne := of_decide_eq_true h1ne
  have htsb := of_decide_eq_true htsb
  have hhead : ∀ X, sendsDesc.head? = some X →
      X ∈ cs.busInteractions.filter (fun bi => bi.busId = busId) ∧ multConst X = some 1 := by
    intro X hX
    rw [hX] at hheadblock
    rw [Bool.and_eq_true] at hheadblock
    exact ⟨of_decide_eq_true hheadblock.1, of_decide_eq_true hheadblock.2⟩
  have hpairs := checkChainRev_sound cs bs B hB busId shape hdecl h1ne htsb env hsat
    sendsDesc recvsDesc [] hhead (fun hr h => absurd h (List.not_mem_nil)) hrev
  intro c hc
  unfold chainEqs at hc
  obtain ⟨SR, hSR, hcmem⟩ := List.mem_flatMap.1 hc
  have hpay : SR.2.payload.map (fun e => e.eval env)
      = SR.1.payload.map (fun e => e.eval env) := hpairs SR hSR
  unfold memEqConstraints at hcmem
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hcmem
  rw [eqExpr_eval, payloadSlot_eval_eq SR.2.payload SR.1.payload env hpay i]
  ring

/-! ## The search (proof-free) and the batch pass -/

/-- Group the sends of a bus by pairwise-matching constant address. -/
def addrBucketsAux (shape : MemoryBusShape) :
    Nat → List (BusInteraction (Expression p)) →
    List (List (BusInteraction (Expression p)))
  | 0, _ => []
  | _, [] => []
  | fuel + 1, S :: rest =>
    (S :: rest.filter (fun S' => addrConstsEq shape S S')) ::
      addrBucketsAux shape fuel (rest.filter (fun S' => !addrConstsEq shape S S'))

def addrBuckets (shape : MemoryBusShape) (l : List (BusInteraction (Expression p))) :
    List (List (BusInteraction (Expression p))) :=
  addrBucketsAux shape l.length l

/-- Sort a bucket's sends descending by their constant timestamp offset from the first,
    all-or-nothing. -/
def sortSendsDesc (shape : MemoryBusShape) (bucket : List (BusInteraction (Expression p))) :
    Option (List (BusInteraction (Expression p))) :=
  match bucket with
  | [] => none
  | base :: _ =>
    let tagged := bucket.map (fun S =>
      ((constDiff (tsExprOf shape base) (tsExprOf shape S)).map (·.val), S))
    if tagged.all (fun t => t.1.isSome) then
      let sorted := (tagged.map (fun t => (t.1.getD 0, t.2))).mergeSort
        (fun a b => b.1 ≤ a.1)
      some (sorted.map Prod.snd)
    else none

/-- Walk the chain top-down assigning each send its unique unrefuted receive; truncate at the
    first ambiguity. Returns `(sendsDesc, recvsDesc)` covering the certified prefix. -/
def assignChain (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (shape : MemoryBusShape) (pool : List (BusInteraction (Expression p))) :
    List (BusInteraction (Expression p)) →
    List (BusInteraction (Expression p)) × List (BusInteraction (Expression p))
  | [] => ([], [])
  | [S] => ([S], [])
  | S' :: S :: sends =>
    match pool.filter (fun r => !notMatchG B shape S r) with
    | [R] =>
      let (restS, restR) := assignChain cs bs B shape (pool.erase R) (S :: sends)
      (S' :: restS, R :: restR)
    | _ => ([S'], [])

/-- All checked chains over all declared buses. -/
def findMemChains (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat) :
    List (Nat × List (BusInteraction (Expression p)) × List (BusInteraction (Expression p))) :=
  ((cs.busInteractions.map (fun bi => bi.busId)).dedup).flatMap (fun busId =>
    match bs.memoryBus busId with
    | none => []
    | some shape =>
      let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
      let sends := L.filter (fun bi => multConst bi = some 1)
      let receives := L.filter (fun bi => multConst bi = some (-1))
      (addrBuckets shape sends).filterMap (fun bucket =>
        match bucket with
        | [] => none
        | base :: _ =>
          if bucket.length < 2 then none
          else match sortSendsDesc shape bucket with
          | none => none
          | some sendsDesc =>
            let pool := receives.filter (fun r => addrConstsEq shape base r)
            let (sd, rd) := assignChain cs bs B shape pool sendsDesc
            if rd.isEmpty then none
            else if checkMemChainG cs bs B busId shape sd rd then some (busId, sd, rd)
            else none))

/-- Re-check every found chain and collect the entailed equality constraints, with proof. -/
def collectChainEqs (cs : ConstraintSystem p) (bs : BusSemantics p)
    (B : Std.HashMap String Nat)
    (hB : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, B[x]? = some b → (env x).val < b) :
    List (Nat × List (BusInteraction (Expression p)) × List (BusInteraction (Expression p))) →
    { out : List (Expression p) //
        ∀ env, cs.satisfies bs env → ∀ c ∈ out, c.eval env = 0 }
  | [] => ⟨[], fun _ _ _ hc => absurd hc (by simp)⟩
  | (busId, sd, rd) :: rest =>
    let ⟨acc, hacc⟩ := collectChainEqs cs bs B hB rest
    match hdecl : bs.memoryBus busId with
    | none => ⟨acc, hacc⟩
    | some shape =>
      if hchk : checkMemChainG cs bs B busId shape sd rd = true then
        ⟨chainEqs shape sd rd ++ acc, by
          intro env hsat c hc
          rcases List.mem_append.1 hc with h | h
          · exact checkMemChainG_sound cs bs B hB busId shape sd rd hdecl hchk env hsat c h
          · exact hacc env hsat c h⟩
      else ⟨acc, hacc⟩

/-- The whole-chain memory-unification pass. -/
def chainUnifyPass : VerifiedPassW p := fun cs bs facts =>
  let Bm : BoundsMap p cs bs := BoundsMap.build facts
  let ⟨eqs, heqs⟩ := collectChainEqs cs bs Bm.map Bm.sound (findMemChains cs bs Bm.map)
  let new := eqs.filter
    (fun c => !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c)
  if new.isEmpty then ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
  else
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new },
     cs.addConstraints_correct bs new (fun env hsat c hc =>
       heqs env hsat c (List.mem_of_mem_filter hc))⟩
