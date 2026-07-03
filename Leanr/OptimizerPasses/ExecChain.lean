import Leanr.OptimizerPasses.MemoryUnifyBatch
import Leanr.OptimizerPasses.DomainBatch

set_option autoImplicit false

/-! # Execution-chain unification (linear-consumption buses)

The consumer of the empty-address instantiation of the audited discipline (an execution
bridge: payload `(pc, timestamp)`, one global cell — see `BusSemantics.memoryBus`). Unlike
the memory bus, consecutive sends here never have a *constant* timestamp gap (each
instruction's timestamp is a fresh variable — the links are exactly what this pass derives),
so `MemoryUnifyBatch`'s pair certificate can never fire. Instead we use an **anchored
maximum** argument:

* An **anchor** send whose payload provably differs from every receive's payload (typically
  the block's final send — its pc constant lies outside the block) can have no in-fragment
  consumer, so by the in-window clause nothing lies strictly above it: it is the
  timestamp-maximal active send.
* Any other send `S` whose payload provably differs from the anchor's has, by the
  timestamp-uniqueness clause, a *strictly* smaller timestamp — so some send lies strictly
  above it, and taking the least such (`Nat.sInf`), the in-window clause gives `S` an
  in-fragment consumer receive with `S`'s exact payload.
* All receives but one (`Rt`) are refuted as that consumer (payload difference), so
  `Rt.payload = S.payload` — for the execution bridge: `pc_{k+1} = pc_k + 4` and
  `ts_{k+1} = ts_k + kₖ`, the cross-instruction links that unlock chaining everywhere else.

Payload differences are certified slot-wise by three routes: the difference normalizes to a
nonzero constant; the bounded-negative-terms certificate (`linNeverZero`, as in
`tsRefuted`); or exhaustive enumeration over fact/constraint-derived domains (`DomainTable`,
e.g. a branch target `pc + cmp·imm + (1-cmp)·4` with `cmp` boolean enumerates to two
constants, both provably outside the block). Blocks whose final branch may target an
in-block pc have no certifiable anchor and are soundly left alone. -/

variable {p : ℕ}

/-! ## Never-zero certificates for a single expression -/

/-- The difference normalizes to a nonzero constant. -/
def exprNeverZeroConst (e : Expression p) : Bool :=
  match linearize e with
  | some l => l.norm.terms.isEmpty && decide (l.norm.const ≠ 0)
  | none => false

theorem exprNeverZeroConst_sound (e : Expression p) (h : exprNeverZeroConst e = true)
    (env : String → ZMod p) : e.eval env ≠ 0 := by
  unfold exprNeverZeroConst at h
  split at h
  · rename_i l hl
    rw [Bool.and_eq_true] at h
    have hterms : l.norm.terms = [] := by simpa using h.1
    have hconst : l.norm.const ≠ 0 := of_decide_eq_true h.2
    intro h0
    apply hconst
    have h1 : l.norm.eval env = 0 := by
      rw [l.norm_eval, ← linearize_eval e l hl]; exact h0
    simpa [LinExpr.eval, hterms] using h1
  · exact absurd h (by simp)

/-- The bounded-negative-terms certificate (the `tsRefuted` core, for any expression). -/
def exprNeverZeroBounded (B : Std.HashMap String Nat) (e : Expression p) : Bool :=
  match linearize e with
  | none => false
  | some l =>
    match boundedSumMax B l.norm.terms with
    | some M => decide (M < l.norm.const.val)
    | none => false

theorem exprNeverZeroBounded_sound (B : Std.HashMap String Nat) (e : Expression p)
    (hp : 0 < p) (h : exprNeverZeroBounded B e = true) (env : String → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (env v).val < bound) : e.eval env ≠ 0 := by
  intro h0
  unfold exprNeverZeroBounded at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hl
    split at h
    · rename_i M hM
      have hzero : l.norm.eval env = 0 := by
        rw [l.norm_eval, ← linearize_eval _ l hl]; exact h0
      exact linNeverZero B l.norm M hp hM (of_decide_eq_true h) env hB hzero
    · exact absurd h (by simp)

/-- Enumeration certificate: all points of the (capped) domain box give a nonzero value. -/
def exprNeverZeroEnum {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (e : Expression p) : Bool :=
  match T.doms e.vars.dedup with
  | none => false
  | some doms =>
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 4096) &&
      (assignments doms).all (fun a => decide (e.eval (envOf a) ≠ 0))

theorem exprNeverZeroEnum_sound {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (e : Expression p) (h : exprNeverZeroEnum T e = true)
    (env : String → ZMod p) (hsat : cs.satisfies bs env) : e.eval env ≠ 0 := by
  unfold exprNeverZeroEnum at h
  split at h
  · exact absurd h (by simp)
  · rename_i doms hdoms
    rw [Bool.and_eq_true] at h
    have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
      mem_assignments doms env (T.doms_sound _ doms hdoms env hsat)
    have hcover : ∀ y ∈ e.vars, y ∈ doms.map Prod.fst := by
      rw [T.doms_fst _ doms hdoms]
      intro y hy
      exact List.mem_dedup.2 hy
    have heval : e.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = e.eval env :=
      Expression.eval_congr e _ _ (fun y hy => envOf_map doms env y (hcover y hy))
    have := of_decide_eq_true (List.all_eq_true.mp h.2 _ hmem)
    rwa [heval] at this

/-! ## Payload inequality between two interactions -/

/-- The `i`-th payload slot as an expression (`0` for out-of-range slots). -/
def slotExprOf (bi : BusInteraction (Expression p)) (i : Nat) : Expression p :=
  (bi.payload[i]?).getD (.const 0)

/-- Certify that the evaluated payloads of `A` and `B` always differ: different lengths, or
    some slot whose difference is provably never zero. -/
def payloadNeq {cs : ConstraintSystem p} {bs : BusSemantics p}
    (Bnd : Std.HashMap String Nat)
    (T : DomainTable p cs bs) (A B : BusInteraction (Expression p)) : Bool :=
  decide (A.payload.length ≠ B.payload.length) ||
  (List.range A.payload.length).any (fun i =>
    let d := eqExpr (slotExprOf A i) (slotExprOf B i)
    exprNeverZeroConst d || exprNeverZeroBounded Bnd d ||
      exprNeverZeroEnum T d)

theorem payloadNeq_sound {cs : ConstraintSystem p} {bs : BusSemantics p}
    (Bnd : Std.HashMap String Nat)
    (hBnd : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, Bnd[x]? = some b → (env x).val < b)
    (T : DomainTable p cs bs)
    (A B : BusInteraction (Expression p)) (hp : 0 < p)
    (h : payloadNeq Bnd T A B = true) (env : String → ZMod p)
    (hsat : cs.satisfies bs env) :
    (A.eval env).payload ≠ (B.eval env).payload := by
  intro heq
  have hbus : ∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false := fun bi hbi => hsat.2.1 bi hbi
  rcases (Bool.or_eq_true _ _).mp h with hlen | hslot
  · -- different payload lengths: the evaluated lists cannot be equal
    have := congrArg List.length heq
    simp only [BusInteraction.eval, List.length_map] at this
    exact of_decide_eq_true hlen this
  · obtain ⟨i, _, hi⟩ := List.any_eq_true.1 hslot
    -- the slot values agree because the payloads are equal…
    have hslots := payloadSlot_eval_eq A.payload B.payload env heq i
    -- …but the difference is provably nonzero
    have hd : (eqExpr (slotExprOf A i) (slotExprOf B i)).eval env = 0 := by
      rw [eqExpr_eval]
      show (slotExprOf A i).eval env - (slotExprOf B i).eval env = 0
      unfold slotExprOf
      rw [hslots]
      ring
    rcases (Bool.or_eq_true _ _).mp hi with hi' | henum
    · rcases (Bool.or_eq_true _ _).mp hi' with hconst | hbounded
      · exact exprNeverZeroConst_sound _ hconst env hd
      · exact exprNeverZeroBounded_sound Bnd _ hp hbounded env (hBnd env hbus) hd
    · exact exprNeverZeroEnum_sound T _ henum env hsat hd

/-! ## The anchored-maximum certificate -/

/-- Not possibly an active receive: constant multiplicity ≠ −1. -/
def notRecv (bi : BusInteraction (Expression p)) : Bool :=
  match multConst bi with
  | some m => decide (m ≠ -1)
  | none => false

/-- All checked side conditions for an execution-chain link on `busId` (an empty-address
    declared bus). `S` is the send we chain; `W` is a **witness send appearing later in the
    interaction list** (`L` splits as `pre ++ S :: post` with `W ∈ post`) whose payload
    provably differs from `S`'s. By the discipline's monotonicity clause `S` is listed before
    `W`, so `tsVal S ≤ tsVal W`; the payload difference plus the timestamp-uniqueness clause
    make it strict, so `S` is not the timestamp maximum and (in-window consumption) is
    consumed in-fragment. Every possible receive except `Rt` provably differs from `S`, so
    `Rt` is that consumer. This avoids needing any fact about the block's terminal
    (possibly symbolic-target) send. -/
def checkExecChain (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bnd : Std.HashMap String Nat)
    (T : DomainTable p cs bs) (busId : Nat) (shape : MemoryBusShape)
    (pre post : List (BusInteraction (Expression p)))
    (S W Rt : BusInteraction (Expression p)) : Bool :=
  let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
  decide ((1 : ZMod p) ≠ 0) &&
  decide (shape.addressFields = []) &&
  decide (L = pre ++ S :: post) &&
  decide (W ∈ post) &&
  decide (Rt ∈ L) &&
  decide (multConst S = some 1) && decide (multConst W = some 1) &&
  decide (multConst Rt = some (-1)) &&
  payloadNeq Bnd T W S &&
  L.all (fun bi => decide (bi = Rt) || notRecv bi || payloadNeq Bnd T S bi)

theorem checkExecChain_sound (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bnd : Std.HashMap String Nat)
    (hBnd : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, Bnd[x]? = some b → (env x).val < b)
    (T : DomainTable p cs bs) (busId : Nat)
    (shape : MemoryBusShape) (pre post : List (BusInteraction (Expression p)))
    (S W Rt : BusInteraction (Expression p))
    (hdecl : bs.memoryBus busId = some shape) (hp : 0 < p)
    (hchk : checkExecChain cs bs Bnd T busId shape pre post S W Rt = true)
    (env : String → ZMod p) (hsat : cs.satisfies bs env) :
    ∀ c ∈ memEqConstraints shape S Rt, c.eval env = 0 := by
  unfold checkExecChain at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1ne, hfields⟩, hsplit⟩, hWpost⟩, hRtmem⟩, hSm⟩, hWm⟩, hRtm⟩,
    hWS⟩, hmatch⟩ := hchk
  have h1ne := of_decide_eq_true h1ne
  have hfields : shape.addressFields = [] := of_decide_eq_true hfields
  have hsplit : cs.busInteractions.filter (fun bi => bi.busId = busId)
      = pre ++ S :: post := of_decide_eq_true hsplit
  have hWpost : W ∈ post := of_decide_eq_true hWpost
  have hRtmem := of_decide_eq_true hRtmem
  have hSm := of_decide_eq_true hSm
  have hWm := of_decide_eq_true hWm
  have hRtm := of_decide_eq_true hRtm
  set L := cs.busInteractions.filter (fun bi => bi.busId = busId) with hL
  set msgs := L.map (fun bi => bi.eval env) with hmsgs
  -- `S` and `W` are in `L`, from the split
  have hSmem : S ∈ L := by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hWmem : W ∈ L := by
    rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hWpost)
  obtain ⟨hc, hb, hd⟩ := hsat
  obtain ⟨c1, c2, c3, c4, c5, cmono⟩ := hd busId shape hdecl
  have hsat' : cs.satisfies bs env := ⟨hc, hb, hd⟩
  -- every message has the same (empty) address
  have haddr : ∀ m m' : BusInteraction (ZMod p), shape.address m = shape.address m' := by
    intro m m'
    simp [MemoryBusShape.address, hfields]
  have hmem : ∀ bi ∈ L, bi.eval env ∈ msgs := fun bi hbi => List.mem_map.2 ⟨bi, hbi, rfl⟩
  -- evaluated multiplicities
  have hSev : (S.eval env).multiplicity = 1 := S.multiplicity.constValue?_sound 1 hSm env
  have hWev : (W.eval env).multiplicity = 1 := W.multiplicity.constValue?_sound 1 hWm env
  -- `S` is listed before `W`, so by monotonicity `tsVal S ≤ tsVal W`
  have hWms : (W.eval env) ∈ post.map (fun bi => bi.eval env) :=
    List.mem_map.2 ⟨W, hWpost, rfl⟩
  have hsplitms : msgs = pre.map (fun bi => bi.eval env) ++
      (S.eval env) :: post.map (fun bi => bi.eval env) := by
    rw [hmsgs, hsplit, List.map_append, List.map_cons]
  have hle : shape.tsVal (S.eval env) ≤ shape.tsVal (W.eval env) := by
    have cmono' : msgs.Pairwise (fun a b => a.multiplicity ≠ 0 → b.multiplicity ≠ 0 →
      shape.tsVal a ≤ shape.tsVal b) := cmono
    rw [hsplitms] at cmono'
    have hpc := (List.pairwise_cons.1 (List.pairwise_append.1 cmono').2.1).1
    exact hpc (W.eval env) hWms (by rw [hSev]; exact h1ne) (by rw [hWev]; exact h1ne)
  -- payload difference + uniqueness make it strict
  have hne : shape.tsVal (S.eval env) ≠ shape.tsVal (W.eval env) := by
    intro heq
    exact payloadNeq_sound Bnd hBnd T W S hp hWS env hsat'
      (c4 (W.eval env) (hmem W hWmem) (S.eval env) (hmem S hSmem)
        hWev hSev (haddr _ _) heq.symm)
  have hSlt : shape.tsVal (S.eval env) < shape.tsVal (W.eval env) := lt_of_le_of_ne hle hne
  -- so `S` is consumed in-fragment (take the least active send strictly above it)
  obtain ⟨R, hRmem, hRmult, hRpay⟩ : ∃ R ∈ msgs, R.multiplicity = -1 ∧
      R.payload = (S.eval env).payload := by
    set TS : Set ℕ := {t | ∃ m' ∈ msgs, m'.multiplicity = 1 ∧ shape.tsVal m' = t ∧
      shape.tsVal (S.eval env) < t} with hTS
    have hne' : TS.Nonempty :=
      ⟨shape.tsVal (W.eval env), W.eval env, hmem W hWmem, hWev, rfl, hSlt⟩
    obtain ⟨m', hm'mem, hm'mult, hm'ts, hm'gt⟩ := Nat.sInf_mem hne'
    have hnobetween : ∀ m'' ∈ msgs, m''.multiplicity = 1 →
        shape.address m'' = shape.address (S.eval env) →
        ¬(shape.tsVal (S.eval env) < shape.tsVal m'' ∧
          shape.tsVal m'' < shape.tsVal m') := by
      rintro m'' hm''mem hm''mult _ ⟨hlo, hhi⟩
      have : shape.tsVal m'' ∈ TS := ⟨m'', hm''mem, hm''mult, rfl, hlo⟩
      have := Nat.sInf_le this
      omega
    exact c2 (S.eval env) (hmem S hSmem) m' hm'mem hSev hm'mult (haddr _ _)
      (by omega) hnobetween
  -- Step 5: the consumer is Rt
  obtain ⟨bi, hbi, hbieq⟩ := List.mem_map.1 hRmem
  have hbiRt : bi = Rt := by
    rcases (Bool.or_eq_true _ _).mp (List.all_eq_true.mp hmatch bi hbi) with hcase | hneq
    · rcases (Bool.or_eq_true _ _).mp hcase with hcase | hnr
      · exact of_decide_eq_true hcase
      · exfalso
        unfold notRecv at hnr
        split at hnr
        · rename_i m hm
          have hme : (bi.eval env).multiplicity = m :=
            bi.multiplicity.constValue?_sound m hm env
          rw [hbieq] at hme
          rw [hme] at hRmult
          exact absurd hRmult (of_decide_eq_true hnr)
        · exact absurd hnr (by simp)
    · exact absurd (hbieq ▸ hRpay) (payloadNeq_sound Bnd hBnd T S bi hp hneq env hsat').symm
  -- Step 6: slot-wise equalities
  have hpay : Rt.payload.map (fun e => e.eval env) = S.payload.map (fun e => e.eval env) := by
    have h' := hRpay
    rw [← hbieq, hbiRt] at h'
    exact h'
  intro c hcmem
  unfold memEqConstraints at hcmem
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hcmem
  rw [eqExpr_eval, payloadSlot_eval_eq Rt.payload S.payload env hpay i]
  ring

/-! ## The search (proof-free) and the batch pass -/

/-- All checked execution-chain links: for each empty-address declared bus, find an anchor
    send (payload-refuted against every possible receive), then for each other send the
    unique unrefuted receive. -/
def findExecChains (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bnd : Std.HashMap String Nat)
    (T : DomainTable p cs bs) :
    List (Nat × List (BusInteraction (Expression p)) × List (BusInteraction (Expression p))
      × BusInteraction (Expression p) × BusInteraction (Expression p)
      × BusInteraction (Expression p)) :=
  ((cs.busInteractions.map (fun bi => bi.busId)).dedup).flatMap (fun busId =>
    match bs.memoryBus busId with
    | none => []
    | some shape =>
      if shape.addressFields.isEmpty then
        let L := cs.busInteractions.filter (fun bi => bi.busId = busId)
        let receives := L.filter (fun bi => multConst bi = some (-1))
        -- chain each send `S` using the next payload-different send after it as the witness
        L.filterMap (fun S =>
          if multConst S ≠ some 1 then none
          else
            let pre := L.takeWhile (fun bi => bi ≠ S)
            let post := (L.dropWhile (fun bi => bi ≠ S)).tail
            match (post.filter (fun bi =>
                multConst bi = some 1 && payloadNeq Bnd T bi S)).head? with
            | none => none
            | some W =>
              match receives.filter (fun r => !payloadNeq Bnd T S r) with
              | [Rt] =>
                if checkExecChain cs bs Bnd T busId shape pre post S W Rt then
                  some (busId, pre, post, S, W, Rt)
                else none
              | _ => none)
      else [])

/-- Re-check every found link and collect the entailed equality constraints, with proof. -/
def collectExecEqs (cs : ConstraintSystem p) (bs : BusSemantics p)
    (Bnd : Std.HashMap String Nat)
    (hBnd : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) →
      ∀ x b, Bnd[x]? = some b → (env x).val < b)
    (T : DomainTable p cs bs) (hp : 0 < p) :
    List (Nat × List (BusInteraction (Expression p)) × List (BusInteraction (Expression p))
      × BusInteraction (Expression p) × BusInteraction (Expression p)
      × BusInteraction (Expression p)) →
    { out : List (Expression p) //
        ∀ env, cs.satisfies bs env → ∀ c ∈ out, c.eval env = 0 }
  | [] => ⟨[], fun _ _ _ hc => absurd hc (by simp)⟩
  | (busId, pre, post, S, W, Rt) :: rest =>
    let ⟨acc, hacc⟩ := collectExecEqs cs bs Bnd hBnd T hp rest
    match hdecl : bs.memoryBus busId with
    | none => ⟨acc, hacc⟩
    | some shape =>
      if hchk : checkExecChain cs bs Bnd T busId shape pre post S W Rt = true then
        ⟨memEqConstraints shape S Rt ++ acc, by
          intro env hsat c hc
          rcases List.mem_append.1 hc with h | h
          · exact checkExecChain_sound cs bs Bnd hBnd T busId shape pre post S W Rt hdecl hp
              hchk env hsat c h
          · exact hacc env hsat c h⟩
      else ⟨acc, hacc⟩

/-- The execution-chain pass: add the entailed consumer-equals-producer equations for every
    checked link on empty-address declared buses (skipping equations already present or
    trivially zero, so the pass is idempotent). The Gauss/affine machinery then substitutes
    the timestamp/pc links, which in turn make the memory bus chain across instructions. -/
def execChainPass : VerifiedPassW p := fun cs bs facts =>
  if hp : 0 < p then
    let T : DomainTable p cs bs :=
      if hpr : p.Prime then
        haveI : Fact p.Prime := ⟨hpr⟩
        haveI : NeZero p := ⟨hpr.ne_zero⟩
        addBusDoms facts cs.busInteractions (fun _ h => h)
          (addConstraintDoms cs.algebraicConstraints (fun _ h => h) DomainTable.empty)
      else DomainTable.empty
    let Bm : BoundsMap p cs bs := BoundsMap.build facts
    let ⟨eqs, heqs⟩ := collectExecEqs cs bs Bm.map Bm.sound T hp
      (findExecChains cs bs Bm.map T)
    let new := eqs.filter
      (fun c => !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c)
    if new.isEmpty then ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
    else
      ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new },
       cs.addConstraints_correct bs new (fun env hsat c hc =>
         heqs env hsat c (List.mem_of_mem_filter hc))⟩
  else ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
