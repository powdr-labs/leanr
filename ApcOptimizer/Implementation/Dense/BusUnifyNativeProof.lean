import ApcOptimizer.Implementation.Dense.BusUnifyNative
import ApcOptimizer.Implementation.Dense.AddrDiseqProof
import ApcOptimizer.Implementation.MemoryBusDrop

set_option autoImplicit false

/-! # Native soundness for the dense `busUnify` pass (Task 3, busUnify cluster, chunk M2 — prover)

Native `DensePassCorrect` for `denseBusUnifyF` (`Dense/BusUnifyNative.lean`), lifted to the audited
`Variable` spec through `DenseVerifiedPassW.ofNative` (`Dense/Bridge.lean`). **This is the first
native pass that consumes `BusFacts` at runtime** (`facts.memShape` in the transform,
`facts.admissible_sound` in the proof), so it also establishes the template later fact-consuming
ports copy.

## Refinement shape

`busUnify` only **adds constraints** — slot equalities between existing payload columns, gated so no
new variable is introduced (`z ∈ d.occ`). Soundness (output-satisfying ⇒ input-satisfying) is a
constraint-superset argument, packaged once as the reusable
`DensePassCorrect.denseAddConstraints`. The substance is **real-trace completeness**: every
admissible satisfying assignment already fulfils the added equalities. That is proved natively over
dense environments `VarId → ZMod p` by re-deriving the spec's entailment chain densely:

* `denseConsecutivePayloadEq` — **the load-bearing fact application.** From dense admissibility, the
  VM memory discipline (`admissibleMemoryBus.consecutive`) applied through `facts.admissible_sound`
  forces `S.payload = R.payload` for a consecutive same-address send→receive pair on a declared bus.
* `denseCheckPair_sound` — composes the M1 (`Dense/AddrDiseqProof.lean`) address-disequality
  certificates (which rule out every `mid` message as a same-address active blocker) with
  `denseConsecutivePayloadEq`, concluding every slot equality (`denseMemEqConstraints`) evaluates to
  zero.
* `denseFindConsumer_split`/`denseCandidateSplits_split` recover the split equation
  `filter busId = pre ++ S :: mid ++ R :: post` that the dense enumerator dropped (the spec carried
  it in a `Subtype`); `denseCollectForBus_sound`/`denseCollectAllBuses_sound` fold the entailment
  over the candidate list and every declared bus.

**Fact-consumption template** (for later chunks): (1) apply `BusFacts` soundness fields at the
*value* level over `denseBIEval` from dense satisfaction — no `BusFacts`-map correspondence, no
decode; (2) reuse the M1 certificate soundness lemmas (already reduced to spec `_sound` via decode),
so no per-certificate representation reasoning appears here; (3) the pass's runtime `facts.memShape`
call and the proof's `facts.admissible_sound` both take the *original* `facts` unchanged. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Small value-level helpers -/

/-- A dense constant-folded expression evaluates to its recognized constant (native analogue of
    `Expression.constValue?_sound`; kept file-local to avoid a heavy cross-pass import). -/
private theorem denseConstValueEval (e : DenseExpr p) (c : ZMod p) (h : e.constValue? = some c)
    (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  unfold DenseExpr.constValue? at h
  cases hf : e.fold with
  | const n => rw [hf] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | var j => rw [hf] at h; simp at h
  | add a b => rw [hf] at h; simp at h
  | mul a b => rw [hf] at h; simp at h

/-- `denseEqExpr e₂ e₁` evaluates to `e₂ − e₁` (mirrors `eqExpr_eval`). -/
theorem denseEqExpr_eval (e2 e1 : DenseExpr p) (denv : VarId → ZMod p) :
    (denseEqExpr e2 e1).eval denv = e2.eval denv - e1.eval denv := by
  show e2.eval denv + (-1) * e1.eval denv = _
  ring

/-- Both entries of equal-under-`denv` payloads evaluate equally (mirrors `payloadSlot_eval_eq`). -/
theorem densePayloadSlot_eval_eq (P Q : List (DenseExpr p)) (denv : VarId → ZMod p)
    (h : P.map (fun e => e.eval denv) = Q.map (fun e => e.eval denv)) (i : Nat) :
    ((P[i]?).getD (.const 0)).eval denv = ((Q[i]?).getD (.const 0)).eval denv := by
  have hi := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map] at hi
  cases hP : P[i]? <;> cases hQ : Q[i]? <;> rw [hP, hQ] at hi <;> simp_all

/-! ## The constant-address (dis)equality certificates -/

/-- **`denseAddrConstsEq` is sound** (mirrors `addrConstsEq_sound`). -/
theorem denseAddrConstsEq_sound (shape : MemoryBusShape) (S S' : BusInteraction (DenseExpr p))
    (h : denseAddrConstsEq shape S S' = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) = shape.address (denseBIEval S' denv) := by
  unfold MemoryBusShape.address
  apply List.map_congr_left
  intro slot hslot
  have hs := List.all_eq_true.mp h slot hslot
  show (S.payload.map (fun e => e.eval denv))[slot]?
    = (S'.payload.map (fun e => e.eval denv))[slot]?
  rw [List.getElem?_map, List.getElem?_map]
  split at hs
  · rename_i e e' hP hQ
    rcases (Bool.or_eq_true _ _).mp hs with hsyn | hs
    · have hee : e = e' := of_decide_eq_true hsyn
      rw [hP, hQ, hee]
    · split at hs
      · rename_i c c' he he'
        have hcc : c = c' := of_decide_eq_true hs
        rw [hP, hQ]
        simp only [Option.map_some]
        rw [denseConstValueEval e c he denv, denseConstValueEval e' c' he' denv, hcc]
      all_goals exact absurd hs (by simp)
  all_goals exact absurd hs (by simp)

/-- **`denseAddrConstsNeq` is sound** (mirrors `addrConstsNeq_sound`). -/
theorem denseAddrConstsNeq_sound (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p))
    (h : denseAddrConstsNeq shape S bi = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => simp [hSp] at hcond
  | some e =>
    cases hbp : bi.payload[slot]? with
    | none => simp [hSp, hbp] at hcond
    | some e' =>
      cases hc : e.constValue? with
      | none => simp [hSp, hbp, hc] at hcond
      | some c =>
        cases hc' : e'.constValue? with
        | none => simp [hSp, hbp, hc, hc'] at hcond
        | some c' =>
          simp only [hSp, hbp, hc, hc'] at hcond
          have hne : e.eval denv ≠ e'.eval denv := by
            rw [denseConstValueEval e c hc denv, denseConstValueEval e' c' hc' denv]
            exact of_decide_eq_true hcond
          exact denseAddr_slot_neq shape S bi denv hslot hSp hbp hne

/-! ## The load-bearing fact application -/

/-- Filtering evaluated dense messages by bus id equals evaluating the bus-filtered interactions
    (mirrors `map_eval_filter_busId`; `denseBIEval` preserves `busId`). -/
theorem dense_map_eval_filter_busId (l : List (BusInteraction (DenseExpr p))) (busId : Nat)
    (denv : VarId → ZMod p) :
    (l.map (fun bi => denseBIEval bi denv)).filter (fun m => m.busId = busId)
    = (l.filter (fun bi => bi.busId = busId)).map (fun bi => denseBIEval bi denv) := by
  induction l with
  | nil => rfl
  | cons bi rest ih =>
    have hbid : (denseBIEval bi denv).busId = bi.busId := rfl
    simp only [List.map_cons, List.filter_cons, hbid]
    by_cases h : bi.busId = busId
    · simp [h, ih]
    · simp [h, ih]

/-- **The consecutive-payload equality (dense).** From dense admissibility, `facts.admissible_sound`
    delivers the memory discipline `admissibleMemoryBus` on the bus's active messages, and
    `admissibleMemoryBus.consecutive` forces a consecutive same-address send→receive pair to carry
    equal payloads. Native mirror of `consecutivePayloadEq` — the load-bearing `BusFacts` use. -/
theorem denseConsecutivePayloadEq (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (denv : VarId → ZMod p)
    (hadm : d.admissible bs denv)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre mid post : List (BusInteraction (DenseExpr p)))
    (S R : BusInteraction (DenseExpr p))
    (hsplit : d.busInteractions.filter (fun bi => bi.busId = busId) = pre ++ S :: mid ++ R :: post)
    (hS : (denseBIEval S denv).multiplicity = shape.setNewMult)
    (hR : (denseBIEval R denv).multiplicity = -shape.setNewMult)
    (haddr : shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv))
    (hmid : ∀ m ∈ mid, (denseBIEval m denv).multiplicity ≠ 0 →
        shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False) :
    (denseBIEval S denv).payload = (denseBIEval R denv).payload := by
  have hadm' : bs.admissible ((d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
  have hb := facts.admissible_sound (d.busInteractions.map (fun bi => denseBIEval bi denv)) hadm'
    busId shape hshape
  rw [dense_map_eval_filter_busId, hsplit, List.map_append, List.map_cons, List.map_append,
    List.map_cons] at hb
  exact admissibleMemoryBus.consecutive shape _ hp1 hb
    (pre.map (fun bi => denseBIEval bi denv)) (mid.map (fun bi => denseBIEval bi denv))
    (post.map (fun bi => denseBIEval bi denv)) (denseBIEval S denv) (denseBIEval R denv) rfl hS hR
    haddr
    (by
      intro m hm hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
      exact hmid m0 hm0 hmne hmaddr)

/-! ## The checked pair and its entailment (dense) -/

/-- **`denseCheckPair` entails the slot equalities.** Native mirror of `checkPair_sound`: the M1
    address-disequality certificates rule out every `mid` message as a same-address active blocker,
    so `denseConsecutivePayloadEq` forces `S.payload = R.payload`, whence every
    `denseMemEqConstraints` slot equality evaluates to zero. The nonzero-witness table is fixed to
    the pass's `DenseNonzeroWits.build d.algebraicConstraints`. -/
theorem denseCheckPair_sound (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre : List (BusInteraction (DenseExpr p))) (S : BusInteraction (DenseExpr p))
    (mid : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p))
    (post : List (BusInteraction (DenseExpr p)))
    (hsplit : d.busInteractions.filter (fun bi => bi.busId = busId) = pre ++ S :: mid ++ R :: post)
    (hchk : denseCheckPair shape T (DenseNonzeroWits.build d.algebraicConstraints) S mid R = true)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseMemEqConstraints shape S R, c.eval denv = 0 := by
  have hmemfilter : ∀ x ∈ pre ++ S :: mid ++ R :: post, x ∈ d.busInteractions := by
    intro x hx; rw [← hsplit] at hx; exact List.mem_of_mem_filter hx
  have hScov : denseBICovered reg S := hcov.2 S (hmemfilter S (by simp))
  have hRcov : denseBICovered reg R := hcov.2 R (hmemfilter R (by simp))
  unfold denseCheckPair at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨hSm, hRm⟩, haddrEq⟩, hmidall⟩ := hchk
  have hSm : denseMultConst S = some shape.setNewMult := of_decide_eq_true hSm
  have hRm : denseMultConst R = some (-shape.setNewMult) := of_decide_eq_true hRm
  have hSev : (denseBIEval S denv).multiplicity = shape.setNewMult :=
    denseConstValueEval S.multiplicity shape.setNewMult hSm denv
  have hRev : (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    denseConstValueEval R.multiplicity (-shape.setNewMult) hRm denv
  have haddr : shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv) :=
    denseAddrConstsEq_sound shape S R haddrEq denv
  have hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  have hmid : ∀ m ∈ mid, (denseBIEval m denv).multiplicity ≠ 0 →
      shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False := by
    intro m hm hmne hmaddr
    have hmcov : denseBICovered reg m := hcov.2 m (hmemfilter m (by simp [hm]))
    rcases (Bool.or_eq_true _ _).mp (List.all_eq_true.mp hmidall m hm) with hcond | hz
    · rcases (Bool.or_eq_true _ _).mp hcond with hcond_a | hnz
      · rcases (Bool.or_eq_true _ _).mp hcond_a with hcond2 | h2r
        · rcases (Bool.or_eq_true _ _).mp hcond2 with hneq | haff
          · exact denseAddrConstsNeq_sound shape S m hneq denv (hmaddr.symm)
          · exact denseAddrAffineNeq_sound reg shape S m hScov hmcov haff denv (hmaddr.symm)
        · exact denseAddrTwoRootNeq_sound reg shape T hT hcov.1 S m hScov hmcov h2r denv hcon
            (hmaddr.symm)
      · exact denseAddrNonzeroNeq_sound reg shape d.algebraicConstraints hcov.1 S m hScov hmcov hnz
          denv hcon (hmaddr.symm)
    · have : (denseBIEval m denv).multiplicity = 0 :=
        denseConstValueEval m.multiplicity 0 (of_decide_eq_true hz) denv
      exact hmne this
  have hpay : (denseBIEval S denv).payload = (denseBIEval R denv).payload :=
    denseConsecutivePayloadEq d bs facts hp1 denv hadm busId shape hshape pre mid post S R
      hsplit hSev hRev haddr hmid
  intro c hc
  unfold denseMemEqConstraints at hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
  rw [denseEqExpr_eval]
  have hPQ : R.payload.map (fun e => e.eval denv) = S.payload.map (fun e => e.eval denv) := hpay.symm
  rw [densePayloadSlot_eval_eq R.payload S.payload denv hPQ i, sub_self]

/-! ## The candidate enumeration recovers the split equation -/

/-- The split equation the dense enumerator dropped: `denseFindConsumer` returns a `(mid, R, post)`
    whose recomposition is `revMid.reverse ++ rest`. Mirrors `findConsumer`'s `Subtype` proof. -/
theorem denseFindConsumer_split {shape : MemoryBusShape} {T : DenseTwoRootMap p}
    {nw : DenseNonzeroWits p} {S : BusInteraction (DenseExpr p)} :
    ∀ (rest revMid : List (BusInteraction (DenseExpr p)))
      (mid : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p))
      (post : List (BusInteraction (DenseExpr p))),
    denseFindConsumer shape T nw S revMid rest = some (mid, R, post) →
    revMid.reverse ++ rest = mid ++ R :: post := by
  intro rest
  induction rest with
  | nil => intro revMid mid R post h; simp [denseFindConsumer] at h
  | cons r rest' ih =>
    intro revMid mid R post h
    rw [denseFindConsumer] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; rfl
    · have hnext := ih (r :: revMid) mid R post h
      rw [← hnext]; simp [List.reverse_cons, List.append_assoc]

/-- Every candidate `denseCandidateSplits` returns recomposes to `revPre.reverse ++ rest`. Mirrors
    the `SplitCand` invariant the spec carried in its `Subtype`. -/
theorem denseCandidateSplits_split {shape : MemoryBusShape} {T : DenseTwoRootMap p}
    {nw : DenseNonzeroWits p} :
    ∀ (rest revPre : List (BusInteraction (DenseExpr p))) (cand : DenseSplitCand p),
    cand ∈ denseCandidateSplits shape T nw revPre rest →
    revPre.reverse ++ rest = cand.1 ++ cand.2.1 :: cand.2.2.1 ++ cand.2.2.2.1 :: cand.2.2.2.2 := by
  intro rest
  induction rest with
  | nil => intro revPre cand h; simp [denseCandidateSplits] at h
  | cons S rest' ih =>
    intro revPre cand h
    rw [denseCandidateSplits, List.mem_append] at h
    rcases h with h | h
    · split_ifs at h with hmc
      · cases hfc : denseFindConsumer shape T nw S [] rest' with
        | none => rw [hfc] at h; simp at h
        | some mrp =>
          obtain ⟨mid, R, post⟩ := mrp
          rw [hfc] at h
          simp only [List.mem_singleton] at h
          subst h
          have hsp := denseFindConsumer_split rest' [] mid R post hfc
          simp only [List.reverse_nil, List.nil_append] at hsp
          show revPre.reverse ++ (S :: rest') = revPre.reverse ++ S :: mid ++ R :: post
          rw [hsp]; simp only [List.append_assoc, List.cons_append]
      · simp at h
    · have hrec := ih (S :: revPre) cand h
      rw [← hrec]; simp [List.reverse_cons, List.append_assoc]

/-! ## The per-bus / all-bus entailment -/

/-- Every entailed equality collected for one bus evaluates to zero on admissible satisfying
    assignments. Mirrors `collectForBus`'s `Subtype` proof, feeding each candidate's split equation
    to `denseCheckPair_sound`. -/
theorem denseCollectForBus_sound (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ (cands : List (DenseSplitCand p)),
    (∀ cand ∈ cands, d.busInteractions.filter (fun bi => bi.busId = busId)
        = cand.1 ++ cand.2.1 :: cand.2.2.1 ++ cand.2.2.2.1 :: cand.2.2.2.2) →
    ∀ c ∈ denseCollectForBus shape T (DenseNonzeroWits.build d.algebraicConstraints) cands,
      c.eval denv = 0 := by
  intro cands
  induction cands with
  | nil => intro _ c hc; simp [denseCollectForBus] at hc
  | cons cand rest ih =>
    intro hsplitc c hc
    obtain ⟨pre, S, mid, R, post⟩ := cand
    have hsplit : d.busInteractions.filter (fun bi => bi.busId = busId)
        = pre ++ S :: mid ++ R :: post := hsplitc (pre, S, mid, R, post) (List.mem_cons_self ..)
    have hrest : ∀ cand ∈ rest, d.busInteractions.filter (fun bi => bi.busId = busId)
        = cand.1 ++ cand.2.1 :: cand.2.2.1 ++ cand.2.2.2.1 :: cand.2.2.2.2 :=
      fun cand h => hsplitc cand (List.mem_cons_of_mem _ h)
    rw [denseCollectForBus] at hc
    split_ifs at hc with hchk
    · rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact denseCheckPair_sound d bs facts hp1 reg hcov T hT busId shape hshape pre S mid R post
          hsplit hchk denv hadm hsat c hc
      · exact ih hrest c hc
    · exact ih hrest c hc

/-- Every entailed equality collected across all declared buses evaluates to zero. Mirrors
    `collectAllBuses`'s `Subtype` proof. -/
theorem denseCollectAllBuses_sound (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ (busIds : List Nat),
    ∀ c ∈ denseCollectAllBuses d bs facts (DenseTwoRootMap.build d.algebraicConstraints)
        (DenseNonzeroWits.build d.algebraicConstraints) busIds,
      c.eval denv = 0 := by
  intro busIds
  induction busIds with
  | nil => intro c hc; simp [denseCollectAllBuses] at hc
  | cons busId rest ih =>
    intro c hc
    rw [denseCollectAllBuses] at hc
    cases hms : facts.memShape busId with
    | none => rw [hms] at hc; exact ih c hc
    | some shape =>
      rw [hms, List.mem_append] at hc
      rcases hc with hc | hc
      · refine denseCollectForBus_sound d bs facts hp1 reg hcov
          (DenseTwoRootMap.build d.algebraicConstraints)
          (DenseTwoRootMap.build_sound d.algebraicConstraints) busId shape hms denv hadm hsat _ ?_ c
          hc
        intro cand hcand
        have hh := denseCandidateSplits_split
          (d.busInteractions.filter (fun bi => bi.busId = busId)) [] cand hcand
        simpa using hh
      · exact ih c hc

/-! ## The reusable native "add entailed constraints" correctness -/

/-- Adding constraints that every admissible satisfying assignment already fulfils (and that
    introduce no new occurring variable) is `DensePassCorrect`. Native mirror of
    `ConstraintSystem.addConstraints_correct`; reusable by every "append entailed equalities" dense
    pass. Soundness is a constraint superset (drop `new`); the added constraints touch no bus
    interaction, so admissibility and side effects are unchanged. -/
theorem DensePassCorrect.denseAddConstraints {isInput : VarId → Bool} (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (new : List (DenseExpr p))
    (hnv : ∀ c ∈ new, ∀ z ∈ c.vars, z ∈ d.occ)
    (H : ∀ denv, d.admissible bs denv → d.satisfies bs denv → ∀ c ∈ new, c.eval denv = 0) :
    DensePassCorrect isInput d
      { d with algebraicConstraints := d.algebraicConstraints ++ new } [] bs := by
  set out : DenseConstraintSystem p :=
    { d with algebraicConstraints := d.algebraicConstraints ++ new } with hout
  have hfwd : ∀ denv, out.satisfies bs denv → d.satisfies bs denv := by
    rintro denv ⟨hc, hb⟩
    exact ⟨fun c hcm => hc c (List.mem_append_left _ hcm), hb⟩
  have hoccsub : ∀ i ∈ out.occ, i ∈ d.occ := by
    intro i hi
    have hi2 : i ∈ (d.algebraicConstraints ++ new).flatMap DenseExpr.vars
        ++ d.busInteractions.flatMap denseBIVars := hi
    rw [List.mem_append, List.mem_flatMap, List.mem_flatMap] at hi2
    rcases hi2 with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
    · rcases List.mem_append.1 hc with h | h
      · exact DenseConstraintSystem.mem_occ_of_constraint h hic
      · exact hnv c h i hic
    · exact DenseConstraintSystem.mem_occ_of_bi hbi hib
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- soundness
    intro denv hsat
    exact ⟨denv, hfwd denv hsat, BusState.equiv_refl _⟩
  · -- invariant preservation
    intro hgi denv hsat bi hbi
    exact hgi denv (hfwd denv hsat) bi hbi
  · -- no new powdr-ID column
    intro i hi _; exact hoccsub i hi
  · -- completeness, witness `denv`
    intro denv hadm hsat
    have hout_sat : out.satisfies bs denv := by
      refine ⟨fun c hcm => ?_, hsat.2⟩
      rcases List.mem_append.1 hcm with h | h
      · exact hsat.1 c h
      · exact H denv hadm hsat c h
    refine ⟨denv, hout_sat, hadm, BusState.equiv_refl _, fun _ _ => rfl, ?_⟩
    intro inputVarIds _ i hi _
    show i ∈ d.occ ∧ denv i = denv i
    exact ⟨hoccsub i hi, rfl⟩

/-- `DensePassCorrect` reflexivity (the no-op branches of `denseBusUnifyF`). Kept file-local to
    avoid a heavy cross-pass import. -/
private theorem dpcRefl (isInput : VarId → Bool) (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    DensePassCorrect isInput d d [] bs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro denv hsat; exact ⟨denv, hsat, BusState.equiv_refl _⟩
  · intro hinv; exact hinv
  · intro i hi _; exact hi
  · intro denv hadm hsat
    refine ⟨denv, hsat, hadm, BusState.equiv_refl _, fun _ _ => rfl, ?_⟩
    intro inputVarIds _ i hi _
    show i ∈ d.occ ∧ denv i = denv i
    exact ⟨hi, rfl⟩

/-! ## The pass transform: correctness and coverage -/

/-- The list of entailed equalities `denseBusUnifyF` appends (mirrors its internal `new`, factored
    out so the guard cases get named hypotheses). -/
def denseBusUnifyNew (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let T := DenseTwoRootMap.build d.algebraicConstraints
  let nw := DenseNonzeroWits.build d.algebraicConstraints
  let eqs := denseCollectAllBuses d bs facts T nw
    ((d.busInteractions.map (fun bi => bi.busId)).dedup)
  let dVarSet := Std.HashSet.ofList d.occ
  let dHashes : Std.HashMap UInt64 (List (DenseExpr p)) :=
    d.algebraicConstraints.foldl (fun m c =>
      let h := c.bHash
      m.insert h (c :: m.getD h [])) ∅
  let containsC : DenseExpr p → Bool := fun c =>
    (dHashes.getD c.bHash []).any (fun c' => c' == c)
  eqs.filter
    (fun c => !c.normalize.fold.isConstZero && !containsC c
      && c.vars.all (fun z => dVarSet.contains z))

theorem denseBusUnifyF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseBusUnifyF bs facts d =
      (if (1 : ZMod p) ≠ 0 then
        (if (denseBusUnifyNew bs facts d).isEmpty then d
         else { d with algebraicConstraints := d.algebraicConstraints ++ denseBusUnifyNew bs facts d })
       else d) := rfl

/-- Every variable of an appended equality is an occurrence of `d`. -/
theorem denseBusUnifyNew_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseBusUnifyNew bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  have hp := (List.mem_filter.1 hc).2
  simp only [Bool.and_eq_true, List.all_eq_true] at hp
  have hz' := hp.2 z hz
  rw [Std.HashSet.contains_ofList] at hz'
  exact List.contains_iff_mem.mp hz'

/-- Every appended equality evaluates to zero on admissible satisfying assignments (the substance,
    via `denseCollectAllBuses_sound`). -/
theorem denseBusUnifyNew_sound (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (hp1 : (1 : ZMod p) ≠ 0)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBusUnifyNew bs facts d, c.eval denv = 0 := by
  intro c hc
  have hmem : c ∈ denseCollectAllBuses d bs facts (DenseTwoRootMap.build d.algebraicConstraints)
      (DenseNonzeroWits.build d.algebraicConstraints)
      ((d.busInteractions.map (fun bi => bi.busId)).dedup) := List.mem_of_mem_filter hc
  exact denseCollectAllBuses_sound d bs facts hp1 reg hcov denv hadm hsat _ c hmem

theorem denseBusUnifyF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseBusUnifyF bs facts d).CoveredBy reg := by
  rw [denseBusUnifyF_eq]
  split_ifs with hp1 hempty
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h | h
    · exact hcov.1 e h
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i (denseBusUnifyNew_vars bs facts d e h i hi)
  · exact hcov

theorem denseBusUnifyF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseBusUnifyF bs facts d) [] bs := by
  rw [denseBusUnifyF_eq]
  split_ifs with hp1 hempty
  · exact dpcRefl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseBusUnifyNew bs facts d)
      (denseBusUnifyNew_vars bs facts d)
      (fun denv hadm hsat => denseBusUnifyNew_sound bs facts reg d hcov hp1 denv hadm hsat)
  · exact dpcRefl reg.isInput d bs

/-! ## The native dense `busUnify` pass -/

/-- **The native dense `busUnify` pass.** Threads the original `facts` unchanged (real
    `facts.memShape` calls at runtime), connects to the audited spec via `DensePassCorrect.lift`
    (through `ofNative`) on the native `DensePassCorrect` proof — no commutation with the reference
    pass. -/
def denseBusUnifyPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofNative denseBusUnifyF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseBusUnifyF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseBusUnifyF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
