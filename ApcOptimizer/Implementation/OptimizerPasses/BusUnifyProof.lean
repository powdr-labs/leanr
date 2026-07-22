import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseqProof
import ApcOptimizer.Implementation.MemoryBusDrop

set_option autoImplicit false

/-! # Native soundness for the dense `busUnify` pass (Task 3, busUnify cluster, chunk M2 — prover)

Native `DensePassCorrect` for `denseBusUnifyF` (`Dense/BusUnifyNative.lean`), lifted to the audited
`Variable` spec through `DenseVerifiedPassW.of` (`Dense/Bridge.lean`). **This is the first
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
* `denseCandidateSplitsSweep_split` (via `denseSweepGo_split`) recovers the split equation
  `filter busId = pre ++ S :: mid ++ R :: post` that the dense sweep enumerator dropped (the spec
  carried it in a `Subtype`); `denseCollectForBus_sound`/`denseCollectAllBuses_sound` fold the
  entailment over the candidate list and every declared bus.

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

/-! ## The consumer sweep recovers the split equation (#165 delta, chunk C2)

Native mirror of the spec sweep's proof layer (`OptimizerPasses/BusUnify.lean:307-506`). The dense
sweep defs are plain data, so the `OpenRec.hi`/`hsplit` invariants and `sweepGo`'s `hsplit`/`hj`
arguments are reconstructed externally: `OpenWF`/`SplitEqC` state them, and `denseSweepGo_split`
threads them across `insert`/`erase`/`getElem?`/`toList` as an all-values-satisfy-P HashMap
invariant. -/

private abbrev SplitEqC (L : List (BusInteraction (DenseExpr p))) (cand : DenseSplitCand p) : Prop :=
  L = cand.1 ++ cand.2.1 :: cand.2.2.1 ++ cand.2.2.2.1 :: cand.2.2.2.2

private def OpenWF (L : List (BusInteraction (DenseExpr p))) (w : DenseOpenRec p) : Prop :=
  w.revPre.length = w.i ∧ L = w.revPre.reverse ++ w.S :: w.restAfter

theorem dense_split_of_positions
    {L revPre restAfter revSeen post : List (BusInteraction (DenseExpr p))}
    {S R : BusInteraction (DenseExpr p)} {i j : Nat}
    (hi : revPre.length = i) (hsplit : L = revPre.reverse ++ S :: restAfter)
    (hj : revSeen.length = j) (hnow : L = revSeen.reverse ++ R :: post) (hlt : i < j) :
    L = revPre.reverse ++ S :: restAfter.take (j - i - 1) ++ R :: post := by
  have hRA : restAfter = L.drop (i + 1) := by
    have h1 : L = (revPre.reverse ++ [S]) ++ restAfter := by rw [hsplit]; simp
    rw [h1, List.drop_left' (by simp [hi])]
  have hRp : R :: post = L.drop j := by rw [hnow, List.drop_left' (by simp [hj])]
  have hdrop : restAfter.drop (j - i - 1) = R :: post := by
    rw [hRA, List.drop_drop, hRp]; congr 1; omega
  have hn : L = revPre.reverse ++ S :: (restAfter.take (j - i - 1) ++ R :: post) := by
    rw [← hdrop, List.take_append_drop]; exact hsplit
  simpa [List.append_assoc] using hn

private theorem denseEmitCand_split {L : List (BusInteraction (DenseExpr p))} (w : DenseOpenRec p)
    (hwf : OpenWF L w)
    {revSeen : List (BusInteraction (DenseExpr p))} (j : Nat) (hj : revSeen.length = j)
    (R : BusInteraction (DenseExpr p)) (post : List (BusInteraction (DenseExpr p)))
    (hnow : L = revSeen.reverse ++ R :: post)
    {ic : Nat × DenseSplitCand p} (h : denseEmitCand w j R post = some ic) :
    SplitEqC L ic.2 := by
  unfold denseEmitCand at h
  by_cases hlt : w.i < j
  · rw [if_pos hlt] at h
    simp only [Option.some.injEq] at h
    subst h
    exact dense_split_of_positions hwf.1 hwf.2 hj hnow hlt
  · rw [if_neg hlt] at h; exact absurd h (by simp)

private theorem denseEmitCand_cons_split {L : List (BusInteraction (DenseExpr p))}
    (w : DenseOpenRec p) (hwf : OpenWF L w)
    {revSeen : List (BusInteraction (DenseExpr p))} (j : Nat) (hj : revSeen.length = j)
    (R : BusInteraction (DenseExpr p)) (post : List (BusInteraction (DenseExpr p)))
    (hnow : L = revSeen.reverse ++ R :: post)
    (acc : List (Nat × DenseSplitCand p)) (hacc : ∀ ic ∈ acc, SplitEqC L ic.2) :
    ∀ ic ∈ (match denseEmitCand w j R post with | some c => c :: acc | none => acc),
      SplitEqC L ic.2 := by
  cases hem : denseEmitCand w j R post with
  | none => intro ic hic; exact hacc ic hic
  | some c =>
    intro ic hic
    simp only [List.mem_cons] at hic
    rcases hic with rfl | hic
    · exact denseEmitCand_split w hwf j hj R post hnow hem
    · exact hacc ic hic

-- HashMap value invariant under insert / erase / erase-fold
private theorem insert_ow {L : List (BusInteraction (DenseExpr p))}
    (cO : Std.HashMap (DenseAddrKey p) (DenseOpenRec p))
    (hcO : ∀ (k : DenseAddrKey p) (w : DenseOpenRec p), cO[k]? = some w → OpenWF L w)
    (k0 : DenseAddrKey p) (w0 : DenseOpenRec p) (hw0 : OpenWF L w0) :
    ∀ (k : DenseAddrKey p) (w : DenseOpenRec p), (cO.insert k0 w0)[k]? = some w → OpenWF L w := by
  intro k w h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rw [Option.some.injEq] at h; subst h; exact hw0
  · exact hcO k w h

private theorem erase_ow {L : List (BusInteraction (DenseExpr p))}
    (cO : Std.HashMap (DenseAddrKey p) (DenseOpenRec p))
    (hcO : ∀ (k : DenseAddrKey p) (w : DenseOpenRec p), cO[k]? = some w → OpenWF L w)
    (k0 : DenseAddrKey p) :
    ∀ (k : DenseAddrKey p) (w : DenseOpenRec p), (cO.erase k0)[k]? = some w → OpenWF L w := by
  intro k w h
  rw [Std.HashMap.getElem?_erase] at h
  split at h
  · exact absurd h (by simp)
  · exact hcO k w h

private theorem eraseFold_ow {L : List (BusInteraction (DenseExpr p))}
    (drops : List (DenseAddrKey p)) (cO : Std.HashMap (DenseAddrKey p) (DenseOpenRec p))
    (hcO : ∀ (k : DenseAddrKey p) (w : DenseOpenRec p), cO[k]? = some w → OpenWF L w) :
    ∀ (k : DenseAddrKey p) (w : DenseOpenRec p),
      (List.foldl (fun x1 x2 => x1.erase x2) cO drops)[k]? = some w → OpenWF L w := by
  induction drops generalizing cO with
  | nil => exact hcO
  | cons d rest ih =>
    rw [List.foldl_cons]
    exact ih (cO.erase d) (erase_ow cO hcO d)


theorem denseSweepGo_split {shape : MemoryBusShape} {T : Thunk (DenseTwoRootMap p)}
    {nw : Thunk (DenseNonzeroWits p)} (L : List (BusInteraction (DenseExpr p)))
    (revSeen rest : List (BusInteraction (DenseExpr p))) (j : Nat)
    (constOpen : Std.HashMap (DenseAddrKey p) (DenseOpenRec p))
    (symOpen : List (DenseOpenRec p)) (acc : List (Nat × DenseSplitCand p))
    (hsplit : L = revSeen.reverse ++ rest) (hj : revSeen.length = j)
    (hcO : ∀ (k : DenseAddrKey p) (w : DenseOpenRec p), constOpen[k]? = some w → OpenWF L w)
    (hsO : ∀ w ∈ symOpen, OpenWF L w)
    (hacc : ∀ ic ∈ acc, SplitEqC L ic.2) :
    ∀ ic ∈ denseSweepGo shape T nw revSeen rest j constOpen symOpen acc, SplitEqC L ic.2 := by
  revert hsplit hj hcO hsO hacc
  fun_induction denseSweepGo shape T nw revSeen rest j constOpen symOpen acc with
  | case1 revSeen j constOpen symOpen acc =>
    intro hsplit hj hcO hsO hacc ic hic
    exact hacc ic hic
  | case2 revSeen m rest' j constOpen symOpen acc mKey mAllC constOpen_1 acc_1 hP1 so a hP2 constOpen_2 symOpen_1 hP3 ih =>
    intro hsplit hj hcO hsO hacc
    clear_value mAllC mKey
    have hnow : L = revSeen.reverse ++ m :: rest' := hsplit
    have hP1inv : (∀ (k : DenseAddrKey p) (w : DenseOpenRec p), constOpen_1[k]? = some w → OpenWF L w)
        ∧ (∀ ic ∈ acc_1, SplitEqC L ic.2) := by
      split at hP1
      · split at hP1
        · rename_i k
          split at hP1
          · rename_i w heqw
            split at hP1
            · simp only [Prod.mk.injEq] at hP1; obtain ⟨rfl, rfl⟩ := hP1
              exact ⟨erase_ow constOpen hcO k,
                denseEmitCand_cons_split w (hcO k w heqw) j hj m rest' hnow acc hacc⟩
            · simp only [Prod.mk.injEq] at hP1; obtain ⟨rfl, rfl⟩ := hP1
              exact ⟨hcO, hacc⟩
            · simp only [Prod.mk.injEq] at hP1; obtain ⟨rfl, rfl⟩ := hP1
              exact ⟨erase_ow constOpen hcO k, hacc⟩
          · simp only [Prod.mk.injEq] at hP1; obtain ⟨rfl, rfl⟩ := hP1
            exact ⟨hcO, hacc⟩
        · simp only [Prod.mk.injEq] at hP1; obtain ⟨rfl, rfl⟩ := hP1
          exact ⟨hcO, hacc⟩
      · have hlst : ∀ kw ∈ constOpen.toList, OpenWF L kw.2 := by
          intro kw hkw
          exact hcO kw.1 kw.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp
            (show (kw.1, kw.2) ∈ constOpen.toList from hkw))
        split at hP1
        rename_i drops accf heqfold
        simp only [Prod.mk.injEq] at hP1; obtain ⟨rfl, rfl⟩ := hP1
        refine ⟨eraseFold_ow drops constOpen hcO, ?_⟩
        show ∀ ic ∈ (drops, accf).2, SplitEqC L ic.2
        rw [← heqfold]
        refine List.foldlRecOn constOpen.toList _
          (motive := fun (dsa : List (DenseAddrKey p) × List (Nat × DenseSplitCand p)) =>
            ∀ ic ∈ dsa.2, SplitEqC L ic.2) hacc ?_
        intro dsa hdsa kw hkw
        obtain ⟨ds, a2⟩ := dsa
        intro ic hic
        cases hst : denseStepTest shape T nw kw.2.S m with
        | consumer =>
          simp only [hst] at hic
          exact denseEmitCand_cons_split kw.2 (hlst kw hkw) j hj m rest' hnow a2 hdsa ic hic
        | excluded => simp only [hst] at hic; exact hdsa ic hic
        | blocker => simp only [hst] at hic; exact hdsa ic hic
    obtain ⟨hcO1, hacc1⟩ := hP1inv
    have hP2inv : (∀ w ∈ so, OpenWF L w) ∧ (∀ ic ∈ a, SplitEqC L ic.2) := by
      split at hP2
      · simp only [Prod.mk.injEq] at hP2; obtain ⟨rfl, rfl⟩ := hP2
        exact ⟨hsO, hacc1⟩
      · have hfr : (∀ w ∈ (so, a).1, OpenWF L w) ∧ (∀ ic ∈ (so, a).2, SplitEqC L ic.2) := by
          rw [← hP2]
          refine List.foldrRecOn symOpen _
            (motive := fun (soa : List (DenseOpenRec p) × List (Nat × DenseSplitCand p)) =>
              (∀ w ∈ soa.1, OpenWF L w) ∧ (∀ ic ∈ soa.2, SplitEqC L ic.2))
            ⟨by intro w hw; simp at hw, hacc1⟩ ?_
          intro soa hsoa w hw
          obtain ⟨so2, a2⟩ := soa
          obtain ⟨hso2, ha2⟩ := hsoa
          cases hst : denseStepTest shape T nw w.S m with
          | consumer => exact ⟨hso2, denseEmitCand_cons_split w (hsO w hw) j hj m rest' hnow a2 ha2⟩
          | excluded =>
            exact ⟨List.forall_mem_cons.mpr ⟨hsO w hw, hso2⟩, ha2⟩
          | blocker => exact ⟨hso2, ha2⟩
        exact ⟨hfr.1, hfr.2⟩
    obtain ⟨hso3, hacc2⟩ := hP2inv
    have hwNew : OpenWF L (⟨revSeen, m, rest', j⟩ : DenseOpenRec p) := ⟨hj, hnow⟩
    have hP3inv : (∀ (k : DenseAddrKey p) (w : DenseOpenRec p), constOpen_2[k]? = some w → OpenWF L w)
        ∧ (∀ w ∈ symOpen_1, OpenWF L w) := by
      split at hP3
      · split at hP3
        · rename_i k
          split at hP3
          · split at hP3
            · rename_i old heqold
              simp only [Prod.mk.injEq] at hP3; obtain ⟨rfl, rfl⟩ := hP3
              exact ⟨insert_ow constOpen_1 hcO1 k _ hwNew,
                List.forall_mem_cons.mpr ⟨hcO1 k old heqold, hso3⟩⟩
            · simp only [Prod.mk.injEq] at hP3; obtain ⟨rfl, rfl⟩ := hP3
              exact ⟨insert_ow constOpen_1 hcO1 k _ hwNew, hso3⟩
          · simp only [Prod.mk.injEq] at hP3; obtain ⟨rfl, rfl⟩ := hP3
            exact ⟨hcO1, List.forall_mem_cons.mpr ⟨hwNew, hso3⟩⟩
        · simp only [Prod.mk.injEq] at hP3; obtain ⟨rfl, rfl⟩ := hP3
          exact ⟨hcO1, hso3⟩
      · simp only [Prod.mk.injEq] at hP3; obtain ⟨rfl, rfl⟩ := hP3
        exact ⟨hcO1, hso3⟩
    intro ic hic
    exact ih (by rw [List.reverse_cons, List.append_assoc]; exact hsplit)
             (by rw [List.length_cons, hj])
             hP3inv.1 hP3inv.2 hacc2 ic hic


/-- Wrapper: every candidate the sweep enumerator returns recomposes the swept list. -/
theorem denseCandidateSplitsSweep_split {shape : MemoryBusShape} {T : Thunk (DenseTwoRootMap p)}
    {nw : Thunk (DenseNonzeroWits p)} (L : List (BusInteraction (DenseExpr p)))
    (cand : DenseSplitCand p) (hcand : cand ∈ denseCandidateSplitsSweep shape T nw L) :
    L = cand.1 ++ cand.2.1 :: cand.2.2.1 ++ cand.2.2.2.1 :: cand.2.2.2.2 := by
  unfold denseCandidateSplitsSweep at hcand
  rw [List.mem_map] at hcand
  obtain ⟨ic, hic, rfl⟩ := hcand
  rw [List.mem_mergeSort] at hic
  exact denseSweepGo_split L [] L 0 ∅ [] []
    (by simp) rfl
    (by intro k w h; rw [Std.HashMap.getElem?_empty] at h; exact absurd h (by simp))
    (by intro w hw; simp at hw)
    (by intro ic hic; simp at hic) ic hic

/-- Every var of an entailed slot equality comes from the send's or receive's payload. Native mirror
    of `memEqConstraints_vars`. -/
theorem denseMemEqConstraints_vars (shape : MemoryBusShape) (S Rt : BusInteraction (DenseExpr p))
    {c : DenseExpr p} (hc : c ∈ denseMemEqConstraints shape S Rt) {z : VarId} (hz : z ∈ c.vars) :
    (∃ e ∈ Rt.payload, z ∈ e.vars) ∨ (∃ e ∈ S.payload, z ∈ e.vars) := by
  unfold denseMemEqConstraints at hc
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.1 hc
  simp only [denseEqExpr, DenseExpr.vars, List.mem_append, List.not_mem_nil, false_or] at hz
  rcases hz with hz | hz
  · cases hR : Rt.payload[i]? with
    | none => rw [hR] at hz; simp [DenseExpr.vars] at hz
    | some e => rw [hR] at hz; exact Or.inl ⟨e, List.mem_of_getElem? hR, hz⟩
  · cases hS : S.payload[i]? with
    | none => rw [hS] at hz; simp [DenseExpr.vars] at hz
    | some e => rw [hS] at hz; exact Or.inr ⟨e, List.mem_of_getElem? hS, hz⟩

/-- A var of a bus interaction's payload occurs in `d`. Native mirror of
    `ConstraintSystem.mem_vars_of_payload`. -/
theorem DenseConstraintSystem.mem_occ_of_payload {d : DenseConstraintSystem p}
    {bi : BusInteraction (DenseExpr p)} {e : DenseExpr p} {z : VarId}
    (hbi : bi ∈ d.busInteractions) (he : e ∈ bi.payload) (hz : z ∈ e.vars) : z ∈ d.occ :=
  DenseConstraintSystem.mem_occ_of_bi hbi (by
    simp only [denseBIVars, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hz⟩)

/-- Every var of an equality collected for one bus is an occurrence of `d`, by construction — the
    split equation gives `S, R ∈ d.busInteractions`, and `denseMemEqConstraints_vars` traces each var
    back to a payload slot. Native mirror of `collectForBus`'s "no new variable" conjunct. -/
theorem denseCollectForBus_vars (d : DenseConstraintSystem p)
    (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p)) (shape : MemoryBusShape)
    (busId : Nat) :
    ∀ (cands : List (DenseSplitCand p)),
    (∀ cand ∈ cands, d.busInteractions.filter (fun bi => bi.busId = busId)
        = cand.1 ++ cand.2.1 :: cand.2.2.1 ++ cand.2.2.2.1 :: cand.2.2.2.2) →
    ∀ c ∈ denseCollectForBus shape T nw cands, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro cands
  induction cands with
  | nil => intro _ c hc; simp [denseCollectForBus] at hc
  | cons cand rest ih =>
    intro hsplitc c hc z hz
    obtain ⟨pre, S, mid, R, post⟩ := cand
    have hsplit : d.busInteractions.filter (fun bi => bi.busId = busId)
        = pre ++ S :: mid ++ R :: post := hsplitc (pre, S, mid, R, post) (List.mem_cons_self ..)
    have hrest : ∀ cand ∈ rest, d.busInteractions.filter (fun bi => bi.busId = busId)
        = cand.1 ++ cand.2.1 :: cand.2.2.1 ++ cand.2.2.2.1 :: cand.2.2.2.2 :=
      fun cand h => hsplitc cand (List.mem_cons_of_mem _ h)
    have hSmem : S ∈ d.busInteractions := by
      have h : S ∈ d.busInteractions.filter (fun bi => bi.busId = busId) := by
        rw [hsplit]
        exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      exact List.mem_of_mem_filter h
    have hRmem : R ∈ d.busInteractions := by
      have h : R ∈ d.busInteractions.filter (fun bi => bi.busId = busId) := by
        rw [hsplit]
        exact List.mem_append_right _ List.mem_cons_self
      exact List.mem_of_mem_filter h
    rw [denseCollectForBus] at hc
    split_ifs at hc with hchk
    · rw [List.mem_append] at hc
      rcases hc with h | h
      · rcases denseMemEqConstraints_vars shape S R h hz with ⟨e, he, hze⟩ | ⟨e, he, hze⟩
        · exact DenseConstraintSystem.mem_occ_of_payload hRmem he hze
        · exact DenseConstraintSystem.mem_occ_of_payload hSmem he hze
      · exact ih hrest c h z hz
    · exact ih hrest c hc z hz

/-- Every var of an equality collected across all declared buses is an occurrence of `d`. Native
    mirror of `collectAllBuses`'s "no new variable" conjunct. -/
theorem denseCollectAllBuses_vars (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p)) :
    ∀ (busIds : List Nat),
    ∀ c ∈ denseCollectAllBuses d bs facts T nw busIds, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro busIds
  induction busIds with
  | nil => intro c hc; simp [denseCollectAllBuses] at hc
  | cons busId rest ih =>
    intro c hc z hz
    rw [denseCollectAllBuses] at hc
    cases hms : facts.memShape busId with
    | none => rw [hms] at hc; exact ih c hc z hz
    | some shape =>
      rw [hms, List.mem_append] at hc
      rcases hc with hc | hc
      · refine denseCollectForBus_vars d T nw shape busId _ ?_ c hc z hz
        intro cand hcand
        exact denseCandidateSplitsSweep_split
          (d.busInteractions.filter (fun bi => bi.busId = busId)) cand hcand
      · exact ih c hc z hz

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
    ∀ c ∈ denseCollectForBus shape (Thunk.pure T)
        (Thunk.pure (DenseNonzeroWits.build d.algebraicConstraints)) cands,
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
    ∀ c ∈ denseCollectAllBuses d bs facts
        (Thunk.mk fun _ => DenseTwoRootMap.build d.algebraicConstraints)
        (Thunk.mk fun _ => DenseNonzeroWits.build d.algebraicConstraints) busIds,
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
        exact denseCandidateSplitsSweep_split
          (d.busInteractions.filter (fun bi => bi.busId = busId)) cand hcand
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
    out so the guard cases get named hypotheses). The `eqs.isEmpty` early-out of `denseBusUnifyF`
    only skips the filter-table build when nothing was collected; the appended list is this filter
    either way (`denseBusUnifyF_eq` collapses the two guards). The `Thunk`s here match
    `denseBusUnifyF`'s exactly, so their `.get`s reduce to the same builds. -/
def denseBusUnifyNew (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let T : Thunk (DenseTwoRootMap p) :=
    Thunk.mk fun _ => DenseTwoRootMap.build d.algebraicConstraints
  let nw : Thunk (DenseNonzeroWits p) :=
    Thunk.mk fun _ => DenseNonzeroWits.build d.algebraicConstraints
  let eqs := denseCollectAllBuses d bs facts T nw
    ((d.busInteractions.map (fun bi => bi.busId)).dedup)
  let dHashes : Std.HashMap UInt64 (List (DenseExpr p)) :=
    d.algebraicConstraints.foldl (fun m c =>
      let h := c.bHash
      m.insert h (c :: m.getD h [])) ∅
  let containsC : DenseExpr p → Bool := fun c =>
    (dHashes.getD c.bHash []).any (fun c' => c' == c)
  eqs.filter
    (fun c => !c.normalize.fold.isConstZero && !containsC c)

/-- Collapsing the two-level `isEmpty` guards: the runtime's outer `eqs.isEmpty` early-out returns
    the same result as the inner `(eqs.filter f).isEmpty` guard, since an empty `eqs` filters to the
    empty list. -/
private theorem outer_isEmpty_collapse {β : Type} (l : List (DenseExpr p)) (f : DenseExpr p → Bool)
    (dd xx : β) :
    (if l.isEmpty then dd else (if (l.filter f).isEmpty then dd else xx))
      = (if (l.filter f).isEmpty then dd else xx) := by
  cases l with
  | nil => simp
  | cons a t => simp

theorem denseBusUnifyF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseBusUnifyF bs facts d =
      (if (1 : ZMod p) ≠ 0 then
        (if (denseBusUnifyNew bs facts d).isEmpty then d
         else { d with algebraicConstraints := d.algebraicConstraints ++ denseBusUnifyNew bs facts d })
       else d) := by
  show (if (1 : ZMod p) ≠ 0 then _ else d) = (if (1 : ZMod p) ≠ 0 then _ else d)
  by_cases hp1 : (1 : ZMod p) ≠ 0
  · rw [if_pos hp1, if_pos hp1]
    exact outer_isEmpty_collapse _ _ d _
  · rw [if_neg hp1, if_neg hp1]

/-- Every variable of an appended equality is an occurrence of `d` — now purely by construction
    (`denseCollectAllBuses_vars`), the `dVarSet` filter clause having been dropped with the #165
    flip. -/
theorem denseBusUnifyNew_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseBusUnifyNew bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  exact denseCollectAllBuses_vars d bs facts _ _ _ c (List.mem_of_mem_filter hc) z hz

/-- Every appended equality evaluates to zero on admissible satisfying assignments (the substance,
    via `denseCollectAllBuses_sound`). -/
theorem denseBusUnifyNew_sound (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (hp1 : (1 : ZMod p) ≠ 0)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBusUnifyNew bs facts d, c.eval denv = 0 := by
  intro c hc
  have hmem : c ∈ denseCollectAllBuses d bs facts
      (Thunk.mk fun _ => DenseTwoRootMap.build d.algebraicConstraints)
      (Thunk.mk fun _ => DenseNonzeroWits.build d.algebraicConstraints)
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
    (through `of`) on the native `DensePassCorrect` proof — no commutation with the reference
    pass. -/
def denseBusUnifyPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseBusUnifyF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseBusUnifyF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseBusUnifyF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
