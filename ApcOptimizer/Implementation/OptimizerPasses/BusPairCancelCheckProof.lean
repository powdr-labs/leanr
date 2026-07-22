import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCore
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelIndexProof

set_option autoImplicit false

/-! # Soundness of the dense region tests + emit slice for `busPairCancel`

Soundness for the region tests + emitted checks defined in `BusPairCancelCheck.lean`, over
`VarId → ZMod p`. The capstone `denseCheckCancel_sound` discharges the full hypothesis list of
`denseDropPair_correct`. The region-test lemmas take `reg` + coverage as a proof-side parameter only
(the address-disequality certs are proved through the registry). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A match at `j` is strictly after `i` and live, recovered from the search's own guard. -/
theorem denseFirstMatchAt_spec (M : Thunk (DenseEqConstraintMap p))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) (i : Nat) :
    ∀ (l : List Nat) {j : Nat}, denseFirstMatchAt M arr alive busId S i l = some j →
      i < j ∧ alive[j]?.getD false = true := by
  intro l
  induction l with
  | nil => intro j h; simp [denseFirstMatchAt] at h
  | cons hd tl ih =>
    intro j h
    rw [denseFirstMatchAt] at h
    split at h
    · rename_i hcond
      rw [Bool.and_eq_true] at hcond
      split at h
      · split at h
        · obtain rfl := Option.some.inj h
          exact ⟨of_decide_eq_true hcond.1, hcond.2⟩
        · exact ih h
      · exact ih h
    · exact ih h

/-- No active same-address message on `busId` survives the between-region test. -/
theorem denseMidRefuted_sound (reg : VarRegistry) (ops : DenseZModOps p) (shape : MemoryBusShape)
    {dcs : List (DenseExpr p)} (T : Thunk (DenseAddrCerts p))
    (hTtworoot : T.get.tworoot.Sound dcs)
    (hTnonzero : T.get.nonzero = DenseNonzeroWits.build dcs)
    (hdcov : ∀ c ∈ dcs, c.CoveredBy reg)
    (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (hScov : denseBICovered reg S) (hmcov : denseBICovered reg m)
    (h : denseMidRefuted ops shape T busId S m = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0)
    (hbid : (denseBIEval m denv).busId = busId) (hmne : (denseBIEval m denv).multiplicity ≠ 0)
    (hmaddr : shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv)) : False := by
  unfold denseMidRefuted at h
  rw [ops.zero_eq] at h
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact absurd hbid (of_decide_eq_true h)
  · exact hmne (m.multiplicity.constValue?_sound 0 (of_decide_eq_true h) denv)
  · exact denseAddrConstsNeq_sound shape S m h denv hmaddr.symm
  · exact denseAddrAffineNeq_sound reg shape S m hScov hmcov h denv hmaddr.symm
  · exact denseAddrTwoRootNeq_sound reg shape T.get.tworoot hTtworoot hdcov S m hScov hmcov h denv
      hcon hmaddr.symm
  · rw [hTnonzero] at h
    exact denseAddrNonzeroNeq_sound reg shape dcs hdcov S m hScov hmcov h denv hcon hmaddr.symm

/-- An active same-address message on `busId` not refuted by the before-region test has multiplicity
    `≠ shape.setNewMult` (it is not a `setNew` send). -/
theorem densePreRefuted_sound (reg : VarRegistry) (ops : DenseZModOps p) (shape : MemoryBusShape)
    {dcs : List (DenseExpr p)} (T : Thunk (DenseAddrCerts p))
    (hTtworoot : T.get.tworoot.Sound dcs)
    (hTnonzero : T.get.nonzero = DenseNonzeroWits.build dcs)
    (hdcov : ∀ c ∈ dcs, c.CoveredBy reg)
    (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (hScov : denseBICovered reg S) (hmcov : denseBICovered reg m)
    (h : densePreRefuted ops shape T busId S m = true) (denv : VarId → ZMod p)
    (hcon : ∀ c ∈ dcs, c.eval denv = 0)
    (hbid : (denseBIEval m denv).busId = busId) (hmne : (denseBIEval m denv).multiplicity ≠ 0)
    (hmaddr : shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv)) :
    (denseBIEval m denv).multiplicity ≠ shape.setNewMult := by
  unfold densePreRefuted at h
  rw [denseSetNewMult_eq ops shape] at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact (denseMidRefuted_sound reg ops shape T hTtworoot hTnonzero hdcov busId S m hScov hmcov h denv
      hcon hbid hmne hmaddr).elim
  · cases hc : denseMultConst m with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      have heval : (denseBIEval m denv).multiplicity = c := m.multiplicity.constValue?_sound c hc denv
      rw [heval]
      exact of_decide_eq_true h

/-- A provable active same-address receive on `busId` really is on-bus, active, same-address, and
    multiplicity `-shape.setNewMult`. -/
theorem denseProvRecv_sound (ops : DenseZModOps p) (shape : MemoryBusShape) (busId : Nat)
    (hp1 : (1 : ZMod p) ≠ 0)
    (S m : BusInteraction (DenseExpr p)) (h : denseProvRecv ops shape busId S m = true)
    (denv : VarId → ZMod p) :
    (denseBIEval m denv).busId = busId ∧ (denseBIEval m denv).multiplicity ≠ 0 ∧
    shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) ∧
      (denseBIEval m denv).multiplicity = -shape.setNewMult := by
  unfold denseProvRecv at h
  rw [denseGetPreviousMult_eq ops shape] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hbid, haddr⟩, hmult⟩ := h
  have hmult' : (denseBIEval m denv).multiplicity = -shape.setNewMult :=
    m.multiplicity.constValue?_sound (-shape.setNewMult) (of_decide_eq_true hmult) denv
  refine ⟨of_decide_eq_true hbid, ?_, (denseAddrConstsEq_sound shape S m haddr denv).symm, hmult'⟩
  rw [hmult']; exact neg_ne_zero.mpr (shape.setNewMult_ne_zero hp1)

/-- If the scan's `hasRecv` flag is set, the list contains a provable receive. -/
theorem denseShieldScan_hasRecv (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) :
    ∀ (l : List (BusInteraction (DenseExpr p))), (denseShieldScan ops shape T busId S l).1 = true →
      ∃ Rp ∈ l, denseProvRecv ops shape busId S Rp = true
  | [], h => by simp [denseShieldScan] at h
  | m0 :: rest, h => by
      rw [denseShieldScan] at h
      dsimp only at h
      rcases Bool.or_eq_true _ _ |>.mp h with h1 | h1
      · obtain ⟨Rp, hRp, hprov⟩ := denseShieldScan_hasRecv ops shape T busId S rest h1
        exact ⟨Rp, List.mem_cons_of_mem _ hRp, hprov⟩
      · exact ⟨m0, List.mem_cons_self .., h1⟩

/-- From a passing `denseShieldOk` and a split `A_pre ++ m0 :: A_suf` whose `m0` is not provably
    excluded (`¬densePreRefuted`), `A_suf` carries a provable active same-address receive. -/
theorem denseShieldOk_sound (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S m0 : BusInteraction (DenseExpr p)) (A_suf : List (BusInteraction (DenseExpr p))) :
    ∀ (A_pre : List (BusInteraction (DenseExpr p))),
      denseShieldOk ops shape T busId S (A_pre ++ m0 :: A_suf) = true →
      densePreRefuted ops shape T busId S m0 = false →
      ∃ Rp ∈ A_suf, denseProvRecv ops shape busId S Rp = true
  | [], h, hpre => by
      unfold denseShieldOk at h
      rw [List.nil_append, denseShieldScan] at h
      dsimp only at h
      rw [Bool.and_eq_true] at h
      obtain ⟨_, h2⟩ := h
      rw [hpre, Bool.false_or] at h2
      exact denseShieldScan_hasRecv ops shape T busId S A_suf h2
  | a :: A_pre', h, hpre => by
      unfold denseShieldOk at h
      rw [List.cons_append, denseShieldScan] at h
      dsimp only at h
      rw [Bool.and_eq_true] at h
      exact denseShieldOk_sound ops shape T busId S m0 A_suf A_pre' h.1 hpre

/-- The evaluation of an emitted single-value byte check. -/
theorem denseMkByteCheck_eval (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p) :
    denseBIEval (denseMkByteCheck spec busId e) denv
      = { busId := busId, multiplicity := 1,
          payload := spec.encode spec.xorOp (e.eval denv) (e.eval denv) 0 } := by
  simp only [denseMkByteCheck, denseBIEval, spec.encode_map, DenseExpr.eval]

/-- An emitted single-value byte check breaks no invariant. -/
theorem denseMkByteCheck_breaks (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e : DenseExpr p) (denv : VarId → ZMod p) :
    bs.breaksInvariant (denseBIEval (denseMkByteCheck spec busId e) denv) = false := by
  obtain ⟨_, hbreak, _⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkByteCheck_eval]; exact hbreak _

/-- A single-value byte check is accepted exactly when its operand is a byte. -/
theorem denseMkByteCheck_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e : DenseExpr p) (denv : VarId → ZMod p) :
    bs.violatesConstraint (denseBIEval (denseMkByteCheck spec busId e) denv) = false
      ↔ (e.eval denv).val < spec.bound := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkByteCheck_eval]
  have hdec : spec.decode (spec.encode spec.xorOp (e.eval denv) (e.eval denv) 0)
      = some (spec.xorOp, e.eval denv, e.eval denv, (0 : ZMod p)) := spec.decode_encode _ _ _ _
  rw [(hsound _ spec.xorOp _ _ 0 1 hdec).1 rfl]
  have hx : (0 : ZMod p).val = Nat.xor (e.eval denv).val (e.eval denv).val := by
    rw [ZMod.val_zero]; exact (Nat.xor_self _).symm
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, h, hx⟩

/-- An emitted byte check introduces no variable beyond its operand's. -/
theorem denseMkByteCheck_payload_vars (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p)
    {x : VarId} (pe : DenseExpr p) (hpe : pe ∈ (denseMkByteCheck spec busId e).payload)
    (hx : x ∈ pe.vars) : x ∈ e.vars := by
  simp only [denseMkByteCheck] at hpe
  rcases spec.encode_mem _ _ _ _ pe hpe with h | h | h | h <;> rw [h] at hx <;>
    first | exact hx | (simp only [DenseExpr.vars, List.not_mem_nil] at hx)

/-- A passing emit certificate makes the check stateless, implied by `R`'s own accepted receive,
    invariant-free, and adding no `VarId`s — `denseDropPair_correct`'s per-check `hchecks` element. -/
theorem denseEmitOk_sound (ops : DenseZModOps p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (busId : Nat)
    (shape : MemoryBusShape) (slots : List Nat) (R ck : BusInteraction (DenseExpr p))
    (h : denseEmitOk ops bs facts busId shape slots R ck = true)
    (hRbus : R.busId = busId)
    (hRmEv : ∀ denv, (denseBIEval R denv).multiplicity = -shape.setNewMult) :
    bs.isStateful ck.busId = false ∧
    (∀ denv, bs.violatesConstraint (denseBIEval R denv) = false →
      bs.violatesConstraint (denseBIEval ck denv) = false) ∧
    (∀ denv, bs.breaksInvariant (denseBIEval ck denv) = false) ∧
    (∀ v ∈ denseBIVars ck, v ∈ denseBIVars R) := by
  unfold denseEmitOk at h
  rw [ops.one_eq, ops.zero_eq, denseGetPreviousMult_eq ops shape] at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hbd, hmultd⟩, hrest⟩ := h
    have hbound : spec.bound = 256 := of_decide_eq_true hbd
    have hmult := of_decide_eq_true hmultd
    have hstateless := (facts.byteXorSpec_sound ck.busId spec hspec).1
    split at hrest
    · rename_i op o1 o2 r hdec
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨hopd, ho12d⟩, hrd⟩, hany⟩ := hrest
      have hop := of_decide_eq_true hopd
      have ho12 := of_decide_eq_true ho12d
      have hr := of_decide_eq_true hrd
      obtain ⟨slot, hslotmem, hslot⟩ := List.any_eq_true.1 hany
      rw [Bool.and_eq_true] at hslot
      obtain ⟨hgetd, hbnd⟩ := hslot
      have hget := of_decide_eq_true hgetd
      have hckeq : ck = denseMkByteCheck spec ck.busId o1 := by
        obtain ⟨ckBus, ckMul, ckPay⟩ := ck
        have hpay : ckPay = spec.encode (.const spec.xorOp) o1 o1 (.const 0) := by
          have he := spec.decode_eq_encode ckPay op o1 o2 r hdec
          rw [hop, ← ho12, hr] at he; exact he
        have hm' : ckMul = DenseExpr.const 1 := hmult
        show ({ busId := ckBus, multiplicity := ckMul, payload := ckPay } :
          BusInteraction (DenseExpr p)) = denseMkByteCheck spec ckBus o1
        rw [hm', hpay]; rfl
      have ho1mem : o1 ∈ R.payload := by
        have := List.getElem?_eq_some_iff.mp hget
        obtain ⟨hlt, hgetE⟩ := this
        exact hgetE ▸ List.getElem_mem hlt
      refine ⟨hstateless, ?_, ?_, ?_⟩
      ·
        intro denv hRok
        cases hb : facts.slotBound busId (-shape.setNewMult) (R.payload.map DenseExpr.constValue?) slot
        with
        | none => rw [hb] at hbnd; simp at hbnd
        | some b =>
          rw [hb] at hbnd
          dsimp only at hbnd
          have hgetEv : (denseBIEval R denv).payload[slot]? = some (o1.eval denv) := by
            show (R.payload.map (fun e => e.eval denv))[slot]? = some (o1.eval denv)
            rw [List.getElem?_map, hget]; rfl
          have hfact : facts.slotBound (denseBIEval R denv).busId (denseBIEval R denv).multiplicity
              (R.payload.map DenseExpr.constValue?) slot = some b := by
            rw [hRmEv denv, show (denseBIEval R denv).busId = busId from hRbus]
            exact hb
          have hbyteE : (o1.eval denv).val < 256 :=
            lt_of_lt_of_le
              (facts.slotBound_sound (denseBIEval R denv) (R.payload.map DenseExpr.constValue?)
                slot b (o1.eval denv) hfact (denseMatches_evalPattern R.payload denv) hRok hgetEv)
              (of_decide_eq_true hbnd)
          rw [hckeq, denseMkByteCheck_accepted bs facts spec ck.busId hspec o1 denv, hbound]
          exact hbyteE
      ·
        intro denv
        rw [hckeq]; exact denseMkByteCheck_breaks bs facts spec ck.busId hspec o1 denv
      ·
        intro v hv
        rw [hckeq] at hv
        unfold denseBIVars at hv
        rw [List.mem_append] at hv
        have hvE : v ∈ o1.vars := by
          rcases hv with hm | hm
          · simp only [denseMkByteCheck, DenseExpr.vars, List.not_mem_nil] at hm
          · obtain ⟨pe, hpe, hve⟩ := List.mem_flatMap.1 hm
            exact denseMkByteCheck_payload_vars spec ck.busId o1 pe hpe hve
        unfold denseBIVars
        rw [List.mem_append]
        exact Or.inr (List.mem_flatMap.2 ⟨o1, ho1mem, hvE⟩)
    · exact absurd hrest (by simp)

/-- A passing `denseCheckCancel` — with the split equation, the scan's region hypotheses, the
    witness/index membership facts, registry coverage, and `Sound` facts for the threaded certs/maps
    — yields `DensePassCorrect` via `denseDropPair_correct`. -/
theorem denseCheckCancel_sound (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (ops : DenseZModOps p)
    (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (slots : List Nat) (bound : Nat)
    (T : Thunk (DenseAddrCerts p))
    (hTtworoot : T.get.tworoot.Sound d.algebraicConstraints)
    (hTnonzero : T.get.nonzero = DenseNonzeroWits.build d.algebraicConstraints)
    (M : Thunk (DenseEqConstraintMap p)) (hM : M.get.Sound d.algebraicConstraints)
    (domCs : List (DenseExpr p)) (candsOf : VarId → List (DenseExpr p))
    (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (A : List (BusInteraction (DenseExpr p))) (S : BusInteraction (DenseExpr p))
    (B : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p))
    (C : List (BusInteraction (DenseExpr p)))
    (hslots : facts.recvByteSlots busId (R.payload.map DenseExpr.constValue?) = some (slots, bound))
    (checks : List (BusInteraction (DenseExpr p)))
    (hsplit : d.busInteractions = A ++ S :: B ++ R :: C)
    (hdomCs : ∀ c ∈ domCs, c ∈ d.algebraicConstraints)
    (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ d.algebraicConstraints)
    (hwits : ∀ v, ∀ bi ∈ wits v, bi ∈ A ++ B ++ C ++ checks)
    (hfwits : ∀ v, ∀ bi ∈ fwits v, bi ∈ A ++ B ++ C ++ checks)
    (hmid : ∀ m0 ∈ B, denseMidRefuted ops shape T busId S m0 = true)
    (hshield : denseShieldOk ops shape T busId S A = true)
    (h : denseCheckCancel ops deep bs facts M domCs candsOf wits fwits busId shape slots bound S R checks
      = true) :
    DensePassCorrect isInput d { d with busInteractions := A ++ B ++ C ++ checks } [] bs := by
  unfold denseCheckCancel at h
  rw [denseSetNewMult_eq ops shape, denseGetPreviousMult_eq ops shape] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hSb, hRb⟩, hSm⟩, hRm⟩, hpay⟩, hemit⟩, hjust⟩ := h
  have hRmEv : ∀ denv, (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    fun denv => R.multiplicity.constValue?_sound (-shape.setNewMult) (of_decide_eq_true hRm) denv
  have hSmem : S ∈ d.busInteractions := by
    rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
  have hScov : denseBICovered reg S := hcov.2 S hSmem
  refine denseDropPair_correct isInput d bs facts hp1 A B C S R busId shape hshape
    (R.payload.map DenseExpr.constValue?) slots bound hslots
    (fun denv => denseMatches_evalPattern R.payload denv) checks
    (fun ck hck => denseEmitOk_sound ops bs facts busId shape slots R ck
      (List.all_eq_true.mp hemit ck hck) (of_decide_eq_true hRb) hRmEv)
    (fun denv hall hbus => denseRecvSlotsJustified_sound bound deep d.algebraicConstraints domCs
      candsOf bs facts (A ++ B ++ C ++ checks) wits fwits slots R hdeep hdomCs hcands hwits hfwits
      hjust denv hall hbus)
    hsplit
    (of_decide_eq_true hSb) (of_decide_eq_true hRb)
    (of_decide_eq_true hSm) (of_decide_eq_true hRm)
    (fun denv hcon => densePayloadEntailedEq_sound M hM S.payload R.payload hpay denv hcon) ?_ ?_
  ·
    intro denv hcon m0 hm0 hbid hmne hmaddr
    have hm0mem : m0 ∈ d.busInteractions := by
      rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
    exact denseMidRefuted_sound reg ops shape T hTtworoot hTnonzero hcov.1 busId S m0 hScov
      (hcov.2 m0 hm0mem) (hmid m0 hm0) denv hcon hbid hmne hmaddr
  ·
    intro denv hcon A_pre m0 A_suf hAeq hbid hmne hmaddr hmult
    have hm0A : m0 ∈ A := by
      rw [hAeq]; simp only [List.mem_append, List.mem_cons]; tauto
    have hm0mem : m0 ∈ d.busInteractions := by
      rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
    have hm0cov : denseBICovered reg m0 := hcov.2 m0 hm0mem
    have hnp : densePreRefuted ops shape T busId S m0 = false := by
      by_contra hp'
      rw [Bool.not_eq_false] at hp'
      exact (densePreRefuted_sound reg ops shape T hTtworoot hTnonzero hcov.1 busId S m0 hScov hm0cov
        hp' denv hcon hbid hmne hmaddr) hmult
    obtain ⟨Rp, hRpmem, hRpprov⟩ :=
      denseShieldOk_sound ops shape T busId S m0 A_suf A_pre (hAeq ▸ hshield) hnp
    exact ⟨Rp, hRpmem, denseProvRecv_sound ops shape busId hp1 S Rp hRpprov denv⟩

end ApcOptimizer.Dense
