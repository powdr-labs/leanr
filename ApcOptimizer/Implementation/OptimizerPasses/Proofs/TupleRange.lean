import ApcOptimizer.Implementation.OptimizerPasses.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.ByteCheckPack

set_option autoImplicit false

/-! # Soundness of the dense `tupleRange` pass

`DensePassCorrect` for the tuple-range packing pass (`TupleRange.lean`), over `VarId → ZMod p`. A
tuple range checker `(256, s2)` accepts `[x, y]` iff `x < 256 ∧ y < s2` — exactly a byte check on
`x` and a range check `[y, b]` with `2 ^ b.val = s2` — so the two stateless interactions pack into
one via `denseMergeStateless2_correct` (`Proofs/ByteCheckPack.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Evaluation shapes of the two packed message forms and the tuple check -/

theorem denseRangeCheck1_eval (busId : Nat) (y b : DenseExpr p) (denv : VarId → ZMod p) :
    denseBIEval (denseRangeCheck1 busId y b) denv
      = { busId := busId, multiplicity := 1, payload := [y.eval denv, b.eval denv] } := rfl

theorem denseTupleCheck_eval (busId : Nat) (x y : DenseExpr p) (denv : VarId → ZMod p) :
    denseBIEval (denseTupleCheck busId x y) denv
      = { busId := busId, multiplicity := 1, payload := [x.eval denv, y.eval denv] } := rfl

/-! ## Recognizer soundness: a hit pins the canonical shape by construction -/

/-- A `denseMatchByteSingle` hit *is* the canonical single-value byte check
    `denseMkByteCheck spec bi.busId x`. -/
theorem denseMatchByteSingle_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    {bi : BusInteraction (DenseExpr p)} {spec : ByteXorSpec p} {x : DenseExpr p}
    (h : denseMatchByteSingle bs facts bi = some (spec, x)) :
    bi = denseMkByteCheck spec bi.busId x ∧ facts.byteXorSpec bi.busId = some spec ∧
      spec.bound = 256 := by
  obtain ⟨busId, mult, payload⟩ := bi
  unfold denseMatchByteSingle at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec' hspec
    split at h
    · rename_i hb
      split at h
      · rename_i op o1 o2 r hdec
        split_ifs at h with hc
        obtain ⟨hm, hop, ho12, hr⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, hspec, of_decide_eq_true hb⟩
        have hpay : payload = spec'.encode (.const spec'.xorOp) o1 o1 (.const 0) := by
          have he := spec'.decode_eq_encode payload op o1 o2 r hdec
          rw [hop, ← ho12, hr] at he; exact he
        have hm' : mult = DenseExpr.const 1 := hm
        show ({ busId := busId, multiplicity := mult, payload := payload } :
          BusInteraction (DenseExpr p)) = denseMkByteCheck spec' busId o1
        rw [hm', hpay]; rfl
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- A `denseMatchRangeCheck` hit *is* the canonical range check, and carries the width facts the
    packing key needs. -/
theorem denseMatchRangeCheck_eq (bs : BusSemantics p) (facts : BusFacts p bs) {s2 : Nat}
    {bi : BusInteraction (DenseExpr p)} {y : DenseExpr p} {b : ZMod p}
    (h : denseMatchRangeCheck bs facts s2 bi = some (y, b)) :
    bi = denseRangeCheck1 bi.busId y (.const b) ∧ facts.varRangeBus bi.busId = true ∧
      b.val ≤ 17 ∧ 2 ^ b.val = s2 := by
  obtain ⟨busId, mult, payload⟩ := bi
  simp only [denseMatchRangeCheck] at h
  split at h
  · rename_i hvr
    split at h
    · rename_i c y' b'
      split at h
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨rfl, hble⟩, hs2⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hvr, hble, hs2⟩
      · cases h
    · cases h
  · cases h

/-- The operand of an emitted single-value byte check is a payload entry. -/
theorem denseMkByteCheck_operand_mem (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p) :
    e ∈ (denseMkByteCheck spec busId e).payload :=
  (spec.decode_mem (denseMkByteCheck spec busId e).payload
    (.const spec.xorOp) e e (.const 0) (spec.decode_encode _ _ _ _)).1

/-! ## The tuple-packing key: byte check + exact-width range check = tuple check -/

/-- The tuple check's obligation is exactly the byte check's and the range check's together, given
    `s1 = 256`, a supported constant width, and `2 ^ b.val = s2`. -/
theorem denseTupleKey (bs : BusSemantics p) (facts : BusFacts p bs)
    (bcBus vrBus trBus : Nat) (s1 s2 : Nat) (spec : ByteXorSpec p)
    (hspec : facts.byteXorSpec bcBus = some spec) (hbound : spec.bound = 256)
    (hvr : facts.varRangeBus vrBus = true)
    (htr : facts.tupleRangeBus trBus = some (s1, s2))
    (hs1 : s1 = 256) (b : ZMod p) (hble : b.val ≤ 17) (hs2 : 2 ^ b.val = s2)
    (x y : DenseExpr p) :
    ∀ denv, bs.violatesConstraint (denseBIEval (denseTupleCheck trBus x y) denv) = false ↔
      bs.violatesConstraint (denseBIEval (denseMkByteCheck spec bcBus x) denv) = false ∧
        bs.violatesConstraint (denseBIEval (denseRangeCheck1 vrBus y (.const b)) denv) = false := by
  intro denv
  obtain ⟨-, -, htriff⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
  obtain ⟨-, hvriff⟩ := facts.varRangeBus_sound vrBus hvr
  rw [denseTupleCheck_eval, denseRangeCheck1_eval,
    denseMkByteCheck_accepted bs facts spec bcBus hspec x denv, hbound]
  rw [htriff (x.eval denv) (y.eval denv) 1]
  have hB : bs.violatesConstraint
      { busId := vrBus, multiplicity := 1,
        payload := [y.eval denv, (DenseExpr.const b).eval denv] } = false ↔
      (b.val ≤ 17 ∧ (y.eval denv).val < 2 ^ b.val) :=
    hvriff (y.eval denv) b 1
  rw [hB, hs1, ← hs2]
  constructor
  · rintro ⟨hx, hy⟩; exact ⟨hx, hble, hy⟩
  · rintro ⟨hx, -, hy⟩; exact ⟨hx, hy⟩

/-! ## The accept certificates (one per pair orientation) -/

/-- Packing a byte check (first) with a range check (second) into a tuple check is
    `DensePassCorrect`, given the canonical split equation and the matched facts. -/
theorem densePackByteFirst_correct (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    (trBus s1 s2 bcBus vrBus : Nat)
    (htr : facts.tupleRangeBus trBus = some (s1, s2)) (hs1 : s1 = 256)
    (x y : DenseExpr p) (b : ZMod p) (spec : ByteXorSpec p)
    (hspec : facts.byteXorSpec bcBus = some spec) (hbound : spec.bound = 256)
    (hvr : facts.varRangeBus vrBus = true) (hble : b.val ≤ 17) (hs2 : 2 ^ b.val = s2)
    (pre mid post : List (BusInteraction (DenseExpr p)))
    (hsplit : d.busInteractions
      = pre ++ denseMkByteCheck spec bcBus x :: mid ++ denseRangeCheck1 vrBus y (.const b) :: post) :
    DensePassCorrect isInput d
      { d with busInteractions := pre ++ denseTupleCheck trBus x y :: mid ++ post } [] bs := by
  obtain ⟨hstT, hbrkT, -⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
  have hstB : bs.isStateful bcBus = false := (facts.byteXorSpec_sound bcBus spec hspec).1
  obtain ⟨hstR, -⟩ := facts.varRangeBus_sound vrBus hvr
  refine denseMergeStateless2_correct isInput d bs hp1
    (denseMkByteCheck spec bcBus x) (denseRangeCheck1 vrBus y (.const b))
    (denseTupleCheck trBus x y) hstB hstR hstT rfl rfl rfl
    (denseTupleKey bs facts bcBus vrBus trBus s1 s2 spec hspec hbound hvr htr hs1 b hble hs2 x y)
    (fun denv => by rw [denseTupleCheck_eval]; exact hbrkT (x.eval denv) (y.eval denv))
    ?_ pre mid post hsplit
  intro v hv
  rw [denseBIVars, List.mem_append] at hv
  rcases hv with hm | he
  · exact absurd hm (by
      rw [show (denseTupleCheck trBus x y).multiplicity.vars = [] from rfl]; simp)
  · obtain ⟨e, he', hve⟩ := List.mem_flatMap.1 he
    have : e = x ∨ e = y := by simpa [denseTupleCheck] using he'
    rcases this with rfl | rfl
    · exact Or.inl (denseMem_biVars_of_payload _ e (denseMkByteCheck_operand_mem spec bcBus e) hve)
    · exact Or.inr (denseMem_biVars_of_payload _ e (by
        show e ∈ [e, DenseExpr.const b]; exact List.mem_cons_self ..) hve)

/-- Packing a range check (first) with a byte check (second) into a tuple check is
    `DensePassCorrect` — the swapped orientation. -/
theorem densePackRangeFirst_correct (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    (trBus s1 s2 bcBus vrBus : Nat)
    (htr : facts.tupleRangeBus trBus = some (s1, s2)) (hs1 : s1 = 256)
    (x y : DenseExpr p) (b : ZMod p) (spec : ByteXorSpec p)
    (hspec : facts.byteXorSpec bcBus = some spec) (hbound : spec.bound = 256)
    (hvr : facts.varRangeBus vrBus = true) (hble : b.val ≤ 17) (hs2 : 2 ^ b.val = s2)
    (pre mid post : List (BusInteraction (DenseExpr p)))
    (hsplit : d.busInteractions
      = pre ++ denseRangeCheck1 vrBus y (.const b) :: mid ++ denseMkByteCheck spec bcBus x :: post) :
    DensePassCorrect isInput d
      { d with busInteractions := pre ++ denseTupleCheck trBus x y :: mid ++ post } [] bs := by
  obtain ⟨hstT, hbrkT, -⟩ := facts.tupleRangeBus_sound trBus s1 s2 htr
  have hstB : bs.isStateful bcBus = false := (facts.byteXorSpec_sound bcBus spec hspec).1
  obtain ⟨hstR, -⟩ := facts.varRangeBus_sound vrBus hvr
  refine denseMergeStateless2_correct isInput d bs hp1
    (denseRangeCheck1 vrBus y (.const b)) (denseMkByteCheck spec bcBus x)
    (denseTupleCheck trBus x y) hstR hstB hstT rfl rfl rfl
    (fun denv => by
      rw [denseTupleKey bs facts bcBus vrBus trBus s1 s2 spec hspec hbound hvr htr hs1 b hble hs2
        x y denv]
      exact and_comm)
    (fun denv => by rw [denseTupleCheck_eval]; exact hbrkT (x.eval denv) (y.eval denv))
    ?_ pre mid post hsplit
  intro v hv
  rw [denseBIVars, List.mem_append] at hv
  rcases hv with hm | he
  · exact absurd hm (by
      rw [show (denseTupleCheck trBus x y).multiplicity.vars = [] from rfl]; simp)
  · obtain ⟨e, he', hve⟩ := List.mem_flatMap.1 he
    have : e = x ∨ e = y := by simpa [denseTupleCheck] using he'
    rcases this with rfl | rfl
    · exact Or.inr (denseMem_biVars_of_payload _ e (denseMkByteCheck_operand_mem spec bcBus e) hve)
    · exact Or.inl (denseMem_biVars_of_payload _ e (by
        show e ∈ [e, DenseExpr.const b]; exact List.mem_cons_self ..) hve)

/-! ## Scan invariants: reconstructing the split equation -/

/-- The positional split reconstructed from `denseFindRangePartner`. -/
theorem denseFindRangePartner_split (bs : BusSemantics p) (facts : BusFacts p bs) (s2 : Nat) :
    ∀ (revMid rest : List (BusInteraction (DenseExpr p)))
      (mid : List (BusInteraction (DenseExpr p))) (y : DenseExpr p) (bw : ZMod p)
      (post : List (BusInteraction (DenseExpr p))),
      denseFindRangePartner bs facts s2 revMid rest = some (mid, y, bw, post) →
      ∃ Bm, revMid.reverse ++ rest = mid ++ Bm :: post ∧
        denseMatchRangeCheck bs facts s2 Bm = some (y, bw) := by
  intro revMid rest
  induction rest generalizing revMid with
  | nil => intro _ _ _ _ h; exact absurd h (by simp [denseFindRangePartner])
  | cons c cs ih =>
    intro mid y bw post h
    rw [denseFindRangePartner] at h
    cases hc : denseMatchRangeCheck bs facts s2 c with
    | none => rw [hc] at h; obtain ⟨Bm, heq, hm⟩ := ih (c :: revMid) mid y bw post h
              exact ⟨Bm, by simpa [List.reverse_cons, List.append_assoc] using heq, hm⟩
    | some yb =>
      obtain ⟨y', bw'⟩ := yb
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hmid, hy, hbw, hpost⟩ := h
      subst hmid; subst hy; subst hbw; subst hpost
      exact ⟨c, rfl, hc⟩

/-- The positional split reconstructed from `denseFindBytePartner`. -/
theorem denseFindBytePartner_split (bs : BusSemantics p) (facts : BusFacts p bs) :
    ∀ (revMid rest : List (BusInteraction (DenseExpr p)))
      (mid : List (BusInteraction (DenseExpr p))) (spec : ByteXorSpec p) (x : DenseExpr p)
      (post : List (BusInteraction (DenseExpr p))),
      denseFindBytePartner bs facts revMid rest = some (mid, spec, x, post) →
      ∃ Bm, revMid.reverse ++ rest = mid ++ Bm :: post ∧
        denseMatchByteSingle bs facts Bm = some (spec, x) := by
  intro revMid rest
  induction rest generalizing revMid with
  | nil => intro _ _ _ _ h; exact absurd h (by simp [denseFindBytePartner])
  | cons c cs ih =>
    intro mid spec x post h
    rw [denseFindBytePartner] at h
    cases hc : denseMatchByteSingle bs facts c with
    | none => rw [hc] at h; obtain ⟨Bm, heq, hm⟩ := ih (c :: revMid) mid spec x post h
              exact ⟨Bm, by simpa [List.reverse_cons, List.append_assoc] using heq, hm⟩
    | some sx =>
      obtain ⟨spec', x'⟩ := sx
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hmid, hspec, hx, hpost⟩ := h
      subst hmid; subst hspec; subst hx; subst hpost
      exact ⟨c, rfl, hc⟩

/-- The positional split and selection facts reconstructed from `denseFindTuplePack`: the packable
    pair is a byte check and an exact-width range check in one of the two orientations, split off
    with `x` the byte value and `y` the range value in both cases. -/
theorem denseFindTuplePack_split (bs : BusSemantics p) (facts : BusFacts p bs) (s2 : Nat) :
    ∀ (revPre bis : List (BusInteraction (DenseExpr p)))
      (pre : List (BusInteraction (DenseExpr p))) (x : DenseExpr p)
      (mid : List (BusInteraction (DenseExpr p))) (y : DenseExpr p)
      (post : List (BusInteraction (DenseExpr p))),
      denseFindTuplePack bs facts s2 revPre bis = some (pre, x, mid, y, post) →
      ∃ (D₁ D₂ : BusInteraction (DenseExpr p)) (spec : ByteXorSpec p) (bw : ZMod p),
        revPre.reverse ++ bis = pre ++ D₁ :: mid ++ D₂ :: post ∧
        ((denseMatchByteSingle bs facts D₁ = some (spec, x) ∧
            denseMatchRangeCheck bs facts s2 D₂ = some (y, bw)) ∨
         (denseMatchRangeCheck bs facts s2 D₁ = some (y, bw) ∧
            denseMatchByteSingle bs facts D₂ = some (spec, x))) := by
  intro revPre bis
  induction bis generalizing revPre with
  | nil => intro _ _ _ _ _ h; exact absurd h (by simp [denseFindTuplePack])
  | cons a rest ih =>
    intro pre x mid y post h
    rw [denseFindTuplePack] at h
    cases hba : denseMatchByteSingle bs facts a with
    | some sx =>
      obtain ⟨specA, xA⟩ := sx
      simp only [hba] at h
      cases hrp : denseFindRangePartner bs facts s2 [] rest with
      | none =>
        simp only [hrp] at h
        obtain ⟨D₁, D₂, spec, bw, heq, hcase⟩ := ih (a :: revPre) pre x mid y post h
        exact ⟨D₁, D₂, spec, bw,
          by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq,
          hcase⟩
      | some res =>
        obtain ⟨mid', yB, bwB, post'⟩ := res
        simp only [hrp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hpre, hx, hmid, hy, hpost⟩ := h
        subst hpre; subst hx; subst hmid; subst hy; subst hpost
        obtain ⟨Bm, hbeq, hbm⟩ := denseFindRangePartner_split bs facts s2 [] rest mid' yB bwB post' hrp
        refine ⟨a, Bm, specA, bwB, ?_, Or.inl ⟨hba, hbm⟩⟩
        rw [List.reverse_nil, List.nil_append] at hbeq
        rw [hbeq]; simp only [List.cons_append, List.append_assoc]
    | none =>
      simp only [hba] at h
      cases hra : denseMatchRangeCheck bs facts s2 a with
      | some yb =>
        obtain ⟨yA, bwA⟩ := yb
        simp only [hra] at h
        cases hbp : denseFindBytePartner bs facts [] rest with
        | none =>
          simp only [hbp] at h
          obtain ⟨D₁, D₂, spec, bw, heq, hcase⟩ := ih (a :: revPre) pre x mid y post h
          exact ⟨D₁, D₂, spec, bw,
            by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq,
            hcase⟩
        | some res =>
          obtain ⟨mid', specB, xB, post'⟩ := res
          simp only [hbp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hpre, hx, hmid, hy, hpost⟩ := h
          subst hpre; subst hx; subst hmid; subst hy; subst hpost
          obtain ⟨Bm, hbeq, hbm⟩ := denseFindBytePartner_split bs facts [] rest mid' specB xB post' hbp
          refine ⟨a, Bm, specB, bwA, ?_, Or.inr ⟨hra, hbm⟩⟩
          rw [List.reverse_nil, List.nil_append] at hbeq
          rw [hbeq]; simp only [List.cons_append, List.append_assoc]
      | none =>
        simp only [hra] at h
        obtain ⟨D₁, D₂, spec, bw, heq, hcase⟩ := ih (a :: revPre) pre x mid y post h
        exact ⟨D₁, D₂, spec, bw,
          by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq,
          hcase⟩

/-! ## Candidate soundness: the omitted re-check is always true by construction -/

/-- Every candidate `denseTupleBusCandidates` emits carries its declaring tuple fact with a
    byte-sized first slot. -/
theorem denseTupleBusCandidates_inv (bs : BusSemantics p) (facts : BusFacts p bs) (maxId : Nat) :
    ∀ c ∈ denseTupleBusCandidates bs facts maxId,
      facts.tupleRangeBus c.1 = some (c.2.1, c.2.2) ∧ c.2.1 = 256 := by
  intro c hc
  simp only [denseTupleBusCandidates, List.mem_filterMap] at hc
  obtain ⟨k, _hk, hfm⟩ := hc
  cases htr : facts.tupleRangeBus k with
  | none => simp only [htr] at hfm; exact absurd hfm (by simp)
  | some s12 =>
    obtain ⟨s1, s2⟩ := s12
    simp only [htr] at hfm
    by_cases hs1 : s1 = 256
    · rw [if_pos hs1, Option.some.injEq] at hfm
      subst hfm
      exact ⟨htr, hs1⟩
    · rw [if_neg hs1] at hfm; exact absurd hfm (by simp)

/-- Soundness of the candidate scan: a hit recovers the chosen bus's tuple fact (byte-sized first
    slot) and the exact-width second slot `s2` the scan matched on, plus the underlying
    `denseFindTuplePack` result. -/
theorem denseTryTupleBuses_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) :
    ∀ (cands : List (Nat × Nat × Nat)),
      (∀ c ∈ cands, facts.tupleRangeBus c.1 = some (c.2.1, c.2.2) ∧ c.2.1 = 256) →
      ∀ (trBus : Nat) (pre : List (BusInteraction (DenseExpr p))) (x : DenseExpr p)
        (mid : List (BusInteraction (DenseExpr p))) (y : DenseExpr p)
        (post : List (BusInteraction (DenseExpr p))),
        denseTryTupleBuses bs facts bis cands = some (trBus, pre, x, mid, y, post) →
        ∃ s2, facts.tupleRangeBus trBus = some (256, s2) ∧
          denseFindTuplePack bs facts s2 [] bis = some (pre, x, mid, y, post) := by
  intro cands
  induction cands with
  | nil => intro _ _ _ _ _ _ _ h; exact absurd h (by simp [denseTryTupleBuses])
  | cons c rest ih =>
    obtain ⟨trBus₀, s1₀, s2₀⟩ := c
    intro hinv trBus pre x mid y post h
    rw [denseTryTupleBuses] at h
    cases hfp : denseFindTuplePack bs facts s2₀ [] bis with
    | none => rw [hfp] at h
              exact ih (fun c hc => hinv c (List.mem_cons_of_mem _ hc)) trBus pre x mid y post h
    | some res =>
      obtain ⟨pre', x', mid', y', post'⟩ := res
      rw [hfp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨htb, hpre, hx, hmid, hy, hpost⟩ := h
      obtain ⟨hfact, hs1⟩ := hinv (trBus₀, s1₀, s2₀) (List.mem_cons_self ..)
      have hfact' : facts.tupleRangeBus trBus₀ = some (s1₀, s2₀) := hfact
      have hs1' : s1₀ = 256 := hs1
      subst hs1'
      refine ⟨s2₀, ?_, ?_⟩
      · rw [← htb]; exact hfact'
      · rw [← hpre, ← hx, ← hmid, ← hy, ← hpost]; exact hfp

/-! ## One drain step: correctness and coverage -/

/-- One drain step is `DensePassCorrect`: the pair `denseTryTupleBuses` selected packs into a single
    tuple check via the appropriate orientation certificate. -/
theorem denseTupleStep_correct (isInput : VarId → Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (ac : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (maxId trBus : Nat)
    (pre : List (BusInteraction (DenseExpr p))) (x : DenseExpr p)
    (mid : List (BusInteraction (DenseExpr p))) (y : DenseExpr p)
    (post : List (BusInteraction (DenseExpr p)))
    (htt : denseTryTupleBuses bs facts bis (denseTupleBusCandidates bs facts maxId)
      = some (trBus, pre, x, mid, y, post)) :
    DensePassCorrect isInput ⟨ac, bis⟩
      ⟨ac, pre ++ denseTupleCheck trBus x y :: mid ++ post⟩ [] bs := by
  obtain ⟨s2, htr, hfp⟩ := denseTryTupleBuses_sound bs facts bis _
    (denseTupleBusCandidates_inv bs facts maxId) trBus pre x mid y post htt
  obtain ⟨D₁, D₂, spec, bw, heq, hcase⟩ :=
    denseFindTuplePack_split bs facts s2 [] bis pre x mid y post hfp
  rw [List.reverse_nil, List.nil_append] at heq
  rcases hcase with ⟨hb, hr⟩ | ⟨hr, hb⟩
  · -- byte-first orientation
    obtain ⟨hD1eq, hspec, hbound⟩ := denseMatchByteSingle_eq bs facts hb
    obtain ⟨hD2eq, hvr, hble, hs2⟩ := denseMatchRangeCheck_eq bs facts hr
    have hsplit : (⟨ac, bis⟩ : DenseConstraintSystem p).busInteractions
        = pre ++ denseMkByteCheck spec D₁.busId x :: mid ++
            denseRangeCheck1 D₂.busId y (.const bw) :: post := by
      show bis = _; rw [heq]; rw [← hD1eq, ← hD2eq]
    exact densePackByteFirst_correct isInput ⟨ac, bis⟩ bs facts hp1 trBus 256 s2 D₁.busId D₂.busId
      htr rfl x y bw spec hspec hbound hvr hble hs2 pre mid post hsplit
  · -- range-first orientation
    obtain ⟨hD1eq, hvr, hble, hs2⟩ := denseMatchRangeCheck_eq bs facts hr
    obtain ⟨hD2eq, hspec, hbound⟩ := denseMatchByteSingle_eq bs facts hb
    have hsplit : (⟨ac, bis⟩ : DenseConstraintSystem p).busInteractions
        = pre ++ denseRangeCheck1 D₁.busId y (.const bw) :: mid ++
            denseMkByteCheck spec D₂.busId x :: post := by
      show bis = _; rw [heq]; rw [← hD1eq, ← hD2eq]
    exact densePackRangeFirst_correct isInput ⟨ac, bis⟩ bs facts hp1 trBus 256 s2 D₂.busId D₁.busId
      htr rfl x y bw spec hspec hbound hvr hble hs2 pre mid post hsplit

/-- One drain step preserves registry coverage of the interaction list. -/
theorem denseTupleStep_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (maxId trBus : Nat)
    (pre : List (BusInteraction (DenseExpr p))) (x : DenseExpr p)
    (mid : List (BusInteraction (DenseExpr p))) (y : DenseExpr p)
    (post : List (BusInteraction (DenseExpr p)))
    (hcov : ∀ bi ∈ bis, denseBICovered reg bi)
    (htt : denseTryTupleBuses bs facts bis (denseTupleBusCandidates bs facts maxId)
      = some (trBus, pre, x, mid, y, post)) :
    ∀ bi ∈ pre ++ denseTupleCheck trBus x y :: mid ++ post, denseBICovered reg bi := by
  obtain ⟨s2, _htr, hfp⟩ := denseTryTupleBuses_sound bs facts bis _
    (denseTupleBusCandidates_inv bs facts maxId) trBus pre x mid y post htt
  obtain ⟨D₁, D₂, spec, bw, heq, hcase⟩ :=
    denseFindTuplePack_split bs facts s2 [] bis pre x mid y post hfp
  rw [List.reverse_nil, List.nil_append] at heq
  have hmemD1 : D₁ ∈ bis := by rw [heq]; simp only [List.mem_append, List.mem_cons]; tauto
  have hmemD2 : D₂ ∈ bis := by rw [heq]; simp only [List.mem_append, List.mem_cons]; tauto
  have hmemPMP : ∀ bi, bi ∈ pre ∨ bi ∈ mid ∨ bi ∈ post → bi ∈ bis := by
    intro bi hbi; rw [heq]; simp only [List.mem_append, List.mem_cons]; tauto
  -- the tuple check is covered: x from the byte half, y from the range half
  have hxcov : x.CoveredBy reg ∧ y.CoveredBy reg := by
    rcases hcase with ⟨hb, hr⟩ | ⟨hr, hb⟩
    · obtain ⟨hD1eq, _, _⟩ := denseMatchByteSingle_eq bs facts hb
      obtain ⟨hD2eq, _, _, _⟩ := denseMatchRangeCheck_eq bs facts hr
      have hxmem : x ∈ D₁.payload := hD1eq.symm ▸ denseMkByteCheck_operand_mem spec D₁.busId x
      have hymem0 : y ∈ (denseRangeCheck1 D₂.busId y (DenseExpr.const bw)).payload :=
        List.mem_cons_self ..
      have hymem : y ∈ D₂.payload := hD2eq.symm ▸ hymem0
      exact ⟨(hcov D₁ hmemD1).2 x hxmem, (hcov D₂ hmemD2).2 y hymem⟩
    · obtain ⟨hD1eq, _, _, _⟩ := denseMatchRangeCheck_eq bs facts hr
      obtain ⟨hD2eq, _, _⟩ := denseMatchByteSingle_eq bs facts hb
      have hxmem : x ∈ D₂.payload := hD2eq.symm ▸ denseMkByteCheck_operand_mem spec D₂.busId x
      have hymem0 : y ∈ (denseRangeCheck1 D₁.busId y (DenseExpr.const bw)).payload :=
        List.mem_cons_self ..
      have hymem : y ∈ D₁.payload := hD1eq.symm ▸ hymem0
      exact ⟨(hcov D₂ hmemD2).2 x hxmem, (hcov D₁ hmemD1).2 y hymem⟩
  have htcov : denseBICovered reg (denseTupleCheck trBus x y) := by
    refine ⟨?_, ?_⟩
    · intro i hi; simp only [denseTupleCheck, DenseExpr.vars, List.not_mem_nil] at hi
    · intro e he
      simp only [denseTupleCheck, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact hxcov.1
      · exact hxcov.2
  intro bi hbi
  simp only [List.mem_append, List.mem_cons] at hbi
  rcases hbi with (h | rfl | h) | h
  · exact hcov bi (hmemPMP bi (Or.inl h))
  · exact htcov
  · exact hcov bi (hmemPMP bi (Or.inr (Or.inl h)))
  · exact hcov bi (hmemPMP bi (Or.inr (Or.inr h)))

/-! ## Draining every packable pair -/

/-- The drain (fuel-bounded) is `DensePassCorrect` and preserves coverage: each step packs one pair
    (`denseTupleStep_correct`/`denseTupleStep_covered`) and the loop composes single steps through
    `DensePassCorrect.trans`. Proven for any fuel; the wired pass uses the interaction-list length. -/
theorem denseDrainTuplePacks_correct (isInput : VarId → Bool) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    (ac : List (DenseExpr p)) :
    ∀ (fuel : Nat) (bis : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ bis, denseBICovered reg bi) →
      DensePassCorrect isInput ⟨ac, bis⟩
          ⟨ac, denseDrainTuplePacks bs facts fuel bis⟩ [] bs ∧
        (∀ bi ∈ denseDrainTuplePacks bs facts fuel bis, denseBICovered reg bi) := by
  intro fuel
  induction fuel with
  | zero =>
    intro bis hcov
    exact ⟨DensePassCorrect.refl isInput ⟨ac, bis⟩ bs, hcov⟩
  | succ fuel ih =>
    intro bis hcov
    rw [denseDrainTuplePacks]
    cases htt : denseTryTupleBuses bs facts bis
      (denseTupleBusCandidates bs facts ((bis.map (fun bi => bi.busId)).foldl max 0 + 65)) with
    | none =>
      exact ⟨DensePassCorrect.refl isInput ⟨ac, bis⟩ bs, hcov⟩
    | some res =>
      obtain ⟨trBus, pre, x, mid, y, post⟩ := res
      have hstep := denseTupleStep_correct isInput bs facts hp1 ac bis
        ((bis.map (fun bi => bi.busId)).foldl max 0 + 65) trBus pre x mid y post htt
      have hstepcov := denseTupleStep_covered reg bs facts bis
        ((bis.map (fun bi => bi.busId)).foldl max 0 + 65) trBus pre x mid y post hcov htt
      obtain ⟨hrec, hreccov⟩ := ih (pre ++ denseTupleCheck trBus x y :: mid ++ post) hstepcov
      exact ⟨hstep.trans hrec, hreccov⟩

/-! ## The dense pass -/

/-- Coverage preservation of the whole dense transform. -/
theorem denseTupleRangeF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseTupleRangeF bs facts d).CoveredBy reg := by
  unfold denseTupleRangeF
  split
  · rename_i hp1
    obtain ⟨hac, hbi⟩ := hcov
    refine ⟨hac, ?_⟩
    exact (denseDrainTuplePacks_correct reg.isInput reg bs facts hp1 d.algebraicConstraints
      d.busInteractions.length d.busInteractions hbi).2
  · exact hcov

/-- Correctness of the whole dense transform. -/
theorem denseTupleRangeF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseTupleRangeF bs facts d) [] bs := by
  unfold denseTupleRangeF
  split
  · rename_i hp1
    obtain ⟨hac, hbi⟩ := hcov
    have h := (denseDrainTuplePacks_correct reg.isInput reg bs facts hp1 d.algebraicConstraints
      d.busInteractions.length d.busInteractions hbi).1
    -- `⟨d.algebraicConstraints, d.busInteractions⟩ = d`
    have hd : (⟨d.algebraicConstraints, d.busInteractions⟩ : DenseConstraintSystem p) = d := rfl
    rw [hd] at h
    exact h
  · exact DensePassCorrect.refl reg.isInput d bs

/-- The dense tuple-range packing pass (see `denseTupleRangeF`, `TupleRange.lean`). -/
def denseTupleRangePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs facts d => denseTupleRangeF bs facts d)
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseTupleRangeF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseTupleRangeF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
