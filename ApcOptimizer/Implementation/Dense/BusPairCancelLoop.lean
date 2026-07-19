import ApcOptimizer.Implementation.Dense.BusPairCancelCheckProof
import ApcOptimizer.Implementation.Dense.BusPairCancelWits
import ApcOptimizer.Implementation.Dense.BusPairCancelIndexProof
import ApcOptimizer.Implementation.Dense.AddrDiseqProof

set_option autoImplicit false

/-! # Dense stable-state cancellation loop assembly for `busPairCancel` (Task 3, chunk C7)

Dense, `VarId`-native transliteration of the final slice of
`OptimizerPasses/BusPairCancel.lean` (:2311-2624): the `DropResult` record, its builder
`mkDropResult`, the indexed left-to-right scan `findCancelGoIdx`, the per-bus search `findCancel`,
the stable-state cancellation loop `cancelLoop`, and the top-level pass `busPairCancelPass` — now the
native dense pass `denseBusPairCancelPass`. Impl and its (interleaved) proof live together because the
loop's well-founded recursion rides on the erased proof fields (`decreases`), and the accepted-drop
builder discharges its single-step correctness inline via C5's `denseCheckCancel_sound`.

## `DenseDropResult` keeps its proof fields

The spec `DropResult` (:2320) carries data (`aliveNew`/`checksNew`/`emitted`/`dropIdx`/`dropPos`) plus
*erased* proof fields (`sizeNew`, `step : PassCorrect …`, `decreases`). `DenseDropResult` keeps them
all — they are erased `Prop`s (zero runtime cost) and `decreases` is load-bearing for the loop's
termination. `step`/`covNew` are stated *quantified over `isInput`/`reg` with the current logical
system's coverage as a hypothesis*, so the loop never carries `reg`/`isInput` as runtime data (they
appear only inside erased proof fields): the loop's data signature mirrors the spec's exactly, and
one lift to the audited `Variable` spec happens at the pass boundary.

## `mkDropResult` discharge of C5/C4/C6

`denseMkDropResult` mirrors `mkDropResult` (:2336): the split of the current logical interactions
around the two live positions (`denseLiveSeg_split`, then appending the checks) feeds C5's
`denseCheckCancel_sound` (its exact hypothesis list was designed for this: `Sound` facts for `T`/`M`
supplied as parameters — `DenseTwoRootMap.build_sound` + `rfl` from the `Thunk.mk`-built certs, C4's
`denseLiveSeg_split` for `hsplit`, the scan's `hmid`/`hshield`, and C6's
`denseDropWits_mem`/`denseDropFormWits_mem` + `denseLiveSeg_mem` for `hwits`/`hfwits`); tombstoning the
two positions (`denseLiveSeg_drop`) rewrites its output into the next logical system, and the two C4
lemmas give the live-count decrease. The coverage-preservation field `covNew` closes over the emitted
checks' coverage witness (`hcheckcov`, discharged at the call site from `denseMkByteCheck_covered`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ### Coverage of an emitted byte check -/

/-- An emitted byte check `denseMkByteCheck spec busId e` mentions no variable beyond `e`'s, so it is
    covered whenever `e` is. -/
theorem denseMkByteCheck_covered (reg : VarRegistry) (spec : ByteXorSpec p) (busId : Nat)
    (e : DenseExpr p) (he : e.CoveredBy reg) :
    denseBICovered reg (denseMkByteCheck spec busId e) := by
  refine ⟨?_, ?_⟩
  · intro i hi; simp only [denseMkByteCheck, DenseExpr.vars, List.not_mem_nil] at hi
  · intro pe hpe i hi
    exact he i (denseMkByteCheck_payload_vars spec busId e pe hpe hi)

/-- Coverage of the emitted-checks list built inside `denseFindCancelGoIdx`: each element (there is at
    most one) is `denseMkByteCheck spec bcBus e` for an `e` in `R`'s payload, hence covered whenever
    `R`'s payload is. -/
theorem denseEmittedChecks_covered (unjust : List Nat) (bcBus? : Option (Nat × ByteXorSpec p))
    (R : BusInteraction (DenseExpr p)) (reg : VarRegistry)
    (hRpay : ∀ e ∈ R.payload, e.CoveredBy reg)
    (bi : BusInteraction (DenseExpr p))
    (hbi : bi ∈ (match unjust, bcBus? with
        | [slot], some (bcBus, spec) =>
            (R.payload[slot]?).elim [] (fun e => [denseMkByteCheck spec bcBus e])
        | _, _ => [])) :
    denseBICovered reg bi := by
  split at hbi
  · rename_i slot bcBus spec
    cases hget : R.payload[slot]? with
    | none => rw [hget] at hbi; simp only [Option.elim] at hbi; exact absurd hbi (by simp)
    | some e =>
        rw [hget] at hbi; simp only [Option.elim, List.mem_singleton] at hbi
        rw [hbi]
        exact denseMkByteCheck_covered reg spec bcBus e (hRpay e (List.mem_of_getElem? hget))
  · exact absurd hbi (by simp)

/-! ### The accepted-drop record

One accepted drop, as consumed by `denseCancelLoop`. `sizeNew`/`step`/`decreases`/`covNew` are erased
`Prop`s; `step`/`covNew` are quantified over `isInput`/`reg` with the current system's coverage as a
hypothesis, so the loop stays `reg`-free at the data level. Native mirror of `DropResult` (:2320). -/
structure DenseDropResult (cs0 : DenseConstraintSystem p) (bs : BusSemantics p)
    (arr : Array (BusInteraction (DenseExpr p)))
    (alive : Array Bool) (checks : List (BusInteraction (DenseExpr p))) where
  aliveNew : Array Bool
  checksNew : List (BusInteraction (DenseExpr p))
  emitted : Bool
  dropIdx : Nat
  dropPos : Nat
  sizeNew : aliveNew.size = arr.size
  step : ∀ (isInput : VarId → Bool) (reg : VarRegistry),
    (denseMkCs cs0 arr alive checks).CoveredBy reg →
    DensePassCorrect isInput (denseMkCs cs0 arr alive checks)
      (denseMkCs cs0 arr aliveNew checksNew) [] bs
  decreases : denseLiveCount arr aliveNew < denseLiveCount arr alive
  covNew : ∀ (reg : VarRegistry), (denseMkCs cs0 arr alive checks).CoveredBy reg →
    (denseMkCs cs0 arr aliveNew checksNew).CoveredBy reg

/-- Assemble the `DenseDropResult` for an accepted candidate. Native mirror of `mkDropResult`
    (:2336); the `T`/`M`/`candsOf` soundness facts (dropped from the plain dense certs/maps) and the
    emitted-checks coverage witness `hcheckcov` are supplied as parameters, and the single step is
    proved by C5's `denseCheckCancel_sound`. All of it is erased. -/
def denseMkDropResult (cs0 : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (T : Thunk (DenseAddrCerts p))
    (hTtworoot : T.get.tworoot.Sound cs0.algebraicConstraints)
    (hTnonzero : T.get.nonzero = DenseNonzeroWits.build cs0.algebraicConstraints)
    (M : Thunk (DenseEqConstraintMap p)) (hM : M.get.Sound cs0.algebraicConstraints)
    (domCs : List (DenseExpr p)) (hdomCs : ∀ c ∈ domCs, c ∈ cs0.algebraicConstraints)
    (candsOf : VarId → List (DenseExpr p))
    (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ cs0.algebraicConstraints)
    (fidx bidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (checksOld : List (BusInteraction (DenseExpr p))) (hsz : alive.size = arr.size)
    (iP jP : Nat) (S R : BusInteraction (DenseExpr p)) (slots : List Nat) (bound : Nat)
    (checks : List (BusInteraction (DenseExpr p)))
    (checksNew : List (BusInteraction (DenseExpr p))) (hchecksNew : checksNew = checksOld ++ checks)
    (hcheckcov : ∀ (reg : VarRegistry), (∀ e ∈ R.payload, e.CoveredBy reg) →
      (∀ bi ∈ checks, denseBICovered reg bi))
    (emitted : Bool) (dropIdx dropPos : Nat)
    (hij : iP < jP) (hjsz : jP < arr.size)
    (hSget : arr[iP]? = some S) (hRget : arr[jP]? = some R)
    (hSalive : alive[iP]?.getD false = true) (hRalive : alive[jP]?.getD false = true)
    (hslots : facts.recvByteSlots busId (R.payload.map DenseExpr.constValue?) = some (slots, bound))
    (hmid : ∀ m0 ∈ denseLiveSeg arr alive (iP + 1) (jP - iP - 1),
      denseMidRefuted shape T busId S m0 = true)
    (hshield : denseShieldOk shape T busId S (denseLiveSeg arr alive 0 iP) = true)
    (hchk : denseCheckCancel deep bs facts M domCs candsOf
      (denseDropWits facts bidx arr alive S R checksOld checks) (denseDropFormWits fidx arr alive S R)
      busId shape slots bound S R checks = true) :
    DenseDropResult cs0 bs arr alive checksOld := by
  let A := denseLiveSeg arr alive 0 iP
  let B := denseLiveSeg arr alive (iP + 1) (jP - iP - 1)
  let C' := denseLiveSeg arr alive (jP + 1) (arr.size - jP - 1)
  let aliveNew := (alive.setIfInBounds iP false).setIfInBounds jP false
  have hisz : iP < alive.size := by rw [hsz]; omega
  have hjsz' : jP < alive.size := by rw [hsz]; exact hjsz
  have hsplitL : denseLiveSeg arr alive 0 arr.size = A ++ S :: B ++ R :: C' :=
    denseLiveSeg_split arr alive iP jP arr.size S R hij hjsz hSget hRget hSalive hRalive
  have hsplit : (denseMkCs cs0 arr alive checksOld).busInteractions
      = A ++ S :: B ++ R :: (C' ++ checksOld) := by
    show denseLiveSeg arr alive 0 arr.size ++ checksOld = _
    rw [hsplitL]; simp only [List.append_assoc, List.cons_append]
  have horig : ∀ bi ∈ denseLiveSeg arr alive 0 arr.size, bi ≠ S → bi ≠ R →
      bi ∈ A ++ B ++ (C' ++ checksOld) := by
    intro bi hbi hnS hnR
    have hb := mem_core_of_ne hsplitL hbi hnS hnR
    simp only [List.mem_append] at hb ⊢; tauto
  have hchecks : ∀ bi ∈ checksOld, bi ∈ A ++ B ++ (C' ++ checksOld) := by
    intro bi hbi; simp only [List.mem_append]; tauto
  have hdropL : denseLiveSeg arr aliveNew 0 arr.size = A ++ B ++ C' :=
    denseLiveSeg_drop arr alive iP jP arr.size hij hjsz hisz hjsz' aliveNew rfl
  have heq : { (denseMkCs cs0 arr alive checksOld) with
        busInteractions := A ++ B ++ (C' ++ checksOld) ++ checks }
      = denseMkCs cs0 arr aliveNew checksNew := by
    show { cs0 with busInteractions := A ++ B ++ (C' ++ checksOld) ++ checks }
        = { cs0 with busInteractions := denseLiveSeg arr aliveNew 0 arr.size ++ checksNew }
    rw [hdropL, hchecksNew]; congr 1; simp only [List.append_assoc]
  refine {
    aliveNew := aliveNew
    checksNew := checksNew
    emitted := emitted
    dropIdx := dropIdx
    dropPos := dropPos
    sizeNew := by simp only [aliveNew, Array.size_setIfInBounds]; exact hsz
    step := fun isInput reg hsys => heq ▸
      denseCheckCancel_sound isInput (denseMkCs cs0 arr alive checksOld) bs facts hp1 deep hdeep
        reg hsys busId shape hshape slots bound T hTtworoot hTnonzero M hM domCs candsOf
        (denseDropWits facts bidx arr alive S R checksOld checks)
        (denseDropFormWits fidx arr alive S R)
        A S B R (C' ++ checksOld) hslots checks hsplit hdomCs hcands
        (denseDropWits_mem facts bidx arr alive S R checksOld checks horig hchecks)
        (denseDropFormWits_mem fidx arr alive S R horig checks) hmid hshield hchk
    decreases := ?_
    covNew := fun reg hsys => by
      refine ⟨hsys.1, ?_⟩
      show ∀ bi ∈ denseLiveSeg arr aliveNew 0 arr.size ++ checksNew, denseBICovered reg bi
      intro bi hbi
      have hbusR : R ∈ denseLiveSeg arr alive 0 arr.size ++ checksOld :=
        List.mem_append_left _ (denseLiveSeg_mem arr alive 0 arr.size jP R (Nat.zero_le _)
          (by omega) hRalive hRget)
      have hRcov : denseBICovered reg R := hsys.2 R hbusR
      rcases List.mem_append.1 hbi with h | h
      · rw [hdropL] at h
        have hbiOld : bi ∈ denseLiveSeg arr alive 0 arr.size := by
          rw [hsplitL]; simp only [List.mem_append, List.mem_cons] at h ⊢; tauto
        exact hsys.2 bi (List.mem_append_left _ hbiOld)
      · rw [hchecksNew, List.mem_append] at h
        rcases h with h | h
        · exact hsys.2 bi (List.mem_append_right _ h)
        · exact hcheckcov reg hRcov.2 bi h }
  show (denseLiveSeg arr aliveNew 0 arr.size).length < (denseLiveSeg arr alive 0 arr.size).length
  rw [hdropL, hsplitL]
  simp only [List.length_append, List.length_cons]
  omega

/-- Indexed left-to-right scan for the first droppable pair on `busId`, from position `i`. Native
    mirror of `findCancelGoIdx` (:2420): at each live send `S`, find its first matching *live* receive
    through the hash index and run the region tests over the *live* before/between regions; the byte
    justification runs only for candidates that already match. The deliberately-thunked continuation
    `next` (:2438) is preserved exactly — it must not run once a pair is accepted. -/
def denseFindCancelGoIdx (cs0 : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (aggressive : Bool)
    (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape)
    (T : Thunk (DenseAddrCerts p))
    (hTtworoot : T.get.tworoot.Sound cs0.algebraicConstraints)
    (hTnonzero : T.get.nonzero = DenseNonzeroWits.build cs0.algebraicConstraints)
    (M : Thunk (DenseEqConstraintMap p)) (hM : M.get.Sound cs0.algebraicConstraints)
    (domCsT : Thunk { l : List (DenseExpr p) // ∀ c ∈ l, c ∈ cs0.algebraicConstraints })
    (candsT : Thunk (DenseVarCsIdx p))
    (hcands : ∀ x, ∀ c ∈ candsT.get.lookup x, c ∈ cs0.algebraicConstraints)
    (bcBus? : Option (Nat × ByteXorSpec p))
    (fidx bidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (checksOld : List (BusInteraction (DenseExpr p))) (hsz : alive.size = arr.size)
    (idx : Std.HashMap UInt64 (List Nat))
    (i : Nat) : Option (DenseDropResult cs0 bs arr alive checksOld) :=
  if hi : i < arr.size then
    let S := arr[i]
    -- (thunked: Lean is strict, and the continuation must not run once a pair is accepted)
    let next := fun (_ : Unit) => denseFindCancelGoIdx cs0 bs facts hp1 deep hdeep aggressive busId
      shape hshape T hTtworoot hTnonzero M hM domCsT candsT hcands bcBus? fidx bidx arr alive
      checksOld hsz idx (i + 1)
    if haliveS : alive[i]?.getD false = true then
    if decide (denseMultConst S = some shape.setNewMult) && decide (S.busId = busId) then
      match hfm : denseFirstMatchAt M arr alive busId S i (idx.getD
          (mixHash (hash busId)
            (if aggressive then denseAddrHash shape S.payload else densePayloadHash S.payload)) []) with
      | some j =>
        match hR : arr[j]? with
        | some R =>
          have hij : i < j := (denseFirstMatchAt_spec M arr alive busId S i _ hfm).1
          have hRalive : alive[j]?.getD false = true :=
            (denseFirstMatchAt_spec M arr alive busId S i _ hfm).2
          have hjlt : j < arr.size := by
            by_contra hc
            rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hR; simp at hR
          have hSget : arr[i]? = some S := Array.getElem?_eq_getElem hi
          let B := denseLiveArr arr alive hsz (i + 1) (j - i - 1) (by omega)
          if hmidB : B.all (denseMidRefuted shape T busId S) = true then
          let A := denseLiveArr arr alive hsz 0 i (by omega)
          if hshieldA : denseShieldOk shape T busId S A = true then
          have hBeq : B = denseLiveSeg arr alive (i + 1) (j - i - 1) :=
            denseLiveArr_eq arr alive hsz (i + 1) (j - i - 1) (by omega)
          have hAeq : A = denseLiveSeg arr alive 0 i := denseLiveArr_eq arr alive hsz 0 i (by omega)
          have hmid : ∀ m0 ∈ denseLiveSeg arr alive (i + 1) (j - i - 1),
              denseMidRefuted shape T busId S m0 = true := by
            rw [← hBeq]; exact fun m0 hm0 => List.all_eq_true.mp hmidB m0 hm0
          have hshield : denseShieldOk shape T busId S (denseLiveSeg arr alive 0 i) = true := by
            rw [← hAeq]; exact hshieldA
          match hslots : facts.recvByteSlots busId (R.payload.map DenseExpr.constValue?) with
          | none => next ()
          | some (slots, bound) =>
          if hchk0 : denseCheckCancel deep bs facts M domCsT.get.val candsT.get.lookup
              (denseDropWits facts bidx arr alive S R checksOld []) (denseDropFormWits fidx arr alive S R)
              busId shape slots bound S R [] = true then
            some (denseMkDropResult cs0 bs facts hp1 deep hdeep busId shape hshape T hTtworoot
              hTnonzero M hM domCsT.get.val domCsT.get.property candsT.get.lookup hcands
              fidx bidx arr alive checksOld hsz i j S R slots bound [] checksOld
              (List.append_nil checksOld).symm (fun reg _ bi hbi => absurd hbi (by simp))
              false 0 i hij hjlt hSget hR haliveS hRalive hslots hmid hshield hchk0)
          else
          let unjust := denseUnjustifiedSlots bound deep domCsT.get.val candsT.get.lookup bs facts
            (denseDropWits facts bidx arr alive S R checksOld []) (denseDropFormWits fidx arr alive S R)
            slots R
          let checks : List (BusInteraction (DenseExpr p)) :=
            match unjust, bcBus? with
            | [slot], some (bcBus, spec) => (R.payload[slot]?).elim [] (fun e =>
                [denseMkByteCheck spec bcBus e])
            | _, _ => []
          if !checks.isEmpty && (aggressive || decide (S.payload = R.payload)) then
            if hchk : denseCheckCancel deep bs facts M domCsT.get.val candsT.get.lookup
                (denseDropWits facts bidx arr alive S R checksOld checks)
                (denseDropFormWits fidx arr alive S R)
                busId shape slots bound S R checks = true then
              some (denseMkDropResult cs0 bs facts hp1 deep hdeep busId shape hshape T hTtworoot
                hTnonzero M hM domCsT.get.val domCsT.get.property candsT.get.lookup hcands
                fidx bidx arr alive checksOld hsz i j S R slots bound checks (checksOld ++ checks) rfl
                (fun reg hRpay bi hbi => denseEmittedChecks_covered unjust bcBus? R reg hRpay bi hbi)
                true 0 i hij hjlt hSget hR haliveS hRalive hslots hmid hshield hchk)
            else next ()
          else next ()
          else next ()
          else next ()
        | none => next ()
      | none => next ()
    else next ()
    else next ()
  else none
  termination_by arr.size - i

/-- Search declared buses from list index `curIdx` for a droppable pair, honouring the resume hint.
    Native mirror of `findCancel` (:2514). -/
def denseFindCancel (cs0 : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (aggressive : Bool)
    (T : Thunk (DenseAddrCerts p))
    (hTtworoot : T.get.tworoot.Sound cs0.algebraicConstraints)
    (hTnonzero : T.get.nonzero = DenseNonzeroWits.build cs0.algebraicConstraints)
    (M : Thunk (DenseEqConstraintMap p)) (hM : M.get.Sound cs0.algebraicConstraints)
    (domCsT : Thunk { l : List (DenseExpr p) // ∀ c ∈ l, c ∈ cs0.algebraicConstraints })
    (candsT : Thunk (DenseVarCsIdx p))
    (hcands : ∀ x, ∀ c ∈ candsT.get.lookup x, c ∈ cs0.algebraicConstraints)
    (fidx bidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (checksOld : List (BusInteraction (DenseExpr p))) (hsz : alive.size = arr.size)
    (idx : Std.HashMap UInt64 (List Nat))
    (bcBus? : Option (Nat × ByteXorSpec p)) (resumeIdx resumePos : Nat) :
    Nat → List Nat → Option (DenseDropResult cs0 bs arr alive checksOld)
  | _, [] => none
  | curIdx, busId :: rest =>
    if curIdx < resumeIdx then
      denseFindCancel cs0 bs facts hp1 deep hdeep aggressive T hTtworoot hTnonzero M hM domCsT candsT
        hcands fidx bidx arr alive checksOld hsz idx bcBus? resumeIdx resumePos (curIdx + 1) rest
    else
      let startPos := if curIdx = resumeIdx then resumePos else 0
      match hshape : facts.memShape busId with
      | some shape =>
        match denseFindCancelGoIdx cs0 bs facts hp1 deep hdeep aggressive busId shape hshape
            T hTtworoot hTnonzero M hM domCsT candsT hcands bcBus? fidx bidx arr alive checksOld
            hsz idx startPos with
        | some dr => some { dr with dropIdx := curIdx }
        | none => denseFindCancel cs0 bs facts hp1 deep hdeep aggressive T hTtworoot hTnonzero M hM
            domCsT candsT hcands fidx bidx arr alive checksOld hsz idx bcBus? resumeIdx resumePos
            (curIdx + 1) rest
      | none => denseFindCancel cs0 bs facts hp1 deep hdeep aggressive T hTtworoot hTnonzero M hM
          domCsT candsT hcands fidx bidx arr alive checksOld hsz idx bcBus? resumeIdx resumePos
          (curIdx + 1) rest

/-! ### The cancellation-loop result bundle

`denseCancelLoop` returns the materialized final system together with (erased) native correctness and
coverage, each quantified over `isInput`/`reg` with `cs0` coverage as the only hypothesis. -/
structure DenseCancelBundle (cs0 : DenseConstraintSystem p) (bs : BusSemantics p) where
  out : DenseConstraintSystem p
  covered : ∀ (reg : VarRegistry), cs0.CoveredBy reg → out.CoveredBy reg
  correct : ∀ (isInput : VarId → Bool) (reg : VarRegistry), cs0.CoveredBy reg →
    DensePassCorrect isInput cs0 out [] bs

/-- Cancel every droppable pair in one pass invocation, iterating over a *stable* tombstoned array and
    receive index. Native mirror of `cancelLoop` (:2553): each accepted drop is certified by
    `denseCheckCancel_sound` (inside its `DenseDropResult.step`) and the composite is
    `DensePassCorrect.andThen`; the coverage invariant is threaded via `DenseDropResult.covNew`. Total,
    recursing on the strictly-decreasing live-interaction count; the final compact interaction list is
    materialized once, here, when the search reports no further pair. -/
def denseCancelLoop (cs0 : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (aggressive : Bool)
    (T : Thunk (DenseAddrCerts p))
    (hTtworoot : T.get.tworoot.Sound cs0.algebraicConstraints)
    (hTnonzero : T.get.nonzero = DenseNonzeroWits.build cs0.algebraicConstraints)
    (M : Thunk (DenseEqConstraintMap p)) (hM : M.get.Sound cs0.algebraicConstraints)
    (domCsT : Thunk { l : List (DenseExpr p) // ∀ c ∈ l, c ∈ cs0.algebraicConstraints })
    (candsT : Thunk (DenseVarCsIdx p))
    (hcands : ∀ x, ∀ c ∈ candsT.get.lookup x, c ∈ cs0.algebraicConstraints)
    (bcBus? : Option (Nat × ByteXorSpec p)) (busIds : List Nat)
    (fidx bidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p)))
    (idx : Std.HashMap UInt64 (List Nat))
    (alive : Array Bool) (checksOld : List (BusInteraction (DenseExpr p)))
    (hsz : alive.size = arr.size) (resumeIdx resumePos : Nat)
    (hcur : ∀ (isInput : VarId → Bool) (reg : VarRegistry), cs0.CoveredBy reg →
      DensePassCorrect isInput cs0 (denseMkCs cs0 arr alive checksOld) [] bs)
    (hsyscov : ∀ (reg : VarRegistry), cs0.CoveredBy reg →
      (denseMkCs cs0 arr alive checksOld).CoveredBy reg) :
    DenseCancelBundle cs0 bs :=
  match hfc : denseFindCancel cs0 bs facts hp1 deep hdeep aggressive T hTtworoot hTnonzero M hM domCsT
      candsT hcands fidx bidx arr alive checksOld hsz idx bcBus? resumeIdx resumePos 0 busIds with
  | none =>
    { out := { cs0 with
        busInteractions := denseLiveArr arr alive hsz 0 arr.size (by omega) ++ checksOld }
      covered := fun reg hcs0 => by
        rw [show ({ cs0 with
                busInteractions := denseLiveArr arr alive hsz 0 arr.size (by omega) ++ checksOld })
              = denseMkCs cs0 arr alive checksOld from by unfold denseMkCs; rw [denseLiveArr_eq]]
        exact hsyscov reg hcs0
      correct := fun isInput reg hcs0 => by
        rw [show ({ cs0 with
                busInteractions := denseLiveArr arr alive hsz 0 arr.size (by omega) ++ checksOld })
              = denseMkCs cs0 arr alive checksOld from by unfold denseMkCs; rw [denseLiveArr_eq]]
        exact hcur isInput reg hcs0 }
  | some dr =>
    let nextIdx := if dr.emitted then 0 else dr.dropIdx
    let nextPos := if dr.emitted then 0 else dr.dropPos
    denseCancelLoop cs0 bs facts hp1 deep hdeep aggressive T hTtworoot hTnonzero M hM domCsT candsT
      hcands bcBus? busIds fidx bidx arr idx dr.aliveNew dr.checksNew dr.sizeNew nextIdx nextPos
      (fun isInput reg hcs0 => (hcur isInput reg hcs0).andThen (dr.step isInput reg (hsyscov reg hcs0)))
      (fun reg hcs0 => dr.covNew reg (hsyscov reg hcs0))
  termination_by denseLiveCount arr alive
  decreasing_by exact dr.decreases

/-- The native value-only dense bus-pair-cancellation pass. Native mirror of `busPairCancelPass`
    (:2590): builds the per-invocation certs/indices once, runs `denseCancelLoop` to its fixpoint, and
    connects to the audited `Variable` spec via `DensePassCorrect.lift` on the native
    `DensePassCorrect` proof (no commutation with the reference pass). Registry unchanged (no fresh
    vars; emitted checks' vars ⊆ `R`'s payload vars ⊆ `cs`'s). -/
def denseBusPairCancelPass (pw : PrimeWitness p) (aggressive : Bool) : DenseVerifiedPassW p :=
  fun reg d hcov bs facts =>
  if hp1 : (1 : ZMod p) ≠ 0 then
    let busIds := (d.busInteractions.map (fun bi => bi.busId)).dedup
    let deep : Bool := pw.isPrime
    let arr := d.busInteractions.toArray
    let idx := denseRecvIndexAll facts aggressive arr
    let alive : Array Bool := Array.replicate arr.size true
    let T : Thunk (DenseAddrCerts p) :=
      Thunk.mk fun _ => DenseAddrCerts.build d.algebraicConstraints
    let M : Thunk (DenseEqConstraintMap p) :=
      Thunk.mk fun _ =>
        if aggressive then DenseEqConstraintMap.build d.algebraicConstraints
        else DenseEqConstraintMap.empty
    let domCsT : Thunk { l : List (DenseExpr p) // ∀ c ∈ l, c ∈ d.algebraicConstraints } :=
      Thunk.mk fun _ => ⟨d.algebraicConstraints.filter DenseExpr.isSingleVar,
        fun _ hc => List.mem_of_mem_filter hc⟩
    let candsT : Thunk (DenseVarCsIdx p) :=
      Thunk.mk fun _ => DenseVarCsIdx.build d.algebraicConstraints
    have hsz : alive.size = arr.size := by simp only [alive, Array.size_replicate]
    have halltrue : ∀ k, k < arr.size → alive[k]?.getD false = true := by
      intro k hk
      simp only [alive, Array.getElem?_replicate, hk, if_true, Option.getD_some]
    have hTtworoot : T.get.tworoot.Sound d.algebraicConstraints :=
      DenseTwoRootMap.build_sound d.algebraicConstraints
    have hTnonzero : T.get.nonzero = DenseNonzeroWits.build d.algebraicConstraints := rfl
    have hM : M.get.Sound d.algebraicConstraints := by
      show (if aggressive then DenseEqConstraintMap.build d.algebraicConstraints
        else DenseEqConstraintMap.empty).Sound d.algebraicConstraints
      split
      · exact DenseEqConstraintMap.build_sound d.algebraicConstraints
      · exact DenseEqConstraintMap.empty_sound d.algebraicConstraints
    have hcands : ∀ x, ∀ c ∈ candsT.get.lookup x, c ∈ d.algebraicConstraints :=
      fun x => DenseVarCsIdx.lookup_mem (DenseVarCsIdx.build_sound d.algebraicConstraints) x
    let fidx := denseBuildFormIdx bs arr
    let bidx := denseBuildBoundIdx bs facts arr
    let bcBus? := busIds.findSome? (fun k => match facts.byteXorSpec k with
      | some spec => if spec.bound = 256 then some (k, spec) else none
      | none => none)
    have hcur0 : ∀ (isInput : VarId → Bool) (reg : VarRegistry), d.CoveredBy reg →
        DensePassCorrect isInput d (denseMkCs d arr alive []) [] bs :=
      fun isInput _ _ => by
        rw [denseMkCs_all d arr rfl alive halltrue]; exact DensePassCorrect.refl isInput d bs
    have hsyscov0 : ∀ (reg : VarRegistry), d.CoveredBy reg →
        (denseMkCs d arr alive []).CoveredBy reg :=
      fun _ hcs0 => by rw [denseMkCs_all d arr rfl alive halltrue]; exact hcs0
    let bundle := denseCancelLoop d bs facts hp1 deep (fun h => pw.correct h) aggressive
      T hTtworoot hTnonzero M hM domCsT candsT hcands bcBus? busIds fidx bidx arr idx alive [] hsz 0 0
      hcur0 hsyscov0
    { reg' := reg
      out := bundle.out
      derivs := []
      ext := VarRegistry.Extends.refl reg
      covered := bundle.covered reg hcov
      dcovered := by intro x hx; simp at hx
      correct := DensePassCorrect.lift hcov (bundle.covered reg hcov) (by intro x hx; simp at hx)
        (bundle.correct reg.isInput reg hcov) }
  else
    { reg' := reg
      out := d
      derivs := []
      ext := VarRegistry.Extends.refl reg
      covered := hcov
      dcovered := by intro x hx; simp at hx
      correct := DensePassCorrect.lift hcov hcov (by intro x hx; simp at hx)
        (DensePassCorrect.refl reg.isInput d bs) }

end ApcOptimizer.Dense
