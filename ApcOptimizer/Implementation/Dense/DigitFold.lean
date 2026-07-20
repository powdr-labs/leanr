import ApcOptimizer.Implementation.Dense.Affine
import ApcOptimizer.Implementation.Dense.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify

set_option autoImplicit false

/-! # Dense bounded-payload digit fold (Task 3)

Dense, `VarId`-native port of `DigitFold.digitFoldPass`. The pass detects a witness limb forced to a
compile-time constant by a byte check over a base-256 ladder, and substitutes it away. This file
mirrors the spec detection on `DenseExpr`/`VarId` so the dense transform decodes to *exactly* the
spec pass's output, inheriting the spec `PassCorrect` (no correctness re-proved).

The one nontrivial ingredient is a dense fact-derived bounds map (`Std.HashMap VarId Nat`) that
corresponds value-for-value, under `resolve`, to the spec `BoundsMap.build facts`. Because the spec
never characterizes its build's contents value-wise (passes only use its `sound` field), we mirror
the build's structure and prove the correspondence by induction. -/

namespace ApcOptimizer.Dense

open DigitFold

variable {p : ℕ}

/-! ## Dense mirrors of the per-interaction bound machinery -/

/-- Dense `isVarOf`: is this dense expression literally `.var i`? -/
def denseIsVarOf (i : VarId) : DenseExpr p → Bool
  | .var j => j = i
  | _ => false

/-- Dense `varSlot`: the first payload slot literally `.var i`. -/
def denseVarSlot (i : VarId) : List (DenseExpr p) → Option Nat
  | [] => none
  | e :: rest => if denseIsVarOf i e then some 0 else (denseVarSlot i rest).map (· + 1)

/-- `denseIsVarOf` commutes with decode (needs `i` and the leaf valid). -/
theorem denseIsVarOf_decode (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) (e : DenseExpr p)
    (he : e.CoveredBy reg) : isVarOf (reg.resolve i) (reg.decodeExpr e) = denseIsVarOf i e := by
  cases e with
  | var j =>
      have hjv : reg.Valid j := he j (by simp [DenseExpr.vars])
      simp only [denseIsVarOf, VarRegistry.decodeExpr, isVarOf, decide_eq_decide]
      constructor
      · intro h; exact reg.resolve_inj hjv hi h
      · intro h; exact h ▸ rfl
  | const n => rfl
  | add a b => rfl
  | mul a b => rfl

/-- `denseVarSlot` commutes with decode. -/
theorem denseVarSlot_decode (reg : VarRegistry) {i : VarId} (hi : reg.Valid i)
    (pl : List (DenseExpr p)) (hpl : ∀ e ∈ pl, e.CoveredBy reg) :
    varSlot (reg.resolve i) (pl.map reg.decodeExpr) = denseVarSlot i pl := by
  induction pl with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map_cons, varSlot, denseVarSlot,
        denseIsVarOf_decode reg hi e (hpl e (List.mem_cons_self ..))]
      rw [ih (fun e' he' => hpl e' (List.mem_cons_of_mem _ he'))]

/-- The dense payload's constant-value pattern equals the decoded payload's. -/
theorem densePayload_constValue?_decode (reg : VarRegistry) (pl : List (DenseExpr p)) :
    (pl.map reg.decodeExpr).map Expression.constValue? = pl.map DenseExpr.constValue? := by
  rw [List.map_map]
  exact List.map_congr_left (fun e _ => reg.decodeExpr_constValue? e)

/-- Scaling preserves a dense linear form's term-variable list. -/
theorem DenseLinExpr.scale_terms_fst (k : ZMod p) (l : DenseLinExpr p) :
    (l.scale k).terms.map Prod.fst = l.terms.map Prod.fst := by
  simp [DenseLinExpr.scale, List.map_map, Function.comp_def]

/-- Dense linearization introduces no `VarId` outside the expression. -/
theorem denseLinearize_vars (e : DenseExpr p) (l : DenseLinExpr p) (h : denseLinearize e = some l) :
    ∀ i ∈ l.terms.map Prod.fst, i ∈ e.vars := by
  induction e generalizing l with
  | const n => simp only [denseLinearize, Option.some.injEq] at h; subst h; simp
  | var x =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      intro i hi; simpa [DenseExpr.vars] using hi
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          intro i hi
          simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hi
          simp only [DenseExpr.vars, List.mem_append]
          exact hi.imp (iha la hla i) (ihb lb hlb i)
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            intro i hi
            rw [DenseLinExpr.scale_terms_fst] at hi
            exact List.mem_append.2 (Or.inr (ihb lb hlb i hi))
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              intro i hi
              rw [DenseLinExpr.scale_terms_fst] at hi
              exact List.mem_append.2 (Or.inl (iha la hla i hi))
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-- Dense `interactionBound`: one value bound for `i` from a constant-nonzero-multiplicity
    interaction carrying `.var i` in a fact-bounded raw payload slot. -/
def denseInteractionBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) : Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot

theorem denseInteractionBound_decode (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) (bi : BusInteraction (DenseExpr p))
    (hc : denseBICovered reg bi) :
    interactionBound bs facts (reg.decodeBI bi) (reg.resolve i) = denseInteractionBound bs facts bi i := by
  unfold interactionBound denseInteractionBound
  rw [show (reg.decodeBI bi).multiplicity = reg.decodeExpr bi.multiplicity from rfl,
    reg.decodeExpr_constValue? bi.multiplicity]
  cases bi.multiplicity.constValue? with
  | none => rfl
  | some mval =>
    dsimp only
    by_cases hmz : mval = 0
    · simp only [hmz, if_pos]
    · rw [if_neg hmz, if_neg hmz,
        show (reg.decodeBI bi).payload = bi.payload.map reg.decodeExpr from rfl,
        denseVarSlot_decode reg hi bi.payload hc.2]
      cases denseVarSlot i bi.payload with
      | none => rfl
      | some slot =>
        dsimp only
        rw [densePayload_constValue?_decode reg bi.payload]
        rfl

/-- Dense probe payload: constant slots at their constants, slot `i` at the candidate, others `0`. -/
def denseProbeBase (payload : List (DenseExpr p)) (i : Nat) (v : ZMod p) : List (ZMod p) :=
  (payload.map (fun e => (DenseExpr.constValue? e).getD 0)).set i v

theorem denseProbeBase_decode (reg : VarRegistry) (pl : List (DenseExpr p)) (i : Nat) (v : ZMod p) :
    probeBase (pl.map reg.decodeExpr) i v = denseProbeBase pl i v := by
  have hmap : (pl.map reg.decodeExpr).map (fun e => (e.constValue?).getD 0)
      = pl.map (fun e => (DenseExpr.constValue? e).getD 0) := by
    rw [List.map_map]
    exact List.map_congr_left
      (fun e _ => by simp only [Function.comp_apply, reg.decodeExpr_constValue?])
  simp only [probeBase, denseProbeBase, hmap]

/-- Dense `probedSlotBoundAt`: a probed value bound for `i` (see the spec `probedSlotBoundAt`). -/
def denseProbedSlotBoundAt (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) (j : Nat) : Option Nat :=
  if p = 0 then none
  else
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some s =>
        if s = j then none
        else
          match facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) s with
          | none => none
          | some B₀ =>
            if 256 < B₀ then none
            else
              match facts.slotFun bi.busId (bi.payload.map DenseExpr.constValue?) j with
              | none => none
              | some f =>
                match bi.payload[j]? with
                | none => none
                | some e =>
                  match denseLinearize e with
                  | none => none
                  | some l =>
                    match l.terms with
                    | [(y, c)] =>
                      if y = i ∧ (List.range bi.payload.length).all (fun k =>
                          k == s || k == j ||
                            ((bi.payload[k]?.map
                              (fun e' => (DenseExpr.constValue? e').isSome)).getD false)) then
                        capBound (probeMax (fun v =>
                          f ((denseProbeBase bi.payload s ((v : ℕ) : ZMod p)).set j 0)
                            == l.const + c * ((v : ℕ) : ZMod p)) B₀) B₀
                      else none
                    | _ => none

theorem denseProbedSlotBoundAt_decode (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) (bi : BusInteraction (DenseExpr p))
    (hc : denseBICovered reg bi) (j : Nat) :
    probedSlotBoundAt bs facts (reg.decodeBI bi) (reg.resolve i) j
      = denseProbedSlotBoundAt bs facts bi i j := by
  unfold probedSlotBoundAt denseProbedSlotBoundAt
  by_cases hp0 : p = 0
  · rw [if_pos hp0, if_pos hp0]
  rw [if_neg hp0, if_neg hp0,
    show (reg.decodeBI bi).multiplicity = reg.decodeExpr bi.multiplicity from rfl,
    reg.decodeExpr_constValue? bi.multiplicity]
  cases bi.multiplicity.constValue? with
  | none => rfl
  | some mval =>
    dsimp only
    by_cases hmz : mval = 0
    · simp only [hmz, if_pos]
    rw [if_neg hmz, if_neg hmz,
      show (reg.decodeBI bi).payload = bi.payload.map reg.decodeExpr from rfl,
      denseVarSlot_decode reg hi bi.payload hc.2]
    cases denseVarSlot i bi.payload with
    | none => rfl
    | some s =>
      dsimp only
      by_cases hsj : s = j
      · rw [if_pos hsj, if_pos hsj]
      rw [if_neg hsj, if_neg hsj,
        show (reg.decodeBI bi).busId = bi.busId from rfl,
        densePayload_constValue?_decode reg bi.payload]
      cases facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) s with
      | none => rfl
      | some B₀ =>
        dsimp only
        by_cases hcap : 256 < B₀
        · rw [if_pos hcap, if_pos hcap]
        rw [if_neg hcap, if_neg hcap]
        cases facts.slotFun bi.busId (bi.payload.map DenseExpr.constValue?) j with
        | none => rfl
        | some f =>
          dsimp only
          rw [List.getElem?_map]
          cases hpj : bi.payload[j]? with
          | none => rfl
          | some e =>
            simp only [Option.map_some]
            have hev : e.CoveredBy reg := hc.2 e (List.mem_of_getElem? hpj)
            have hlin := reg.denseLinearize_decode e
            cases hdl : denseLinearize e with
            | none => rw [hdl] at hlin; simp only [Option.map_none] at hlin; rw [← hlin]
            | some dl =>
              rw [hdl] at hlin
              simp only [Option.map_some] at hlin
              rw [← hlin]
              dsimp only [VarRegistry.decodeLin]
              -- match on dl.terms
              cases hterms : dl.terms with
              | nil => simp only [List.map_nil]
              | cons t rest =>
                cases rest with
                | cons t2 rest2 => simp only [List.map_cons]
                | nil =>
                  obtain ⟨i', c⟩ := t
                  have hi'mem : i' ∈ e.vars :=
                    denseLinearize_vars e dl hdl i' (by rw [hterms]; simp)
                  have hi'v : reg.Valid i' := hev i' hi'mem
                  have hcond : (reg.resolve i' = reg.resolve i) = (i' = i) :=
                    propext ⟨fun h => reg.resolve_inj hi'v hi h, fun h => by rw [h]⟩
                  simp only [List.map_cons, List.map_nil, List.length_map, List.getElem?_map,
                    Option.map_map, Function.comp_def, reg.decodeExpr_constValue?,
                    denseProbeBase_decode, hcond]

/-! ## Dense bounds map (`Std.HashMap VarId Nat`)

A plain runtime map (no soundness field — correctness flows through the decode-commutation of the
whole pass). We mirror the spec `BoundsMap.build`'s structure and prove the built map corresponds,
value-for-value under `resolve`, to `(BoundsMap.build facts).map`. -/

/-- Dense `insertEntry`: keep the smaller of two bounds for `i`. -/
def denseInsertEntry (T : Std.HashMap VarId Nat) (i : VarId) (b : Nat) : Std.HashMap VarId Nat :=
  let keep : Bool := match T[i]? with
    | some b0 => decide (b < b0)
    | none => true
  if keep then T.insert i b else T

/-- Dense raw-variable payload entries. -/
def denseRawVarsOf (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.payload.filterMap (fun e => match e with | .var i => some i | _ => none)

/-- Dense probed-bound candidate `(VarId, slot)` pairs. -/
def denseProbeCandidatesOf (bi : BusInteraction (DenseExpr p)) : List (VarId × Nat) :=
  if (bi.multiplicity.constValue?).isSome then
    (List.range bi.payload.length).filterMap (fun j =>
      match bi.payload[j]? with
      | some e =>
        match denseLinearize e with
        | some l => match l.terms with
          | [(y, _)] => some (y, j)
          | _ => none
        | none => none
      | none => none)
  else []

/-- Dense `goCands`: for candidate `(y, j)`s matching `i`, insert the probed bound. -/
def denseGoCands (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (i : VarId) : List (VarId × Nat) → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | (y, j) :: cl, T =>
    if y = i then
      match denseProbedSlotBoundAt bs facts bi i j with
      | some b => denseGoCands bs facts bi i cl (denseInsertEntry T i b)
      | none => denseGoCands bs facts bi i cl T
    else denseGoCands bs facts bi i cl T

/-- Dense `addVars`: for each raw variable `i`, insert its interaction bound then its probed bounds. -/
def denseAddVars (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (cands : List (VarId × Nat)) :
    List VarId → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | i :: xs, T =>
    let T1 := match denseInteractionBound bs facts bi i with
      | some b => denseInsertEntry T i b
      | none => T
    denseAddVars bs facts bi cands xs (denseGoCands bs facts bi i cands T1)

/-- Dense `addAll`: collect bounds from every interaction's fact-bounded raw payload slots. -/
def denseAddAll (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | bi :: rest, T =>
    denseAddAll bs facts rest (denseAddVars bs facts bi (denseProbeCandidatesOf bi)
      (denseRawVarsOf bi) T)

/-- Dense bounds-map build. -/
def denseBuild (bs : BusSemantics p) (facts : BusFacts p bs)
    (dbis : List (BusInteraction (DenseExpr p))) : Std.HashMap VarId Nat :=
  denseAddAll bs facts dbis ∅

/-! ## Bounds-map correspondence under `resolve` -/

/-- The `.map` field of `insertEntry` (proof-agnostic). -/
theorem BoundsMap.insertEntry_map {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : BoundsMap p cs bs) (x : Variable) (b : Nat) (h) :
    (T.insertEntry x b h).map
      = (if (match T.map[x]? with | some b0 => decide (b < b0) | none => (true : Bool)) = true
         then T.map.insert x b else T.map) := by
  unfold BoundsMap.insertEntry
  rw [apply_ite BoundsMap.map]
  rfl

/-- `insertEntry` preserves the `denseBM[i]? = specBM.map[resolve i]?` invariant. -/
theorem denseInsertEntry_decode {cs : ConstraintSystem p} {bs : BusSemantics p}
    (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) (b : Nat)
    (Tspec : BoundsMap p cs bs) (Tdense : Std.HashMap VarId Nat)
    (h : ∀ env, (∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false) → (env (reg.resolve i)).val < b)
    (hinv : ∀ k, reg.Valid k → Tdense[k]? = Tspec.map[reg.resolve k]?) :
    ∀ k, reg.Valid k →
      (denseInsertEntry Tdense i b)[k]?
        = (Tspec.insertEntry (reg.resolve i) b h).map[reg.resolve k]? := by
  intro k hk
  rw [BoundsMap.insertEntry_map]
  unfold denseInsertEntry
  simp only [hinv i hi]
  by_cases hkeep : (match Tspec.map[reg.resolve i]? with
      | some b0 => decide (b < b0) | none => (true : Bool)) = true
  · rw [if_pos hkeep, if_pos hkeep, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    by_cases hik : i = k
    · subst hik; simp
    · have hik' : ¬ reg.resolve i = reg.resolve k := fun he => hik (reg.resolve_inj hi hk he)
      rw [if_neg (by simpa using hik), if_neg (by simpa using hik')]
      exact hinv k hk
  · rw [if_neg hkeep, if_neg hkeep]
    exact hinv k hk

/-- `rawVarsOf` commutes with decode. -/
theorem denseRawVarsOf_decode (reg : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    BoundsMap.rawVarsOf (reg.decodeBI bi) = (denseRawVarsOf bi).map reg.resolve := by
  unfold BoundsMap.rawVarsOf denseRawVarsOf
  show (bi.payload.map reg.decodeExpr).filterMap _ = _
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext e
  cases e <;> rfl

/-- Raw variables of a covered interaction are valid. -/
theorem denseRawVarsOf_valid {reg : VarRegistry} {bi : BusInteraction (DenseExpr p)}
    (hc : denseBICovered reg bi) : ∀ i ∈ denseRawVarsOf bi, reg.Valid i := by
  intro i hi
  unfold denseRawVarsOf at hi
  rw [List.mem_filterMap] at hi
  obtain ⟨e, hemem, he⟩ := hi
  cases e with
  | var j =>
      simp only [Option.some.injEq] at he
      subst he
      exact hc.2 _ hemem j (by simp [DenseExpr.vars])
  | const n => simp at he
  | add a b => simp at he
  | mul a b => simp at he

/-- `probeCandidatesOf` commutes with decode. -/
theorem denseProbeCandidatesOf_decode (reg : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    BoundsMap.probeCandidatesOf (reg.decodeBI bi)
      = (denseProbeCandidatesOf bi).map (fun t => (reg.resolve t.1, t.2)) := by
  unfold BoundsMap.probeCandidatesOf denseProbeCandidatesOf
  rw [show (reg.decodeBI bi).multiplicity = reg.decodeExpr bi.multiplicity from rfl,
    reg.decodeExpr_constValue? bi.multiplicity]
  by_cases hm : (bi.multiplicity.constValue?).isSome
  · rw [if_pos hm, if_pos hm,
      show (reg.decodeBI bi).payload = bi.payload.map reg.decodeExpr from rfl, List.length_map,
      List.map_filterMap]
    congr 1
    funext j
    rw [List.getElem?_map]
    cases hpj : bi.payload[j]? with
    | none => rfl
    | some e =>
      simp only [Option.map_some]
      have hlin := reg.denseLinearize_decode e
      cases hdl : denseLinearize e with
      | none => rw [hdl] at hlin; simp only [Option.map_none] at hlin; rw [← hlin]; rfl
      | some dl =>
        rw [hdl] at hlin; simp only [Option.map_some] at hlin; rw [← hlin]
        dsimp only [VarRegistry.decodeLin]
        cases hterms : dl.terms with
        | nil => simp
        | cons hd tl =>
          cases tl with
          | cons t2 tl2 => simp
          | nil => obtain ⟨i', c⟩ := hd; simp
  · rw [if_neg hm, if_neg hm, List.map_nil]

/-- Probe-candidate variables of a covered interaction are valid. -/
theorem denseProbeCandidatesOf_valid {reg : VarRegistry} {bi : BusInteraction (DenseExpr p)}
    (hc : denseBICovered reg bi) : ∀ t ∈ denseProbeCandidatesOf bi, reg.Valid t.1 := by
  intro t ht
  unfold denseProbeCandidatesOf at ht
  by_cases hm : (bi.multiplicity.constValue?).isSome
  · rw [if_pos hm, List.mem_filterMap] at ht
    obtain ⟨j, _, hj⟩ := ht
    revert hj
    cases hpj : bi.payload[j]? with
    | none => simp
    | some e =>
      have hev : e.CoveredBy reg := hc.2 e (List.mem_of_getElem? hpj)
      dsimp only
      cases hdl : denseLinearize e with
      | none => simp
      | some dl =>
        dsimp only
        cases hterms : dl.terms with
        | nil => simp
        | cons hd tl =>
          cases tl with
          | cons t2 tl2 => simp
          | nil =>
            obtain ⟨i', cc⟩ := hd
            simp only [Option.some.injEq]
            intro hj
            subst hj
            exact hev _ (denseLinearize_vars e dl hdl i' (by rw [hterms]; simp))
  · rw [if_neg hm] at ht; simp at ht

/-- `goCands` preserves the correspondence invariant. -/
theorem denseGoCands_decode {cs : ConstraintSystem p} {bs : BusSemantics p}
    (facts : BusFacts p bs) (reg : VarRegistry) {i : VarId} (hi : reg.Valid i)
    (bi : BusInteraction (DenseExpr p)) (hc : denseBICovered reg bi)
    (hbi : reg.decodeBI bi ∈ cs.busInteractions) :
    ∀ (cl : List (VarId × Nat)) (Tspec : BoundsMap p cs bs) (Tdense : Std.HashMap VarId Nat),
      (∀ t ∈ cl, reg.Valid t.1) →
      (∀ k, reg.Valid k → Tdense[k]? = Tspec.map[reg.resolve k]?) →
      ∀ k, reg.Valid k →
        (denseGoCands bs facts bi i cl Tdense)[k]?
          = (BoundsMap.addAll.addVars.goCands facts (reg.decodeBI bi) hbi (reg.resolve i)
              (cl.map (fun t => (reg.resolve t.1, t.2))) Tspec).map[reg.resolve k]? := by
  intro cl
  induction cl with
  | nil =>
      intro Tspec Tdense _ hinv k hk
      show (Tdense)[k]? = (BoundsMap.addAll.addVars.goCands facts (reg.decodeBI bi) hbi (reg.resolve i)
        [] Tspec).map[reg.resolve k]?
      unfold BoundsMap.addAll.addVars.goCands
      exact hinv k hk
  | cons c cl ih =>
      intro Tspec Tdense hclv hinv k hk
      obtain ⟨y, j⟩ := c
      have hyv : reg.Valid y := hclv (y, j) (List.mem_cons_self ..)
      have hclv' : ∀ t ∈ cl, reg.Valid t.1 := fun t ht => hclv t (List.mem_cons_of_mem _ ht)
      show (denseGoCands bs facts bi i ((y, j) :: cl) Tdense)[k]?
        = (BoundsMap.addAll.addVars.goCands facts (reg.decodeBI bi) hbi (reg.resolve i)
            ((reg.resolve y, j) :: cl.map (fun t => (reg.resolve t.1, t.2))) Tspec).map[reg.resolve k]?
      unfold denseGoCands BoundsMap.addAll.addVars.goCands
      by_cases hyi : y = i
      · subst hyi
        have hpb := denseProbedSlotBoundAt_decode bs facts reg hi bi hc j
        rw [if_pos rfl, if_pos rfl]
        split
        · rename_i b heq_d
          have hps : probedSlotBoundAt bs facts (reg.decodeBI bi) (reg.resolve y) j = some b :=
            hpb.trans heq_d
          split
          · rename_i b' heq_s
            rw [hps] at heq_s
            obtain rfl := Option.some.inj heq_s
            exact ih (Tspec.insertEntry (reg.resolve y) b _) (denseInsertEntry Tdense y b) hclv'
              (denseInsertEntry_decode reg hi b Tspec Tdense _ hinv) k hk
          · rename_i heq_s; rw [hps] at heq_s; exact absurd heq_s (by simp)
        · rename_i heq_d
          have hps : probedSlotBoundAt bs facts (reg.decodeBI bi) (reg.resolve y) j = none :=
            hpb.trans heq_d
          split
          · rename_i b heq_s; rw [hps] at heq_s; exact absurd heq_s (by simp)
          · exact ih Tspec Tdense hclv' hinv k hk
      · have hyi' : ¬ reg.resolve y = reg.resolve i := fun he => hyi (reg.resolve_inj hyv hi he)
        rw [if_neg hyi, if_neg hyi']
        exact ih Tspec Tdense hclv' hinv k hk

/-- `addVars` preserves the correspondence invariant. -/
theorem denseAddVars_decode {cs : ConstraintSystem p} {bs : BusSemantics p}
    (facts : BusFacts p bs) (reg : VarRegistry) (bi : BusInteraction (DenseExpr p))
    (hc : denseBICovered reg bi) (hbi : reg.decodeBI bi ∈ cs.busInteractions)
    (cands : List (VarId × Nat)) (hcandv : ∀ t ∈ cands, reg.Valid t.1) :
    ∀ (xs : List VarId) (Tspec : BoundsMap p cs bs) (Tdense : Std.HashMap VarId Nat),
      (∀ x ∈ xs, reg.Valid x) →
      (∀ k, reg.Valid k → Tdense[k]? = Tspec.map[reg.resolve k]?) →
      ∀ k, reg.Valid k →
        (denseAddVars bs facts bi cands xs Tdense)[k]?
          = (BoundsMap.addAll.addVars facts (reg.decodeBI bi) hbi
              (cands.map (fun t => (reg.resolve t.1, t.2))) (xs.map reg.resolve) Tspec).map[reg.resolve k]? := by
  intro xs
  induction xs with
  | nil => intro Tspec Tdense _ hinv k hk; exact hinv k hk
  | cons x xs ih =>
      intro Tspec Tdense hxsv hinv k hk
      have hxv : reg.Valid x := hxsv x (List.mem_cons_self ..)
      have hxsv' : ∀ x' ∈ xs, reg.Valid x' := fun x' hx' => hxsv x' (List.mem_cons_of_mem _ hx')
      show (denseAddVars bs facts bi cands (x :: xs) Tdense)[k]?
        = (BoundsMap.addAll.addVars facts (reg.decodeBI bi) hbi
            (cands.map (fun t => (reg.resolve t.1, t.2))) (reg.resolve x :: xs.map reg.resolve)
            Tspec).map[reg.resolve k]?
      unfold denseAddVars BoundsMap.addAll.addVars
      have hib := denseInteractionBound_decode bs facts reg hxv bi hc
      refine ih _ _ hxsv'
        (denseGoCands_decode facts reg hxv bi hc hbi cands _ _ hcandv ?_) k hk
      intro kk hkk
      split
      · rename_i b heq_d
        have hib2 : interactionBound bs facts (reg.decodeBI bi) (reg.resolve x) = some b :=
          hib.trans heq_d
        split
        · rename_i b' heq_s; rw [hib2] at heq_s; obtain rfl := Option.some.inj heq_s
          exact denseInsertEntry_decode reg hxv b Tspec Tdense _ hinv kk hkk
        · rename_i heq_s; rw [hib2] at heq_s; exact absurd heq_s (by simp)
      · rename_i heq_d
        have hib2 : interactionBound bs facts (reg.decodeBI bi) (reg.resolve x) = none :=
          hib.trans heq_d
        split
        · rename_i b heq_s; rw [hib2] at heq_s; exact absurd heq_s (by simp)
        · exact hinv kk hkk

/-- `addAll` preserves the correspondence invariant. -/
theorem denseAddAll_decode {cs : ConstraintSystem p} {bs : BusSemantics p}
    (facts : BusFacts p bs) (reg : VarRegistry) :
    ∀ (dbis : List (BusInteraction (DenseExpr p))) (Tspec : BoundsMap p cs bs)
      (Tdense : Std.HashMap VarId Nat) (_hcov : ∀ bi ∈ dbis, denseBICovered reg bi)
      (hmem : ∀ b ∈ dbis.map reg.decodeBI, b ∈ cs.busInteractions),
      (∀ k, reg.Valid k → Tdense[k]? = Tspec.map[reg.resolve k]?) →
      ∀ k, reg.Valid k →
        (denseAddAll bs facts dbis Tdense)[k]?
          = (BoundsMap.addAll facts (dbis.map reg.decodeBI) hmem Tspec).map[reg.resolve k]? := by
  intro dbis
  induction dbis with
  | nil => intro Tspec Tdense _ _ hinv k hk; exact hinv k hk
  | cons bi rest ih =>
      intro Tspec Tdense hcov hmem hinv k hk
      have hbc : denseBICovered reg bi := hcov bi (List.mem_cons_self ..)
      have hcov' : ∀ b ∈ rest, denseBICovered reg b := fun b hb => hcov b (List.mem_cons_of_mem _ hb)
      have hbi : reg.decodeBI bi ∈ cs.busInteractions :=
        hmem (reg.decodeBI bi) (by rw [List.map_cons]; exact List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest.map reg.decodeBI, b ∈ cs.busInteractions :=
        fun b hb => hmem b (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hb)
      show (denseAddAll bs facts (bi :: rest) Tdense)[k]?
        = (BoundsMap.addAll facts (reg.decodeBI bi :: rest.map reg.decodeBI) hmem Tspec).map[reg.resolve k]?
      unfold denseAddAll BoundsMap.addAll
      rw [denseProbeCandidatesOf_decode reg bi, denseRawVarsOf_decode reg bi]
      exact ih _ _ hcov' hrest
        (denseAddVars_decode facts reg bi hbc hbi (denseProbeCandidatesOf bi)
          (denseProbeCandidatesOf_valid hbc) (denseRawVarsOf bi) Tspec Tdense
          (denseRawVarsOf_valid hbc) hinv) k hk

/-! ## Dense byte-pair recognizer -/

/-- Decoding sends a dense expression to a literal constant exactly when it already is one. -/
theorem VarRegistry.decodeExpr_eq_const (reg : VarRegistry) (e : DenseExpr p) (c : ZMod p) :
    reg.decodeExpr e = Expression.const c ↔ e = DenseExpr.const c := by
  cases e <;> simp [VarRegistry.decodeExpr]

/-- Dense byte-pair-check recognizer: a `pairOp`/`result 0`/`mult 1` check on a `byteXorSpec` bus. -/
def densePairByteOps? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | some (op, o1, o2, _r) =>
      if spec.bound = 256 ∧ op = DenseExpr.const spec.pairOp ∧ _r = DenseExpr.const 0
          ∧ bi.multiplicity = DenseExpr.const 1
      then some (o1, o2) else none
    | none => none

theorem densePairByteOps?_decode (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (bi : BusInteraction (DenseExpr p)) :
    pairByteOps? bs facts (reg.decodeBI bi)
      = (densePairByteOps? bs facts bi).map (fun t => (reg.decodeExpr t.1, reg.decodeExpr t.2)) := by
  unfold pairByteOps? densePairByteOps?
  rw [show (reg.decodeBI bi).busId = bi.busId from rfl]
  cases facts.byteXorSpec bi.busId with
  | none => rfl
  | some spec =>
      dsimp only
      rw [show (reg.decodeBI bi).payload = bi.payload.map reg.decodeExpr from rfl,
        spec.decode_map reg.decodeExpr bi.payload]
      cases spec.decode bi.payload with
      | none => rfl
      | some t =>
          obtain ⟨op, o1, o2, r⟩ := t
          simp only [Option.map_some,
            show (reg.decodeBI bi).multiplicity = reg.decodeExpr bi.multiplicity from rfl,
            reg.decodeExpr_eq_const]
          by_cases hcond : spec.bound = 256 ∧ op = DenseExpr.const spec.pairOp
              ∧ r = DenseExpr.const 0 ∧ bi.multiplicity = DenseExpr.const 1
          · rw [if_pos hcond, if_pos hcond]; rfl
          · rw [if_neg hcond, if_neg hcond]; rfl

/-! ## Dense ladder recognition and grid solving -/

/-- Dense ladder-shape check (coefficient-only, so `VarId`-agnostic). -/
def denseIsLadder (pos : Bool) : ℕ → List (VarId × ZMod p) → Bool
  | _, [] => true
  | n, (_, c) :: rest => coeffNat pos c == n && denseIsLadder pos (256 * n) rest

theorem denseIsLadder_decode (reg : VarRegistry) (pos : Bool) :
    ∀ (n : ℕ) (l : List (VarId × ZMod p)),
      isLadder pos n (l.map (fun t => (reg.resolve t.1, t.2))) = denseIsLadder pos n l := by
  intro n l
  induction l generalizing n with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨i, c⟩ := t
      simp only [List.map_cons, isLadder, denseIsLadder, ih]

/-- Dense ladder recognition: sort by sign-interpreted coefficient, check the shape. -/
def denseTryLadder (pos : Bool) (terms : List (VarId × ZMod p)) :
    Option (ℕ × List (VarId × ZMod p)) :=
  match terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2) with
  | [] => none
  | t :: rest =>
    if 0 < coeffNat pos t.2 ∧ denseIsLadder pos (coeffNat pos t.2) (t :: rest) = true
    then some (coeffNat pos t.2, t :: rest) else none

theorem denseTryLadder_decode (reg : VarRegistry) (pos : Bool) (terms : List (VarId × ZMod p)) :
    tryLadder pos (terms.map (fun t => (reg.resolve t.1, t.2)))
      = (denseTryLadder pos terms).map
          (fun gs => (gs.1, gs.2.map (fun t => (reg.resolve t.1, t.2)))) := by
  unfold tryLadder denseTryLadder
  rw [← List.map_mergeSort
    (r := fun a b : VarId × ZMod p => coeffNat pos a.2 ≤ coeffNat pos b.2)
    (s := fun a b : Variable × ZMod p => coeffNat pos a.2 ≤ coeffNat pos b.2)
    (f := fun t => (reg.resolve t.1, t.2)) (l := terms) (fun a _ b _ => rfl)]
  cases terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2) with
  | nil => rfl
  | cons t rest =>
      obtain ⟨i, c⟩ := t
      simp only [List.map_cons]
      have hlad : isLadder pos (coeffNat pos c)
            ((reg.resolve i, c) :: rest.map (fun t => (reg.resolve t.1, t.2)))
          = denseIsLadder pos (coeffNat pos c) ((i, c) :: rest) := by
        simpa [List.map_cons] using denseIsLadder_decode reg pos (coeffNat pos c) ((i, c) :: rest)
      simp only [hlad]
      by_cases hcond : 0 < coeffNat pos c ∧ denseIsLadder pos (coeffNat pos c) ((i, c) :: rest) = true
      · rw [if_pos hcond, if_pos hcond]; rfl
      · rw [if_neg hcond, if_neg hcond]; rfl

/-- The recognised ladder's terms are a subset of the input terms (they are a sorted permutation). -/
theorem denseTryLadder_mem (pos : Bool) (terms : List (VarId × ZMod p))
    (gs : ℕ × List (VarId × ZMod p)) (h : denseTryLadder pos terms = some gs) :
    ∀ t ∈ gs.2, t ∈ terms := by
  have hperm := List.mergeSort_perm terms (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2)
  unfold denseTryLadder at h
  cases hms : terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2) with
  | nil => rw [hms] at h; simp at h
  | cons t0 rest =>
      rw [hms] at h hperm
      dsimp only at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      exact hperm.mem_iff.1 ht

/-- Dense fact-bound lookup for a ladder's variables, in order. -/
def denseLookupBounds (bounds : Std.HashMap VarId Nat) :
    List (VarId × ZMod p) → Option (List ℕ)
  | [] => some []
  | (v, _) :: rest =>
    match bounds[v]? with
    | some B => if B ≤ 256 then (denseLookupBounds bounds rest).map (B :: ·) else none
    | none => none

theorem denseLookupBounds_decode (reg : VarRegistry) (bm : Std.HashMap Variable Nat)
    (denseBM : Std.HashMap VarId Nat)
    (hbm : ∀ i, reg.Valid i → denseBM[i]? = bm[reg.resolve i]?) :
    ∀ (l : List (VarId × ZMod p)), (∀ t ∈ l, reg.Valid t.1) →
      lookupBounds bm (l.map (fun t => (reg.resolve t.1, t.2))) = denseLookupBounds denseBM l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons t rest ih =>
      intro hlv
      obtain ⟨v, c⟩ := t
      have hvv : reg.Valid v := hlv (v, c) (List.mem_cons_self ..)
      simp only [List.map_cons, lookupBounds, denseLookupBounds, hbm v hvv]
      cases bm[reg.resolve v]? with
      | none => rfl
      | some B =>
          dsimp only
          by_cases hB : B ≤ 256
          · rw [if_pos hB, if_pos hB, ih (fun t ht => hlv t (List.mem_cons_of_mem _ ht))]
          · rw [if_neg hB, if_neg hB]

/-- Dense one-sign ladder attempt: recognise, bound, enumerate, force a singleton digit vector. -/
def denseAttemptLadder (pos : Bool) (bounds : Std.HashMap VarId Nat) (l : DenseLinExpr p) :
    Option (VarId × ℕ) :=
  match denseTryLadder pos l.terms with
  | none => none
  | some gs =>
    match denseLookupBounds bounds gs.2 with
    | none => none
    | some Bs =>
      match solutions p (tval pos l.const) gs.1 Bs (gs.1 * ladderVal (Bs.map (· - 1))) with
      | [_ds] =>
        match gs.2, _ds with
        | t :: _, d :: _ => some (t.1, d)
        | _, _ => none
      | _ => none

theorem denseAttemptLadder_decode (reg : VarRegistry) (bm : Std.HashMap Variable Nat)
    (denseBM : Std.HashMap VarId Nat) (hbm : ∀ i, reg.Valid i → denseBM[i]? = bm[reg.resolve i]?)
    (pos : Bool) (l : DenseLinExpr p) (hlv : ∀ t ∈ l.terms, reg.Valid t.1) :
    attemptLadder pos bm (reg.decodeLin l)
      = (denseAttemptLadder pos denseBM l).map (fun r => (reg.resolve r.1, r.2)) := by
  unfold attemptLadder denseAttemptLadder
  rw [show (reg.decodeLin l).terms = l.terms.map (fun t => (reg.resolve t.1, t.2)) from rfl,
    denseTryLadder_decode reg pos l.terms]
  cases hgs : denseTryLadder pos l.terms with
  | none => rfl
  | some gs =>
      simp only [Option.map_some]
      have hgsv : ∀ t ∈ gs.2, reg.Valid t.1 :=
        fun t ht => hlv t (denseTryLadder_mem pos l.terms gs hgs t ht)
      rw [denseLookupBounds_decode reg bm denseBM hbm gs.2 hgsv]
      cases denseLookupBounds denseBM gs.2 with
      | none => rfl
      | some Bs =>
          dsimp only
          rw [show (reg.decodeLin l).const = l.const from rfl]
          cases solutions p (tval pos l.const) gs.1 Bs (gs.1 * ladderVal (Bs.map (· - 1))) with
          | nil => rfl
          | cons ds dstl =>
              cases dstl with
              | cons _ _ => rfl
              | nil =>
                  cases gs.2 with
                  | nil => rfl
                  | cons t0 rest =>
                      cases ds with
                      | nil => rfl
                      | cons d dtl => rfl

/-- Dense operand solver: linearize, require ≥2 ladder digits, try both sign interpretations. -/
def denseSolveOperand (bounds : Std.HashMap VarId Nat) (E : DenseExpr p) : Option (VarId × ℕ) :=
  match denseLinearize E with
  | none => none
  | some l =>
    if l.terms.length < 2 then none
    else
      match denseAttemptLadder true bounds l with
      | some r => some r
      | none => denseAttemptLadder false bounds l

theorem denseSolveOperand_decode (reg : VarRegistry) (bm : Std.HashMap Variable Nat)
    (denseBM : Std.HashMap VarId Nat) (hbm : ∀ i, reg.Valid i → denseBM[i]? = bm[reg.resolve i]?)
    (E : DenseExpr p) (hcov : E.CoveredBy reg) :
    solveOperand bm (reg.decodeExpr E)
      = (denseSolveOperand denseBM E).map (fun r => (reg.resolve r.1, r.2)) := by
  unfold solveOperand denseSolveOperand
  rw [← reg.denseLinearize_decode E]
  cases hdl : denseLinearize E with
  | none => rfl
  | some l =>
      have hlenr : (reg.decodeLin l).terms.length = l.terms.length := by
        simp only [VarRegistry.decodeLin, List.length_map]
      simp only [Option.map_some, hlenr]
      have hlv : ∀ t ∈ l.terms, reg.Valid t.1 :=
        fun t ht => hcov t.1 (denseLinearize_vars E l hdl t.1 (List.mem_map.2 ⟨t, ht, rfl⟩))
      by_cases hlen : l.terms.length < 2
      · rw [if_pos hlen, if_pos hlen]; rfl
      · rw [if_neg hlen, if_neg hlen,
          denseAttemptLadder_decode reg bm denseBM hbm true l hlv]
        cases denseAttemptLadder true denseBM l with
        | some r0 => rfl
        | none =>
            simp only [Option.map_none]
            rw [denseAttemptLadder_decode reg bm denseBM hbm false l hlv]

/-! ## Dense scan for a forced digit and the pass -/

/-- A recognized byte-pair check's operands are covered. -/
theorem densePairByteOps?_covered {bs : BusSemantics p} {facts : BusFacts p bs} {reg : VarRegistry}
    {bi : BusInteraction (DenseExpr p)} (hc : denseBICovered reg bi) {x y : DenseExpr p}
    (h : densePairByteOps? bs facts bi = some (x, y)) : x.CoveredBy reg ∧ y.CoveredBy reg := by
  unfold densePairByteOps? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i op o1 o2 r hdec
      split_ifs at h with hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ho1, ho2, _⟩ := spec.decode_mem bi.payload op o1 o2 r hdec
      exact ⟨hc.2 o1 ho1, hc.2 o2 ho2⟩
    · exact absurd h (by simp)

/-- Dense scan for the first byte-checked ladder operand with a forced digit. -/
def denseFindFold (bs : BusSemantics p) (facts : BusFacts p bs) (denseBM : Std.HashMap VarId Nat) :
    List (BusInteraction (DenseExpr p)) → Option (VarId × ℕ)
  | [] => none
  | bi :: rest =>
    match densePairByteOps? bs facts bi with
    | none => denseFindFold bs facts denseBM rest
    | some (x, y) =>
      match denseSolveOperand denseBM x with
      | some r => some r
      | none =>
        match denseSolveOperand denseBM y with
        | some r => some r
        | none => denseFindFold bs facts denseBM rest

theorem denseFindFold_decode [NeZero p] (hp : 256 < p) {cs : ConstraintSystem p}
    {bs : BusSemantics p} (facts : BusFacts p bs) (bm : BoundsMap p cs bs) (reg : VarRegistry)
    (denseBM : Std.HashMap VarId Nat)
    (hbm : ∀ i, reg.Valid i → denseBM[i]? = bm.map[reg.resolve i]?) :
    ∀ (dpending : List (BusInteraction (DenseExpr p)))
      (hmemproof : ∀ b ∈ dpending.map reg.decodeBI, b ∈ cs.busInteractions),
      (∀ bi ∈ dpending, denseBICovered reg bi) →
      (findFold hp facts bm (dpending.map reg.decodeBI) hmemproof).map (fun f => (f.v, f.d))
        = (denseFindFold bs facts denseBM dpending).map (fun r => (reg.resolve r.1, r.2)) := by
  intro dpending
  induction dpending with
  | nil => intro _ _; rfl
  | cons bi rest ih =>
      intro hmemproof hcov
      have hbc : denseBICovered reg bi := hcov bi (List.mem_cons_self ..)
      have hcov' : ∀ b ∈ rest, denseBICovered reg b := fun b hb => hcov b (List.mem_cons_of_mem _ hb)
      have hrestmem : ∀ b ∈ rest.map reg.decodeBI, b ∈ cs.busInteractions :=
        fun b hb => hmemproof b (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hb)
      have hpc := densePairByteOps?_decode bs facts reg bi
      show Option.map (fun f => (f.v, f.d))
          (findFold hp facts bm (reg.decodeBI bi :: rest.map reg.decodeBI) hmemproof)
        = Option.map (fun r => (reg.resolve r.1, r.2)) (denseFindFold bs facts denseBM (bi :: rest))
      unfold findFold denseFindFold
      cases hdp : densePairByteOps? bs facts bi with
      | none =>
          split
          · exact ih hrestmem hcov'
          · rename_i x' y' hop; rw [hpc, hdp] at hop; exact absurd hop (by simp)
      | some xy =>
          obtain ⟨x, y⟩ := xy
          dsimp only
          obtain ⟨hxc, hyc⟩ := densePairByteOps?_covered hbc hdp
          have hsx := denseSolveOperand_decode reg bm.map denseBM hbm x hxc
          have hsy := denseSolveOperand_decode reg bm.map denseBM hbm y hyc
          split
          · rename_i hop; rw [hpc, hdp] at hop; exact absurd hop (by simp)
          · rename_i x'' y'' hop
            rw [hpc, hdp] at hop
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hop
            obtain ⟨rfl, rfl⟩ := hop
            cases hdx : denseSolveOperand denseBM x with
            | some r =>
                rw [hdx] at hsx; simp only [Option.map_some] at hsx
                split
                · rename_i v d hx
                  rw [hsx] at hx; simp only [Option.some.injEq, Prod.mk.injEq] at hx
                  obtain ⟨rfl, rfl⟩ := hx; rfl
                · rename_i hx; rw [hsx] at hx; exact absurd hx (by simp)
            | none =>
                rw [hdx] at hsx; simp only [Option.map_none] at hsx
                split
                · rename_i v d hx; rw [hsx] at hx; exact absurd hx (by simp)
                · cases hdy : denseSolveOperand denseBM y with
                  | some r =>
                      rw [hdy] at hsy; simp only [Option.map_some] at hsy
                      split
                      · rename_i v d hy
                        rw [hsy] at hy; simp only [Option.some.injEq, Prod.mk.injEq] at hy
                        obtain ⟨rfl, rfl⟩ := hy; rfl
                      · rename_i hy; rw [hsy] at hy; exact absurd hy (by simp)
                  | none =>
                      rw [hdy] at hsy; simp only [Option.map_none] at hsy
                      split
                      · rename_i v d hy; rw [hsy] at hy; exact absurd hy (by simp)
                      · exact ih hrestmem hcov'

/-! ## Validity of the substituted variable -/

theorem denseAttemptLadder_valid (reg : VarRegistry) (bounds : Std.HashMap VarId Nat) (pos : Bool)
    (l : DenseLinExpr p) (i : VarId) (dd : ℕ)
    (h : denseAttemptLadder pos bounds l = some (i, dd)) (hlv : ∀ t ∈ l.terms, reg.Valid t.1) :
    reg.Valid i := by
  unfold denseAttemptLadder at h
  cases hgs : denseTryLadder pos l.terms with
  | none => rw [hgs] at h; simp at h
  | some gs =>
      rw [hgs] at h; dsimp only at h
      cases hlb : denseLookupBounds bounds gs.2 with
      | none => rw [hlb] at h; simp at h
      | some Bs =>
          rw [hlb] at h; dsimp only at h
          cases hsol : solutions p (tval pos l.const) gs.1 Bs (gs.1 * ladderVal (Bs.map (· - 1))) with
          | nil => rw [hsol] at h; simp at h
          | cons ds dstl =>
              rw [hsol] at h
              cases dstl with
              | cons _ _ => simp at h
              | nil =>
                  dsimp only at h
                  cases hg2 : gs.2 with
                  | nil => rw [hg2] at h; simp at h
                  | cons t gtail =>
                      cases ds with
                      | nil => rw [hg2] at h; simp at h
                      | cons d dtail =>
                          rw [hg2] at h
                          simp only [Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨rfl, rfl⟩ := h
                          exact hlv t
                            (denseTryLadder_mem pos l.terms gs hgs t (hg2 ▸ List.mem_cons_self ..))

theorem denseSolveOperand_valid (reg : VarRegistry) (bounds : Std.HashMap VarId Nat)
    (E : DenseExpr p) (i : VarId) (dd : ℕ) (h : denseSolveOperand bounds E = some (i, dd))
    (hcov : E.CoveredBy reg) : reg.Valid i := by
  unfold denseSolveOperand at h
  cases hdl : denseLinearize E with
  | none => rw [hdl] at h; simp at h
  | some l =>
      rw [hdl] at h; dsimp only at h
      have hlv : ∀ t ∈ l.terms, reg.Valid t.1 :=
        fun t ht => hcov t.1 (denseLinearize_vars E l hdl t.1 (List.mem_map.2 ⟨t, ht, rfl⟩))
      by_cases hlen : l.terms.length < 2
      · rw [if_pos hlen] at h; simp at h
      · rw [if_neg hlen] at h
        cases hat : denseAttemptLadder true bounds l with
        | some r =>
            rw [hat] at h; dsimp only at h; simp only [Option.some.injEq] at h
            subst h
            exact denseAttemptLadder_valid reg bounds true l i dd hat hlv
        | none =>
            rw [hat] at h; dsimp only at h
            exact denseAttemptLadder_valid reg bounds false l i dd h hlv

theorem denseFindFold_valid {bs : BusSemantics p} (facts : BusFacts p bs) (reg : VarRegistry)
    (denseBM : Std.HashMap VarId Nat) :
    ∀ (dpending : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ dpending, denseBICovered reg bi) →
      ∀ i dd, denseFindFold bs facts denseBM dpending = some (i, dd) → reg.Valid i := by
  intro dpending
  induction dpending with
  | nil => intro _ i dd h; simp [denseFindFold] at h
  | cons bi rest ih =>
      intro hcov i dd h
      have hbc : denseBICovered reg bi := hcov bi (List.mem_cons_self ..)
      have hcov' : ∀ b ∈ rest, denseBICovered reg b := fun b hb => hcov b (List.mem_cons_of_mem _ hb)
      unfold denseFindFold at h
      cases hdp : densePairByteOps? bs facts bi with
      | none => rw [hdp] at h; dsimp only at h; exact ih hcov' i dd h
      | some xy =>
          obtain ⟨x, y⟩ := xy
          rw [hdp] at h; dsimp only at h
          obtain ⟨hxc, hyc⟩ := densePairByteOps?_covered hbc hdp
          cases hsx : denseSolveOperand denseBM x with
          | some r =>
              rw [hsx] at h; dsimp only at h; simp only [Option.some.injEq] at h
              subst h
              exact denseSolveOperand_valid reg denseBM x i dd hsx hxc
          | none =>
              rw [hsx] at h; dsimp only at h
              cases hsy : denseSolveOperand denseBM y with
              | some r =>
                  rw [hsy] at h; dsimp only at h; simp only [Option.some.injEq] at h
                  subst h
                  exact denseSolveOperand_valid reg denseBM y i dd hsy hyc
              | none => rw [hsy] at h; dsimp only at h; exact ih hcov' i dd h

/-- The dense transform: substitute one forced digit per invocation (identity if none found). -/
def denseDigitFoldF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if 256 < p then
    match denseFindFold bs facts (denseBuild bs facts d.busInteractions) d.busInteractions with
    | some (i, dd) => d.subst i (DenseExpr.const (dd : ZMod p))
    | none => d
  else d

/-- The dense bounded-payload digit fold pass. Inherits `DigitFold.digitFoldPass`'s `PassCorrect`
    through the decode-commutation of its transform. -/
def denseDigitFoldPass : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := denseDigitFoldF bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := by
      unfold denseDigitFoldF
      by_cases hp : 256 < p
      · rw [if_pos hp]
        cases denseFindFold bs facts (denseBuild bs facts d.busInteractions) d.busInteractions with
        | none => exact hcov
        | some idd =>
            obtain ⟨i, dd⟩ := idd
            exact DenseConstraintSystem.subst_covered hcov (DenseExpr.coveredBy_const reg _)
      · rw [if_neg hp]; exact hcov
    dcovered := by intro x hx; simp at hx
    correct := by
      show PassCorrect (reg.decodeCS d) (reg.decodeCS (denseDigitFoldF bs facts d))
        (reg.decodeDerivs ([] : DenseDerivations p)) bs
      have hout : reg.decodeCS (denseDigitFoldF bs facts d)
          = (DigitFold.digitFoldPass (reg.decodeCS d) bs facts).out := by
        unfold denseDigitFoldF DigitFold.digitFoldPass
        by_cases hp : 256 < p
        · rw [if_pos hp, dif_pos hp]
          haveI : NeZero p := ⟨by omega⟩
          have hbm : ∀ i, reg.Valid i → (denseBuild bs facts d.busInteractions)[i]?
              = (BoundsMap.build facts (cs := reg.decodeCS d) (bs := bs)).map[reg.resolve i]? := by
            intro i hi
            unfold denseBuild BoundsMap.build
            exact denseAddAll_decode facts reg d.busInteractions BoundsMap.empty ∅ hcov.2
              (fun _ h => h) (fun kk _ => by simp [BoundsMap.empty]) i hi
          have hcorr := denseFindFold_decode hp facts (BoundsMap.build facts) reg
            (denseBuild bs facts d.busInteractions) hbm d.busInteractions (fun _ h => h) hcov.2
          cases hff : denseFindFold bs facts (denseBuild bs facts d.busInteractions)
              d.busInteractions with
          | none =>
              rw [hff] at hcorr
              simp only [Option.map_none, Option.map_eq_none_iff] at hcorr
              have hf2 : findFold hp facts (BoundsMap.build facts) (reg.decodeCS d).busInteractions
                  (fun _ h => h) = none := hcorr
              simp only [hf2]
          | some idd =>
              obtain ⟨i, dd⟩ := idd
              rw [hff] at hcorr
              simp only [Option.map_some, Option.map_eq_some_iff] at hcorr
              obtain ⟨f, hf, hfeq⟩ := hcorr
              simp only [Prod.mk.injEq] at hfeq
              obtain ⟨hfv, hfd⟩ := hfeq
              have hiv : reg.Valid i :=
                denseFindFold_valid facts reg _ d.busInteractions hcov.2 i dd hff
              have hf2 : findFold hp facts (BoundsMap.build facts) (reg.decodeCS d).busInteractions
                  (fun _ h => h) = some f := hf
              simp only [hf2]
              rw [reg.decodeCS_subst hiv (DenseExpr.const (dd : ZMod p)) d hcov, hfv, hfd]
              rfl
        · rw [if_neg hp, dif_neg hp]
      rw [show reg.decodeDerivs ([] : DenseDerivations p) = [] from rfl, hout]
      have hderiv : (DigitFold.digitFoldPass (reg.decodeCS d) bs facts).derivs = [] := by
        unfold DigitFold.digitFoldPass
        by_cases hp : 256 < p
        · rw [dif_pos hp]
          haveI : NeZero p := ⟨by omega⟩
          dsimp only
          split <;> rfl
        · rw [dif_neg hp]
      have hc := (DigitFold.digitFoldPass (reg.decodeCS d) bs facts).correct
      rw [hderiv] at hc
      exact hc }

end ApcOptimizer.Dense
