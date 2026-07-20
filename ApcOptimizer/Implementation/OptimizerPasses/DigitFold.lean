import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
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

/-! ## Dense byte-pair recognizer -/

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

/-! ## Dense ladder recognition and grid solving -/

/-- Dense ladder-shape check (coefficient-only, so `VarId`-agnostic). -/
def denseIsLadder (pos : Bool) : ℕ → List (VarId × ZMod p) → Bool
  | _, [] => true
  | n, (_, c) :: rest => coeffNat pos c == n && denseIsLadder pos (256 * n) rest

/-- Dense ladder recognition: sort by sign-interpreted coefficient, check the shape. -/
def denseTryLadder (pos : Bool) (terms : List (VarId × ZMod p)) :
    Option (ℕ × List (VarId × ZMod p)) :=
  match terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2) with
  | [] => none
  | t :: rest =>
    if 0 < coeffNat pos t.2 ∧ denseIsLadder pos (coeffNat pos t.2) (t :: rest) = true
    then some (coeffNat pos t.2, t :: rest) else none

/-- Dense fact-bound lookup for a ladder's variables, in order. -/
def denseLookupBounds (bounds : Std.HashMap VarId Nat) :
    List (VarId × ZMod p) → Option (List ℕ)
  | [] => some []
  | (v, _) :: rest =>
    match bounds[v]? with
    | some B => if B ≤ 256 then (denseLookupBounds bounds rest).map (B :: ·) else none
    | none => none

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

/-! ## Dense scan for a forced digit and the pass -/

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

/-- The dense transform: substitute one forced digit per invocation (identity if none found). -/
def denseDigitFoldF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if 256 < p then
    match denseFindFold bs facts (denseBuild bs facts d.busInteractions) d.busInteractions with
    | some (i, dd) => d.subst i (DenseExpr.const (dd : ZMod p))
    | none => d
  else d

end ApcOptimizer.Dense
