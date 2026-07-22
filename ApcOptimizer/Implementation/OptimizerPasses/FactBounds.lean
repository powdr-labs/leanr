import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp

set_option autoImplicit false

/-! # Dense fact-derived variable bounds (runtime)

The shared bounds map `denseBuild : bus interactions -> HashMap VarId Nat` ("`denv i < b` on any
non-violating assignment"), fed by declared and probed slot bounds; soundness in
`Proofs/FactBounds.lean`. Consumed by the domain, interval, unification, and cancellation passes. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Per-interaction bound machinery -/

def denseIsVarOf (i : VarId) : DenseExpr p → Bool
  | .var j => j = i
  | _ => false

/-- The first payload slot index literally `.var i`. -/
def denseVarSlot (i : VarId) : List (DenseExpr p) → Option Nat
  | [] => none
  | e :: rest => if denseIsVarOf i e then some 0 else (denseVarSlot i rest).map (· + 1)

/-- One value bound for `i` from a constant-nonzero-multiplicity interaction carrying `.var i`
    in a fact-bounded raw payload slot. -/
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

/-- Probe payload: constant slots at their constants, slot `i` at the candidate, others `0`. -/
def denseProbeBase (payload : List (DenseExpr p)) (i : Nat) (v : ZMod p) : List (ZMod p) :=
  (payload.map (fun e => (DenseExpr.constValue? e).getD 0)).set i v

/-- A probed value bound for `i`. -/
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

/-! ## Dense bounds map (`Std.HashMap VarId Nat`); soundness in `Proofs/FactBounds.lean`. -/

/-- Keep the smaller of two bounds for `i`. -/
def denseInsertEntry (T : Std.HashMap VarId Nat) (i : VarId) (b : Nat) : Std.HashMap VarId Nat :=
  let keep : Bool := match T[i]? with
    | some b0 => decide (b < b0)
    | none => true
  if keep then T.insert i b else T

/-- The raw-variable payload entries. -/
def denseRawVarsOf (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.payload.filterMap (fun e => match e with | .var i => some i | _ => none)

/-- The probed-bound candidate `(VarId, slot)` pairs. -/
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

/-- For candidate `(y, j)`s matching `i`, insert the probed bound. -/
def denseGoCands (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (i : VarId) : List (VarId × Nat) → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | (y, j) :: cl, T =>
    if y = i then
      match denseProbedSlotBoundAt bs facts bi i j with
      | some b => denseGoCands bs facts bi i cl (denseInsertEntry T i b)
      | none => denseGoCands bs facts bi i cl T
    else denseGoCands bs facts bi i cl T

/-- For each raw variable `i`, insert its interaction bound then its probed bounds. -/
def denseAddVars (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (cands : List (VarId × Nat)) :
    List VarId → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | i :: xs, T =>
    let T1 := match denseInteractionBound bs facts bi i with
      | some b => denseInsertEntry T i b
      | none => T
    denseAddVars bs facts bi cands xs (denseGoCands bs facts bi i cands T1)

/-- Collect bounds from every interaction's fact-bounded raw payload slots. -/
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

end ApcOptimizer.Dense
