import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp

set_option autoImplicit false

/-! # Dense bounded-payload digit fold (runtime). Bounds map `denseBuild` proved sound in
`DigitFoldProof.lean`. -/

/-! ## ℕ-side ladder arithmetic and solution grid (representation-independent) -/

namespace DigitFold

/-! ### ℕ-side ladder arithmetic -/

/-- Little-endian base-256 positional value of a digit list. -/
def ladderVal : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 256 * ladderVal xs

/-- Decode `T` as `Bs.length` base-256 digits (little-endian) with exclusive digit bounds `Bs`,
    requiring the final quotient to vanish; `none` if any digit breaches its bound. -/
def unpack? : List ℕ → ℕ → Option (List ℕ)
  | [], T => if T = 0 then some [] else none
  | B :: Bs, T =>
    if T % 256 < B then (unpack? Bs (T / 256)).map (T % 256 :: ·) else none

/-- Decoding is a retraction of the positional value on bounded digit lists. -/
theorem unpack?_ladderVal : ∀ (xs Bs : List ℕ), List.Forall₂ (· < ·) xs Bs →
    (∀ B ∈ Bs, B ≤ 256) → unpack? Bs (ladderVal xs) = some xs := by
  intro xs Bs h
  induction h with
  | nil => intro _; rfl
  | @cons x B xs Bs hxB _ ih =>
    intro hB
    have hx256 : x < 256 := lt_of_lt_of_le hxB (hB B (by simp))
    have hmod : (x + 256 * ladderVal xs) % 256 = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx256]
    have hdiv : (x + 256 * ladderVal xs) / 256 = ladderVal xs := by
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256), Nat.div_eq_of_lt hx256, Nat.zero_add]
    simp only [ladderVal, unpack?, hmod, hdiv, if_pos hxB,
      ih (fun B hBmem => hB B (by simp [hBmem]))]
    rfl

/-- Positional value is monotone into the bound box. -/
theorem ladderVal_le_box : ∀ (xs Bs : List ℕ), List.Forall₂ (· < ·) xs Bs →
    ladderVal xs ≤ ladderVal (Bs.map (· - 1)) := by
  intro xs Bs h
  induction h with
  | nil => exact le_refl _
  | @cons x B xs Bs hxB _ ih =>
    simp only [ladderVal, List.map_cons]
    have hx : x ≤ B - 1 := Nat.le_sub_one_of_lt hxB
    exact Nat.add_le_add hx (Nat.mul_le_mul_left _ ih)

/-! ### The (byte, wrap) solution grid -/

/-- All digit vectors compatible with "the checked value is a byte": for each byte `b` and wrap
    count `m`, decode `tval b + m·p` as a `g`-scaled bounded ladder (`tval b` = the ℕ-residue the
    ladder sum must have when the byte reads `b`). -/
def solutions (p : ℕ) (tval : ℕ → ℕ) (g : ℕ) (Bs : List ℕ) (maxM : ℕ) : List (List ℕ) :=
  (List.range 256).flatMap fun b =>
    (List.range (maxM / p + 1)).filterMap fun m =>
      let M := tval b + m * p
      if M % g = 0 ∧ M ≤ maxM then unpack? Bs (M / g) else none

/-- Completeness of the grid: the digit vector of any assignment whose ladder sum `g·ladderVal xs`
    has residue `tval b` (for its byte value `b < 256`) and fits under `maxM` is enumerated. -/
theorem solutions_complete (p : ℕ) (tval : ℕ → ℕ) (g : ℕ) (Bs : List ℕ) (maxM : ℕ)
    (_hp : 0 < p) (hg : 0 < g)
    (xs : List ℕ) (hxB : List.Forall₂ (· < ·) xs Bs) (hB : ∀ B ∈ Bs, B ≤ 256)
    (b : ℕ) (hb : b < 256)
    (hmod : (g * ladderVal xs) % p = tval b) (hle : g * ladderVal xs ≤ maxM) :
    xs ∈ solutions p tval g Bs maxM := by
  set S := g * ladderVal xs with hS
  have hSsplit : tval b + S / p * p = S := by
    rw [← hmod, Nat.mod_add_div' S p]
  have hm : S / p < maxM / p + 1 :=
    Nat.lt_succ_of_le (Nat.div_le_div_right hle)
  refine List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, ?_⟩
  refine List.mem_filterMap.2 ⟨S / p, List.mem_range.2 hm, ?_⟩
  have hMg : S % g = 0 := by
    rw [hS]; exact Nat.mul_mod_right g _
  have hMdiv : S / g = ladderVal xs := by
    rw [hS]; exact Nat.mul_div_cancel_left _ hg
  rw [hSsplit, if_pos ⟨hMg, hle⟩, hMdiv]
  exact unpack?_ladderVal xs Bs hxB hB

/-- The payoff: a singleton grid forces the digit vector. -/
theorem solutions_forced (p : ℕ) (tval : ℕ → ℕ) (g : ℕ) (Bs : List ℕ) (maxM : ℕ)
    (hp : 0 < p) (hg : 0 < g) (ds : List ℕ)
    (hsol : solutions p tval g Bs maxM = [ds])
    (xs : List ℕ) (hxB : List.Forall₂ (· < ·) xs Bs) (hB : ∀ B ∈ Bs, B ≤ 256)
    (b : ℕ) (hb : b < 256)
    (hmod : (g * ladderVal xs) % p = tval b) (hle : g * ladderVal xs ≤ maxM) :
    xs = ds := by
  have := solutions_complete p tval g Bs maxM hp hg xs hxB hB b hb hmod hle
  rw [hsol, List.mem_singleton] at this
  exact this

variable {p : ℕ}

/-! ### Ladder recognition on linear forms (representation-independent coefficient layer) -/

/-- The ℕ-coefficient of a term under a sign interpretation: `c.val` when the ladder is added to
    the constant, `(-c).val` when it is subtracted. -/
def coeffNat (pos : Bool) (c : ZMod p) : ℕ := if pos then c.val else (-c).val

/-- The ladder's sign as a field element. -/
def signum (pos : Bool) : ZMod p := if pos then 1 else -1

@[simp] theorem signum_true : (signum true : ZMod p) = 1 := rfl
@[simp] theorem signum_false : (signum false : ZMod p) = -1 := rfl

/-- The ℕ-residue the ladder sum must have when the byte-checked value reads `b`. -/
def tval (pos : Bool) (K : ZMod p) (b : ℕ) : ℕ :=
  (if pos then (b : ZMod p) - K else K - (b : ZMod p)).val

end DigitFold

namespace ApcOptimizer.Dense

open DigitFold

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

/-! ## Dense bounds map (`Std.HashMap VarId Nat`); soundness in `DigitFoldProof.lean`. -/

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

/-- Digit-fold transform: when a witness limb is forced to a compile-time constant by a byte check
    over a base-256 ladder (e.g. a limb pinned to `7`), substitute it away. One forced digit per
    invocation; identity if none found. -/
def denseDigitFoldF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if 256 < p then
    match denseFindFold bs facts (denseBuild bs facts d.busInteractions) d.busInteractions with
    | some (i, dd) => d.subst i (DenseExpr.const (dd : ZMod p))
    | none => d
  else d

end ApcOptimizer.Dense
