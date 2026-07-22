import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Dense flag unification across duplicate scaled range checks

Data and runtime definitions; the top transform `denseFlagUnifyF` is wrapped directly with
`DenseVerifiedPassW.of` (proof in `FlagUnifyProof.lean`). -/

/-- Two summands below `M` that complete the same integer against multiples of `M` are equal. -/
theorem residue_uniq (M A B w1 w2 : Nat) (h : M * A + w1 = M * B + w2)
    (h1 : w1 < M) (h2 : w2 < M) : w1 = w2 := by
  have e1 : (M * A + w1) % M = w1 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h1
  have e2 : (M * B + w2) % M = w2 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h2
  rw [← e1, h, e2]

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The pair certificate (dense) -/

/-- Pair-level certificate data: everything independent of the target flag pair. `pts` pairs each
    enumerated joint flag point with whether the two offset values coincide there. -/
structure DenseFuData (p : ℕ) where
  rxVars : List VarId
  ryVars : List VarId
  payXVars : List VarId
  pts : List (List (VarId × ZMod p) × Bool)

/-- The pair-level half of the certificate: slot decompositions, fact bounds, no-wrap checks,
    domain cover, and the per-point offset bounds — computed once per matched pair. Reads
    `facts.slotBound` at runtime. -/
def denseFuPairData? (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (DenseExpr p))
    (biX biY : BusInteraction (DenseExpr p)) (x : VarId) : Option (DenseFuData p) :=
  match biX.multiplicity.constValue?, biY.multiplicity.constValue? with
  | some mx, some my =>
    if mx = 0 then none else if my = 0 then none else
    (match biX.payload[0]?, biY.payload[0]? with
     | some OX, some OY =>
       (match facts.slotBound biX.busId mx (biX.payload.map DenseExpr.constValue?) 0,
              facts.slotBound biY.busId my (biY.payload.map DenseExpr.constValue?) 0 with
        | some bX, some bY =>
          (match OX.splitAt x, OY.splitAt x with
           | some (k, RX), some (k2, RY) =>
             let m := k⁻¹
             if k2 = k ∧ k * m = 1 ∧
                 m.val * (bX - 1) + (m.val - 1) < p ∧
                 m.val * (bY - 1) + (m.val - 1) < p then
               let jointVars := (RX.vars ++ RY.vars).eraseDups
               let doms := jointVars.filterMap (fun v =>
                 (denseFindDomainAlg domCs v).map (fun d => (v, d)))
               if doms.map Prod.fst = jointVars ∧
                   (doms.map (fun vd => vd.2.length)).prod ≤ 32 then
                 let pts0 := denseAssignments doms
                 if pts0.all (fun pt =>
                     decide (((-m) * RX.eval (denseEnvOfFast pt)).val < m.val) &&
                     decide (((-m) * RY.eval (denseEnvOfFast pt)).val < m.val)) then
                   some { rxVars := RX.vars, ryVars := RY.vars,
                          payXVars := biX.payload.flatMap DenseExpr.vars,
                          pts := pts0.map (fun pt =>
                            (pt, decide (((-m) * RX.eval (denseEnvOfFast pt)).val
                              = ((-m) * RY.eval (denseEnvOfFast pt)).val))) }
                 else none
               else none
             else none
           | _, _ => none)
        | _, _ => none)
     | _, _ => none)
  | _, _ => none

/-- The per-target half: memberships, disequality, and pointwise flag agreement wherever the
    offsets coincide. -/
def denseFuCheckWith (d : DenseFuData p) (vx vy : VarId) : Bool :=
  decide (vx ∈ d.rxVars) && decide (vy ∈ d.ryVars) && !(decide (vy = vx)) &&
  decide (vx ∈ d.payXVars) &&
  d.pts.all (fun ptb => !ptb.2 || decide (denseEnvOfFast ptb.1 vy = denseEnvOfFast ptb.1 vx))

/-- Decidable certificate that `biX`, `biY` are scaled range checks of the same carrier `x` whose
    offset parts pin `vy` (in `biY`) to `vx` (in `biX`). Not called by `denseFuLoop`; provided for
    the prover's soundness lemmas. -/
def denseFuCheck (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (DenseExpr p))
    (biX biY : BusInteraction (DenseExpr p)) (x vx vy : VarId) : Bool :=
  match denseFuPairData? bs facts domCs biX biY x with
  | some d => denseFuCheckWith d vx vy
  | none => false

/-! ## The scan loop and the pass (dense) -/

/-- A previously seen scaled-check candidate: the interaction, its carrier variable, and the
    matching key `(busId, second-slot constant, k, carrier)`. -/
structure DenseFUSeen (p : ℕ) where
  bi : BusInteraction (DenseExpr p)
  x : VarId
  key : Nat × Option (ZMod p) × ZMod p × VarId

/-- Hash of a `DenseFUSeen` match key for bucketing `seen`. Reads only fields the `key == key'` test
    compares, so equal keys share a bucket (no match hidden); collisions are separated by the exact
    `e.key == xk.2` check in the scan. -/
def denseFuKeyHash (key : Nat × Option (ZMod p) × ZMod p × VarId) : UInt64 :=
  mixHash (hash key.1) (mixHash (hash (key.2.1.map ZMod.val))
    (mixHash (hash key.2.2.1.val) (hash key.2.2.2)))

/-- Prepend seen-entries into their key-hash buckets. `foldr` keeps each bucket in `es ++ seen`
    order, so the bucketed scan returns the identical earliest twin. -/
def denseFuInsertAll (m : Std.HashMap UInt64 (List (DenseFUSeen p)))
    (es : List (DenseFUSeen p)) : Std.HashMap UInt64 (List (DenseFUSeen p)) :=
  es.foldr (fun e acc => acc.insert (denseFuKeyHash e.key) (e :: acc.getD (denseFuKeyHash e.key) []))
    m

/-- Scaled-check candidates of one interaction: carrier variables of the first payload slot with a
    constant-coefficient decomposition and a *nonempty* offset part (raw checks have nothing to
    unify). -/
def denseFuCandidates (bi : BusInteraction (DenseExpr p)) :
    List (VarId × (Nat × Option (ZMod p) × ZMod p × VarId)) :=
  match bi.payload[0]? with
  | none => []
  | some O =>
    O.vars.eraseDups.filterMap (fun x =>
      match O.splitAt x with
      | some (k, R) =>
        if R.vars.isEmpty then none
        else some (x, (bi.busId, (bi.payload[1]?).bind DenseExpr.constValue?, k, x))
      | none => none)

/-- Flag-target combinations for a matched pair: variables of the two offset parts. -/
def denseFuTargets (biX biY : BusInteraction (DenseExpr p)) (x : VarId) :
    List (VarId × VarId) :=
  match biX.payload[0]?, biY.payload[0]? with
  | some OX, some OY =>
    match OX.splitAt x, OY.splitAt x with
    | some (_, RX), some (_, RY) =>
      RY.vars.eraseDups.flatMap (fun vy => RX.vars.eraseDups.map (fun vx => (vy, vx)))
    | _, _ => []
  | _, _ => []

/-- Scan the interactions: for each scaled-check candidate, find an earlier twin with the same key
    and adopt every flag pair the certificate confirms, accumulating into `DenseSolved`. -/
def denseFuLoop (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (DenseExpr p)) :
    List (BusInteraction (DenseExpr p)) → Std.HashMap UInt64 (List (DenseFUSeen p)) →
      DenseSolved p → DenseSolved p
  | [], _, σ => σ
  | c :: rest, seen, σ =>
    let cands := denseFuCandidates c
    match cands.findSome? (fun xk =>
        (seen.getD (denseFuKeyHash xk.2) []).findSome? (fun e =>
          if e.key == xk.2 then some (e, xk.1) else none)) with
    | some ex =>
        -- pair-level work once; per-target checks share it (definitionally `denseFuCheck`)
        match denseFuPairData? bs facts domCs ex.1.bi c ex.2 with
        | none =>
            denseFuLoop bs facts domCs rest
              (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseFUSeen p)))) σ
        | some d =>
        let pairs := (denseFuTargets ex.1.bi c ex.2).filterMap (fun t =>
          if denseFuCheckWith d t.2 t.1
          then some (t.1, DenseExpr.var t.2) else none)
        denseFuLoop bs facts domCs rest
          (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseFUSeen p))))
          (σ.insertAll pairs)
    | none =>
        denseFuLoop bs facts domCs rest
          (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseFUSeen p)))) σ

/-- Flag unification across duplicate scaled range checks. When two checks decompose over the same
    carrier `x` with equal coefficient (`k*x + R`, `k*x + R'`) and their offsets force flag `vy` to
    equal `vx` on the shared finite domain, infers `vy := vx` and substitutes everywhere. Prime `p`
    only; runs after `denseRootPairUnifyF` (carrier limbs already shared) and before dedup. -/
def denseFlagUnifyF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseFuLoop bs facts d.algebraicConstraints d.busInteractions ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

end ApcOptimizer.Dense
