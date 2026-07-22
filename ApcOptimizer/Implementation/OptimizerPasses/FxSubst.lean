import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify

set_option autoImplicit false

/-! # Dense entailed nonlinear substitution — `flagFold` part A.
Impl-only (correctness in `Proofs/FxSubst.lean`); shares `flagUnify`'s pair-level machinery
(`DenseFuData`/`denseFuPairData?`/`DenseFUSeen`/`denseFuCandidates`) wholesale. Assembled with the
other `flagFold` sub-passes in `FlagFold.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part A: the entailed nonlinear substitution (dense) -/

/-- Boolean indicator product `∏ (v or 1−v)` selecting one point of the box. Heuristic data —
    the certificate validates its values pointwise, so the construction carries no proof. -/
def denseIndicatorProd (others : List VarId) (pt : List (VarId × ZMod p)) : DenseExpr p :=
  others.foldl (fun acc v =>
    if denseEnvOfFast pt v = 1 then DenseExpr.mul acc (DenseExpr.var v)
    else DenseExpr.mul acc (DenseExpr.add (DenseExpr.const 1)
      (DenseExpr.mul (DenseExpr.const (-1)) (DenseExpr.var v)))) (DenseExpr.const 1)

/-- Interpolate the target's value over the survivor-side flags from the compatible points. -/
def denseBuildE (d : DenseFuData p) (vy : VarId) : DenseExpr p :=
  let others := d.rxVars.eraseDups.filter (fun v => v != vy)
  d.pts.foldl (fun acc ptb =>
    if ptb.2 && (denseEnvOfFast ptb.1 vy == 1) then
      DenseExpr.add acc (denseIndicatorProd others ptb.1)
    else acc) (DenseExpr.const 0)

/-- Per-target certificate: `vy` is a Y-side flag, the candidate solution `E` mentions neither
    `vy` nor anything outside the survivor's payload, and at every offset-compatible point the
    target equals `E`. -/
def denseFxCheckWith (d : DenseFuData p) (E : DenseExpr p) (vy : VarId) : Bool :=
  decide (vy ∈ d.ryVars) && !(E.mentions vy) &&
  decide (E.vars.all (fun v => v ∈ d.rxVars ∨ v ∈ d.ryVars)) &&
  decide (E.vars.all (fun v => v ∈ d.payXVars)) &&
  d.pts.all (fun ptb => !ptb.2 || decide (denseEnvOfFast ptb.1 vy = E.eval (denseEnvOfFast ptb.1)))

/-- The full certificate, defined through the shared pair data `denseFuPairData?`. -/
def denseFxCheck (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (DenseExpr p))
    (biX biY : BusInteraction (DenseExpr p)) (x : VarId) (E : DenseExpr p)
    (vy : VarId) : Bool :=
  match denseFuPairData? bs facts domCs biX biY x with
  | some d => denseFxCheckWith d E vy
  | none => false

/-! ## The scan loop and the substitution pass (dense) -/

/-- Scan for matched scaled-check pairs and adopt every certified interpolation `vy := E`. -/
def denseFxLoop (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (DenseExpr p)) :
    List (BusInteraction (DenseExpr p)) → Std.HashMap UInt64 (List (DenseFUSeen p)) →
      DenseSolved p → DenseSolved p
  | [], _, σ => σ
  | c :: rest, seen, σ =>
    let cands := denseFuCandidates c
    match cands.findSome? (fun xk =>
        (seen.getD (denseFuKeyHash xk.2) []).findSome? (fun e =>
          if e.key == xk.2 then some (e, xk.1) else none)) with
    | some ex =>
        -- pair-level work once per match; per-target checks share it (see `denseFxCheck`)
        match denseFuPairData? bs facts domCs ex.1.bi c ex.2 with
        | none =>
            denseFxLoop bs facts domCs rest
              (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseFUSeen p)))) σ
        | some d =>
        let pairs := (d.ryVars.eraseDups.filter (fun v => !(v ∈ d.rxVars))).filterMap (fun vy =>
          if denseFxCheckWith d (denseBuildE d vy) vy
          then some (vy, denseBuildE d vy) else none)
        denseFxLoop bs facts domCs rest
          (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseFUSeen p))))
          (σ.insertAll pairs)
    | none =>
        denseFxLoop bs facts domCs rest
          (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseFUSeen p)))) σ

/-- Entailed nonlinear substitution. When two bus interactions match up to a scaled range check,
    a survivor-side flag `vy` is often pinned to an interpolation `E` over the other flags (e.g.
    `vy := f * g`); this certifies each such `vy := E` and substitutes it everywhere. Prime `p`
    only (re-checked at runtime); identity otherwise. -/
def denseFxSubstF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseFxLoop bs facts d.algebraicConstraints d.busInteractions ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

end ApcOptimizer.Dense
