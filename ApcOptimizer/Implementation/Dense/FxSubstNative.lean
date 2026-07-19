import ApcOptimizer.Implementation.Dense.FlagUnifyNative

set_option autoImplicit false

/-! # Dense entailed nonlinear substitution — flagFold part A (Task 3, busUnify cluster,
chunk S4a — impl)

Dense, `VarId`-native transliteration of `OptimizerPasses/FlagFold.lean`'s **part A** runtime
definitions (`indicatorProd`, `buildE`, `fxCheckWith`, `fxCheck`, `fxLoop`, `fxSubstPass`,
~613–978). Parts B/C (`boxTautoDropPass`/`pointwiseDupDropPass`) are already ported
(`Dense/FlagFoldDropsNative.lean`, chunk S3); the composite `flagFoldPass` is superseded by
`flagFoldPass'` elsewhere and is not scheduled, so it is not ported. This file is **impl-only**:
no theorem/lemma from the spec file is ported (`fxCheck_vars`, `fxCheck_sound` are proof-side, the
prover's job), and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the
top-level transform `denseFxSubstF` is shaped exactly like `denseFlagUnifyF`
(`Dense/FlagUnifyNative.lean`) and `denseRootPairUnifyF` (`Dense/RootPairUnifyNative.lean`), so
the prover wraps it directly with `DenseVerifiedPassW.ofNative`.

Notes on how spec pieces map here:

* **`fuPairData?`/`FuData`/`fuCandidates`/`FUSeen`/`fuKeyHash`/`fuInsertAll` are reused wholesale
  from `Dense/FlagUnifyNative.lean`, not re-derived.** `fxLoop`/`fxCheck` share exactly the
  pair-level machinery `fuLoop`/`fuCheck` already built (the spec file itself calls
  `fuPairData?`/`fuCandidates`/`FUSeen`/`fuKeyHash`/`fuInsertAll` directly — this file's scope note
  in the task explicitly flags this reuse); the dense mirrors are `DenseFuData`,
  `denseFuPairData?`, `denseFuCandidates`, `DenseFUSeen`, `denseFuKeyHash`, `denseFuInsertAll`.
* **`envOf`/`denseEnvOfFast` reuse.** `indicatorProd`/`buildE`/`fxCheckWith` all read `envOf pt v`
  over the already-built `FuData`/`DenseFuData` points — `denseEnvOfFast`
  (`Dense/DomainBatch.lean`) is reused unchanged (the S1/S2/S3 precedent), not re-derived.
* **`fxLoop`'s `cs`-threading drops exactly as `fuLoop`'s did.** The spec `fxLoop` threads `cs` and
  a `∀ bi ∈ pending, bi ∈ cs.busInteractions` membership proof solely so `fuPairData?` can be
  handed `cs.algebraicConstraints` as `domCs` and so `Solved.insertAll` can be given its
  `hpairs`/`hpairsV` proof obligations; with those proof-only pieces gone the only genuinely-read
  piece is `cs.algebraicConstraints` itself, so `denseFxLoop` threads it explicitly as a plain
  `domCs` parameter — precisely `denseFuLoop`'s shape (`Dense/FlagUnifyNative.lean`), reusing its
  candidate/seen machinery (`denseFuCandidates`/`DenseFUSeen`/`denseFuInsertAll`/`denseFuKeyHash`)
  rather than re-deriving it, per the task's explicit instruction.
* **`fxCheck` is proof-side-only in the reference runtime path** (only `fxCheck_vars`/
  `fxCheck_sound` call it; `fxLoop`/`fxSubstPass` never do — the loop calls `fxCheckWith` directly
  on the once-built `FuData`, exactly like `fuCheck`/`fuCheckWith` in the sibling pass). It is
  transliterated anyway (`denseFxCheck`) per the assigned scope, purely so the prover has a
  ready-made dense mirror to restate its own certificate-extraction/soundness lemmas against,
  mirroring `fxCheck`'s exact shape and check order. It consumes `facts.slotBound` at RUNTIME
  (through `denseFuPairData?`), so the `facts` parameter is kept — the established precedent
  (`denseFuCheck`, `denseScaledSlotBound`).
* **Proof-witness drops.** Every spec `dif`/named `match hdata : …` that exists only to bind a
  certificate for a later proof term (`fxLoop`'s named `hdata` match, `fxSubstPass`'s
  `haveI : Fact p.Prime := ⟨pw.correct hpB⟩`, its `PassCorrect` terms, `fxLoop`'s `hpairs`/
  `hpairsV` arguments to `Solved.insertAll`) is dropped; every decidable condition that gates
  *behavior* (the `pw.isPrime = true` primality gate, `fxCheckWith`'s per-target checks) is kept
  as a plain `if`/`Bool` computation with identical control flow — the M1/S1/S2/S3 precedent.
  Neither `fxCheckWith` nor `fxCheck` needs `[Fact p.Prime]` to *compute* (only the soundness
  theorem `fxCheck_sound` does), so the dense mirrors drop the instance argument entirely, not
  just its construction. `Solved.insertAll` in `denseFxLoop` becomes `DenseSolved.insertAll`,
  which takes the pair list directly with no soundness/vars proof arguments
  (`Dense/Gauss.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part A: the entailed nonlinear substitution (dense) -/

/-- Boolean indicator product `∏ (v or 1−v)` selecting one point of the box. Heuristic data — the
    certificate validates its values pointwise, so the construction carries no proof. Mirrors
    `indicatorProd`, reusing `denseEnvOfFast` (`Dense/DomainBatch.lean`). -/
def denseIndicatorProd (others : List VarId) (pt : List (VarId × ZMod p)) : DenseExpr p :=
  others.foldl (fun acc v =>
    if denseEnvOfFast pt v = 1 then DenseExpr.mul acc (DenseExpr.var v)
    else DenseExpr.mul acc (DenseExpr.add (DenseExpr.const 1)
      (DenseExpr.mul (DenseExpr.const (-1)) (DenseExpr.var v)))) (DenseExpr.const 1)

/-- Interpolate the target's value over the survivor-side flags from the compatible points.
    Mirrors `buildE`. -/
def denseBuildE (d : DenseFuData p) (vy : VarId) : DenseExpr p :=
  let others := d.rxVars.eraseDups.filter (fun v => v != vy)
  d.pts.foldl (fun acc ptb =>
    if ptb.2 && (denseEnvOfFast ptb.1 vy == 1) then
      DenseExpr.add acc (denseIndicatorProd others ptb.1)
    else acc) (DenseExpr.const 0)

/-- Per-target certificate: `vy` is a Y-side flag, the candidate solution `E` mentions neither
    `vy` nor anything outside the survivor's payload, and at every offset-compatible point the
    target equals `E`. Mirrors `fxCheckWith`, reusing `DenseExpr.mentions`
    (`Dense/SubstMap.lean`). -/
def denseFxCheckWith (d : DenseFuData p) (E : DenseExpr p) (vy : VarId) : Bool :=
  decide (vy ∈ d.ryVars) && !(E.mentions vy) &&
  decide (E.vars.all (fun v => v ∈ d.rxVars ∨ v ∈ d.ryVars)) &&
  decide (E.vars.all (fun v => v ∈ d.payXVars)) &&
  d.pts.all (fun ptb => !ptb.2 || decide (denseEnvOfFast ptb.1 vy = E.eval (denseEnvOfFast ptb.1)))

/-- The full certificate, defined through the shared pair data (as `denseFuCheck`). Mirrors
    `fxCheck`, reusing `denseFuPairData?` (`Dense/FlagUnifyNative.lean`); consumes
    `facts.slotBound` at RUNTIME (through `denseFuPairData?`), same as the spec. -/
def denseFxCheck (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (DenseExpr p))
    (biX biY : BusInteraction (DenseExpr p)) (x : VarId) (E : DenseExpr p)
    (vy : VarId) : Bool :=
  match denseFuPairData? bs facts domCs biX biY x with
  | some d => denseFxCheckWith d E vy
  | none => false

/-! ## The scan loop and the substitution pass (dense) -/

/-- Scan for matched scaled-check pairs (reusing `denseFuCandidates`/`DenseFUSeen`, per the task's
    explicit instruction) and adopt every certified interpolation `vy := E`. Mirrors `fxLoop`,
    threading `domCs` explicitly in place of the spec's `cs`-scoped field access (see the module
    header) and `DenseSolved` in place of the proof-carrying `Solved` — exactly `denseFuLoop`'s
    shape (`Dense/FlagUnifyNative.lean`). -/
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
        -- pair-level work once per match; per-target checks share it (definitionally the same
        -- value as `denseFxCheck` — see its definition)
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

/-- Part A's runtime transform: substitute every certified interpolation. Prime `p` only
    (re-checked at runtime); identity otherwise. Mirrors `fxSubstPass`'s computed output (dropping
    its `PassCorrect` term); shaped as `(pw) → (bs) → (facts) → (d) → out`, matching
    `denseFlagUnifyF`/`denseRootPairUnifyF`'s shape exactly for `DenseVerifiedPassW.ofNative`. -/
def denseFxSubstF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseFxLoop bs facts d.algebraicConstraints d.busInteractions ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

end ApcOptimizer.Dense
