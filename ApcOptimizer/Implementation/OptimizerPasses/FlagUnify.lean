import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Dense flag unification across duplicate scaled range checks (Task 3, busUnify cluster,
chunk S2 — impl)

Dense, `VarId`-native transliteration of `OptimizerPasses/FlagUnify.lean`'s **runtime**
definitions (`FuData`, `fuPairData?`, `fuCheckWith`, `fuCheck`, `FUSeen`, `fuKeyHash`,
`fuInsertAll`, `fuCandidates`, `fuTargets`, `fuLoop`, `flagUnifyPass`). This file is **impl-only**:
no theorem/lemma from the spec file is ported, and no `DenseVerifiedPassW`/`DensePassCorrect`
wrapper is built here — the top-level transform `denseFlagUnifyF` is shaped exactly like
`denseRootPairUnifyF` (`Dense/RootPairUnifyNative.lean`), so the prover wraps it directly with
`DenseVerifiedPassW.ofNative`.

Notes on how spec pieces map here (mirroring the `RootPairUnifyNative` chunk S1 precedent):

* **`Expression.splitAt` reuse.** Already ported as `DenseExpr.splitAt` in
  `Dense/RootPairUnifyNative.lean` (chunk S1) — reused unchanged here, not re-derived, per that
  file's own header instruction.
* **`findDomainAlg`/`assignments`/`envOf` reuse.** These are owned by `OptimizerPasses/DomainProp.lean`,
  not `FlagUnify.lean`. Already ported: `denseFindDomainAlg` (`Dense/DomainFold.lean`) and
  `denseAssignments` (`Dense/DomainFold.lean`) / `denseEnvOfFast` (`Dense/DomainBatch.lean` —
  structurally identical recursions to `assignments`/`envOf` once there is no name/`powdrId?` split
  to fast-path around, reused as-is). `facts.slotBound` is read directly at runtime (unchanged
  `BusFacts`, values-only signature — no `Expression`/`DenseExpr` type parameter to port).
* **`FuData`'s fields are data-only** (`List Variable`/`List (Variable × ZMod p) × Bool` become
  `List VarId`/`List (VarId × ZMod p) × Bool`) — a plain 4-field struct, no proof, direct port.
* **`FUSeen`'s `cs`-scoping is dropped, not just its `mem` proof.** The spec struct is parametrized
  by `cs : ConstraintSystem p` solely so `mem : bi ∈ cs.busInteractions` typechecks; with `mem`
  dropped there is nothing left needing `cs` (the `RootPairUnify`/`DenseRPSeen` precedent). `bi`
  itself is genuinely read (`fuLoop` calls `fuPairData? … ex.1.bi c ex.2` on the matched seen-entry's
  interaction), so it stays a plain field, unlike `mem`.
* **`fuLoop`'s `cs`-threading.** The spec `fuLoop` threads `cs`/a membership proof solely so
  `fuPairData?` can be handed `cs.algebraicConstraints` as `domCs`; with the proof gone, the only
  genuinely-read piece is `cs.algebraicConstraints` itself, so `denseFuLoop` threads it explicitly as
  a plain `domCs` parameter (the `denseRpLoop`-threads-`bis`/`domCs` precedent). Unlike
  `rpCheckPair`/`denseRpCheckPair`, `fuPairData?`/`denseFuPairData?` never consult the interaction
  list itself (`biX`/`biY` are handed in directly, not looked up), so no `bis` parameter is needed
  here.
* **`fuCheck` is proof-side-only in the reference runtime path** (only `fuCheck_vars`/`fuCheck_sound`
  call it; `fuLoop`/`flagUnifyPass` never do — the loop calls `fuCheckWith` directly on the once-built
  `FuData`). It is transliterated anyway (`denseFuCheck`) per the assigned scope, purely so the
  prover has a ready-made dense mirror to restate its own certificate-extraction/soundness lemmas
  against, mirroring `fuCheck`'s exact shape and check order.
* **Proof-witness drops.** Every spec `dif`/named `match hdata : …` that exists only to bind a
  certificate for a later proof term (`fuLoop`'s named `hdata` match, `flagUnifyPass`'s
  `haveI : Fact p.Prime := ⟨pw.correct hpB⟩`, its `PassCorrect` terms, `fuLoop`'s `hpairs`/`hpairsV`
  arguments to `Solved.insertAll`) is dropped; every decidable condition that gates *behavior* (the
  `pw.isPrime = true` primality gate, the `mx = 0`/`my = 0` degenerate-multiplicity checks,
  `fuPairData?`'s whole certificate, `fuCheckWith`'s per-target checks) is kept as a plain `if`/`Bool`
  computation with identical control flow — the M1/S1 precedent. Neither `fuPairData?` nor
  `fuCheckWith`/`fuCheck` needs `[Fact p.Prime]` to *compute* (only the soundness theorem
  `fuCheck_sound` does — `ZMod p`'s `Inv` is total for every `p`), so the dense mirrors drop the
  instance argument entirely, not just its construction. `Solved.insertAll` in `denseFuLoop` becomes
  `DenseSolved.insertAll`, which takes the pair list directly with no soundness/vars proof arguments
  (`Dense/Gauss.lean`). -/

/-- Two summands below `M` that complete the same integer against multiples of `M` are equal.

    Representation-independent (`Nat`-only) arithmetic lemma, re-homed here from
    `OldVariableBased/FlagUnify.lean` so the dense proof tree (`FlagUnifyProof.lean`) can consume it
    without importing the reference pass; the reference pass imports it back. -/
theorem residue_uniq (M A B w1 w2 : Nat) (h : M * A + w1 = M * B + w2)
    (h1 : w1 < M) (h2 : w2 < M) : w1 = w2 := by
  have e1 : (M * A + w1) % M = w1 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h1
  have e2 : (M * B + w2) % M = w2 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h2
  rw [← e1, h, e2]

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The pair certificate (dense) -/

/-- Pair-level certificate data: everything independent of the target flag pair. `pts` pairs each
    enumerated joint flag point with whether the two offset values coincide there. Data-only mirror
    of `FuData`. -/
structure DenseFuData (p : ℕ) where
  rxVars : List VarId
  ryVars : List VarId
  payXVars : List VarId
  pts : List (List (VarId × ZMod p) × Bool)

/-- The pair-level half of the certificate: slot decompositions, fact bounds, no-wrap checks,
    domain cover, and the per-point offset bounds — computed **once per matched pair**. Mirrors
    `fuPairData?`, reusing `DenseExpr.splitAt` (`Dense/RootPairUnifyNative.lean`),
    `denseFindDomainAlg`/`denseAssignments` (`Dense/DomainFold.lean`) and `denseEnvOfFast`
    (`Dense/DomainBatch.lean`) unchanged. Consumes `facts.slotBound` at RUNTIME, same as the spec. -/
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
    offsets coincide. Mirrors `fuCheckWith`. -/
def denseFuCheckWith (d : DenseFuData p) (vx vy : VarId) : Bool :=
  decide (vx ∈ d.rxVars) && decide (vy ∈ d.ryVars) && !(decide (vy = vx)) &&
  decide (vx ∈ d.payXVars) &&
  d.pts.all (fun ptb => !ptb.2 || decide (denseEnvOfFast ptb.1 vy = denseEnvOfFast ptb.1 vx))

/-- Decidable certificate that interactions `biX`, `biY` are scaled range checks of the same carrier
    `x` whose offset parts pin `vy` (in `biY`'s flags) to `vx` (in `biX`'s flags). Mirrors `fuCheck`
    — proof-side-only in the reference runtime path (see the module header), transliterated for the
    prover's own certificate-extraction/soundness lemmas. -/
def denseFuCheck (bs : BusSemantics p) (facts : BusFacts p bs) (domCs : List (DenseExpr p))
    (biX biY : BusInteraction (DenseExpr p)) (x vx vy : VarId) : Bool :=
  match denseFuPairData? bs facts domCs biX biY x with
  | some d => denseFuCheckWith d vx vy
  | none => false

/-! ## The scan loop and the pass (dense) -/

/-- A previously seen scaled-check candidate: the interaction, its carrier variable, and the
    matching key `(busId, second-slot constant, k, carrier)`. Data-only mirror of `FUSeen`, dropping
    the `mem : bi ∈ cs.busInteractions` proof field — with it gone there is no remaining reason to
    parametrize the struct by `cs` either (see the module header). `bi` itself is genuinely read (by
    `denseFuLoop`'s matched-entry lookup into `denseFuPairData?`), unlike `mem`, so it stays a plain
    field. -/
structure DenseFUSeen (p : ℕ) where
  bi : BusInteraction (DenseExpr p)
  x : VarId
  key : Nat × Option (ZMod p) × ZMod p × VarId

/-- Hash of a `DenseFUSeen` match key, used to bucket the `seen` accumulator of `denseFuLoop`. It
    reads only fields the `key == key'` test compares, so equal keys share a bucket (a match is never
    hidden); unequal keys that collide are separated by the retained exact `e.key == xk.2` check
    inside the scan. Mirrors `fuKeyHash`. -/
def denseFuKeyHash (key : Nat × Option (ZMod p) × ZMod p × VarId) : UInt64 :=
  mixHash (hash key.1) (mixHash (hash (key.2.1.map ZMod.val))
    (mixHash (hash key.2.2.1.val) (hash key.2.2.2)))

/-- Prepend seen-entries into their key-hash buckets. `foldr` keeps each bucket in the same order as
    the old flat `es ++ seen` list, so the bucketed scan returns the identical earliest twin — output
    unchanged, per-candidate scan now over one bucket instead of the whole history. Mirrors
    `fuInsertAll`. -/
def denseFuInsertAll (m : Std.HashMap UInt64 (List (DenseFUSeen p)))
    (es : List (DenseFUSeen p)) : Std.HashMap UInt64 (List (DenseFUSeen p)) :=
  es.foldr (fun e acc => acc.insert (denseFuKeyHash e.key) (e :: acc.getD (denseFuKeyHash e.key) []))
    m

/-- Scaled-check candidates of one interaction: carrier variables of the first payload slot with a
    constant-coefficient decomposition and a *nonempty* offset part (raw checks have nothing to
    unify). Mirrors `fuCandidates`. -/
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

/-- Flag-target combinations for a matched pair: variables of the two offset parts. Mirrors
    `fuTargets`. -/
def denseFuTargets (biX biY : BusInteraction (DenseExpr p)) (x : VarId) :
    List (VarId × VarId) :=
  match biX.payload[0]?, biY.payload[0]? with
  | some OX, some OY =>
    match OX.splitAt x, OY.splitAt x with
    | some (_, RX), some (_, RY) =>
      RY.vars.eraseDups.flatMap (fun vy => RX.vars.eraseDups.map (fun vx => (vy, vx)))
    | _, _ => []
  | _, _ => []

/-- Scan the interactions: for each scaled-check candidate, look for an earlier twin with the same
    key and adopt every flag pair the certificate confirms. Mirrors `fuLoop`, threading `domCs`
    explicitly in place of the spec's `cs`-scoped field access (see the module header) and
    `DenseSolved` in place of the proof-carrying `Solved`. -/
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
        -- pair-level work once per match; per-target checks share it (definitionally the same
        -- value as `denseFuCheck` — see its definition)
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

/-- Flag unification across duplicate scaled range checks' runtime transform. Prime `p` only
    (re-checked at runtime); identity otherwise. One sweep; the cleanup fixpoint iterates the pass.
    Runs after `denseRootPairUnifyF` — the carrier limbs must already be shared — and before dedup,
    which collects the checks this pass makes syntactically identical. Mirrors `flagUnifyPass`'s
    computed output (dropping its `PassCorrect` term); shaped as `(pw) → (bs) → (facts) → (d) → out`,
    matching `denseRootPairUnifyF`'s shape exactly for `DenseVerifiedPassW.ofNative`. -/
def denseFlagUnifyF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseFuLoop bs facts d.algebraicConstraints d.busInteractions ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

end ApcOptimizer.Dense
