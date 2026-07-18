import ApcOptimizer.Implementation.Dense.AddrDiseq
import ApcOptimizer.Implementation.Dense.DomainFold

set_option autoImplicit false

/-! # Dense two-root decomposition unification (Task 3, busUnify cluster, chunk S1 — impl)

Dense, `VarId`-native transliteration of `OptimizerPasses/RootPairUnify.lean`'s **runtime**
definitions (`twoRootVarsOk`, `Expression.splitAt`, `scaledSlotBound`, `anyVarBound`, `rpCheckPair`,
`RPSeen`, `rpCandidates`, `rpKeyHash`, `rpInsertAll`, `rpLoop`, `rootPairUnifyPass`). This file is
**impl-only**: no theorem/lemma from the spec file is ported, and no `DenseVerifiedPassW`/
`DensePassCorrect` wrapper is built here — the top-level transform `denseRootPairUnifyF` is shaped
exactly like `denseBusUnifyF` (`Dense/BusUnifyNative.lean`), so the prover wraps it directly with
`DenseVerifiedPassW.ofNative`.

Notes on how spec pieces map here:

* **`twoRootOf?` reuse.** Already ported as `denseTwoRootOf?` in `Dense/AddrDiseq.lean` (chunk M1);
  reused unchanged here, not re-derived.
* **`Expression.splitAt` is a NEW shared dense helper**, placed in *this* file — mirroring where
  the spec `Expression.splitAt` itself lives (`RootPairUnify.lean`, not a generic expr-ops file).
  `flagUnify`/`flagFold` (later chunks of this cluster) should import `Dense.RootPairUnifyNative`
  and reuse `DenseExpr.splitAt` directly, not re-derive it.
* **`findDomainAlg`/`findVarBound`/`assignments`/`envOf` companions.** These are owned by
  `OptimizerPasses/DomainProp.lean`, not `RootPairUnify.lean`. `findDomainAlg` and `assignments`/
  `envOf` are **already ported** — `denseFindDomainAlg` (`Dense/DomainFold.lean`, built there for the
  group-domain enumeration; reused unchanged, not re-derived) and `denseAssignments`
  (`Dense/DomainFold.lean`) / `denseEnvOfFast` (`Dense/DomainBatch.lean` — structurally identical
  recursions to `assignments`/`envOf`, reused as-is). `findVarBound` has no dense port yet, so the
  minimal slice is transliterated here (`denseFindVarBound`) as this pass's first consumer —
  mirroring the `AddrDiseq`/`BusUnifyNative` precedent of placing a not-yet-owned helper at its first
  dense consumer; it is built entirely from `denseInteractionBound` (`Dense/DigitFold.lean`).
* **`RPSeen`'s `cs`-scoping is dropped, not just its `mem` proof.** The spec struct is parametrized
  by `cs : ConstraintSystem p` solely so `mem : c ∈ cs.algebraicConstraints` typechecks; with `mem`
  dropped there is nothing left needing `cs`, so `DenseRPSeen` carries no such parameter. For the
  same reason `rpLoop`'s `cs`/`hdomCs`/`hmem` proof-threading disappears; but `cs.busInteractions`
  *is* read by a real runtime call inside `rpCheckPair` (unlike the busUnify precedent's proof-only
  drops), so `denseRpLoop` threads it explicitly as a plain `bis` parameter, exactly as it already
  threads `domCs` (also read by `rpCheckPair`'s bound machinery).
* **Proof-witness drops.** Every spec `dif` that exists only to extract `Fact p.Prime`/a
  certificate witness (`rpLoop`'s `haveI : Fact p.Prime := ⟨pw.correct hpB⟩`, `rpLoop`'s `hcert`/
  `hpairs`/`hpairsV` construction, `rootPairUnifyPass`'s `PassCorrect` terms) is dropped; every
  decidable condition that gates *behavior* (the `pw.isPrime = true` primality gate, `rpCheckPair`'s
  whole certificate) is kept as a plain `if`/`Bool` computation with identical control flow — the M1
  precedent. Neither `rpCheckPair` nor `rpLoop` needs `[Fact p.Prime]` to *compute* (only their
  soundness theorems do — `ZMod p`'s `Inv` is total for every `p`), so the dense mirrors drop the
  instance argument entirely, not just its construction. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `twoRootVarsOk` (dense) -/

/-- `x` genuinely occurs in a recognized constraint (needed for `Solved.varsIn`). Mirrors
    `twoRootVarsOk` — unused elsewhere in the reference file too (dead code there, kept here for
    line-parallel fidelity, not dropped as an "improvement"). -/
def denseTwoRootVarsOk (c : DenseExpr p) (x : VarId) : Bool :=
  decide (x ∈ c.vars)

/-! ## Constant-coefficient decomposition (`DenseExpr.splitAt`, NEW shared dense helper)

`e = k·x + r` with `k` a field constant and `r` an `x`-free expression — unlike `denseLinearize`,
the remainder may be *nonlinear*, so this succeeds exactly where the affine machinery gives up.
Mirrors `Expression.splitAt` (`RootPairUnify.lean:145`). -/

/-- Decompose `e` as `k·x + r`: `k` a field constant, `r` not mentioning `x` (by construction).
    Mirrors `Expression.splitAt`. -/
def DenseExpr.splitAt (x : VarId) : DenseExpr p → Option (ZMod p × DenseExpr p)
  | .const n => some (0, .const n)
  | .var y => if y = x then some (1, .const 0) else some (0, .var y)
  | .add a b =>
      match a.splitAt x, b.splitAt x with
      | some (ca, ra), some (cb, rb) => some (ca + cb, .add ra rb)
      | _, _ => none
  | .mul a b =>
      if a.mentions x || b.mentions x then
        match a.constValue? with
        | some k =>
            match b.splitAt x with
            | some (cb, rb) => some (k * cb, .mul a rb)
            | none => none
        | none =>
            match b.constValue? with
            | some k =>
                match a.splitAt x with
                | some (ca, ra) => some (k * ca, .mul ra b)
                | none => none
            | none => none
      else some (0, .mul a b)

/-! ## Bounds through scaled range checks

`scaledSlotBound`'s `findDomainAlg` dependency (`DomainProp.lean:219`) is **already ported** as
`denseFindDomainAlg` in `Dense/DomainFold.lean` (its own first consumer, for the group-domain
enumeration) — reused unchanged here, not re-derived under a new name.

### `scaledSlotBound` itself

The low mem-ptr limb's range check does not carry the limb raw: the checked slot is
`4⁻¹·(x − F)` for a small flag polynomial `F`. The slot *value* is still fact-bounded, so
`x = k⁻¹·slot − k⁻¹·R` is bounded once the offset part enumerates over its (tiny, provable)
flag domains. Mirrors `scaledSlotBound`. Consumes `facts.slotBound` at RUNTIME — the facts
parameter is kept (precedent: `denseCollectAllBuses` in `Dense/BusUnifyNative.lean`). Reuses
`denseAssignments` (`Dense/DomainFold.lean`) and `denseEnvOfFast` (`Dense/DomainBatch.lean`) —
structurally identical recursions to the spec's `assignments`/`envOf`, not re-derived under new
names. -/

/-- Bound `x` through one interaction: find a slot whose expression is affine in `x` with a unit
    coefficient and a bus-fact value bound; enumerate the remaining variables' proven finite domains
    for the offset part. Returns `B` with `x.val < B` under acceptance. Mirrors `scaledSlotBound`. -/
def denseScaledSlotBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (bi : BusInteraction (DenseExpr p)) (x : VarId) :
    Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none else
    (List.range bi.payload.length).findSome? (fun slot =>
      match bi.payload[slot]? with
      | none => none
      | some O =>
        match facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot with
        | none => none
        | some bound =>
          match O.splitAt x with
          | none => none
          | some (k, R) =>
            let m := k⁻¹
            let others := R.vars.eraseDups
            let doms := others.filterMap (fun v =>
              (denseFindDomainAlg domCs v).map (fun d => (v, d)))
            if k * m = 1 ∧ doms.map Prod.fst = others ∧
                (doms.map (fun vd => vd.2.length)).prod ≤ 16 then
              if m.val * (bound - 1) + ((denseAssignments doms).map
                    (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 < p then
                some (m.val * (bound - 1) + ((denseAssignments doms).map
                  (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 + 1)
              else none
            else none)

/-! ## `anyVarBound` (dense)

### `findVarBound` companion (dense, first consumer here — see the module header)

Mirrors `findVarBound` (`DomainProp.lean:568`), reusing `denseInteractionBound`
(`Dense/DigitFold.lean`). -/

/-- The value bound of `x` derived from the first bus obligation that bounds it. Mirrors
    `findVarBound`. -/
def denseFindVarBound (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → VarId → Option Nat
  | [], _ => none
  | bi :: rest, x =>
    match denseInteractionBound bs facts bi x with
    | some bound => some bound
    | none => denseFindVarBound bs facts rest x

/-- Bound `x` from a raw slot (`denseFindVarBound`) or, failing that, through a scaled slot
    (`denseScaledSlotBound`). Mirrors `anyVarBound`. -/
def denseAnyVarBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (x : VarId) : Option Nat :=
  match denseFindVarBound bs facts bis x with
  | some B => some B
  | none => bis.findSome? (fun bi => denseScaledSlotBound bs facts domCs bi x)

/-! ## The pair certificate (dense) -/

/-- Decidable certificate that constraints `cX` (in `x`) and `cY` (in `y`) are two-root twins and
    both variables are range-bounded below the root gap. Mirrors `rpCheckPair`. Neither `rpCheckPair`
    nor its dense mirror needs `[Fact p.Prime]` to compute — `ZMod p`'s `Inv` is total for every
    `p`; only the soundness theorem (the prover's job) needs primality. -/
def denseRpCheckPair (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (cX cY : DenseExpr p) (x y : VarId) : Bool :=
  match denseTwoRootOf? cX x, denseTwoRootOf? cY y with
  | some (k, A, δ), some (k', A', δ') =>
    decide (k' = k) && decide (A'.terms = A.terms) && decide (A'.const = A.const) &&
    decide (δ' = δ) && decide (k * k⁻¹ = 1) &&
    decide (x ∈ cX.vars) && decide (y ∈ cY.vars) &&
    (match denseAnyVarBound bs facts bis domCs x, denseAnyVarBound bs facts bis domCs y with
     | some Bx, some By =>
       decide (max Bx By ≤ (k⁻¹ * δ).val) && decide (max Bx By ≤ p - (k⁻¹ * δ).val)
     | _, _ => false)
  | _, _ => false

/-! ## The scan loop and the pass (dense) -/

/-- A previously seen two-root constraint: the constraint, its variable, and the matching key
    `(k, A.terms, A.const, δ)`. Keys are compared before the (expensive) certificate is attempted.
    Data-only mirror of `RPSeen`, dropping the `mem : c ∈ cs.algebraicConstraints` proof field —
    with it gone there is no remaining reason to parametrize the struct by `cs` either (see the
    module header). -/
structure DenseRPSeen (p : ℕ) where
  c : DenseExpr p
  x : VarId
  key : ZMod p × List (VarId × ZMod p) × ZMod p × ZMod p

/-- The two-root candidates of one constraint, with their matching keys. Candidates whose root gap
    `g = k⁻¹·δ` is tiny are dropped up front (see the spec doc: never-unifiable, expensive-to-reject
    booleanity candidates). Mirrors `rpCandidates`. -/
def denseRpCandidates (c : DenseExpr p) :
    List (VarId × (ZMod p × List (VarId × ZMod p) × ZMod p × ZMod p)) :=
  c.vars.eraseDups.filterMap (fun x =>
    match denseTwoRootOf? c x with
    | some (k, A, δ) =>
      if 256 ≤ min (k⁻¹ * δ).val (p - (k⁻¹ * δ).val) then
        some (x, (k, A.terms, A.const, δ))
      else none
    | none => none)

/-- Hash of a candidate key, used to bucket the `seen` accumulator (bucketing never hides a twin;
    the exact `key == key'` check inside the scan separates any hash collision). Mirrors
    `rpKeyHash`. -/
def denseRpKeyHash (key : ZMod p × List (VarId × ZMod p) × ZMod p × ZMod p) : UInt64 :=
  mixHash (hash key.1.val)
    (mixHash (hash key.2.2.1.val) (mixHash (hash key.2.2.2.val) (hash key.2.1.length)))

/-- Prepend seen-entries into their key-hash buckets, preserving the same per-bucket order the old
    flat scan would produce. Mirrors `rpInsertAll`. -/
def denseRpInsertAll (m : Std.HashMap UInt64 (List (DenseRPSeen p)))
    (es : List (DenseRPSeen p)) : Std.HashMap UInt64 (List (DenseRPSeen p)) :=
  es.foldr (fun e acc => acc.insert (denseRpKeyHash e.key) (e :: acc.getD (denseRpKeyHash e.key) []))
    m

/-- Scan the constraints: for each two-root candidate, look for an earlier twin with the same key
    whose pair certificate passes, and adopt the entailed equality into the solution map. Mirrors
    `rpLoop`, threading `bis`/`domCs` explicitly in place of the spec's `cs`-scoped field access (see
    the module header) and `DenseSolved` in place of the proof-carrying `Solved`. -/
def denseRpLoop (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p)) :
    List (DenseExpr p) → Std.HashMap UInt64 (List (DenseRPSeen p)) → DenseSolved p → DenseSolved p
  | [], _, σ => σ
  | c :: rest, seen, σ =>
    let cands := denseRpCandidates c
    match cands.findSome? (fun xk =>
        (seen.getD (denseRpKeyHash xk.2) []).findSome? (fun e =>
          if e.key == xk.2 && e.x != xk.1 &&
              denseRpCheckPair bs facts bis domCs e.c c e.x xk.1
          then some (e, xk.1) else none)) with
    | some ex =>
        denseRpLoop bs facts bis domCs rest
          (denseRpInsertAll seen ((cands.filter (fun xk => xk.1 != ex.2)).map
            (fun xk => (⟨c, xk.1, xk.2⟩ : DenseRPSeen p))))
          (σ.insertAll [(ex.2, DenseExpr.var ex.1.x)])
    | none =>
        denseRpLoop bs facts bis domCs rest
          (denseRpInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseRPSeen p)))) σ

/-- Two-root decomposition unification's runtime transform. Prime `p` only (re-checked at runtime,
    as in `busPairCancelPass`/`denseDomainBatchTransformV`); identity otherwise. One sweep; the
    cleanup fixpoint iterates the pass. Solutions are bare variables, so substitution can never grow
    a degree. Mirrors `rootPairUnifyPass`'s computed output (dropping its `PassCorrect` term); shaped
    as `(pw) → (bs) → (facts) → (d) → out`, so after currying `pw` it matches `denseBusUnifyF`'s
    shape for `DenseVerifiedPassW.ofNative` (`Dense/BusUnifyNative.lean`). -/
def denseRootPairUnifyF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseRpLoop bs facts d.busInteractions d.algebraicConstraints
      d.algebraicConstraints ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

end ApcOptimizer.Dense
