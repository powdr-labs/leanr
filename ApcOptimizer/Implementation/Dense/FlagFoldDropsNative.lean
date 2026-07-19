import ApcOptimizer.Implementation.Dense.FlagUnifyNative

set_option autoImplicit false

/-! # Dense flagFold drop sub-passes: box-tautology + pointwise-duplicate removal (Task 3,
busUnify cluster, chunk S3 — impl)

Dense, `VarId`-native transliteration of the runtime pieces of `OptimizerPasses/FlagFold.lean`'s
parts **B** (box-tautology replacement, ~25–189) and **C** (pointwise-duplicate stateless check
removal, ~259–611). Part A (`fxSubstPass`, the entailed nonlinear substitution) and the
`boxRewritePass` sub-pass of the scheduled composite are a LATER chunk — not touched here. This
file is **impl-only**: no theorem/lemma from the spec file is ported (`btKeep_cert`,
`btKeep_of_cert_false`, `singleVar_mem_boxTautoReplace`, `ConstraintSystem.boxTautoReplace_correct`,
`ConstraintSystem.filterBusEntailed_correct`, `boxAgree_sound`, `slotEqCert_sound`,
`msgEqCert_sound`, `pdFirst_keep`, `ConstraintSystem.pointwiseDupDrop_correct` are all proof-side,
the prover's job), and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the two
top-level transforms `denseBoxTautoDropF`/`densePointwiseDupDropF` are shaped like
`denseFlagUnifyF` (`Dense/FlagUnifyNative.lean`) MINUS the `facts` argument (see below), so the
prover wraps each directly with `DenseVerifiedPassW.ofNative`.

Notes on how spec pieces map here:

* **No `facts` parameter.** Both `boxTautoDropPass` and `pointwiseDupDropPass` are spec
  `VerifiedPass p` (`fun cs bs => …`), not `VerifiedPassW p` — unlike every busUnify-cluster pass
  ported so far, neither consults `BusFacts` (their certificates are purely
  `findDomainAlg`/domain-box-enumeration and syntactic/domain-agreement checks). The dense mirrors
  therefore drop `facts` entirely rather than threading an unused parameter, mirroring the spec
  signature exactly; the prover's `ofNative` wrapper (which always takes `(bs) (facts) (d)` at that
  layer) will simply ignore `facts` at the call site, the same way `denseConstantFoldPass` ignores
  both `bs` and `facts` (`Dense/ExprOps.lean`).
* **`bs` is threaded but genuinely unused by part B's *output*.** `boxTautoDropPass`'s spec `.out`
  (`cs.boxTautoReplaceWith singles domOf`) does not read `bs` at all — `bs` only appears in the
  (proof-only) `PassCorrect` term. `denseBoxTautoDropF` keeps the parameter anyway (unused, named
  `_bs`) purely for shape parity with the spec function `fun cs bs => …` and with the other
  `denseXxxF` transforms in this cluster; it costs nothing (erased at the call site once the
  prover's wrapper ignores it too). Part C's `bs` *is* genuinely read at runtime
  (`bs.isStateful`), so `densePointwiseDupDropF` uses it directly.
* **`findDomainAlg`/`assignments`/`envOf` reuse.** Owned by `OptimizerPasses/DomainProp.lean`,
  already ported: `denseFindDomainAlg`/`denseAssignments` (`Dense/DomainFold.lean`) and
  `denseEnvOfFast` (`Dense/DomainBatch.lean`), reused unchanged (the S1/S2 precedent).
* **`Expression.splitAt` reuse.** Already ported as `DenseExpr.splitAt` in
  `Dense/RootPairUnifyNative.lean` (chunk S1) — reused unchanged for `slotEqCert`'s dense mirror.
* **`Expression.mentions` reuse.** Already ported as `DenseExpr.mentions` in `Dense/SubstMap.lean`
  — reused unchanged for `slotEqCert`'s carrier-membership gate.
* **`Expression.constValue?` reuse.** Already ported as `DenseExpr.constValue?` in
  `Dense/DropPasses.lean` — reused unchanged for `msgEqCert`'s dense mirror.
* **`Expression.pdStructHash` is reused wholesale as `DenseExpr.bHash` (`Dense/Dedup.lean`), not
  re-derived.** Both mix the same constants (`11`/`13`/`17`/`19`) over the same recursion; the only
  difference is the leaf case, where `pdStructHash` hashes `mixHash (hash y.name) (hash
  y.powdrId?)` — exactly `Variable`'s own `Hashable` instance
  (`instance : Hashable Variable := ⟨fun a => mixHash (hash a.name) (hash a.powdrId?)⟩`,
  `Implementation/Variable.lean`) — while `bHash` hashes `hash y` directly. So at the *spec* level
  `Expression.pdStructHash = Expression.bHash` already (definitionally, via that `Hashable`
  instance); porting `pdStructHash` to `VarId` and porting `bHash` to `VarId` are the identical
  exercise, and `bHash` got there first (the dedup chunk). Reusing it here is not a simplification
  of the algorithm, just not duplicating an identical function under a second name.
* **`Expression.pdVarBloom` has no existing dense counterpart** (Bloom masks are new to this pass),
  so it gets a genuine local mirror (`DenseExpr.pdVarBloom`): identical shift/mask recursion, only
  the leaf hash changes (`hash y` in place of `mixHash (hash y.name) (hash y.powdrId?)`), the same
  substitution `bHash` already made.
* **`pdDropSet`'s imperative structure (`Id.run do` with `mut` accumulators) is preserved exactly**:
  the same three mutable maps (`buckets`/`firstMemo`/`drops`), the same `pos` counter incremented
  once per outer iteration regardless of the stateful/degenerate-multiplicity early exits, the same
  per-bucket linear scan with the `dropped`-latch inner loop, and the same lazily-memoized
  first-of-class recursion via `firstMemo[e.pos]?`. Only `Expression`/`Variable` become
  `DenseExpr`/`VarId` and `pdStructHash`/`pdVarBloom` become `bHash`/`pdVarBloom`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part B: box-tautology replacement (dense) -/

/-- The single-variable constraints of a list (the only `findDomainAlg` sources). Mirrors
    `singleVarCs`. -/
def denseSingleVarCs (all : List (DenseExpr p)) : List (DenseExpr p) :=
  all.filter (fun c => c.vars.eraseDups.length == 1)

/-- Certificate: `c` mentions ≥ 2 distinct variables, every one carries a proven finite domain
    (from the single-variable constraints), the joint box is small, and `c` vanishes on all of it.
    Mirrors `btCert`. -/
def denseBtCert (singles : List (DenseExpr p)) (c : DenseExpr p) : Bool :=
  2 ≤ c.vars.eraseDups.length &&
  (let doms := c.vars.eraseDups.filterMap (fun v =>
     (denseFindDomainAlg singles v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = c.vars.eraseDups) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (denseAssignments doms).all (fun pt => decide (c.eval (denseEnvOfFast pt) = 0)))

/-- Cheap mirror of `denseBtCert` over a precomputed (pure, memoized) domain lookup — a prefilter
    only; accepted candidates re-run the real certificate. Mirrors `btPre`. -/
def denseBtPre (domOf : VarId → Option (List (ZMod p))) (c : DenseExpr p) : Bool :=
  2 ≤ c.vars.eraseDups.length &&
  (let doms := c.vars.eraseDups.filterMap (fun v => (domOf v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = c.vars.eraseDups) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (denseAssignments doms).all (fun pt => decide (c.eval (denseEnvOfFast pt) = 0)))

/-- The replacement condition: the memoized prefilter gates the (expensive) certificate. Mirrors
    `btKeep`. -/
def denseBtKeep (singles : List (DenseExpr p)) (domOf : VarId → Option (List (ZMod p)))
    (c : DenseExpr p) : Bool :=
  denseBtPre domOf c && denseBtCert singles c

/-- Replace certified box tautologies by the trivial constraint (parameterized over the
    precomputed prefilter inputs). Mirrors `ConstraintSystem.boxTautoReplaceWith`. -/
def DenseConstraintSystem.boxTautoReplaceWith (d : DenseConstraintSystem p)
    (singles : List (DenseExpr p)) (domOf : VarId → Option (List (ZMod p))) :
    DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map (fun c =>
      if denseBtKeep singles domOf c then DenseExpr.const 0 else c) }

/-- Part B's runtime transform: prime `p` only (re-checked at runtime, as elsewhere in this
    cluster); identity otherwise. Builds the per-variable domain cache in one linear pass over all
    occurrences (the `m.contains v` guard against a quadratic pre-dedup), exactly as
    `boxTautoDropPass` does. Mirrors `boxTautoDropPass`'s computed output (dropping its
    `PassCorrect` term); no `facts` parameter (see the module header) — shaped as
    `(pw) → (bs) → (d) → out`. -/
def denseBoxTautoDropF (pw : PrimeWitness p) (_bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let singles := denseSingleVarCs d.algebraicConstraints
    let cache : Std.HashMap VarId (Option (List (ZMod p))) :=
      (d.algebraicConstraints.flatMap DenseExpr.vars).foldl
        (fun m v => if m.contains v then m else m.insert v (denseFindDomainAlg singles v)) ∅
    d.boxTautoReplaceWith singles (fun v => cache.getD v none)
  else d

/-! ## Part C: pointwise-duplicate stateless check removal (dense) -/

/-- Joint-box agreement: every joint variable of `R`/`R'` has a proven finite domain, the box is
    small, and the two expressions agree at every box point. Mirrors `boxAgree`. -/
def denseBoxAgree (singles : List (DenseExpr p)) (R R' : DenseExpr p) : Bool :=
  let jv := (R.vars ++ R'.vars).eraseDups
  let doms := jv.filterMap (fun v =>
    (denseFindDomainAlg singles v).map (fun d => (v, d)))
  decide (doms.map Prod.fst = jv) &&
  decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
  (denseAssignments doms).all (fun pt =>
    decide (R.eval (denseEnvOfFast pt) = R'.eval (denseEnvOfFast pt)))

/-- Slot-pair certificate: the two expressions are syntactically equal, or they decompose over the
    same carrier with the same constant coefficient and their offset difference vanishes on the
    joint (proven, small) domain box of the offset variables. Mirrors `slotEqCert`, reusing
    `DenseExpr.splitAt` (`Dense/RootPairUnifyNative.lean`) and `DenseExpr.mentions`
    (`Dense/SubstMap.lean`). -/
def denseSlotEqCert (singles : List (DenseExpr p)) (e e' : DenseExpr p) : Bool :=
  e == e' ||
  e.vars.eraseDups.any (fun x =>
    e'.mentions x &&
    match e.splitAt x, e'.splitAt x with
    | some (k, R), some (k2, R') => k2 == k && denseBoxAgree singles R R'
    | _, _ => false)

/-- Full-message certificate: same bus, same constant multiplicity, pointwise-equal payloads.
    Mirrors `msgEqCert`, reusing `DenseExpr.constValue?` (`Dense/DropPasses.lean`). -/
def denseMsgEqCert (singles : List (DenseExpr p)) (bi bi' : BusInteraction (DenseExpr p)) : Bool :=
  bi.busId == bi'.busId &&
  (match bi.multiplicity.constValue?, bi'.multiplicity.constValue? with
   | some m, some m' => m == m'
   | _, _ => false) &&
  bi.payload.length == bi'.payload.length &&
  (bi.payload.zip bi'.payload).all (fun ee => denseSlotEqCert singles ee.1 ee.2)

/-- Is `bi` the first of its pointwise class (no earlier certified twin)? Mirrors `pdFirst`. -/
def densePdFirst (bs : BusSemantics p) (singles : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match bis.findIdx? (fun b => b == bi) with
  | none => true
  | some i => (bis.take i).all (fun b => bs.isStateful b.busId || !(denseMsgEqCert singles b bi))

/-- Keep unless a *first-of-class* earlier stateless twin exists (depth-1 rule: the twin that
    justifies a drop is itself provably kept, so no chain induction is needed). Mirrors `pdKeep`. -/
def densePdKeep (bs : BusSemantics p) (singles : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  bs.isStateful bi.busId ||
  (match bis.findIdx? (fun b => b == bi) with
   | none => true
   | some i =>
     !((bis.take i).any (fun b => !bs.isStateful b.busId && denseMsgEqCert singles b bi
         && densePdFirst bs singles bis b)))

/-! ### The fast duplicate analysis (dense)

Mirrors the spec's "fast duplicate analysis" section (`FlagFold.lean:447–546`): the certified
`densePdKeep`/`densePdFirst` above pay an O(#interactions) `findIdx?` (deep structural equality)
plus a prefix scan of `denseMsgEqCert`s per interaction; `densePdDropSet` computes the identical
drop set in one left-to-right sweep, bucketed by the certificate's necessary invariants and
prefiltered by per-slot structural hashes and variable Bloom masks, consumed as a *prefilter*
only. -/

/-- A 64-bit Bloom mask of the expression's variables (for the shared-variable prefilter). Mirrors
    `Expression.pdVarBloom` — the only substitution from the spec recursion is the leaf hash
    (`hash y` in place of `mixHash (hash y.name) (hash y.powdrId?)`, the same substitution `bHash`
    already made for `pdStructHash`; see the module header). -/
def DenseExpr.pdVarBloom : DenseExpr p → UInt64
  | .const _ => 0
  | .var y => (1 : UInt64) <<< (UInt64.ofNat ((hash y).toNat % 64))
  | .add a b => a.pdVarBloom ||| b.pdVarBloom
  | .mul a b => a.pdVarBloom ||| b.pdVarBloom

/-- Necessary condition for `denseMsgEqCert` on two payloads, from the precomputed per-slot
    signatures: each slot pair is syntactically equal (hash) or shares a variable (Blooms). Mirrors
    `pdSigsCompatible` — representation-independent, unchanged. -/
def densePdSigsCompatible (a b : Array (UInt64 × UInt64)) : Bool :=
  Array.isEqv a b (fun x y => x.1 == y.1 || (x.2 &&& y.2) != 0)

/-- Full-value hash of an interaction, for the dropped-value buckets. Mirrors `pdValHash`, reusing
    `DenseExpr.bHash` in place of `pdStructHash` (see the module header). -/
def densePdValHash (bi : BusInteraction (DenseExpr p)) : UInt64 :=
  mixHash (hash bi.busId) (mixHash bi.multiplicity.bHash
    (bi.payload.foldl (fun h e => mixHash h e.bHash) 7))

/-- One bucket entry of the sweep: position, the interaction, its slot signatures, and whether it
    was kept. Mirrors `PdEntry`. -/
structure DensePdEntry (p : ℕ) where
  pos : Nat
  bi : BusInteraction (DenseExpr p)
  sigs : Array (UInt64 × UInt64)
  kept : Bool

/-- The value-keyed set of interactions the sweep decides to drop — exactly `densePdKeep`'s drop
    set (drops are value-based there too: `findIdx?` evaluates every duplicate at its first
    occurrence). Mirrors `pdDropSet`; the imperative structure (three mutable accumulators, the
    per-bucket scan, the lazily-memoized first-of-class recursion) is preserved exactly (see the
    module header). -/
def densePdDropSet (bs : BusSemantics p) (singles : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) :
    Std.HashMap UInt64 (List (BusInteraction (DenseExpr p))) := Id.run do
  let mut buckets : Std.HashMap UInt64 (List (DensePdEntry p)) := ∅
  let mut firstMemo : Std.HashMap Nat Bool := ∅
  let mut drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p))) := ∅
  let mut pos := 0
  for bi in bis do
    if !bs.isStateful bi.busId then
      match bi.multiplicity.constValue? with
      | none => pure ()   -- can neither be dropped nor certify a drop
      | some m =>
        let key := mixHash (hash bi.busId) (mixHash (hash m.val) (hash bi.payload.length))
        let sigs : Array (UInt64 × UInt64) :=
          (bi.payload.map (fun e => (e.bHash, e.pdVarBloom))).toArray
        let entries := buckets.getD key []
        -- an exact duplicate mirrors its first occurrence's decision (findIdx? semantics)
        match entries.find? (fun e => decide (e.bi = bi)) with
        | some e =>
          if !e.kept then
            let vk := densePdValHash bi
            drops := drops.insert vk (bi :: (drops.getD vk []))
        | none =>
          -- drop iff an earlier kept, first-of-class, certified twin exists
          let mut dropped := false
          for e in entries do
            if !dropped && e.kept && densePdSigsCompatible e.sigs sigs then
              if denseMsgEqCert singles e.bi bi then
                -- lazily decide whether `e` is first of its class
                let isFirst ← do
                  match firstMemo[e.pos]? with
                  | some b => pure b
                  | none =>
                    let b := entries.all (fun e' =>
                      !(e'.pos < e.pos && densePdSigsCompatible e'.sigs e.sigs
                        && denseMsgEqCert singles e'.bi e.bi))
                    firstMemo := firstMemo.insert e.pos b
                    pure b
                if isFirst then
                  dropped := true
          if dropped then
            let vk := densePdValHash bi
            drops := drops.insert vk (bi :: (drops.getD vk []))
          buckets := buckets.insert key ({ pos, bi, sigs, kept := !dropped } :: entries)
    pos := pos + 1
  return drops

/-- Was `bi` flagged by the sweep? (`false` = flagged as a drop candidate.) Mirrors `pdFastKeep`. -/
def densePdFastKeep (drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p))))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match drops[densePdValHash bi]? with
  | some l => !(l.any (fun b => decide (b = bi)))
  | none => true

/-- Part C's runtime transform: prime `p` only; identity otherwise. The fast sweep flags exactly
    `densePdKeep`'s drop set; the certified `densePdKeep` re-verifies each flagged drop
    (short-circuited away for the unflagged rest by the `||`), exactly as `pointwiseDupDropPass`
    does. Mirrors `pointwiseDupDropPass`'s computed output (dropping its `PassCorrect` term); no
    `facts` parameter (see the module header) — shaped as `(pw) → (bs) → (d) → out`. -/
def densePointwiseDupDropF (pw : PrimeWitness p) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let singles := denseSingleVarCs d.algebraicConstraints
    let drops := densePdDropSet bs singles d.busInteractions
    d.filterBus (fun bi => densePdFastKeep drops bi || densePdKeep bs singles d.busInteractions bi)
  else d

end ApcOptimizer.Dense
