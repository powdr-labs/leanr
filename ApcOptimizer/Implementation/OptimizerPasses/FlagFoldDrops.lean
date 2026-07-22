import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense flagFold drop sub-passes: box-tautology + pointwise-duplicate removal

This file defines two of the flagFold drop sub-passes: box-tautology replacement and
pointwise-duplicate stateless check removal. The entailed nonlinear substitution sub-pass
(`FxSubst.lean`) and the box-rewrite sub-pass of the scheduled composite are defined elsewhere.
This file is **impl-only**: no correctness theorem is stated here, and no
`DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the two top-level transforms
`denseBoxTautoDropF`/`densePointwiseDupDropF` are shaped like `denseFlagUnifyF`
(`Dense/FlagUnifyNative.lean`) minus the `facts` argument (see below), so the prover wraps each
directly with `DenseVerifiedPassW.of`.

Notes:

* **No `facts` parameter.** Neither transform consults `BusFacts` (their certificates are purely
  `findDomainAlg`/domain-box-enumeration and syntactic/domain-agreement checks), so both drop
  `facts` entirely rather than threading an unused parameter; the prover's `of` wrapper (which
  always takes `(bs) (facts) (d)` at that layer) will simply ignore `facts` at the call site, the
  same way `denseConstantFoldPass` ignores both `bs` and `facts` (`Dense/ExprOps.lean`).
* **`bs` is threaded but unused by the box-tautology output.** `denseBoxTautoDropF` keeps a `bs`
  parameter (unused, named `_bs`) for shape parity with the other `denseXxxF` transforms in this
  cluster; it costs nothing (erased at the call site once the prover's wrapper ignores it too).
  Part C's `bs` *is* genuinely read at runtime (`bs.isStateful`), so `densePointwiseDupDropF` uses
  it directly.
* `denseFindDomainAlg`/`denseAssignments` (`Dense/DomainFold.lean`) and `denseEnvOfFast`
  (`Dense/DomainBatch.lean`) are reused unchanged from elsewhere in the codebase.
* `DenseExpr.splitAt` (`Dense/RootPairUnifyNative.lean`) is reused unchanged for
  `denseSlotEqCert`.
* `DenseExpr.mentions` (`Dense/SubstMap.lean`) is reused unchanged for `denseSlotEqCert`'s
  carrier-membership gate.
* `DenseExpr.constValue?` (`Dense/DropPasses.lean`) is reused unchanged for `denseMsgEqCert`.
* `DenseExpr.bHash` (`Dense/Dedup.lean`) is reused wholesale as the structural hash used
  throughout this file, rather than defining a new one: it mixes the same constants
  (`11`/`13`/`17`/`19`) over the same recursion, hashing `hash y` directly at variable leaves.
* `DenseExpr.pdVarBloom` (below) is a Bloom mask of an expression's variables, defined via the
  same shift/mask recursion as `DenseExpr.bHash`.
* `densePdDropSet` (below) uses an imperative structure (`Id.run do` with `mut` accumulators):
  three mutable maps (`buckets`/`firstMemo`/`drops`), a `pos` counter incremented once per outer
  iteration regardless of the stateful/degenerate-multiplicity early exits, a per-bucket linear
  scan with a `dropped`-latch inner loop, and a lazily-memoized first-of-class recursion via
  `firstMemo[e.pos]?`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part B: box-tautology replacement (dense) -/

/-- The single-variable constraints of a list (the only `findDomainAlg` sources). The
    distinct-variable count uses the bucketed dedup (`hashedEraseDups_eq` — the identical list, so
    the filter and everything downstream is value-unchanged); occurrence-heavy constraints made the
    plain quadratic `eraseDups` measurable here. -/
def denseSingleVarCs (all : List (DenseExpr p)) : List (DenseExpr p) :=
  all.filter (fun c => (HashedDedup.hashedEraseDups (hash ·) c.vars).length == 1)

/-- Certificate: `c` mentions ≥ 2 distinct variables, every one carries a proven finite domain
    (from the single-variable constraints), the joint box is small, and `c` vanishes on all of it. -/
def denseBtCert (singles : List (DenseExpr p)) (c : DenseExpr p) : Bool :=
  2 ≤ c.vars.eraseDups.length &&
  (let doms := c.vars.eraseDups.filterMap (fun v =>
     (denseFindDomainAlg singles v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = c.vars.eraseDups) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (denseAssignments doms).all (fun pt => decide (c.eval (denseEnvOfFast pt) = 0)))

/-- A cheap version of `denseBtCert` over a precomputed (pure, memoized) domain lookup — a
    prefilter only; accepted candidates re-run the real certificate. The distinct-variable list is
    computed once (bucketed, `hashedEraseDups_eq` keeps it the identical list) instead of three
    `eraseDups` scans per constraint. -/
def denseBtPre (domOf : VarId → Option (List (ZMod p))) (c : DenseExpr p) : Bool :=
  let vs := HashedDedup.hashedEraseDups (hash ·) c.vars
  2 ≤ vs.length &&
  (let doms := vs.filterMap (fun v => (domOf v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = vs) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (denseAssignments doms).all (fun pt => decide (c.eval (denseEnvOfFast pt) = 0)))

/-- The replacement condition: the memoized prefilter gates the (expensive) certificate. -/
def denseBtKeep (singles : List (DenseExpr p)) (domOf : VarId → Option (List (ZMod p)))
    (c : DenseExpr p) : Bool :=
  denseBtPre domOf c && denseBtCert singles c

/-- Replace certified box tautologies by the trivial constraint (parameterized over the
    precomputed prefilter inputs). -/
def DenseConstraintSystem.boxTautoReplaceWith (d : DenseConstraintSystem p)
    (singles : List (DenseExpr p)) (domOf : VarId → Option (List (ZMod p))) :
    DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map (fun c =>
      if denseBtKeep singles domOf c then DenseExpr.const 0 else c) }

/-- Part B's runtime transform: prime `p` only (re-checked at runtime, as elsewhere in this
    cluster); identity otherwise. Builds the per-variable domain cache in one linear pass over all
    occurrences (the `m.contains v` guard against a quadratic pre-dedup). No `facts` parameter
    (see the module header) — shaped as `(pw) → (bs) → (d) → out`. -/
def denseBoxTautoDropF (pw : PrimeWitness p) (_bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let singles := denseSingleVarCs d.algebraicConstraints
    -- Bucket the single-variable constraints by their variable once: `denseFindDomainAlg singles v`
    -- skips every constraint not mentioning `v`, and a single-variable constraint mentions exactly
    -- its one variable — so scanning `v`'s own bucket (original order preserved) yields the identical
    -- domain without the O(#singles) `mentions` walk per distinct variable (the pass's dominant cost
    -- on large circuits).
    let singlesBy : Std.HashMap VarId (List (DenseExpr p)) :=
      singles.reverse.foldl (fun m c =>
        match HashedDedup.hashedEraseDups (hash ·) c.vars with
        | [v] => m.insert v (c :: m.getD v [])
        | _ => m) ∅
    let cache : Std.HashMap VarId (Option (List (ZMod p))) :=
      (d.algebraicConstraints.flatMap DenseExpr.vars).foldl
        (fun m v => if m.contains v then m
         else m.insert v (denseFindDomainAlg (singlesBy.getD v []) v)) ∅
    d.boxTautoReplaceWith singles (fun v => cache.getD v none)
  else d

/-! ## Part C: pointwise-duplicate stateless check removal (dense) -/

/-- Joint-box agreement: every joint variable of `R`/`R'` has a proven finite domain, the box is
    small, and the two expressions agree at every box point. -/
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
    joint (proven, small) domain box of the offset variables. Reuses `DenseExpr.splitAt`
    (`Dense/RootPairUnifyNative.lean`) and `DenseExpr.mentions` (`Dense/SubstMap.lean`). -/
def denseSlotEqCert (singles : List (DenseExpr p)) (e e' : DenseExpr p) : Bool :=
  e == e' ||
  e.vars.eraseDups.any (fun x =>
    e'.mentions x &&
    match e.splitAt x, e'.splitAt x with
    | some (k, R), some (k2, R') => k2 == k && denseBoxAgree singles R R'
    | _, _ => false)

/-- Full-message certificate: same bus, same constant multiplicity, pointwise-equal payloads.
    Reuses `DenseExpr.constValue?` (`Dense/DropPasses.lean`). -/
def denseMsgEqCert (singles : List (DenseExpr p)) (bi bi' : BusInteraction (DenseExpr p)) : Bool :=
  bi.busId == bi'.busId &&
  (match bi.multiplicity.constValue?, bi'.multiplicity.constValue? with
   | some m, some m' => m == m'
   | _, _ => false) &&
  bi.payload.length == bi'.payload.length &&
  (bi.payload.zip bi'.payload).all (fun ee => denseSlotEqCert singles ee.1 ee.2)

/-- Is `bi` the first of its pointwise class (no earlier certified twin)? -/
def densePdFirst (bs : BusSemantics p) (singles : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match bis.findIdx? (fun b => b == bi) with
  | none => true
  | some i => (bis.take i).all (fun b => bs.isStateful b.busId || !(denseMsgEqCert singles b bi))

/-- Keep unless a *first-of-class* earlier stateless twin exists (depth-1 rule: the twin that
    justifies a drop is itself provably kept, so no chain induction is needed). -/
def densePdKeep (bs : BusSemantics p) (singles : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  bs.isStateful bi.busId ||
  (match bis.findIdx? (fun b => b == bi) with
   | none => true
   | some i =>
     !((bis.take i).any (fun b => !bs.isStateful b.busId && denseMsgEqCert singles b bi
         && densePdFirst bs singles bis b)))

/-! ### The fast duplicate analysis (dense)

The certified `densePdKeep`/`densePdFirst` above pay an O(#interactions) `findIdx?` (deep
structural equality) plus a prefix scan of `denseMsgEqCert`s per interaction; `densePdDropSet`
computes the identical drop set in one left-to-right sweep, bucketed by the certificate's
necessary invariants and prefiltered by per-slot structural hashes and variable Bloom masks,
consumed as a *prefilter* only. -/

/-- A 64-bit Bloom mask of the expression's variables (for the shared-variable prefilter), via the
    same shift/mask recursion `DenseExpr.bHash` uses. -/
def DenseExpr.pdVarBloom : DenseExpr p → UInt64
  | .const _ => 0
  | .var y => (1 : UInt64) <<< (UInt64.ofNat ((hash y).toNat % 64))
  | .add a b => a.pdVarBloom ||| b.pdVarBloom
  | .mul a b => a.pdVarBloom ||| b.pdVarBloom

/-- Necessary condition for `denseMsgEqCert` on two payloads, from the precomputed per-slot
    signatures: each slot pair is syntactically equal (hash) or shares a variable (Blooms). -/
def densePdSigsCompatible (a b : Array (UInt64 × UInt64)) : Bool :=
  Array.isEqv a b (fun x y => x.1 == y.1 || (x.2 &&& y.2) != 0)

/-- Full-value hash of an interaction, for the dropped-value buckets. -/
def densePdValHash (bi : BusInteraction (DenseExpr p)) : UInt64 :=
  mixHash (hash bi.busId) (mixHash bi.multiplicity.bHash
    (bi.payload.foldl (fun h e => mixHash h e.bHash) 7))

/-- One bucket entry of the sweep: position, the interaction, its slot signatures, and whether it
    was kept. -/
structure DensePdEntry (p : ℕ) where
  pos : Nat
  bi : BusInteraction (DenseExpr p)
  sigs : Array (UInt64 × UInt64)
  kept : Bool

/-- The value-keyed set of interactions the sweep decides to drop — the same set `densePdKeep`
    would drop (drops are value-based there too: `findIdx?` evaluates every duplicate at its first
    occurrence). Uses an imperative structure (three mutable accumulators, the per-bucket scan, the
    lazily-memoized first-of-class recursion); see the module header. -/
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

/-- The verdict-map keep test: drop `bi` iff its value bucket holds a *certified* dropped twin
    (an entry provably `densePdKeep = false`, structurally equal to `bi`). The
    `{b // densePdKeep … = false}` subtype is load-bearing: each stored entry carries its own
    `densePdKeep = false` proof. -/
def densePdVerdictKeep {p : ℕ} {P : BusInteraction (DenseExpr p) → Prop}
    (verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) // P b }))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match verdicts[densePdValHash bi]? with
  | some l => !(l.any (fun b => decide (b.val = bi)))
  | none => true

/-- A `densePdVerdictKeep` drop carries its certificate: the bucket entry is structurally equal to
    `bi`, so its stored property transports. -/
theorem densePdVerdictKeep_false {p : ℕ} {P : BusInteraction (DenseExpr p) → Prop}
    (verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) // P b }))
    (bi : BusInteraction (DenseExpr p)) (h : densePdVerdictKeep verdicts bi = false) : P bi := by
  unfold densePdVerdictKeep at h
  cases hv : verdicts[densePdValHash bi]? with
  | none => rw [hv] at h; simp at h
  | some l =>
    rw [hv] at h
    simp only [Bool.not_eq_false'] at h
    obtain ⟨b, _hb, hbe⟩ := List.any_eq_true.1 h
    exact of_decide_eq_true hbe ▸ b.property

/-- Part C's runtime transform: prime `p` only; identity otherwise. The fast sweep flags exactly
    `densePdKeep`'s drop set; the certified `densePdKeep` then re-verifies each flagged drop **once
    per distinct value** — `densePdKeep` is value-determined (its `findIdx?` locates the value's
    first occurrence), so equal interactions share one run instead of paying the deep-equality scan
    and prefix certificates per occurrence. No `facts` parameter (see the module header) — shaped
    as `(pw) → (bs) → (d) → out`. -/
def densePointwiseDupDropF (pw : PrimeWitness p) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let singles := denseSingleVarCs d.algebraicConstraints
    let drops := densePdDropSet bs singles d.busInteractions
    let verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) //
        densePdKeep bs (denseSingleVarCs d.algebraicConstraints) d.busInteractions b = false }) :=
      drops.fold (init := ∅) fun m h l =>
        m.insert h (l.eraseDups.filterMap (fun b =>
          if hpd : densePdKeep bs (denseSingleVarCs d.algebraicConstraints)
              d.busInteractions b = false
          then some ⟨b, hpd⟩ else none))
    d.filterBus (densePdVerdictKeep verdicts)
  else d

end ApcOptimizer.Dense
