import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense flagFold drop sub-passes: box-tautology + pointwise-duplicate removal

Impl-only (no correctness here): the two transforms `denseBoxTautoDropF`/`densePointwiseDupDropF`
are shaped like `denseFlagUnifyF` minus `facts`, and wrapped with `DenseVerifiedPassW.of` in
`Proofs/FlagFoldDrops.lean`. Part C's `bs` is read (`bs.isStateful`); part B's is unused. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part B: box-tautology replacement (dense) -/

/-- The single-variable constraints of a list (the only `findDomainAlg` sources). -/
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

/-- A cheap prefilter over a precomputed domain lookup; accepted candidates re-run the real
    `denseBtCert`. -/
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

/-- Replace certified box tautologies by the trivial constraint `0`. -/
def DenseConstraintSystem.boxTautoReplaceWith (d : DenseConstraintSystem p)
    (singles : List (DenseExpr p)) (domOf : VarId → Option (List (ZMod p))) :
    DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map (fun c =>
      if denseBtKeep singles domOf c then DenseExpr.const 0 else c) }

/-- Box-tautology drop (part B): a multi-variable constraint that vanishes at every point of its
    variables' proven finite-domain box is replaced by the literal `0`. E.g. with `x, y ∈ {0,1}`
    established by single-variable constraints, a constraint that is `0` on all four `(x,y)` points
    becomes `0`. Prime `p` only; identity otherwise. -/
def denseBoxTautoDropF (pw : PrimeWitness p) (_bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let singles := denseSingleVarCs d.algebraicConstraints
    -- Bucket single-variable constraints by their one variable, so `denseFindDomainAlg` scans only
    -- that variable's bucket (same domain, no O(#singles) walk per variable).
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

/-- Slot-pair certificate: the two expressions are syntactically equal, or decompose over the same
    carrier with the same constant coefficient and offsets agreeing on the joint domain box. -/
def denseSlotEqCert (singles : List (DenseExpr p)) (e e' : DenseExpr p) : Bool :=
  e == e' ||
  e.vars.eraseDups.any (fun x =>
    e'.mentions x &&
    match e.splitAt x, e'.splitAt x with
    | some (k, R), some (k2, R') => k2 == k && denseBoxAgree singles R R'
    | _, _ => false)

/-- Full-message certificate: same bus, same constant multiplicity, pointwise-equal payloads. -/
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

`densePdDropSet` computes the identical drop set as `densePdKeep` in one bucketed left-to-right
sweep, prefiltered by per-slot structural hashes and variable Bloom masks. -/

/-- A 64-bit Bloom mask of the expression's variables (for the shared-variable prefilter). -/
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
    would drop (drops are value-based: `findIdx?` evaluates each duplicate at its first occurrence). -/
def densePdDropSet (bs : BusSemantics p) (singles : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) :
    Std.HashMap UInt64 (List (BusInteraction (DenseExpr p))) := Id.run do
  -- Per coarse key (bus id, constant multiplicity, payload length), keep only the first-of-class
  -- *representatives* seen so far; a later interaction certified equal to a representative is a
  -- drop. Storing representatives only (never the dropped entries) keeps the per-interaction scan
  -- proportional to the number of distinct classes in a bucket rather than its total size, and
  -- makes the first-of-class memo unnecessary (a stored representative is first-of-class by
  -- construction). Only a heuristic drop *proposal*: `densePointwiseDupDropF` re-verifies every
  -- proposal against `densePdKeep`, so this carries no soundness obligation.
  let mut reps : Std.HashMap UInt64 (List (DensePdEntry p)) := ∅
  let mut drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p))) := ∅
  for bi in bis do
    if !bs.isStateful bi.busId then
      match bi.multiplicity.constValue? with
      | none => pure ()
      | some m =>
        let key := mixHash (hash bi.busId) (mixHash (hash m.val) (hash bi.payload.length))
        let sigs : Array (UInt64 × UInt64) :=
          (bi.payload.map (fun e => (e.bHash, e.pdVarBloom))).toArray
        let entries := reps.getD key []
        if entries.any (fun e => densePdSigsCompatible e.sigs sigs && denseMsgEqCert singles e.bi bi)
        then
          let vk := densePdValHash bi
          drops := drops.insert vk (bi :: (drops.getD vk []))
        else
          reps := reps.insert key ({ pos := 0, bi, sigs, kept := true } :: entries)
  return drops

/-- Drop `bi` iff its value bucket holds a certified dropped twin. The `{b // densePdKeep … = false}`
    subtype is load-bearing: each stored entry carries its own `densePdKeep = false` proof. -/
def densePdVerdictKeep {p : ℕ} {P : BusInteraction (DenseExpr p) → Prop}
    (verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) // P b }))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match verdicts[densePdValHash bi]? with
  | some l => !(l.any (fun b => decide (b.val = bi)))
  | none => true

/-- A `densePdVerdictKeep` drop carries its certificate (the bucket entry equals `bi`). -/
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

/-- Pointwise-duplicate drop (part C): a stateless interaction (e.g. a range check) is dropped when
    an earlier kept interaction sends a message equal to it at every point of the shared finite
    domain box — the duplicate check is redundant. The fast `densePdDropSet` sweep flags the drops;
    `densePdKeep` re-verifies each once per distinct value. Prime `p` only; identity otherwise. -/
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
