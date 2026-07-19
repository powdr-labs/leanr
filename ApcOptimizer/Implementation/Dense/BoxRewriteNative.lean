import ApcOptimizer.Implementation.Dense.FlagFoldDropsNative
import ApcOptimizer.Implementation.Dense.SubstMap

set_option autoImplicit false

/-! # Dense box-certified multilinear rewriting — flagFold's `boxRewritePass` sub-pass (Task 3,
busUnify cluster, chunk S4b — impl)

Dense, `VarId`-native transliteration of `OptimizerPasses/BoxRewrite.lean`'s **runtime**
definitions (`addMono`/`mulMono`/`polyOf`/`monoExpr`/`exprOfPoly`/`reduceExpr`, `ptFun`/`canonEq`/
`brCert`, `brRw`/`brBi`, `ConstraintSystem.boxRewrite`, `boxRewritePass`). This is the last unported
sub-pass of the scheduled composite `flagFoldPass'` (`BoxRewrite.lean:393`) — parts A
(`fxSubstPass`, `Dense/FxSubstNative.lean`) and B/C (`boxTautoDropPass`/`pointwiseDupDropPass`,
`Dense/FlagFoldDropsNative.lean`) are already ported. This file is **impl-only**: no theorem/lemma
from the spec file is ported (`envF_ptFun_self`, `brCert_sound`, `brRw_sound`, `brRw_vars`,
`brRw_singleVar`, `brBi_eval`, `ConstraintSystem.boxRewrite_correct` are all proof-side, the
prover's job), and no `DenseVerifiedPassW`/`DensePassCorrect` wrapper is built here — the top-level
transform `denseBoxRewriteF` is shaped exactly like `denseBoxTautoDropF`/`densePointwiseDupDropF`
(`Dense/FlagFoldDropsNative.lean`), so the prover wraps it directly with
`DenseVerifiedPassW.ofNative`. `flagFoldPass'` itself (the chain assembly) is chunk S5, not touched
here.

Notes on how spec pieces map here:

* **`boxRewritePass` is a fact-free `VerifiedPass p`** (`fun cs bs => …`), like the part B/C passes —
  it takes `pw` and a `DegreeBound b` (its OWN bound parameter, used to decide "over-bound" and to
  rewrite bus-interaction payloads, *not* the outer `guardDegree` wrapper's bound) and never reads
  `bs` at all except in the (proof-only) `PassCorrect` term. `denseBoxRewriteF` mirrors this exact
  shape: `(pw) (b) (_bs) (d)` — the drop-pass precedent's `(pw) (bs) (d)` plus the pass's own extra
  `DegreeBound` argument, unused `_bs` kept only for shape parity with the other `denseXxxF`
  transforms in this cluster (erased at the call site once the prover's `ofNative` wrapper ignores
  it too, exactly as `denseBoxTautoDropF`'s `_bs` already does).
* **`findDomainAlg`/`assignments`/`envOf` reuse.** Owned by `OptimizerPasses/DomainProp.lean`,
  already ported: `denseFindDomainAlg`/`denseAssignments` (`Dense/DomainFold.lean`, transitively
  imported here through `FlagFoldDropsNative → FlagUnifyNative → RootPairUnifyNative → DomainFold`)
  and `denseEnvOfFast` (`Dense/DomainBatch.lean`, transitively imported through `DomainFold`),
  reused unchanged — the S1–S3 precedent. As in `FlagFoldDropsNative.lean`, every spec `envOf` call
  in this file (`ptFun`'s point lookup) is ported to `denseEnvOfFast`, not a fresh `denseEnvOf`:
  for `VarId` the `envOf`/`envOfFast` split collapses (the whole point of `envOfFast` is to test the
  cheap `Variable.powdrId?` discriminator before the `Variable.name` `String` comparison — see
  `DomainBatch.lean:420–426` — but `VarId` equality is already a single `Nat` comparison, so there is
  only one sensible dense lookup).
* **`Expression.substF`/`linearize`/`LinExpr.norm` reuse.** Already ported unchanged:
  `DenseExpr.substF` (`Dense/SubstMap.lean`, imported explicitly — not on the transitive path from
  the rest of this cluster), `denseLinearize`/`DenseLinExpr` (`Dense/Affine.lean`, transitively
  imported through `Dense/Normalize.lean`), `DenseLinExpr.norm` (`Dense/Normalize.lean`, transitively
  imported).
* **`denseSingleVarCs` reuse.** Already ported in `Dense/FlagFoldDropsNative.lean` (chunk S3);
  reused unchanged (mirrors `singleVarCs`).

## The two Variable-keyed sort sites (representation-forced divergence, flagged per the standing
instructions)

The spec `mulMono` and `canonEq` each canonicalise a list by `List.mergeSort`ing on `Variable.name`
(a `String` order) before comparing/merging:

```
(a ++ b).mergeSort (fun u v => decide (u.name ≤ v.name))          -- mulMono
l1.terms.mergeSort (fun a b => decide (a.1.name ≤ b.1.name))      -- canonEq (×2)
```

Neither list is otherwise sorted or exposed — the sort exists purely so that two equal *multisets*
(of monomial variables in `mulMono`; of `(VarId, coeff)` terms up to permutation in `canonEq`,
after `LinExpr.norm`'s merge-by-first-occurrence already collapsed duplicates but did not sort) turn
into *syntactically equal lists*, regardless of the multiset's construction order. Since `VarId`
carries no name, this exact key is unavailable; per `VarId.md`/`VarIdAddendum.md` ("VarId sort keys
may replace Variable sort keys ONLY where the spec itself sorts") and the `domainFold` precedent
(`Dense/DomainFoldNative.lean`'s `denseTargetsV`, which replaced a `Variable`-`compare` mergeSort key
with `compare a.index b.index`), both sites below sort by **`VarId.index`** instead
(`decide (u.index ≤ v.index)`, the literal `≤`-for-`≤` substitution of the spec's
`decide (u.name ≤ v.name)`). This is a total, stable order exactly like the `String` order it
replaces, so `mergeSort`'s adjacency/merge behaviour is preserved bit-for-bit modulo the relabelling
— it changes *which* permutation of a tied multiset is produced, never *whether* two multisets
match. `mulMono`'s output is itself never read on its own (only equality-compared inside `addMono`,
and rebuilt back to an expression by `monoExpr`, which folds over it in whatever order it comes in —
so a different tie order changes the associativity of the rebuilt `mul` chain, not any decision).
`canonEq`'s two sorted lists come from the SAME two-list comparison, so a consistent order is all
correctness needs. **LOUD FLAG for the prover**: these are the one class of representation-forced
divergence in this chunk; no other sort/hash/order-sensitive site exists in `BoxRewrite.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The heuristic reducer -/

/-- Merge-insert a monomial into a sorted association list. Mirrors `addMono`. -/
def denseAddMono (m : List VarId) (c : ZMod p) :
    List (List VarId × ZMod p) → List (List VarId × ZMod p)
  | [] => [(m, c)]
  | (m', c') :: rest =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: denseAddMono m c rest

/-- Multiply two variable multisets, capping exponents of `boolSet` members at one. Keeps lists
    sorted by `VarId.index` for canonical merging (the spec sorts by `Variable.name`; see the
    module header's flagged divergence). Mirrors `mulMono`. -/
def denseMulMono (boolSet : List VarId) (a b : List VarId) : List VarId :=
  ((a ++ b).mergeSort (fun u v => decide (u.index ≤ v.index))).foldl
    (fun acc v =>
      match acc.head? with
      | some w => if w = v ∧ v ∈ boolSet then acc else v :: acc
      | none => [v]) []

/-- Sparse monomial expansion (with boolean exponent capping); `none` when the monomial count
    exceeds the cap. Heuristic only. Mirrors `polyOf`. -/
def densePolyOf (boolSet : List VarId) : DenseExpr p →
    Option (List (List VarId × ZMod p))
  | .const c => some [([], c)]
  | .var v => some [([v], 1)]
  | .add a b => do
    let pa ← densePolyOf boolSet a
    let pb ← densePolyOf boolSet b
    let r := pb.foldl (fun acc mc => denseAddMono mc.1 mc.2 acc) pa
    if r.length ≤ 64 then some r else none
  | .mul a b => do
    let pa ← densePolyOf boolSet a
    let pb ← densePolyOf boolSet b
    let r := pa.foldl (fun acc ma =>
      pb.foldl (fun acc2 mb =>
        denseAddMono (denseMulMono boolSet ma.1 mb.1) (ma.2 * mb.2) acc2) acc) []
    if r.length ≤ 64 then some r else none

/-- One monomial as an expression. Mirrors `monoExpr`. -/
def denseMonoExpr (mc : List VarId × ZMod p) : DenseExpr p :=
  mc.1.foldl (fun m v => DenseExpr.mul m (DenseExpr.var v)) (DenseExpr.const mc.2)

/-- Rebuild an expression from monomials (dropping zero coefficients). Mirrors `exprOfPoly`. -/
def denseExprOfPoly (ms : List (List VarId × ZMod p)) : DenseExpr p :=
  match ms.filter (fun mc => !(mc.2 == 0)) with
  | [] => DenseExpr.const 0
  | mc :: rest => rest.foldl (fun acc mc' => DenseExpr.add acc (denseMonoExpr mc')) (denseMonoExpr mc)

/-- The heuristic multilinear reduction. Mirrors `reduceExpr`. -/
def denseReduceExpr (boolSet : List VarId) (e : DenseExpr p) : Option (DenseExpr p) :=
  (densePolyOf boolSet e).map denseExprOfPoly

/-! ## The certificate -/

/-- Constant-solution map for a box point (used with `substF`). Mirrors `ptFun`, reusing
    `denseEnvOfFast` for the lookup (see the module header). -/
def densePtFun (pt : List (VarId × ZMod p)) : VarId → Option (DenseExpr p) :=
  fun v => if pt.any (fun t => t.1 == v) then some (DenseExpr.const (denseEnvOfFast pt v)) else none

/-- Canonical equality of normalized linear forms: equal constants and equal index-sorted term
    lists (the spec sorts by `Variable.name`; see the module header's flagged divergence). Mirrors
    `canonEq`. -/
def denseCanonEq (l1 l2 : DenseLinExpr p) : Bool :=
  l1.const == l2.const &&
  l1.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))
    == l2.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))

/-- Certificate: on every point of the joint small-domain box, both expressions partially evaluate
    to the same affine form in the remaining symbolic variables. Mirrors `brCert`. -/
def denseBrCert (singles : List (DenseExpr p)) (e e' : DenseExpr p) : Bool :=
  2 ≤ e.vars.eraseDups.length &&
  (let jv := (e.vars ++ e'.vars).eraseDups
   let boxed := jv.filter (fun v =>
     match denseFindDomainAlg singles v with
     | some d => d.length ≤ 2
     | none => false)
   let doms := boxed.filterMap (fun v =>
     (denseFindDomainAlg singles v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = boxed) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 16) &&
   (denseAssignments doms).all (fun pt =>
     match denseLinearize (e.substF (densePtFun pt)), denseLinearize (e'.substF (densePtFun pt)) with
     | some l1, some l2 => denseCanonEq l1.norm l2.norm
     | _, _ => false))

/-! ## The pass -/

/-- Per-expression rewrite: only over-bound expressions, only when the reduction is within bound,
    introduces no variable, and is certified. Mirrors `brRw`. -/
def denseBrRw (singles : List (DenseExpr p)) (bound : Nat) (e : DenseExpr p) : DenseExpr p :=
  if e.degree ≤ bound then e
  else
    let boolSet := e.vars.eraseDups.filter (fun v =>
      match denseFindDomainAlg singles v with
      | some d => d.length ≤ 2
      | none => false)
    match denseReduceExpr boolSet e with
    | some e' =>
      if e'.degree ≤ bound && e'.vars.all (fun v => v ∈ e.vars) && denseBrCert singles e e'
      then e' else e
    | none => e

/-- The per-interaction rewrite (bus id untouched). Mirrors `brBi`. -/
def denseBrBi (singles : List (DenseExpr p)) (db : DegreeBound)
    (bi : BusInteraction (DenseExpr p)) : BusInteraction (DenseExpr p) :=
  { busId := bi.busId,
    multiplicity := denseBrRw singles db.busInteractions bi.multiplicity,
    payload := bi.payload.map (denseBrRw singles db.busInteractions) }

/-- Rewrite every over-bound expression of the system to its certified reduction. Mirrors
    `ConstraintSystem.boxRewrite`. -/
def DenseConstraintSystem.boxRewrite (d : DenseConstraintSystem p) (b : DegreeBound) :
    DenseConstraintSystem p :=
  let singles := denseSingleVarCs d.algebraicConstraints
  { algebraicConstraints := d.algebraicConstraints.map (denseBrRw singles b.identities),
    busInteractions := d.busInteractions.map (denseBrBi singles b) }

/-- The rewriter as a standalone (unguarded) pass runtime: prime `p` only (re-checked at runtime,
    as elsewhere in this cluster); identity otherwise. Mirrors `boxRewritePass`'s computed output
    (dropping its `PassCorrect` term); shaped as `(pw) (b) (_bs) (d) → out` (see the module header).
    -/
def denseBoxRewriteF (pw : PrimeWitness p) (b : DegreeBound) (_bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then d.boxRewrite b else d

end ApcOptimizer.Dense
