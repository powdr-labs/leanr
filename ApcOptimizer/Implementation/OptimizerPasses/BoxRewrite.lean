import ApcOptimizer.Implementation.OptimizerPasses.FlagFoldDrops
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Dense box-certified multilinear rewriting — flagFold's `boxRewritePass` sub-pass

Runtime definitions for `boxRewrite`: `denseAddMono`/`denseMulMono`/`densePolyOf`/`denseMonoExpr`/
`denseExprOfPoly`/`denseReduceExpr`, `densePtFun`/`denseCanonEq`/`denseBrCert`,
`denseBrRw`/`denseBrBi`, `DenseConstraintSystem.boxRewrite`, `denseBoxRewriteF`. This file is
**impl-only**: it carries no soundness lemma, and no `DenseVerifiedPassW`/`DensePassCorrect`
wrapper is built here — the top-level transform `denseBoxRewriteF` is shaped exactly like
`denseBoxTautoDropF`/`densePointwiseDupDropF` (`FlagFoldDrops.lean`), so the prover wraps it
directly with `DenseVerifiedPassW.of`. `denseFlagFoldPass'` itself (the chain assembly,
`FlagFold.lean`) is not touched here.

Notes on the definitions below:

* **The pass takes its own `DegreeBound`.** `denseBoxRewriteF` takes `pw` and a `DegreeBound b` —
  its OWN bound parameter, used to decide "over-bound" and to rewrite bus-interaction payloads,
  *not* the outer `guardDegree` wrapper's bound — and never reads `bs` except for shape parity with
  the other `denseXxxF` transforms in this cluster (`_bs`, unused, erased at the call site once the
  prover's `of` wrapper ignores it too, exactly as `denseBoxTautoDropF`'s `_bs` already does).
* **`findDomainAlg`/`assignments`/`envOf` reuse.** `denseFindDomainAlg`/`denseAssignments`
  (`DomainFold.lean`, transitively imported here through `FlagFoldDrops → FlagUnify → RootPairUnify
  → DomainFold`) and `denseEnvOfFast` (`DomainBatch.lean`, transitively imported through
  `DomainFold`) are reused unchanged. As in `FlagFoldDrops.lean`, every point lookup in this file
  (`densePtFun`) goes through `denseEnvOfFast`: for `VarId` equality is already a single `Nat`
  comparison, so there is only one sensible dense lookup (no separate fast/slow variant is needed).
* **`Expression.substF`/`linearize`/`LinExpr.norm` reuse.** `DenseExpr.substF` (`SubstMap.lean`,
  imported explicitly — not on the transitive path from the rest of this cluster),
  `denseLinearize`/`DenseLinExpr` (`Affine.lean`, transitively imported through `Normalize.lean`),
  `DenseLinExpr.norm` (`Normalize.lean`, transitively imported).
* **`denseSingleVarCs` reuse.** Defined in `FlagFoldDrops.lean`; reused unchanged.

## The two `VarId`-keyed sort sites

`denseMulMono` and `denseCanonEq` each canonicalise a list by `List.mergeSort`ing on `VarId.index`
before comparing/merging:

```
(a ++ b).mergeSort (fun u v => decide (u.index ≤ v.index))          -- denseMulMono
l1.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))      -- denseCanonEq (×2)
```

Neither list is otherwise sorted or exposed — the sort exists purely so that two equal *multisets*
(of monomial variables in `denseMulMono`; of `(VarId, coeff)` terms up to permutation in
`denseCanonEq`, after `LinExpr.norm`'s merge-by-first-occurrence already collapsed duplicates but
did not sort) turn into *syntactically equal lists*, regardless of the multiset's construction
order. `VarId.index` gives a total, stable order for this purpose — it changes *which* permutation
of a tied multiset is produced, never *whether* two multisets match. `denseMulMono`'s output is
itself never read on its own (only equality-compared inside `denseAddMono`, and rebuilt back to an
expression by `denseMonoExpr`, which folds over it in whatever order it comes in — so a different
tie order changes the associativity of the rebuilt `mul` chain, not any decision). `denseCanonEq`'s
two sorted lists come from the SAME two-list comparison, so a consistent order is all correctness
needs. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The heuristic reducer -/

/-- Merge-insert a monomial into a sorted association list. -/
def denseAddMono (m : List VarId) (c : ZMod p) :
    List (List VarId × ZMod p) → List (List VarId × ZMod p)
  | [] => [(m, c)]
  | (m', c') :: rest =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: denseAddMono m c rest

/-- Multiply two variable multisets, capping exponents of `boolSet` members at one. Keeps lists
    sorted by `VarId.index` for canonical merging (see the module header). -/
def denseMulMono (boolSet : List VarId) (a b : List VarId) : List VarId :=
  ((a ++ b).mergeSort (fun u v => decide (u.index ≤ v.index))).foldl
    (fun acc v =>
      match acc.head? with
      | some w => if w = v ∧ v ∈ boolSet then acc else v :: acc
      | none => [v]) []

/-- Sparse monomial expansion (with boolean exponent capping); `none` when the monomial count
    exceeds the cap. Heuristic only. -/
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

/-- One monomial as an expression. -/
def denseMonoExpr (mc : List VarId × ZMod p) : DenseExpr p :=
  mc.1.foldl (fun m v => DenseExpr.mul m (DenseExpr.var v)) (DenseExpr.const mc.2)

/-- Rebuild an expression from monomials (dropping zero coefficients). -/
def denseExprOfPoly (ms : List (List VarId × ZMod p)) : DenseExpr p :=
  match ms.filter (fun mc => !(mc.2 == 0)) with
  | [] => DenseExpr.const 0
  | mc :: rest => rest.foldl (fun acc mc' => DenseExpr.add acc (denseMonoExpr mc')) (denseMonoExpr mc)

/-- The heuristic multilinear reduction. -/
def denseReduceExpr (boolSet : List VarId) (e : DenseExpr p) : Option (DenseExpr p) :=
  (densePolyOf boolSet e).map denseExprOfPoly

/-! ## The certificate -/

/-- Constant-solution map for a box point (used with `substF`). Reuses `denseEnvOfFast` for the
    lookup (see the module header). -/
def densePtFun (pt : List (VarId × ZMod p)) : VarId → Option (DenseExpr p) :=
  fun v => if pt.any (fun t => t.1 == v) then some (DenseExpr.const (denseEnvOfFast pt v)) else none

/-- Canonical equality of normalized linear forms: equal constants and equal index-sorted term
    lists (see the module header). -/
def denseCanonEq (l1 l2 : DenseLinExpr p) : Bool :=
  l1.const == l2.const &&
  l1.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))
    == l2.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))

/-- Certificate: on every point of the joint small-domain box, both expressions partially evaluate
    to the same affine form in the remaining symbolic variables. -/
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
    introduces no variable, and is certified. -/
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

/-- The per-interaction rewrite (bus id untouched). -/
def denseBrBi (singles : List (DenseExpr p)) (db : DegreeBound)
    (bi : BusInteraction (DenseExpr p)) : BusInteraction (DenseExpr p) :=
  { busId := bi.busId,
    multiplicity := denseBrRw singles db.busInteractions bi.multiplicity,
    payload := bi.payload.map (denseBrRw singles db.busInteractions) }

/-- Rewrite every over-bound expression of the system to its certified reduction. -/
def DenseConstraintSystem.boxRewrite (d : DenseConstraintSystem p) (b : DegreeBound) :
    DenseConstraintSystem p :=
  let singles := denseSingleVarCs d.algebraicConstraints
  { algebraicConstraints := d.algebraicConstraints.map (denseBrRw singles b.identities),
    busInteractions := d.busInteractions.map (denseBrBi singles b) }

/-- The rewriter as a standalone (unguarded) pass runtime: prime `p` only (re-checked at runtime,
    as elsewhere in this cluster); identity otherwise. Shaped as `(pw) (b) (_bs) (d) → out` (see
    the module header). -/
def denseBoxRewriteF (pw : PrimeWitness p) (b : DegreeBound) (_bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then d.boxRewrite b else d

end ApcOptimizer.Dense
