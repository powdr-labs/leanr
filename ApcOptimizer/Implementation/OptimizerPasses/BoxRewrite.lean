import ApcOptimizer.Implementation.OptimizerPasses.FlagFoldDrops
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Dense box-certified multilinear rewriting — flagFold's `boxRewritePass` sub-pass

Runtime definitions for `boxRewrite` (proof in `Proofs/BoxRewrite.lean`). `denseBoxRewriteF` takes its
OWN `DegreeBound` (to decide "over-bound" and rewrite payloads), not the outer `guardDegree`
wrapper's.

`denseMulMono` and `denseCanonEq` each `List.mergeSort` on `VarId.index` only to turn equal
multisets into syntactically equal lists, regardless of construction order; the exact key is
irrelevant, the two lists just need the same total order. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The heuristic reducer -/

/-- Merge-insert a monomial into a sorted association list. -/
def denseAddMono (m : List VarId) (c : ZMod p) :
    List (List VarId × ZMod p) → List (List VarId × ZMod p)
  | [] => [(m, c)]
  | (m', c') :: rest =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: denseAddMono m c rest

/-- Multiply two variable multisets, capping exponents of `boolSet` members at one. Sorts by
    `VarId.index` for canonical merging. -/
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

/-- Constant-solution map for a box point (used with `substF`). -/
def densePtFun (pt : List (VarId × ZMod p)) : VarId → Option (DenseExpr p) :=
  fun v => if pt.any (fun t => t.1 == v) then some (DenseExpr.const (denseEnvOfFast pt v)) else none

/-- Canonical equality of normalized linear forms: equal constants and equal index-sorted term
    lists. -/
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

/-- Rewrites every over-bound expression to a certified lower-degree equivalent by reducing
    multilinearly over small-domain (boxed) variables — e.g. for a boolean `x`, `x * x` collapses to
    `x`. The reduction is heuristic; `denseBrCert` re-verifies it pointwise. -/
def DenseConstraintSystem.boxRewrite (d : DenseConstraintSystem p) (b : DegreeBound) :
    DenseConstraintSystem p :=
  let singles := denseSingleVarCs d.algebraicConstraints
  { algebraicConstraints := d.algebraicConstraints.map (denseBrRw singles b.identities),
    busInteractions := d.busInteractions.map (denseBrBi singles b) }

/-- The rewriter as a standalone pass runtime: guarded on `p` prime (re-checked at runtime),
    identity otherwise. -/
def denseBoxRewriteF (pw : PrimeWitness p) (b : DegreeBound) (_bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then d.boxRewrite b else d

end ApcOptimizer.Dense
