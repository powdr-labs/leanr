import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import Batteries.Data.BinaryHeap

set_option autoImplicit false

/-! # Dense Gauss elimination: pivot scoring, the loop, the transform.
Correctness and the wired `denseGaussElimPass` live in `Proofs/Gauss.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Fold variable leaves in left-to-right order without materializing `vars`. -/
def DenseExpr.foldVars {α : Type} (e : DenseExpr p) (f : α → VarId → α) (init : α) : α :=
  match e with
  | .const _ => init
  | .var x => f init x
  | .add a b => b.foldVars f (a.foldVars f init)
  | .mul a b => b.foldVars f (a.foldVars f init)

def DenseExpr.isVar : DenseExpr p → Bool
  | .var _ => true
  | _ => false

/-- The occurrence-weighted duplication cost of pivoting on `v`, with a protection penalty. -/
def denseGaussScore (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId)
    (oc : Nat) : Nat :=
  let base := (occ.getD v 1 - 1) * (1 + oc)
  if prot.contains v then base + 1000000 else base

/-- One index step: add `t`'s coefficient and one occurrence to `t.1`'s entry (0 if absent). -/
def denseIdxStep (m : Std.HashMap VarId (ZMod p × Nat)) (t : VarId × ZMod p) :
    Std.HashMap VarId (ZMod p × Nat) :=
  m.insert t.1 (((m[t.1]?).getD (0, 0)).1 + t.2, ((m[t.1]?).getD (0, 0)).2 + 1)

/-- The coefficient/occurrence index of a term list. -/
def denseCoeffIdx (terms : List (VarId × ZMod p)) : Std.HashMap VarId (ZMod p × Nat) :=
  terms.foldl denseIdxStep ∅

/-! ## Descriptors -/

/-- `±1`-pivot descriptor: `some (v, score)` exactly when `l.trySolve v` succeeds. -/
def densePm1Desc (idx : Std.HashMap VarId (ZMod p × Nat)) (total : Nat)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    Option (VarId × Nat) :=
  if ((idx[v]?).getD (0, 0)).1 = 1 ∨ ((idx[v]?).getD (0, 0)).1 = -1 then
    some (v, denseGaussScore occ prot v (total - ((idx[v]?).getD (0, 0)).2))
  else none

/-- Unit-pivot descriptor: `some (v, score)` exactly when `l.trySolve v` fails but
    `l.trySolveUnit v` succeeds. -/
def denseUnitDesc (idx : Std.HashMap VarId (ZMod p × Nat)) (total : Nat)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    Option (VarId × Nat) :=
  if ¬(((idx[v]?).getD (0, 0)).1 = 1 ∨ ((idx[v]?).getD (0, 0)).1 = -1)
      ∧ ((idx[v]?).getD (0, 0)).1 * (((idx[v]?).getD (0, 0)).1)⁻¹ = 1 then
    some (v, denseGaussScore occ prot v (total - ((idx[v]?).getD (0, 0)).2))
  else none

/-- All pivot descriptors, `±1` first (matching the order of `densePm1PivotsOf ++
    denseUnitPivotsOf`). -/
def densePivotDescs (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    List (VarId × Nat) :=
  let idx := denseCoeffIdx l.terms
  let total := l.terms.length
  (l.terms.map Prod.fst).filterMap (densePm1Desc idx total occ prot)
    ++ (l.terms.map Prod.fst).filterMap (denseUnitDesc idx total occ prot)

/-! ## Boxed runtime twins -/

def denseIdxStepWith (ops : DenseZModOps p) (m : Std.HashMap VarId (ZMod p × Nat))
    (t : VarId × ZMod p) : Std.HashMap VarId (ZMod p × Nat) :=
  let old := (m[t.1]?).getD (ops.zero, 0)
  m.insert t.1 (ops.add old.1 t.2, old.2 + 1)

def denseCoeffIdxWith (ops : DenseZModOps p) :
    List (VarId × ZMod p) → Std.HashMap VarId (ZMod p × Nat) →
      Std.HashMap VarId (ZMod p × Nat)
  | [], m => m
  | t :: rest, m => denseCoeffIdxWith ops rest (denseIdxStepWith ops m t)

def denseCoeffIdxFast (terms : List (VarId × ZMod p)) : Std.HashMap VarId (ZMod p × Nat) :=
  let ops : DenseZModOps p := denseZModOps
  denseCoeffIdxWith ops terms ∅

theorem denseIdxStepWith_eq (ops : DenseZModOps p) (m : Std.HashMap VarId (ZMod p × Nat))
    (t : VarId × ZMod p) : denseIdxStepWith ops m t = denseIdxStep m t := by
  simp only [denseIdxStepWith, denseIdxStep, ops.zero_eq, ops.add_eq]

theorem denseCoeffIdxWith_eq (ops : DenseZModOps p) (terms : List (VarId × ZMod p))
    (m : Std.HashMap VarId (ZMod p × Nat)) :
    denseCoeffIdxWith ops terms m = terms.foldl denseIdxStep m := by
  induction terms generalizing m with
  | nil => rfl
  | cons t rest ih =>
    rw [denseCoeffIdxWith, denseIdxStepWith_eq, List.foldl_cons, ih]

@[csimp] theorem denseCoeffIdx_eq_fast : @denseCoeffIdx = @denseCoeffIdxFast := by
  funext p terms
  simp only [denseCoeffIdx, denseCoeffIdxFast, denseCoeffIdxWith_eq]

def densePm1DescWith (ops : DenseZModOps p) (idx : Std.HashMap VarId (ZMod p × Nat))
    (total : Nat) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    Option (VarId × Nat) :=
  let cv := (idx[v]?).getD (ops.zero, 0)
  if cv.1 = ops.one ∨ cv.1 = ops.negOne then
    some (v, denseGaussScore occ prot v (total - cv.2))
  else none

def denseUnitDescWith (ops : DenseZModOps p) (idx : Std.HashMap VarId (ZMod p × Nat))
    (total : Nat) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    Option (VarId × Nat) :=
  let cv := (idx[v]?).getD (ops.zero, 0)
  if ¬(cv.1 = ops.one ∨ cv.1 = ops.negOne) ∧
      ops.mul cv.1 cv.1⁻¹ = ops.one then
    some (v, denseGaussScore occ prot v (total - cv.2))
  else none

def densePivotDescsWith (ops : DenseZModOps p) (l : DenseLinExpr p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) : List (VarId × Nat) :=
  let idx := denseCoeffIdxWith ops l.terms ∅
  let total := l.terms.length
  (l.terms.map Prod.fst).filterMap (densePm1DescWith ops idx total occ prot) ++
    (l.terms.map Prod.fst).filterMap (denseUnitDescWith ops idx total occ prot)

def densePivotDescsFast (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) : List (VarId × Nat) :=
  let ops : DenseZModOps p := denseZModOps
  densePivotDescsWith ops l occ prot

theorem densePm1DescWith_eq (ops : DenseZModOps p) (idx : Std.HashMap VarId (ZMod p × Nat))
    (total : Nat) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    densePm1DescWith ops idx total occ prot v = densePm1Desc idx total occ prot v := by
  simp only [densePm1DescWith, densePm1Desc, ops.zero_eq, ops.one_eq, ops.negOne_eq]

theorem denseUnitDescWith_eq (ops : DenseZModOps p) (idx : Std.HashMap VarId (ZMod p × Nat))
    (total : Nat) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    denseUnitDescWith ops idx total occ prot v = denseUnitDesc idx total occ prot v := by
  simp only [denseUnitDescWith, denseUnitDesc, ops.zero_eq, ops.one_eq, ops.negOne_eq, ops.mul_eq]

theorem densePivotDescsWith_eq (ops : DenseZModOps p) (l : DenseLinExpr p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    densePivotDescsWith ops l occ prot = densePivotDescs l occ prot := by
  unfold densePivotDescsWith densePivotDescs denseCoeffIdx
  rw [denseCoeffIdxWith_eq]
  simp only [densePm1DescWith_eq, denseUnitDescWith_eq]

@[csimp] theorem densePivotDescs_eq_fast : @densePivotDescs = @densePivotDescsFast := by
  funext p l occ prot
  exact (densePivotDescsWith_eq denseZModOps l occ prot).symm

/-- Occurrence counts of every variable across the dense system (one traversal). -/
def denseOccurrenceMap (d : DenseConstraintSystem p) : Std.HashMap VarId Nat :=
  let addE := fun (m : Std.HashMap VarId Nat) (e : DenseExpr p) =>
    e.foldVars (fun m x => m.insert x (m.getD x 0 + 1)) m
  let m := d.algebraicConstraints.foldl addE ∅
  d.busInteractions.foldl (fun m bi => bi.payload.foldl addE (addE m bi.multiplicity)) m

/-- Variables occurring as a *raw* payload slot of a stateless interaction. -/
def denseProtectedVars (d : DenseConstraintSystem p) (bs : BusSemantics p) : Std.HashSet VarId :=
  d.busInteractions.foldl (init := ∅) fun s bi =>
    if bs.isStateful bi.busId then s
    else bi.payload.foldl (fun s e => match e with | .var x => s.insert x | _ => s) s

/-- A plain (proof-free) solution map keyed by `VarId`; correctness is established by the
    correctness proof (`Proofs/Gauss.lean`), not carried as a structure invariant. -/
structure DenseSolved (p : ℕ) where
  map : Std.HashMap VarId (DenseExpr p)
  revDeps : Std.HashMap VarId (Std.HashSet VarId)

namespace DenseSolved

def empty : DenseSolved p := { map := ∅, revDeps := ∅ }

/-- The map as a lookup function (what `substF` consumes). -/
def fn (dσ : DenseSolved p) : VarId → Option (DenseExpr p) := fun i => dσ.map[i]?

/-- Insert a list of pairs: for each, insert into the map and fold the value's variables into the
    reverse-dependency index. -/
def insertAll (dσ : DenseSolved p) : List (VarId × DenseExpr p) → DenseSolved p
  | [] => dσ
  | (x, t) :: rest =>
      DenseSolved.insertAll
        { map := dσ.map.insert x t,
          revDeps := t.foldVars (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert x)) dσ.revDeps }
        rest

theorem insertAll_map :
    ∀ (pairs : List (VarId × DenseExpr p)) (dσ : DenseSolved p),
      (dσ.insertAll pairs).map = pairs.foldl (fun m p => m.insert p.1 p.2) dσ.map := by
  intro pairs
  induction pairs with
  | nil => intro dσ; rfl
  | cons hd tl ih =>
      intro dσ; obtain ⟨x, t⟩ := hd
      simp only [insertAll, List.foldl_cons]
      rw [ih]

end DenseSolved

/-! ## Dynamic sparse scheduling -/

def DenseExpr.uniqueVars (e : DenseExpr p) : List VarId :=
  let st := e.foldVars (fun (out, seen) x =>
    if seen.contains x then (out, seen) else (x :: out, seen.insert x))
    (([], ∅) : List VarId × Std.HashSet VarId)
  st.1.reverse

/-- Substitute sparse affine rows into an affine row, preserving first-occurrence term order. -/
def denseLinSubstF (l : DenseLinExpr p) (σ : VarId → Option (DenseLinExpr p)) :
    DenseLinExpr p :=
  let const := l.terms.foldl (fun out yc =>
    match σ yc.1 with
    | some t => out + yc.2 * t.const
    | none => out) l.const
  let terms := l.terms.flatMap (fun yc =>
    match σ yc.1 with
    | some t => t.terms.map (fun zc => (zc.1, yc.2 * zc.2))
    | none => [yc])
  (DenseLinExpr.mk const terms).norm

/-- Substitute one canonical affine row into another. -/
def denseLinSubst (l : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p) : DenseLinExpr p :=
  denseLinSubstF l (fun y => if y = x then some t else none)

def denseLinAdd (a b : DenseLinExpr p) : DenseLinExpr p :=
  (a.add b).norm

def denseLinScale (k : ZMod p) (l : DenseLinExpr p) : DenseLinExpr p :=
  (l.scale k).norm

def DenseLinExpr.mentions (l : DenseLinExpr p) (x : VarId) : Bool :=
  l.terms.any (fun yc => yc.1 = x)

inductive DenseGaussReduced (p : ℕ) where
  | affine (row : DenseLinExpr p)
  | nonlinear (expr : DenseExpr p)

namespace DenseGaussReduced

def toExpr : DenseGaussReduced p → DenseExpr p
  | .affine row => row.toExpr
  | .nonlinear expr => expr

def vars : DenseGaussReduced p → List VarId
  | .affine row => row.terms.map Prod.fst
  | .nonlinear expr => expr.uniqueVars

def fromExpr (e : DenseExpr p) : DenseGaussReduced p :=
  match denseLinearize e with
  | some row => .affine row.norm
  | none =>
      let normalized := e.normalize
      match denseLinearize normalized with
      | some row => .affine row.norm
      | none => .nonlinear normalized

end DenseGaussReduced

def denseReducedAdd (ra rb : DenseGaussReduced p) : DenseGaussReduced p :=
  match ra, rb with
  | .affine la, .affine lb => .affine (denseLinAdd la lb)
  | _, _ => .nonlinear (.add ra.toExpr rb.toExpr)

def denseReducedMul (ra rb : DenseGaussReduced p) : DenseGaussReduced p :=
  match ra, rb with
  | .affine la, .affine lb =>
      if la.terms.isEmpty then .affine (denseLinScale la.const lb)
      else if lb.terms.isEmpty then .affine (denseLinScale lb.const la)
      else .nonlinear (.mul la.toExpr lb.toExpr)
  | _, _ => .nonlinear (.mul ra.toExpr rb.toExpr)

/-- Simultaneous sparse substitution and affine normalization, retaining expressions only for
    genuinely nonlinear subtrees. -/
def denseSparseSubstF (σ : VarId → Option (DenseLinExpr p)) : DenseExpr p → DenseGaussReduced p
  | .const n => .affine ⟨n, []⟩
  | .var x =>
      match σ x with
      | some row => .affine row
      | none => .affine ⟨0, [(x, 1)]⟩
  | e@(.add a b) =>
      match denseLinearize e with
      | some row => .affine (denseLinSubstF row σ)
      | none =>
          let ra := denseSparseSubstF σ a
          let rb := denseSparseSubstF σ b
          denseReducedAdd ra rb
  | e@(.mul a b) =>
      match denseLinearize e with
      | some row => .affine (denseLinSubstF row σ)
      | none =>
          let ra := denseSparseSubstF σ a
          let rb := denseSparseSubstF σ b
          denseReducedMul ra rb

def denseReducedSubst (r : DenseGaussReduced p) (x : VarId)
    (t : DenseLinExpr p) : DenseGaussReduced p :=
  match r with
  | .affine row => .affine (denseLinSubst row x t)
  | .nonlinear expr => denseSparseSubstF (fun y => if y = x then some t else none) expr

structure DenseSparseSolved (p : ℕ) where
  map : Std.HashMap VarId (DenseLinExpr p)
  revDeps : Std.HashMap VarId (Std.HashSet VarId)

namespace DenseSparseSolved

def empty : DenseSparseSolved p := { map := ∅, revDeps := ∅ }

def fn (dσ : DenseSparseSolved p) : VarId → Option (DenseLinExpr p) := fun i => dσ.map[i]?

def insertAll (dσ : DenseSparseSolved p) :
    List (VarId × DenseLinExpr p) → DenseSparseSolved p
  | [] => dσ
  | (x, t) :: rest =>
      DenseSparseSolved.insertAll
        { map := dσ.map.insert x t
          revDeps := t.terms.foldl
            (fun rd zc => rd.insert zc.1 (((rd[zc.1]?).getD ∅).insert x)) dσ.revDeps }
        rest

def materialize (dσ : DenseSparseSolved p) : DenseSolved p :=
  let map := dσ.map.toList.foldl
    (fun out xt => out.insert xt.1 xt.2.toExpr) (∅ : Std.HashMap VarId (DenseExpr p))
  { map, revDeps := ∅ }

end DenseSparseSolved

def denseSparseSolveAt (l : DenseLinExpr p) (x : VarId) :
    Option (VarId × DenseLinExpr p) :=
  if l.coeff x = 1 then some (x, denseLinScale (-1) (l.others x))
  else if l.coeff x = -1 then some (x, l.others x)
  else if l.coeff x * (l.coeff x)⁻¹ = 1 then
    some (x, denseLinScale (-(l.coeff x)⁻¹) (l.others x))
  else none

def denseSparseBest (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) : Option (VarId × DenseLinExpr p) :=
  match (densePivotDescs l occ prot).argmin Prod.snd with
  | none => none
  | some (x, _) => denseSparseSolveAt l x

def denseReducedBest (r : DenseGaussReduced p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) : Option (VarId × DenseLinExpr p) :=
  match r with
  | .affine row => denseSparseBest row occ prot
  | .nonlinear _ => none

def denseSparseGaussLoop (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    List (DenseExpr p) → DenseSparseSolved p → DenseSparseSolved p
  | [], dσ => dσ
  | c :: rest, dσ =>
      let c' := denseSparseSubstF dσ.fn c
      match denseReducedBest c' occ prot with
      | none => denseSparseGaussLoop occ prot rest dσ
      | some (x, t) =>
          let touched := ((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
            (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))
          let pairs := touched.map (fun ys => (ys.1, denseLinSubst ys.2 x t)) ++ [(x, t)]
          denseSparseGaussLoop occ prot rest (dσ.insertAll pairs)

structure DenseMarkowitzPivot where
  var : VarId
  rhsNnz : Nat

structure DenseMarkowitzRow (p : ℕ) where
  rowId : Nat
  reduced : DenseGaussReduced p
  vars : List VarId
  pivots : List DenseMarkowitzPivot
  generation : Nat
  active : Bool

structure DenseMarkowitzEntry where
  isProtected : Nat
  fill : Nat
  rewrite : Nat
  localScore : Nat
  rowId : Nat
  pivot : VarId
  generation : Nat

def denseMarkowitzEntryBetter (a b : DenseMarkowitzEntry) : Bool :=
  if a.isProtected < b.isProtected then true
  else if b.isProtected < a.isProtected then false
  else if a.fill < b.fill then true
  else if b.fill < a.fill then false
  else if a.rewrite < b.rewrite then true
  else if b.rewrite < a.rewrite then false
  else if a.localScore < b.localScore then true
  else if b.localScore < a.localScore then false
  else if a.rowId < b.rowId then true
  else if b.rowId < a.rowId then false
  else if a.pivot.index < b.pivot.index then true
  else if b.pivot.index < a.pivot.index then false
  else a.generation < b.generation

def denseMarkowitzHeapLt (a b : DenseMarkowitzEntry) : Bool :=
  denseMarkowitzEntryBetter b a

abbrev DenseMarkowitzHeap :=
  Batteries.BinaryHeap DenseMarkowitzEntry denseMarkowitzHeapLt

structure DenseMarkowitzState (p : ℕ) where
  rows : Array (DenseMarkowitzRow p)
  degrees : Std.HashMap VarId Nat
  rowDeps : Std.HashMap VarId (Std.HashSet Nat)
  pivotRows : Std.HashMap VarId (Std.HashSet Nat)
  heap : DenseMarkowitzHeap

def denseMarkowitzPivots (r : DenseGaussReduced p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) : List DenseMarkowitzPivot :=
  match r with
  | .nonlinear _ => []
  | .affine l =>
      let idx := denseCoeffIdx l.terms
      let vars := l.terms.map Prod.fst
      let descs := vars.filterMap (densePm1Desc idx l.terms.length occ prot) ++
        vars.filterMap (denseUnitDesc idx l.terms.length occ prot)
      let out := descs.foldl (fun (out, seen) (x, _) =>
        if seen.contains x then (out, seen)
        else
          let cv := (idx[x]?).getD (0, 0)
          ({ var := x, rhsNnz := l.terms.length - cv.2 } :: out, seen.insert x))
        (([], ∅) : List DenseMarkowitzPivot × Std.HashSet VarId)
      out.1.reverse

def denseMarkowitzRow (rowId : Nat) (e : DenseExpr p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) (generation : Nat := 0) : DenseMarkowitzRow p :=
  let reduced := DenseGaussReduced.fromExpr e
  { rowId
    reduced
    vars := reduced.vars
    pivots := denseMarkowitzPivots reduced occ prot
    generation
    active := true }

def denseMarkowitzRefreshRow (r : DenseMarkowitzRow p) (x : VarId) (t : DenseLinExpr p)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) : DenseMarkowitzRow p :=
  let reduced := denseReducedSubst r.reduced x t
  { rowId := r.rowId
    reduced
    vars := reduced.vars
    pivots := denseMarkowitzPivots reduced occ prot
    generation := r.generation + 1
    active := true }

def denseMarkowitzDegreeAdd (m : Std.HashMap VarId Nat) (xs : List VarId) :
    Std.HashMap VarId Nat :=
  xs.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m

def denseMarkowitzDegreeSub (m : Std.HashMap VarId Nat) (xs : List VarId) :
    Std.HashMap VarId Nat :=
  xs.foldl (fun m x => m.insert x (m.getD x 0 - 1)) m

def denseMarkowitzIndexRow (idx : Std.HashMap VarId (Std.HashSet Nat))
    (rowId : Nat) (xs : List VarId) : Std.HashMap VarId (Std.HashSet Nat) :=
  xs.foldl (fun idx x => idx.insert x (((idx[x]?).getD ∅).insert rowId)) idx

def denseMarkowitzUnindexRow (idx : Std.HashMap VarId (Std.HashSet Nat))
    (rowId : Nat) (xs : List VarId) : Std.HashMap VarId (Std.HashSet Nat) :=
  xs.foldl (fun idx x => idx.insert x (((idx[x]?).getD ∅).erase rowId)) idx

def denseMarkowitzIndexPivots (idx : Std.HashMap VarId (Std.HashSet Nat))
    (rowId : Nat) (pivots : List DenseMarkowitzPivot) :
    Std.HashMap VarId (Std.HashSet Nat) :=
  pivots.foldl
    (fun idx q => idx.insert q.var (((idx[q.var]?).getD ∅).insert rowId)) idx

def denseMarkowitzUnindexPivots (idx : Std.HashMap VarId (Std.HashSet Nat))
    (rowId : Nat) (pivots : List DenseMarkowitzPivot) :
    Std.HashMap VarId (Std.HashSet Nat) :=
  pivots.foldl
    (fun idx q => idx.insert q.var (((idx[q.var]?).getD ∅).erase rowId)) idx

def denseMarkowitzEntryOf (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (dσ : DenseSparseSolved p) (st : DenseMarkowitzState p) (rowId : Nat)
    (r : DenseMarkowitzRow p) (q : DenseMarkowitzPivot) : DenseMarkowitzEntry :=
  let solvedDegree := ((dσ.revDeps[q.var]?).getD ∅).size
  let activeDegree := st.degrees.getD q.var 1
  { isProtected := if prot.contains q.var then 1 else 0
    fill := q.rhsNnz * (activeDegree - 1)
    rewrite := q.rhsNnz * solvedDegree
    localScore := denseGaussScore occ prot q.var q.rhsNnz
    rowId
    pivot := q.var
    generation := r.generation }

def denseMarkowitzBestEntry? (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (dσ : DenseSparseSolved p) (st : DenseMarkowitzState p) (rowId : Nat)
    (r : DenseMarkowitzRow p) : Option DenseMarkowitzEntry :=
  r.pivots.foldl (fun best q =>
    let entry := denseMarkowitzEntryOf occ prot dσ st rowId r q
    match best with
    | none => some entry
    | some old => if denseMarkowitzEntryBetter entry old then some entry else best) none

def denseMarkowitzPushRow (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (dσ : DenseSparseSolved p) (st : DenseMarkowitzState p) (rowId : Nat) :
    DenseMarkowitzState p :=
  match st.rows[rowId]? with
  | none => st
  | some r =>
      if !r.active then st
      else
        let r' := { r with generation := r.generation + 1 }
        let st' := { st with rows := st.rows.setIfInBounds rowId r' }
        match denseMarkowitzBestEntry? occ prot dσ st' rowId r' with
        | none => st'
        | some entry => { st' with heap := st'.heap.insert entry }

def denseMarkowitzBuild (constraints : List (DenseExpr p))
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) : DenseMarkowitzState p :=
  let base : DenseMarkowitzState p :=
    { rows := #[]
      degrees := ∅
      rowDeps := ∅
      pivotRows := ∅
      heap := ∅ }
  let indexed := constraints.foldl (fun st c =>
    let rowId := st.rows.size
    let r := denseMarkowitzRow rowId c occ prot
    { st with
      rows := st.rows.push r
      degrees := denseMarkowitzDegreeAdd st.degrees r.vars
      rowDeps := denseMarkowitzIndexRow st.rowDeps rowId r.vars
      pivotRows := denseMarkowitzIndexPivots st.pivotRows rowId r.pivots }) base
  indexed.rows.foldl (fun st r =>
    match denseMarkowitzBestEntry? occ prot DenseSparseSolved.empty st r.rowId r with
    | none => st
    | some entry => { st with heap := st.heap.insert entry }) indexed

def denseMarkowitzEntryValid (st : DenseMarkowitzState p)
    (entry : DenseMarkowitzEntry) : Bool :=
  match st.rows[entry.rowId]? with
  | none => false
  | some r =>
      r.active && r.generation == entry.generation

def denseMarkowitzPopValid : Nat → DenseMarkowitzState p →
    Option (DenseMarkowitzEntry × DenseMarkowitzState p)
  | 0, _ => none
  | fuel + 1, st =>
      let (entry?, heap) := st.heap.extractMax
      let st := { st with heap }
      match entry? with
      | none => none
      | some entry =>
          if denseMarkowitzEntryValid st entry then some (entry, st)
          else denseMarkowitzPopValid fuel st

def denseMarkowitzCollectIds (idx : Std.HashMap VarId (Std.HashSet Nat))
    (xs : Std.HashSet VarId) : Std.HashSet Nat :=
  xs.toList.foldl (fun out x =>
    ((idx[x]?).getD ∅).toList.foldl (fun out rowId => out.insert rowId) out) ∅

def denseMarkowitzRekey (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (dσ : DenseSparseSolved p) (changed : Std.HashSet VarId) (st : DenseMarkowitzState p) :
    DenseMarkowitzState p :=
  (denseMarkowitzCollectIds st.pivotRows changed).toList.foldl
    (denseMarkowitzPushRow occ prot dσ) st

def denseMarkowitzRefreshRows (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (x : VarId) (t : DenseLinExpr p) (st : DenseMarkowitzState p) :
    DenseMarkowitzState p × Std.HashSet VarId :=
  let rowIds := ((st.rowDeps[x]?).getD ∅).toList
  rowIds.foldl (fun (st, changed) rowId =>
    match st.rows[rowId]? with
    | none => (st, changed)
    | some r =>
        if !r.active || !r.vars.contains x then (st, changed)
        else
          let r' := denseMarkowitzRefreshRow r x t occ prot
          let changed := (r.vars ++ r'.vars).foldl (fun s y => s.insert y) changed
          ({ st with
              rows := st.rows.setIfInBounds rowId r'
              degrees := denseMarkowitzDegreeAdd
                (denseMarkowitzDegreeSub st.degrees r.vars) r'.vars
              rowDeps := denseMarkowitzIndexRow
                (denseMarkowitzUnindexRow st.rowDeps rowId r.vars) rowId r'.vars
              pivotRows := denseMarkowitzIndexPivots
                (denseMarkowitzUnindexPivots st.pivotRows rowId r.pivots) rowId r'.pivots },
            changed)) (st, ∅)

def denseMarkowitzDeactivate (rowId : Nat) (st : DenseMarkowitzState p) :
    DenseMarkowitzState p × Std.HashSet VarId :=
  match st.rows[rowId]? with
  | none => (st, ∅)
  | some r =>
      let changed := r.vars.foldl (fun s x => s.insert x) ∅
      ({ st with
          rows := st.rows.setIfInBounds rowId
            { r with active := false, generation := r.generation + 1 }
          degrees := denseMarkowitzDegreeSub st.degrees r.vars
          rowDeps := denseMarkowitzUnindexRow st.rowDeps rowId r.vars
          pivotRows := denseMarkowitzUnindexPivots st.pivotRows rowId r.pivots },
        changed)

def denseMarkowitzAdoptPairs (dσ : DenseSparseSolved p) (x : VarId) (t : DenseLinExpr p) :
    List (VarId × DenseLinExpr p) :=
  let touched := ((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
    (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))
  touched.map (fun ys => (ys.1, denseLinSubst ys.2 x t)) ++ [(x, t)]

def denseMarkowitzAdopt (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (entry : DenseMarkowitzEntry) (x : VarId) (t : DenseLinExpr p)
    (pairs : List (VarId × DenseLinExpr p)) (st : DenseMarkowitzState p)
    (dσ : DenseSparseSolved p) : DenseMarkowitzState p :=
  let (st, selectedVars) := denseMarkowitzDeactivate entry.rowId st
  let (st, rowVars) := denseMarkowitzRefreshRows occ prot x t st
  let changed := pairs.foldl (fun changed yt =>
    yt.2.terms.foldl (fun changed yc => changed.insert yc.1) changed) (selectedVars ∪ rowVars)
  denseMarkowitzRekey occ prot dσ changed st

def denseMarkowitzPick (r : DenseGaussReduced p) (x : VarId) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) : Option (VarId × DenseLinExpr p) :=
  let hinted := match r with
    | .affine l => denseSparseSolveAt l x
    | .nonlinear _ => none
  match hinted with
  | some xt => some xt
  | none => denseReducedBest r occ prot

def denseMarkowitzLoop (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (sources : Array (DenseExpr p)) : Nat → DenseMarkowitzState p →
      DenseSparseSolved p → DenseSparseSolved p
  | 0, _, dσ => dσ
  | fuel + 1, st, dσ =>
      match denseMarkowitzPopValid (st.heap.size + 1) st with
      | none => dσ
      | some (entry, st) =>
          match sources[entry.rowId]? with
          | none => denseMarkowitzLoop occ prot sources fuel
              (denseMarkowitzDeactivate entry.rowId st).1 dσ
          | some c =>
              let c' := denseSparseSubstF dσ.fn c
              match denseMarkowitzPick c' entry.pivot occ prot with
              | none => denseMarkowitzLoop occ prot sources fuel
                  (denseMarkowitzDeactivate entry.rowId st).1 dσ
              | some (x, t) =>
                  let pairs := denseMarkowitzAdoptPairs dσ x t
                  let dσ := dσ.insertAll pairs
                  let st := denseMarkowitzAdopt occ prot entry x t pairs st dσ
                  denseMarkowitzLoop occ prot sources fuel
                    st dσ

def denseMarkowitzSchedule (constraints : List (DenseExpr p)) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) : DenseSparseSolved p :=
  let sources := constraints.toArray
  let st := denseMarkowitzBuild constraints occ prot
  denseMarkowitzLoop occ prot sources sources.size st DenseSparseSolved.empty

def denseSourceOrderSchedule (constraints : List (DenseExpr p))
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) : DenseSparseSolved p :=
  let first := denseSparseGaussLoop occ prot constraints DenseSparseSolved.empty
  if first.map.isEmpty then first else denseSparseGaussLoop occ prot constraints first

def denseMarkowitzMinRows : Nat := 8192

def denseGaussSchedule (constraints : List (DenseExpr p))
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) : DenseSolved p :=
  (if constraints.length < denseMarkowitzMinRows
    then denseSourceOrderSchedule constraints occ prot
    else denseMarkowitzSchedule constraints occ prot).materialize

theorem DenseLinExpr.others_terms_fst_mem (l : DenseLinExpr p) (v : VarId) (x : VarId)
    (h : x ∈ (l.others v).terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [DenseLinExpr.others, List.mem_map] at h ⊢
  obtain ⟨tt, htt, rfl⟩ := h
  exact ⟨tt, List.mem_of_mem_filter htt, rfl⟩

/-- Batch linear (Gauss) elimination. From a constraint like `x - 2*y - 3 = 0` it derives the
    assignment `x := 2*y + 3`, choosing pivots globally by dynamic Markowitz fill cost on large
    systems and preserving source order on smaller systems. -/
def denseGaussElim (bs : BusSemantics p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let occ := denseOccurrenceMap d
  let prot := denseProtectedVars d bs
  let solved := denseGaussSchedule d.algebraicConstraints occ prot
  if solved.map.isEmpty then d else d.substF solved.fn

/-- `denseGaussElim` as an explicit `if` (the `let` zeta-reduces). -/
theorem denseGaussElim_eq (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    denseGaussElim bs d =
      if (denseGaussSchedule d.algebraicConstraints
          (denseOccurrenceMap d) (denseProtectedVars d bs)).map.isEmpty
      then d
      else d.substF (denseGaussSchedule d.algebraicConstraints
          (denseOccurrenceMap d) (denseProtectedVars d bs)).fn := rfl

/-! `denseGaussElimPass` (the wired pass) is built and proved in `Proofs/Gauss.lean`. -/

end ApcOptimizer.Dense
