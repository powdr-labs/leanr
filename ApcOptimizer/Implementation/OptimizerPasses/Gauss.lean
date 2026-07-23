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

abbrev DenseGaussOcc := Array Nat
abbrev DenseGaussProt := ByteArray

/-- The occurrence-weighted duplication cost of pivoting on `v`, with a protection penalty. -/
def denseGaussScore (occ : DenseGaussOcc) (prot : DenseGaussProt) (v : VarId)
    (oc : Nat) : Nat :=
  let base := ((occ[v.index]?).getD 1 - 1) * (1 + oc)
  if (prot[v.index]?).getD 0 != 0 then base + 1000000 else base

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
    (occ : DenseGaussOcc) (prot : DenseGaussProt) (v : VarId) :
    Option (VarId × Nat) :=
  if ((idx[v]?).getD (0, 0)).1 = 1 ∨ ((idx[v]?).getD (0, 0)).1 = -1 then
    some (v, denseGaussScore occ prot v (total - ((idx[v]?).getD (0, 0)).2))
  else none

/-- Unit-pivot descriptor: `some (v, score)` exactly when `l.trySolve v` fails but
    `l.trySolveUnit v` succeeds. -/
def denseUnitDesc (idx : Std.HashMap VarId (ZMod p × Nat)) (total : Nat)
    (occ : DenseGaussOcc) (prot : DenseGaussProt) (v : VarId) :
    Option (VarId × Nat) :=
  if ¬(((idx[v]?).getD (0, 0)).1 = 1 ∨ ((idx[v]?).getD (0, 0)).1 = -1)
      ∧ ((idx[v]?).getD (0, 0)).1 * (((idx[v]?).getD (0, 0)).1)⁻¹ = 1 then
    some (v, denseGaussScore occ prot v (total - ((idx[v]?).getD (0, 0)).2))
  else none

/-- All pivot descriptors, `±1` first (matching the order of `densePm1PivotsOf ++
    denseUnitPivotsOf`). -/
def densePivotDescs (l : DenseLinExpr p) (occ : DenseGaussOcc) (prot : DenseGaussProt) :
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
    (total : Nat) (occ : DenseGaussOcc) (prot : DenseGaussProt) (v : VarId) :
    Option (VarId × Nat) :=
  let cv := (idx[v]?).getD (ops.zero, 0)
  if cv.1 = ops.one ∨ cv.1 = ops.negOne then
    some (v, denseGaussScore occ prot v (total - cv.2))
  else none

def denseUnitDescWith (ops : DenseZModOps p) (idx : Std.HashMap VarId (ZMod p × Nat))
    (total : Nat) (occ : DenseGaussOcc) (prot : DenseGaussProt) (v : VarId) :
    Option (VarId × Nat) :=
  let cv := (idx[v]?).getD (ops.zero, 0)
  if ¬(cv.1 = ops.one ∨ cv.1 = ops.negOne) ∧
      ops.mul cv.1 cv.1⁻¹ = ops.one then
    some (v, denseGaussScore occ prot v (total - cv.2))
  else none

def densePivotDescsWith (ops : DenseZModOps p) (l : DenseLinExpr p)
    (occ : DenseGaussOcc) (prot : DenseGaussProt) : List (VarId × Nat) :=
  let idx := denseCoeffIdxWith ops l.terms ∅
  let total := l.terms.length
  (l.terms.map Prod.fst).filterMap (densePm1DescWith ops idx total occ prot) ++
    (l.terms.map Prod.fst).filterMap (denseUnitDescWith ops idx total occ prot)

def densePivotDescsFast (l : DenseLinExpr p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) : List (VarId × Nat) :=
  let ops : DenseZModOps p := denseZModOps
  densePivotDescsWith ops l occ prot

theorem densePm1DescWith_eq (ops : DenseZModOps p) (idx : Std.HashMap VarId (ZMod p × Nat))
    (total : Nat) (occ : DenseGaussOcc) (prot : DenseGaussProt) (v : VarId) :
    densePm1DescWith ops idx total occ prot v = densePm1Desc idx total occ prot v := by
  simp only [densePm1DescWith, densePm1Desc, ops.zero_eq, ops.one_eq, ops.negOne_eq]

theorem denseUnitDescWith_eq (ops : DenseZModOps p) (idx : Std.HashMap VarId (ZMod p × Nat))
    (total : Nat) (occ : DenseGaussOcc) (prot : DenseGaussProt) (v : VarId) :
    denseUnitDescWith ops idx total occ prot v = denseUnitDesc idx total occ prot v := by
  simp only [denseUnitDescWith, denseUnitDesc, ops.zero_eq, ops.one_eq, ops.negOne_eq, ops.mul_eq]

theorem densePivotDescsWith_eq (ops : DenseZModOps p) (l : DenseLinExpr p)
    (occ : DenseGaussOcc) (prot : DenseGaussProt) :
    densePivotDescsWith ops l occ prot = densePivotDescs l occ prot := by
  unfold densePivotDescsWith densePivotDescs denseCoeffIdx
  rw [denseCoeffIdxWith_eq]
  simp only [densePm1DescWith_eq, denseUnitDescWith_eq]

@[csimp] theorem densePivotDescs_eq_fast : @densePivotDescs = @densePivotDescsFast := by
  funext p l occ prot
  exact (densePivotDescsWith_eq denseZModOps l occ prot).symm

/-- Occurrence counts of every variable across the dense system (one traversal). -/
def denseOccurrenceMap (capacity : Nat) (d : DenseConstraintSystem p) : DenseGaussOcc :=
  let addE := fun (m : DenseGaussOcc) (e : DenseExpr p) =>
    e.foldVars (fun m x =>
      m.setIfInBounds x.index ((m[x.index]?).getD 0 + 1)) m
  let m := d.algebraicConstraints.foldl addE (Array.replicate capacity 0)
  d.busInteractions.foldl
    (fun m bi => bi.payload.foldl addE (addE m bi.multiplicity)) m

/-- Variables occurring as a *raw* payload slot of a stateless interaction. -/
def denseProtectedVars (capacity : Nat) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) : DenseGaussProt :=
  d.busInteractions.foldl (init := ⟨Array.replicate capacity 0⟩) fun s bi =>
    if bs.isStateful bi.busId then s
    else bi.payload.foldl
      (fun s e => match e with | .var x => s.set! x.index 1 | _ => s) s

/-- A plain (proof-free) solution map keyed by `VarId`; correctness is established by the
    correctness proof (`Proofs/Gauss.lean`), not carried as a structure invariant. -/
structure DenseSolved (p : ℕ) where
  map : Std.HashMap VarId (DenseExpr p)
  revDeps : Std.HashMap VarId (Std.HashSet VarId)

namespace DenseSolved

def empty : DenseSolved p := { map := ∅, revDeps := ∅ }

/-- The map as a lookup function (what `substF` consumes). -/
def fn (dσ : DenseSolved p) : VarId → Option (DenseExpr p) := fun i => dσ.map[i]?

def insertRevDeps (owner : VarId) : DenseExpr p →
    Std.HashMap VarId (Std.HashSet VarId) → Std.HashMap VarId (Std.HashSet VarId)
  | .const _, rd => rd
  | .var x, rd => rd.insert x (((rd[x]?).getD ∅).insert owner)
  | .add a b, rd => insertRevDeps owner b (insertRevDeps owner a rd)
  | .mul a b, rd => insertRevDeps owner b (insertRevDeps owner a rd)

/-- Insert a list of pairs: for each, insert into the map and fold the value's variables into the
    reverse-dependency index. -/
def insertAll (dσ : DenseSolved p) : List (VarId × DenseExpr p) → DenseSolved p
  | [] => dσ
  | (x, t) :: rest =>
      DenseSolved.insertAll
        { map := dσ.map.insert x t,
          revDeps := insertRevDeps x t dσ.revDeps }
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
  let const := l.terms.foldl
    (fun out yc => if yc.1 = x then out + yc.2 * t.const else out) l.const
  let terms := l.terms.flatMap (fun yc =>
    if yc.1 = x then t.terms.map (fun zc => (zc.1, yc.2 * zc.2)) else [yc])
  (DenseLinExpr.mk const terms).norm

def denseLinAdd (a b : DenseLinExpr p) : DenseLinExpr p :=
  (a.add b).norm

def denseLinScale (k : ZMod p) (l : DenseLinExpr p) : DenseLinExpr p :=
  (l.scale k).norm

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

def denseSparseSubstOne (x : VarId) (t : DenseLinExpr p) : DenseExpr p → DenseGaussReduced p
  | .const n => .affine ⟨n, []⟩
  | .var y => if y = x then .affine t else .affine ⟨0, [(y, 1)]⟩
  | e@(.add a b) =>
      match denseLinearize e with
      | some row => .affine (denseLinSubst row x t)
      | none =>
          let ra := denseSparseSubstOne x t a
          let rb := denseSparseSubstOne x t b
          denseReducedAdd ra rb
  | e@(.mul a b) =>
      match denseLinearize e with
      | some row => .affine (denseLinSubst row x t)
      | none =>
          let ra := denseSparseSubstOne x t a
          let rb := denseSparseSubstOne x t b
          denseReducedMul ra rb

def denseReducedSubst (r : DenseGaussReduced p) (x : VarId)
    (t : DenseLinExpr p) : DenseGaussReduced p :=
  match r with
  | .affine row => .affine (denseLinSubst row x t)
  | .nonlinear expr => denseSparseSubstOne x t expr

structure DenseSparseSolved (p : ℕ) where
  rows : Array (Option (DenseLinExpr p))
  revDeps : Array (Std.HashSet VarId)
  rewriteSeen : Array (Std.HashSet VarId)
  supportMarks : ByteArray
  keys : Array VarId

namespace DenseSparseSolved

def empty (capacity : Nat) : DenseSparseSolved p :=
  { rows := Array.replicate capacity none
    revDeps := Array.replicate capacity ∅
    rewriteSeen := Array.replicate capacity ∅
    supportMarks := ⟨Array.replicate capacity 0⟩
    keys := #[] }

def lookup (dσ : DenseSparseSolved p) (x : VarId) : Option (DenseLinExpr p) :=
  (dσ.rows[x.index]?).join

def fn (dσ : DenseSparseSolved p) : VarId → Option (DenseLinExpr p) := dσ.lookup

def fnExpr (dσ : DenseSparseSolved p) : VarId → Option (DenseExpr p) :=
  fun x => (dσ.lookup x).map DenseLinExpr.toExpr

def deps (dσ : DenseSparseSolved p) (x : VarId) : Std.HashSet VarId :=
  (dσ.revDeps[x.index]?).getD ∅

def rewriteCount (dσ : DenseSparseSolved p) (x : VarId) : Nat :=
  ((dσ.rewriteSeen[x.index]?).getD ∅).size

def isEmpty (dσ : DenseSparseSolved p) : Bool := dσ.keys.isEmpty

def markOldDeps : DenseSparseSolved p → List (VarId × ZMod p) → DenseSparseSolved p
  | dσ, [] => dσ
  | dσ, yc :: rest =>
      markOldDeps { dσ with supportMarks := dσ.supportMarks.set! yc.1.index 1 } rest

def addNewDeps (owner : VarId) :
    DenseSparseSolved p → List (VarId × ZMod p) → DenseSparseSolved p
  | dσ, [] => dσ
  | dσ, yc :: rest =>
      if (dσ.supportMarks[yc.1.index]?).getD 0 == 0 then
        let bucket := ((dσ.revDeps[yc.1.index]?).getD ∅).insert owner
        let seen := ((dσ.rewriteSeen[yc.1.index]?).getD ∅).insert owner
        addNewDeps owner
          { dσ with
            revDeps := dσ.revDeps.setIfInBounds yc.1.index bucket
            rewriteSeen := dσ.rewriteSeen.setIfInBounds yc.1.index seen
            supportMarks := dσ.supportMarks.set! yc.1.index 2 } rest
      else
        addNewDeps owner
          { dσ with supportMarks := dσ.supportMarks.set! yc.1.index 2 } rest

def removeOldDeps (owner : VarId) :
    DenseSparseSolved p → List (VarId × ZMod p) → DenseSparseSolved p
  | dσ, [] => dσ
  | dσ, yc :: rest =>
      let mark := (dσ.supportMarks[yc.1.index]?).getD 0
      let dσ :=
        if mark == 1 then
          let bucket := ((dσ.revDeps[yc.1.index]?).getD ∅).erase owner
          { dσ with revDeps := dσ.revDeps.setIfInBounds yc.1.index bucket }
        else dσ
      removeOldDeps owner
        { dσ with supportMarks := dσ.supportMarks.set! yc.1.index 0 } rest

def clearNewDepMarks :
    DenseSparseSolved p → List (VarId × ZMod p) → DenseSparseSolved p
  | dσ, [] => dσ
  | dσ, yc :: rest =>
      clearNewDepMarks
        { dσ with supportMarks := dσ.supportMarks.set! yc.1.index 0 } rest

def diffDeps (dσ : DenseSparseSolved p) (owner : VarId)
    (oldTerms newTerms : List (VarId × ZMod p)) : DenseSparseSolved p :=
  let dσ := markOldDeps dσ oldTerms
  let dσ := addNewDeps owner dσ newTerms
  let dσ := removeOldDeps owner dσ oldTerms
  clearNewDepMarks dσ newTerms

def clearDeps (dσ : DenseSparseSolved p) (x : VarId) : DenseSparseSolved p :=
  { dσ with revDeps := dσ.revDeps.setIfInBounds x.index ∅ }

def replace (dσ : DenseSparseSolved p) (x : VarId)
    (t : DenseLinExpr p) : DenseSparseSolved p :=
  let old := dσ.lookup x
  let oldTerms := old.map (·.terms) |>.getD []
  let dσ := dσ.diffDeps x oldTerms t.terms
  { dσ with
    rows := dσ.rows.setIfInBounds x.index (some t)
    keys := if old.isSome || dσ.rows[x.index]?.isNone then dσ.keys else dσ.keys.push x }

end DenseSparseSolved

def denseSparseExprSubst (dσ : DenseSparseSolved p) : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var x =>
      match dσ.lookup x with
      | some row => row.toExpr
      | none => .var x
  | .add a b => .add (denseSparseExprSubst dσ a) (denseSparseExprSubst dσ b)
  | .mul a b => .mul (denseSparseExprSubst dσ a) (denseSparseExprSubst dσ b)

def denseSparseBISubst (dσ : DenseSparseSolved p)
    (bi : BusInteraction (DenseExpr p)) : BusInteraction (DenseExpr p) :=
  { busId := bi.busId
    multiplicity := denseSparseExprSubst dσ bi.multiplicity
    payload := bi.payload.map (denseSparseExprSubst dσ) }

def DenseConstraintSystem.substSparse
    (d : DenseConstraintSystem p) (dσ : DenseSparseSolved p) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map (denseSparseExprSubst dσ)
    busInteractions := d.busInteractions.map (denseSparseBISubst dσ) }

structure DenseSparseAdoption (p : ℕ) where
  solved : DenseSparseSolved p
  changed : Std.HashSet VarId

def denseSparseAdoptStep (trackChanged : Bool) (x : VarId) (t : DenseLinExpr p)
    (acc : DenseSparseAdoption p) (y : VarId) : DenseSparseAdoption p :=
  match acc.solved.lookup y with
  | none => acc
  | some row =>
      let row := denseLinSubst row x t
      let changed :=
        if trackChanged then
          row.terms.foldl (fun changed yc => changed.insert yc.1) acc.changed
        else acc.changed
      { solved := acc.solved.replace y row, changed }

def denseSparseAdopt (trackChanged : Bool) (dσ : DenseSparseSolved p) (x : VarId)
    (t : DenseLinExpr p) : DenseSparseAdoption p :=
  let touched := dσ.deps x
  let dσ := dσ.clearDeps x
  let changed :=
    if trackChanged then
      t.terms.foldl (fun changed yc => changed.insert yc.1)
        (Std.HashSet.emptyWithCapacity t.terms.length)
    else ∅
  let out := touched.fold (denseSparseAdoptStep trackChanged x t) { solved := dσ, changed }
  { out with solved := out.solved.replace x t }

def denseLinSubstSolved (l : DenseLinExpr p) (dσ : DenseSparseSolved p) :
    DenseLinExpr p :=
  let const := l.terms.foldl (fun out yc =>
    match dσ.lookup yc.1 with
    | some t => out + yc.2 * t.const
    | none => out) l.const
  let terms := l.terms.flatMap (fun yc =>
    match dσ.lookup yc.1 with
    | some t => t.terms.map (fun zc => (zc.1, yc.2 * zc.2))
    | none => [yc])
  (DenseLinExpr.mk const terms).norm

def denseSparseSubstSolved (dσ : DenseSparseSolved p) : DenseExpr p → DenseGaussReduced p
  | .const n => .affine ⟨n, []⟩
  | .var x =>
      match dσ.lookup x with
      | some row => .affine row
      | none => .affine ⟨0, [(x, 1)]⟩
  | e@(.add a b) =>
      match denseLinearize e with
      | some row => .affine (denseLinSubstSolved row dσ)
      | none =>
          let ra := denseSparseSubstSolved dσ a
          let rb := denseSparseSubstSolved dσ b
          denseReducedAdd ra rb
  | e@(.mul a b) =>
      match denseLinearize e with
      | some row => .affine (denseLinSubstSolved row dσ)
      | none =>
          let ra := denseSparseSubstSolved dσ a
          let rb := denseSparseSubstSolved dσ b
          denseReducedMul ra rb

def denseSparseSolveAt (l : DenseLinExpr p) (x : VarId) :
    Option (VarId × DenseLinExpr p) :=
  if l.coeff x = 1 then some (x, denseLinScale (-1) (l.others x))
  else if l.coeff x = -1 then some (x, l.others x)
  else if l.coeff x * (l.coeff x)⁻¹ = 1 then
    some (x, denseLinScale (-(l.coeff x)⁻¹) (l.others x))
  else none

def densePm1BestStepWith (ops : DenseZModOps p)
    (total : Nat) (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (best : Option (VarId × Nat)) (yc : VarId × ZMod p) : Option (VarId × Nat) :=
  if yc.2 = ops.one ∨ yc.2 = ops.negOne then
    let score := denseGaussScore occ prot yc.1 (total - 1)
    match best with
    | none => some (yc.1, score)
    | some old => if score < old.2 then some (yc.1, score) else best
  else best

def denseUnitBestStepWith (ops : DenseZModOps p)
    (total : Nat) (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (best : Option (VarId × Nat)) (yc : VarId × ZMod p) : Option (VarId × Nat) :=
  if ¬(yc.2 = ops.one ∨ yc.2 = ops.negOne) ∧
      ops.mul yc.2 yc.2⁻¹ = ops.one then
    let score := denseGaussScore occ prot yc.1 (total - 1)
    match best with
    | none => some (yc.1, score)
    | some old => if score < old.2 then some (yc.1, score) else best
  else best

def denseBestPivotWith (ops : DenseZModOps p) (l : DenseLinExpr p)
    (occ : DenseGaussOcc) (prot : DenseGaussProt) : Option (VarId × Nat) :=
  let total := l.terms.length
  l.terms.foldl (denseUnitBestStepWith ops total occ prot)
    (l.terms.foldl (densePm1BestStepWith ops total occ prot) none)

def denseBestPivot (l : DenseLinExpr p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) : Option (VarId × Nat) :=
  let ops : DenseZModOps p := denseZModOps
  denseBestPivotWith ops l occ prot

def denseSparseBest (l : DenseLinExpr p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) : Option (VarId × DenseLinExpr p) :=
  match denseBestPivot l occ prot with
  | none => none
  | some (x, _) => denseSparseSolveAt l x

def denseReducedBest (r : DenseGaussReduced p) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) : Option (VarId × DenseLinExpr p) :=
  match r with
  | .affine row => denseSparseBest row occ prot
  | .nonlinear _ => none

def denseSparseGaussLoop (occ : DenseGaussOcc) (prot : DenseGaussProt) :
    List (DenseExpr p) → DenseSparseSolved p → DenseSparseSolved p
  | [], dσ => dσ
  | c :: rest, dσ =>
      let c' := denseSparseSubstSolved dσ c
      match denseReducedBest c' occ prot with
      | none => denseSparseGaussLoop occ prot rest dσ
      | some (x, t) =>
          denseSparseGaussLoop occ prot rest (denseSparseAdopt false dσ x t).solved

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
  degrees : Array Nat
  rowDeps : Array (Std.HashSet Nat)
  pivotRows : Array (Std.HashSet Nat)
  heap : DenseMarkowitzHeap

def denseMarkowitzPm1StepWith (ops : DenseZModOps p)
    (total : Nat) (rev : List DenseMarkowitzPivot)
    (yc : VarId × ZMod p) : List DenseMarkowitzPivot :=
  if yc.2 = ops.one ∨ yc.2 = ops.negOne then
    { var := yc.1, rhsNnz := total - 1 } :: rev
  else rev

def denseMarkowitzUnitStepWith (ops : DenseZModOps p)
    (total : Nat) (rev : List DenseMarkowitzPivot)
    (yc : VarId × ZMod p) : List DenseMarkowitzPivot :=
  if ¬(yc.2 = ops.one ∨ yc.2 = ops.negOne) ∧
      ops.mul yc.2 yc.2⁻¹ = ops.one then
    { var := yc.1, rhsNnz := total - 1 } :: rev
  else rev

def denseMarkowitzPivots (r : DenseGaussReduced p) : List DenseMarkowitzPivot :=
  match r with
  | .nonlinear _ => []
  | .affine l =>
      let ops : DenseZModOps p := denseZModOps
      let total := l.terms.length
      let pm1 := l.terms.foldl (denseMarkowitzPm1StepWith ops total) []
      let unit := l.terms.foldl (denseMarkowitzUnitStepWith ops total) pm1
      unit.reverse

def denseMarkowitzRow (rowId : Nat) (e : DenseExpr p)
    (generation : Nat := 0) : DenseMarkowitzRow p :=
  let reduced := DenseGaussReduced.fromExpr e
  { rowId
    reduced
    vars := reduced.vars
    pivots := denseMarkowitzPivots reduced
    generation
    active := true }

def denseMarkowitzRefreshRow (r : DenseMarkowitzRow p) (x : VarId) (t : DenseLinExpr p)
    : DenseMarkowitzRow p :=
  let reduced := denseReducedSubst r.reduced x t
  { rowId := r.rowId
    reduced
    vars := reduced.vars
    pivots := denseMarkowitzPivots reduced
    generation := r.generation + 1
    active := true }

def denseMarkowitzDegreeAdd (degrees : Array Nat) (xs : List VarId) : Array Nat :=
  xs.foldl (fun degrees x =>
    degrees.setIfInBounds x.index ((degrees[x.index]?).getD 0 + 1)) degrees

def denseMarkowitzDegreeSub (degrees : Array Nat) (xs : List VarId) : Array Nat :=
  xs.foldl (fun degrees x =>
    degrees.setIfInBounds x.index ((degrees[x.index]?).getD 0 - 1)) degrees

def denseMarkowitzIndexRow (idx : Array (Std.HashSet Nat))
    (rowId : Nat) (xs : List VarId) : Array (Std.HashSet Nat) :=
  xs.foldl (fun idx x =>
    idx.setIfInBounds x.index (((idx[x.index]?).getD ∅).insert rowId)) idx

def denseMarkowitzUnindexRow (idx : Array (Std.HashSet Nat))
    (rowId : Nat) (xs : List VarId) : Array (Std.HashSet Nat) :=
  xs.foldl (fun idx x =>
    idx.setIfInBounds x.index (((idx[x.index]?).getD ∅).erase rowId)) idx

def denseMarkowitzIndexPivots (idx : Array (Std.HashSet Nat))
    (rowId : Nat) (pivots : List DenseMarkowitzPivot) :
    Array (Std.HashSet Nat) :=
  pivots.foldl
    (fun idx q =>
      idx.setIfInBounds q.var.index (((idx[q.var.index]?).getD ∅).insert rowId)) idx

def denseMarkowitzUnindexPivots (idx : Array (Std.HashSet Nat))
    (rowId : Nat) (pivots : List DenseMarkowitzPivot) :
    Array (Std.HashSet Nat) :=
  pivots.foldl
    (fun idx q =>
      idx.setIfInBounds q.var.index (((idx[q.var.index]?).getD ∅).erase rowId)) idx

def denseMarkowitzEntryOf (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (dσ : DenseSparseSolved p) (st : DenseMarkowitzState p) (rowId : Nat)
    (r : DenseMarkowitzRow p) (q : DenseMarkowitzPivot) : DenseMarkowitzEntry :=
  let solvedDegree := dσ.rewriteCount q.var
  let activeDegree := (st.degrees[q.var.index]?).getD 1
  { isProtected := if (prot[q.var.index]?).getD 0 != 0 then 1 else 0
    fill := q.rhsNnz * (activeDegree - 1)
    rewrite := q.rhsNnz * solvedDegree
    localScore := denseGaussScore occ prot q.var q.rhsNnz
    rowId
    pivot := q.var
    generation := r.generation }

def denseMarkowitzBestEntry? (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (dσ : DenseSparseSolved p) (st : DenseMarkowitzState p) (rowId : Nat)
    (r : DenseMarkowitzRow p) : Option DenseMarkowitzEntry :=
  r.pivots.foldl (fun best q =>
    let entry := denseMarkowitzEntryOf occ prot dσ st rowId r q
    match best with
    | none => some entry
    | some old => if denseMarkowitzEntryBetter entry old then some entry else best) none

def denseMarkowitzPushRow (occ : DenseGaussOcc) (prot : DenseGaussProt)
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
    (occ : DenseGaussOcc) (prot : DenseGaussProt) (capacity : Nat) :
    DenseMarkowitzState p :=
  let base : DenseMarkowitzState p :=
    { rows := #[]
      degrees := Array.replicate capacity 0
      rowDeps := Array.replicate capacity ∅
      pivotRows := Array.replicate capacity ∅
      heap := ∅ }
  let indexed := constraints.foldl (fun st c =>
    let rowId := st.rows.size
    let r := denseMarkowitzRow rowId c
    { st with
      rows := st.rows.push r
      degrees := denseMarkowitzDegreeAdd st.degrees r.vars
      rowDeps := denseMarkowitzIndexRow st.rowDeps rowId r.vars
      pivotRows := denseMarkowitzIndexPivots st.pivotRows rowId r.pivots }) base
  let emptySolved : DenseSparseSolved p := DenseSparseSolved.empty capacity
  indexed.rows.foldl (fun st r =>
    match denseMarkowitzBestEntry? occ prot emptySolved st r.rowId r with
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

def denseMarkowitzCollectIds (idx : Array (Std.HashSet Nat))
    (xs : Std.HashSet VarId) : Std.HashSet Nat :=
  xs.toList.foldl (fun out x =>
    ((idx[x.index]?).getD ∅).toList.foldl (fun out rowId => out.insert rowId) out)
    (Std.HashSet.emptyWithCapacity xs.size)

def denseMarkowitzRekey (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (dσ : DenseSparseSolved p) (changed : Std.HashSet VarId) (st : DenseMarkowitzState p) :
    DenseMarkowitzState p :=
  (denseMarkowitzCollectIds st.pivotRows changed).toList.foldl
    (denseMarkowitzPushRow occ prot dσ) st

def denseMarkowitzRefreshRows (x : VarId) (t : DenseLinExpr p)
    (st : DenseMarkowitzState p) :
    DenseMarkowitzState p × Std.HashSet VarId :=
  let rowIds := ((st.rowDeps[x.index]?).getD ∅).toList
  rowIds.foldl (fun (st, changed) rowId =>
    match st.rows[rowId]? with
    | none => (st, changed)
    | some r =>
        if !r.active || !r.vars.contains x then (st, changed)
        else
          let r' := denseMarkowitzRefreshRow r x t
          let changed := (r.vars ++ r'.vars).foldl (fun s y => s.insert y) changed
          ({ st with
              rows := st.rows.setIfInBounds rowId r'
              degrees := denseMarkowitzDegreeAdd
                (denseMarkowitzDegreeSub st.degrees r.vars) r'.vars
              rowDeps := denseMarkowitzIndexRow
                (denseMarkowitzUnindexRow st.rowDeps rowId r.vars) rowId r'.vars
              pivotRows := denseMarkowitzIndexPivots
                (denseMarkowitzUnindexPivots st.pivotRows rowId r.pivots) rowId r'.pivots },
            changed)) (st, Std.HashSet.emptyWithCapacity rowIds.length)

def denseMarkowitzDeactivate (rowId : Nat) (st : DenseMarkowitzState p) :
    DenseMarkowitzState p × Std.HashSet VarId :=
  match st.rows[rowId]? with
  | none => (st, ∅)
  | some r =>
      let changed := r.vars.foldl (fun s x => s.insert x)
        (Std.HashSet.emptyWithCapacity r.vars.length)
      ({ st with
          rows := st.rows.setIfInBounds rowId
            { r with active := false, generation := r.generation + 1 }
          degrees := denseMarkowitzDegreeSub st.degrees r.vars
          rowDeps := denseMarkowitzUnindexRow st.rowDeps rowId r.vars
          pivotRows := denseMarkowitzUnindexPivots st.pivotRows rowId r.pivots },
        changed)

def denseMarkowitzAdopt (occ : DenseGaussOcc) (prot : DenseGaussProt)
    (entry : DenseMarkowitzEntry) (x : VarId) (t : DenseLinExpr p)
    (solvedVars : Std.HashSet VarId) (st : DenseMarkowitzState p)
    (dσ : DenseSparseSolved p) : DenseMarkowitzState p :=
  let (st, selectedVars) := denseMarkowitzDeactivate entry.rowId st
  let (st, rowVars) := denseMarkowitzRefreshRows x t st
  let changed := solvedVars ∪ (selectedVars ∪ rowVars)
  denseMarkowitzRekey occ prot dσ changed st

def denseMarkowitzPick (r : DenseGaussReduced p) (x : VarId) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) : Option (VarId × DenseLinExpr p) :=
  let hinted := match r with
    | .affine l => denseSparseSolveAt l x
    | .nonlinear _ => none
  match hinted with
  | some xt => some xt
  | none => denseReducedBest r occ prot

def denseMarkowitzLoop (occ : DenseGaussOcc) (prot : DenseGaussProt)
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
              let c' := denseSparseSubstSolved dσ c
              match denseMarkowitzPick c' entry.pivot occ prot with
              | none => denseMarkowitzLoop occ prot sources fuel
                  (denseMarkowitzDeactivate entry.rowId st).1 dσ
              | some (x, t) =>
                  let adopted := denseSparseAdopt true dσ x t
                  let dσ := adopted.solved
                  let st := denseMarkowitzAdopt occ prot entry x t adopted.changed st dσ
                  denseMarkowitzLoop occ prot sources fuel
                    st dσ

def denseMarkowitzSchedule (constraints : List (DenseExpr p)) (occ : DenseGaussOcc)
    (prot : DenseGaussProt) (capacity : Nat) : DenseSparseSolved p :=
  let sources := constraints.toArray
  let st := denseMarkowitzBuild constraints occ prot capacity
  denseMarkowitzLoop occ prot sources sources.size st (DenseSparseSolved.empty capacity)

def denseSourceOrderSchedule (constraints : List (DenseExpr p))
    (occ : DenseGaussOcc) (prot : DenseGaussProt) (capacity : Nat) :
    DenseSparseSolved p :=
  let first := denseSparseGaussLoop occ prot constraints (DenseSparseSolved.empty capacity)
  if first.isEmpty then first else denseSparseGaussLoop occ prot constraints first

def denseMarkowitzMinRows : Nat := 8192

def denseGaussSparseSchedule (constraints : List (DenseExpr p))
    (occ : DenseGaussOcc) (prot : DenseGaussProt) (capacity : Nat) :
    DenseSparseSolved p :=
  if constraints.length < denseMarkowitzMinRows
    then denseSourceOrderSchedule constraints occ prot capacity
    else denseMarkowitzSchedule constraints occ prot capacity

theorem DenseLinExpr.others_terms_fst_mem (l : DenseLinExpr p) (v : VarId) (x : VarId)
    (h : x ∈ (l.others v).terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [DenseLinExpr.others, List.mem_map] at h ⊢
  obtain ⟨tt, htt, rfl⟩ := h
  exact ⟨tt, List.mem_of_mem_filter htt, rfl⟩

/-- Batch linear (Gauss) elimination. From a constraint like `x - 2*y - 3 = 0` it derives the
    assignment `x := 2*y + 3`, choosing pivots globally by dynamic Markowitz fill cost on large
    systems and preserving source order on smaller systems. -/
def denseGaussElimSized (capacity : Nat) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let occ := denseOccurrenceMap capacity d
  let prot := denseProtectedVars capacity d bs
  let solved := denseGaussSparseSchedule d.algebraicConstraints occ prot capacity
  if solved.isEmpty then d else d.substSparse solved

/-! `denseGaussElimPass` (the wired pass) is built and proved in `Proofs/Gauss.lean`. -/

end ApcOptimizer.Dense
