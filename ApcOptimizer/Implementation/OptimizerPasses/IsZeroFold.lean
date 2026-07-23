import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Multi-limb is-zero constraint fold — dense `VarId` port (impl-only)

Folds a group of per-limb zero constraints `L·vᵢ = 0` (all sharing one factor `L`, each `vᵢ` a
byte-bounded variable not occurring in `L`) into a single `L·(Σvᵢ) = 0`, dropping the members. This
recognizes the un-collapsed branch-on-zero cluster left after `monicScale`/`seqzCollapse`
(`(-1 + cmp)·aᵢ = 0` for BNE, `cmp·aᵢ = 0` for BEQ). Bus interactions are untouched. Soundness (in
`Proofs/IsZeroFold.lean`) rests on the byte bounds of the `vᵢ` (from bus-6 op-0 pair checks, via
`denseBuild`) plus a no-wraparound argument: a bounded sum of bytes that is `0` in `ZMod p` forces
each summand to `0`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `v₀ + (v₁ + … + 0)`, the folded limb sum. -/
def denseSumVars : List VarId → DenseExpr p
  | [] => .const 0
  | v :: rest => .add (.var v) (denseSumVars rest)

/-- Recognize a per-limb zero constraint `L·v = 0` written `.mul L (.var v)` with `v` not occurring
    in `L` (the latter excludes a booleanity `cmp·(cmp − 1)` written `(cmp − 1)·cmp`). -/
def denseIsZeroMember? : DenseExpr p → Option (DenseExpr p × VarId)
  | .mul L (.var v) => if L.mentions v then none else some (L, v)
  | _ => none

/-- The byte-bounded members sharing factor `L`, in first-occurrence order, deduped. -/
def denseIsZeroGroupVars (Bm : Std.HashMap VarId Nat) (ms : List (DenseExpr p × VarId))
    (L : DenseExpr p) : List VarId :=
  (((ms.filter (fun m => m.1 == L)).map Prod.snd).dedup).filter (fun v =>
    match Bm[v]? with | some b => decide (b ≤ 256) | none => false)

/-- All conditions making the fold of group `(L, vs)` sound: prime field with `256·|vs| ≤ p` (no
    wraparound), at least two members, each byte-bounded (`Bm`) and present as `L·v = 0`. -/
def denseIsZeroPlanOK (pw : PrimeWitness p) (Bm : Std.HashMap VarId Nat)
    (d : DenseConstraintSystem p) (L : DenseExpr p) (vs : List VarId) : Bool :=
  pw.isPrime && decide (2 ≤ vs.length) && decide (256 * vs.length ≤ p) &&
  vs.all (fun v => match Bm[v]? with | some b => decide (b ≤ 256) | none => false) &&
  vs.all (fun v => d.algebraicConstraints.contains (DenseExpr.mul L (.var v)))

/-- The first foldable group: the earliest recognized factor `L` whose byte-bounded members
    (`denseIsZeroGroupVars`) pass `denseIsZeroPlanOK`. -/
def denseIsZeroFindPlan (pw : PrimeWitness p) (Bm : Std.HashMap VarId Nat)
    (d : DenseConstraintSystem p) : Option (DenseExpr p × List VarId) :=
  let ms := d.algebraicConstraints.filterMap denseIsZeroMember?
  ms.findSome? (fun m =>
    let vs := denseIsZeroGroupVars Bm ms m.1
    if denseIsZeroPlanOK pw Bm d m.1 vs then some (m.1, vs) else none)

/-- Drop the group members `L·vᵢ = 0` and append the single folded `L·(Σvᵢ) = 0`; bus untouched. -/
def denseIsZeroFoldSystem (d : DenseConstraintSystem p) (L : DenseExpr p) (vs : List VarId) :
    DenseConstraintSystem p :=
  { d with algebraicConstraints :=
      (d.algebraicConstraints.filter
        (fun c => !((vs.map (fun v => DenseExpr.mul L (.var v))).contains c)))
      ++ [DenseExpr.mul L (denseSumVars vs)] }

/-- Folds a maximal group of per-limb zero constraints `L·vᵢ = 0` — same affine factor `L`, each
    `vᵢ` a byte-bounded variable not in `L` — into one `L·(Σvᵢ) = 0` (dropping the members). For
    the branch-on-zero cluster `(-1 + cmp)·a₀ = … = (-1 + cmp)·a₃ = 0` this yields the single
    `(-1 + cmp)·(a₀ + a₁ + a₂ + a₃) = 0`. -/
def denseIsZeroFoldF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  match denseIsZeroFindPlan pw (denseBuild bs facts d.busInteractions) d with
  | some (L, vs) => denseIsZeroFoldSystem d L vs
  | none => d

end ApcOptimizer.Dense
