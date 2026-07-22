import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.ListSplit

set_option autoImplicit false

/-! # Dense Gauss elimination: scoring, the loop, the transform (Task 3, WP-E — Gauss foundation)

The `VarId`-native runtime of the batch linear-elimination pass, keyed on `VarId`/`DenseExpr`:

* the descriptor-based, `argmin`-free pivot scoring (mirroring the spec `occurrenceMap`/
  `protectedVars`/`pivotScore`, the `coeffIdx` index, the `pm1Desc`/`unitDesc` descriptors and
  `fastBest`) — `denseFastBest` builds the solution only for the winner, proved equal to the naive
  `argmin` over `densePm1PivotsOf ++ denseUnitPivotsOf` by `denseFastBest_eq`;
* the proof-free solution map `DenseSolved` (shared with the domain/flag/rootPair substitution
  passes) with its reverse-dependency index;
* the Gauss loop `denseGaussLoop` and the transform `denseGaussElim`.

The pass's **native** `DensePassCorrect` — with no dependency on the reference `gaussElimPass` —
lives downstream in `OptimizerPasses/GaussProof.lean` (which also builds the wired
`denseGaussElimPass` via `DenseVerifiedPassW.ofNative`). The commutation-era `Corr` bisimulation and
the decode-correspondence lemmas that inherited the reference `PassCorrect` have been removed. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense expression size (mirrors `Expression.varCount` / `Expression.isVar`) -/

/-- Number of variable occurrences (with multiplicity), mirroring `Expression.varCount`. -/
def DenseExpr.varCount : DenseExpr p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add a b => a.varCount + b.varCount
  | .mul a b => a.varCount + b.varCount

/-- Is the dense expression literally a variable? Mirrors `Expression.isVar`. -/
def DenseExpr.isVar : DenseExpr p → Bool
  | .var _ => true
  | _ => false

/-- Decoding preserves the "is a bare variable" test. -/
theorem VarRegistry.decodeExpr_isVar (reg : VarRegistry) (e : DenseExpr p) :
    (reg.decodeExpr e).isVar = e.isVar := by
  cases e <;> rfl

/-! ## The pivot score (mirrors `pivotScore`) -/

/-- The duplication cost of a dense pivot `x := t`, with the protection penalty (mirrors
    `pivotScore`). -/
def densePivotScore (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (xt : VarId × DenseExpr p) : Nat :=
  let base := (occ.getD xt.1 1 - 1) * (1 + xt.2.varCount)
  if prot.contains xt.1 && !xt.2.isVar then base + 1000000 else base

/-! ## `toExpr` size facts (score a candidate without building it) -/

theorem denseToExpr_foldl_varCount (terms : List (VarId × ZMod p)) :
    ∀ init : DenseExpr p,
      (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).varCount
        = init.varCount + terms.length := by
  induction terms with
  | nil => intro init; simp
  | cons t rest ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp only [DenseExpr.varCount, List.length_cons]
      omega

theorem DenseLinExpr.toExpr_varCount (l : DenseLinExpr p) : l.toExpr.varCount = l.terms.length := by
  rw [DenseLinExpr.toExpr, denseToExpr_foldl_varCount]
  simp [DenseExpr.varCount]

theorem DenseLinExpr.scale_terms_length (k : ZMod p) (l : DenseLinExpr p) :
    (l.scale k).terms.length = l.terms.length := by
  simp [DenseLinExpr.scale]

theorem denseToExpr_foldl_isVar (terms : List (VarId × ZMod p)) :
    ∀ init : DenseExpr p, init.isVar = false →
      (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).isVar = false := by
  induction terms with
  | nil => intro init h; simpa using h
  | cons t rest ih => intro init _; exact ih _ rfl

theorem DenseLinExpr.toExpr_isVar (l : DenseLinExpr p) : l.toExpr.isVar = false :=
  denseToExpr_foldl_isVar l.terms _ rfl

/-! ## Descriptor score (mirrors `gaussScore`) -/

/-- Score of a dense pivot on `v` whose solution has `oc` variable occurrences (mirrors
    `gaussScore`); the `densePivotScore` protection penalty reduces to `prot.contains v`, since a
    `toExpr` solution is never a bare variable. -/
def denseGaussScore (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId)
    (oc : Nat) : Nat :=
  let base := (occ.getD v 1 - 1) * (1 + oc)
  if prot.contains v then base + 1000000 else base

theorem denseGaussScore_eq_densePivotScore (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (v : VarId) (t : DenseExpr p) (oc : Nat) (hiv : t.isVar = false) (hvc : t.varCount = oc) :
    denseGaussScore occ prot v oc = densePivotScore occ prot (v, t) := by
  subst hvc
  simp only [denseGaussScore, densePivotScore, hiv, Bool.not_false, Bool.and_true]

/-! ## Closed forms for `trySolve` / `trySolveUnit` -/

theorem DenseLinExpr.trySolve_eq_of_one (l : DenseLinExpr p) (v : VarId) (h : l.coeff v = 1) :
    l.trySolve v = some (v, ((l.others v).scale (-1)).toExpr) := by
  unfold DenseLinExpr.trySolve; rw [if_pos h]

theorem DenseLinExpr.trySolve_eq_of_negOne (l : DenseLinExpr p) (v : VarId) (h1 : l.coeff v ≠ 1)
    (h2 : l.coeff v = -1) : l.trySolve v = some (v, (l.others v).toExpr) := by
  unfold DenseLinExpr.trySolve; rw [if_neg h1, if_pos h2]

theorem DenseLinExpr.trySolve_eq_none (l : DenseLinExpr p) (v : VarId)
    (h : ¬(l.coeff v = 1 ∨ l.coeff v = -1)) : l.trySolve v = none := by
  unfold DenseLinExpr.trySolve
  rw [if_neg (fun hh => h (Or.inl hh)), if_neg (fun hh => h (Or.inr hh))]

theorem DenseLinExpr.trySolveUnit_eq_of (l : DenseLinExpr p) (v : VarId)
    (h : l.coeff v * (l.coeff v)⁻¹ = 1) :
    l.trySolveUnit v = some (v, ((l.others v).scale (-(l.coeff v)⁻¹)).toExpr) := by
  unfold DenseLinExpr.trySolveUnit; rw [if_pos h]

theorem DenseLinExpr.trySolveUnit_eq_none (l : DenseLinExpr p) (v : VarId)
    (h : ¬l.coeff v * (l.coeff v)⁻¹ = 1) : l.trySolveUnit v = none := by
  unfold DenseLinExpr.trySolveUnit; rw [if_neg h]

/-! ## Coefficient / occurrence index (mirrors `coeffIdx`) -/

/-- Coefficient sum of the terms whose variable is `v`. -/
def denseCsum (terms : List (VarId × ZMod p)) (v : VarId) : ZMod p :=
  ((terms.filter (fun t => t.1 = v)).map Prod.snd).sum

/-- Occurrence count of `v` among the terms. -/
def denseCcnt (terms : List (VarId × ZMod p)) (v : VarId) : Nat :=
  (terms.filter (fun t => t.1 = v)).length

/-- One index step: add `t`'s coefficient and one occurrence to `t.1`'s entry (0 if absent). -/
def denseIdxStep (m : Std.HashMap VarId (ZMod p × Nat)) (t : VarId × ZMod p) :
    Std.HashMap VarId (ZMod p × Nat) :=
  m.insert t.1 (((m[t.1]?).getD (0, 0)).1 + t.2, ((m[t.1]?).getD (0, 0)).2 + 1)

/-- The coefficient/occurrence index of a term list. -/
def denseCoeffIdx (terms : List (VarId × ZMod p)) : Std.HashMap VarId (ZMod p × Nat) :=
  terms.foldl denseIdxStep ∅

theorem denseIdxStep_fold (terms : List (VarId × ZMod p)) :
    ∀ (m : Std.HashMap VarId (ZMod p × Nat)) (v : VarId),
      ((terms.foldl denseIdxStep m)[v]?).getD (0, 0)
        = (((m[v]?).getD (0, 0)).1 + denseCsum terms v,
           ((m[v]?).getD (0, 0)).2 + denseCcnt terms v) := by
  induction terms with
  | nil => intro m v; simp [denseCsum, denseCcnt]
  | cons t rest ih =>
      intro m v
      rw [List.foldl_cons, ih (denseIdxStep m t) v]
      have hstep : ((denseIdxStep m t)[v]?).getD (0, 0)
          = (((m[v]?).getD (0, 0)).1 + (if t.1 = v then t.2 else 0),
             ((m[v]?).getD (0, 0)).2 + (if t.1 = v then 1 else 0)) := by
        unfold denseIdxStep
        rw [Std.HashMap.getElem?_insert]
        by_cases htv : t.1 = v
        · subst htv; simp
        · rw [if_neg (by simpa using htv), if_neg htv, if_neg htv]
          simp
      rw [hstep]
      have hcsum : denseCsum (t :: rest) v = (if t.1 = v then t.2 else 0) + denseCsum rest v := by
        unfold denseCsum; by_cases htv : t.1 = v <;> simp [htv]
      have hccnt : denseCcnt (t :: rest) v = denseCcnt rest v + (if t.1 = v then 1 else 0) := by
        unfold denseCcnt; by_cases htv : t.1 = v <;> simp [htv]
      rw [hcsum, hccnt]
      refine Prod.ext ?_ ?_ <;> ring

theorem denseCoeffIdx_get (terms : List (VarId × ZMod p)) (v : VarId) :
    ((denseCoeffIdx terms)[v]?).getD (0, 0) = (denseCsum terms v, denseCcnt terms v) := by
  simp [denseCoeffIdx, denseIdxStep_fold terms ∅ v]

theorem denseCoeffIdx_coeff (l : DenseLinExpr p) (v : VarId) :
    (((denseCoeffIdx l.terms)[v]?).getD (0, 0)).1 = l.coeff v := by
  rw [denseCoeffIdx_get]; rfl

theorem dense_filter_eq_ne_length (terms : List (VarId × ZMod p)) (v : VarId) :
    (terms.filter (fun t => t.1 ≠ v)).length + (terms.filter (fun t => t.1 = v)).length
      = terms.length := by
  induction terms with
  | nil => rfl
  | cons t rest ih => by_cases htv : t.1 = v <;> simp_all <;> omega

theorem denseCoeffIdx_others (l : DenseLinExpr p) (v : VarId) :
    l.terms.length - (((denseCoeffIdx l.terms)[v]?).getD (0, 0)).2 = (l.others v).terms.length := by
  rw [denseCoeffIdx_get]
  simp only [DenseLinExpr.others, denseCcnt]
  have h := dense_filter_eq_ne_length l.terms v
  omega

/-! ## Descriptors (mirror `pm1Desc` / `unitDesc` / `pivotDescs`) -/

/-- `±1`-pivot descriptor: `some (v, score)` exactly when `l.trySolve v` succeeds. -/
def densePm1Desc (idx : Std.HashMap VarId (ZMod p × Nat)) (total : Nat)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    Option (VarId × Nat) :=
  if ((idx[v]?).getD (0, 0)).1 = 1 ∨ ((idx[v]?).getD (0, 0)).1 = -1 then
    some (v, denseGaussScore occ prot v (total - ((idx[v]?).getD (0, 0)).2))
  else none

theorem densePm1Desc_eq (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (v : VarId) :
    densePm1Desc (denseCoeffIdx l.terms) l.terms.length occ prot v
      = (l.trySolve v).map (fun xt => (xt.1, densePivotScore occ prot xt)) := by
  unfold densePm1Desc
  rw [denseCoeffIdx_coeff l v, denseCoeffIdx_others l v]
  by_cases h1 : l.coeff v = 1
  · rw [if_pos (Or.inl h1), DenseLinExpr.trySolve_eq_of_one l v h1, Option.map_some,
      denseGaussScore_eq_densePivotScore occ prot v (((l.others v).scale (-1)).toExpr)
        (l.others v).terms.length (DenseLinExpr.toExpr_isVar _)
        (by rw [DenseLinExpr.toExpr_varCount, DenseLinExpr.scale_terms_length])]
  · by_cases h2 : l.coeff v = -1
    · rw [if_pos (Or.inr h2), DenseLinExpr.trySolve_eq_of_negOne l v h1 h2, Option.map_some,
        denseGaussScore_eq_densePivotScore occ prot v ((l.others v).toExpr)
          (l.others v).terms.length (DenseLinExpr.toExpr_isVar _) (DenseLinExpr.toExpr_varCount _)]
    · rw [if_neg (by rintro (h | h); exacts [h1 h, h2 h]),
        DenseLinExpr.trySolve_eq_none l v (by rintro (h | h); exacts [h1 h, h2 h]), Option.map_none]

/-- Unit-pivot descriptor: `some (v, score)` exactly when `l.trySolve v` fails but
    `l.trySolveUnit v` succeeds. -/
def denseUnitDesc (idx : Std.HashMap VarId (ZMod p × Nat)) (total : Nat)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (v : VarId) :
    Option (VarId × Nat) :=
  if ¬(((idx[v]?).getD (0, 0)).1 = 1 ∨ ((idx[v]?).getD (0, 0)).1 = -1)
      ∧ ((idx[v]?).getD (0, 0)).1 * (((idx[v]?).getD (0, 0)).1)⁻¹ = 1 then
    some (v, denseGaussScore occ prot v (total - ((idx[v]?).getD (0, 0)).2))
  else none

theorem denseUnitDesc_eq (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId)
    (v : VarId) :
    denseUnitDesc (denseCoeffIdx l.terms) l.terms.length occ prot v
      = (match l.trySolve v with | some _ => none | none => l.trySolveUnit v).map
          (fun xt : VarId × DenseExpr p => (xt.1, densePivotScore occ prot xt)) := by
  unfold denseUnitDesc
  rw [denseCoeffIdx_coeff l v, denseCoeffIdx_others l v]
  by_cases h1 : l.coeff v = 1
  · rw [if_neg (fun hc => hc.1 (Or.inl h1)), DenseLinExpr.trySolve_eq_of_one l v h1]; rfl
  · by_cases h2 : l.coeff v = -1
    · rw [if_neg (fun hc => hc.1 (Or.inr h2)), DenseLinExpr.trySolve_eq_of_negOne l v h1 h2]; rfl
    · rw [DenseLinExpr.trySolve_eq_none l v (by rintro (h | h); exacts [h1 h, h2 h])]
      by_cases h3 : l.coeff v * (l.coeff v)⁻¹ = 1
      · rw [if_pos ⟨by rintro (h | h); exacts [h1 h, h2 h], h3⟩,
          DenseLinExpr.trySolveUnit_eq_of l v h3,
          denseGaussScore_eq_densePivotScore occ prot v (((l.others v).scale (-(l.coeff v)⁻¹)).toExpr)
            (l.others v).terms.length (DenseLinExpr.toExpr_isVar _)
            (by rw [DenseLinExpr.toExpr_varCount, DenseLinExpr.scale_terms_length])]
        rfl
      · rw [if_neg (fun hc => h3 hc.2), DenseLinExpr.trySolveUnit_eq_none l v h3]; rfl

/-- All pivot descriptors, `±1` first (mirroring `densePm1PivotsOf ++ denseUnitPivotsOf`). -/
def densePivotDescs (l : DenseLinExpr p) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    List (VarId × Nat) :=
  let idx := denseCoeffIdx l.terms
  let total := l.terms.length
  (l.terms.map Prod.fst).filterMap (densePm1Desc idx total occ prot)
    ++ (l.terms.map Prod.fst).filterMap (denseUnitDesc idx total occ prot)

theorem densePivotDescs_eq (c : DenseExpr p) (l : DenseLinExpr p) (hlin : denseLinearize c = some l)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    densePivotDescs l occ prot
      = (densePm1PivotsOf c ++ denseUnitPivotsOf c).map (fun xt => (xt.1, densePivotScore occ prot xt)) := by
  show (l.terms.map Prod.fst).filterMap (densePm1Desc (denseCoeffIdx l.terms) l.terms.length occ prot)
      ++ (l.terms.map Prod.fst).filterMap (denseUnitDesc (denseCoeffIdx l.terms) l.terms.length occ prot)
      = (densePm1PivotsOf c ++ denseUnitPivotsOf c).map (fun xt => (xt.1, densePivotScore occ prot xt))
  unfold densePm1PivotsOf denseUnitPivotsOf
  rw [hlin, List.map_append, map_filterMap, map_filterMap]
  congr 1
  · exact List.filterMap_congr (fun v _ => densePm1Desc_eq l occ prot v)
  · exact List.filterMap_congr (fun v _ => denseUnitDesc_eq l occ prot v)

/-! ## Fast pivot selection (mirrors `fastBest`) -/

/-- The cheapest solvable dense pivot of a constraint, building the solution only for the winner. -/
def denseFastBest (c : DenseExpr p) (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    Option (VarId × DenseExpr p) :=
  match denseLinearize c with
  | none => none
  | some l =>
      match (densePivotDescs l occ prot).argmin Prod.snd with
      | none => none
      | some (x, _) =>
          match l.trySolve x with
          | some xt => some xt
          | none => l.trySolveUnit x

theorem DenseLinExpr.trySolve_fst (l : DenseLinExpr p) (v : VarId) (w : VarId × DenseExpr p)
    (h : l.trySolve v = some w) : w.1 = v := by
  unfold DenseLinExpr.trySolve at h
  split_ifs at h
  all_goals simp_all [Prod.ext_iff]

theorem DenseLinExpr.trySolveUnit_fst (l : DenseLinExpr p) (v : VarId) (w : VarId × DenseExpr p)
    (h : l.trySolveUnit v = some w) : w.1 = v := by
  unfold DenseLinExpr.trySolveUnit at h
  split_ifs at h
  all_goals simp_all [Prod.ext_iff]

theorem denseMem_pm1_trySolve (c : DenseExpr p) (l : DenseLinExpr p)
    (hlin : denseLinearize c = some l) (w : VarId × DenseExpr p) (h : w ∈ densePm1PivotsOf c) :
    l.trySolve w.1 = some w := by
  unfold densePm1PivotsOf at h
  rw [hlin] at h
  obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
  rw [DenseLinExpr.trySolve_fst l v w hv]; exact hv

theorem denseMem_unit_trySolveUnit (c : DenseExpr p) (l : DenseLinExpr p)
    (hlin : denseLinearize c = some l) (w : VarId × DenseExpr p) (h : w ∈ denseUnitPivotsOf c) :
    l.trySolve w.1 = none ∧ l.trySolveUnit w.1 = some w := by
  unfold denseUnitPivotsOf at h
  rw [hlin] at h
  obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
  cases hts : l.trySolve v with
  | some r => rw [hts] at hv; simp at hv
  | none =>
      rw [hts] at hv
      rw [DenseLinExpr.trySolveUnit_fst l v w hv]
      exact ⟨hts, hv⟩

theorem denseFastBest_eq (c : DenseExpr p) (occ : Std.HashMap VarId Nat)
    (prot : Std.HashSet VarId) :
    denseFastBest c occ prot
      = (densePm1PivotsOf c ++ denseUnitPivotsOf c).argmin (densePivotScore occ prot) := by
  unfold denseFastBest
  split
  · next hlin => simp [densePm1PivotsOf, denseUnitPivotsOf, hlin]
  · next l hlin =>
      rw [densePivotDescs_eq c l hlin occ prot,
        argmin_map_key (fun xt => (xt.1, densePivotScore occ prot xt)) (densePivotScore occ prot)
          Prod.snd (fun _ => rfl)]
      cases hA : (densePm1PivotsOf c ++ denseUnitPivotsOf c).argmin (densePivotScore occ prot) with
      | none => simp
      | some w =>
          simp only [Option.map_some]
          have hmem : w ∈ densePm1PivotsOf c ++ denseUnitPivotsOf c :=
            List.argmin_mem (by rw [hA]; exact Option.mem_some_self w)
          rcases List.mem_append.1 hmem with hp | hu
          · rw [denseMem_pm1_trySolve c l hlin w hp]
          · obtain ⟨hn, hs⟩ := denseMem_unit_trySolveUnit c l hlin w hu
            rw [hn, hs]

/-- Occurrence counts of every variable across the dense system (one traversal). -/
def denseOccurrenceMap (d : DenseConstraintSystem p) : Std.HashMap VarId Nat :=
  let addE := fun (m : Std.HashMap VarId Nat) (e : DenseExpr p) =>
    e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m
  let m := d.algebraicConstraints.foldl addE ∅
  d.busInteractions.foldl (fun m bi => bi.payload.foldl addE (addE m bi.multiplicity)) m

/-! ## Protected variables (mirrors `protectedVars`) -/

/-- Variables occurring as a *raw* payload slot of a stateless interaction (mirrors
    `protectedVars`). -/
def denseProtectedVars (d : DenseConstraintSystem p) (bs : BusSemantics p) : Std.HashSet VarId :=
  d.busInteractions.foldl (init := ∅) fun s bi =>
    if bs.isStateful bi.busId then s
    else bi.payload.foldl (fun s e => match e with | .var x => s.insert x | _ => s) s

/-! ## The dense (runtime-only) solution map

`DenseSolved` is the `VarId`-native mirror of the spec `Solved`, but a **plain** structure — no proof
fields. Its correctness comes from the bisimulation (`denseGaussLoop_corr`), not from carried
invariants. The data updates mirror `Solved.empty`/`Solved.fn`/`Solved.insertAll` exactly. -/

structure DenseSolved (p : ℕ) where
  map : Std.HashMap VarId (DenseExpr p)
  revDeps : Std.HashMap VarId (Std.HashSet VarId)

namespace DenseSolved

/-- The empty dense solution map. -/
def empty : DenseSolved p := { map := ∅, revDeps := ∅ }

/-- The map as a lookup function (what `substF` consumes), mirroring `Solved.fn`. -/
def fn (dσ : DenseSolved p) : VarId → Option (DenseExpr p) := fun i => dσ.map[i]?

/-- Insert a list of pairs, mirroring `Solved.insertAll`'s data updates (map insert + revDeps fold
    over the value's variables), dropping the proof arguments. -/
def insertAll (dσ : DenseSolved p) : List (VarId × DenseExpr p) → DenseSolved p
  | [] => dσ
  | (x, t) :: rest =>
      DenseSolved.insertAll
        { map := dσ.map.insert x t,
          revDeps := t.vars.foldl (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert x)) dσ.revDeps }
        rest

/-- `insertAll`'s `map` is a left fold of inserts (data-only; independent of the proof fields). -/
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

/-! ## The dense Gauss loop

The `VarId`-native mirror of `gaussLoop`: reduce each pending constraint by the current solutions,
adopt the cheapest solvable pivot, resolve it into the affected stored solutions, continue. No proof
arguments — structural recursion on the dense pending list, mirroring `gaussLoop`'s body exactly. -/

def denseGaussLoop (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) :
    List (DenseExpr p) → DenseSolved p → DenseSolved p
  | [], dσ => dσ
  | c :: rest, dσ =>
      let c' := (c.substF dσ.fn).normalize
      match denseFastBest c' occ prot with
      | none => denseGaussLoop occ prot rest dσ
      | some (x, t) =>
          let touched := ((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
            (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))
          let pairs := touched.map (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)]
          denseGaussLoop occ prot rest (dσ.insertAll pairs)

/-! ## The adopted pivot is valid and its right-hand side is covered

The pivot `denseFastBest` returns comes from a solvable candidate of a covered constraint, so its key
is a registered id and its solution mentions only that constraint's (covered) variables. `corr_step`
needs both facts. -/

/-- A variable of `l.others v` is a variable of `l`. -/
theorem DenseLinExpr.others_terms_fst_mem (l : DenseLinExpr p) (v : VarId) (x : VarId)
    (h : x ∈ (l.others v).terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [DenseLinExpr.others, List.mem_map] at h ⊢
  obtain ⟨tt, htt, rfl⟩ := h
  exact ⟨tt, List.mem_of_mem_filter htt, rfl⟩

/-- A `trySolve` solution's variables are variables of the linear form. -/
theorem denseTrySolve_vars_subset (l : DenseLinExpr p) (v : VarId) (w : VarId × DenseExpr p)
    (h : l.trySolve v = some w) : ∀ x ∈ w.2.vars, x ∈ l.terms.map Prod.fst := by
  by_cases h1 : l.coeff v = 1
  · rw [DenseLinExpr.trySolve_eq_of_one l v h1] at h
    injection h with h'; subst h'
    intro x hx
    exact l.others_terms_fst_mem v x
      (by rw [← DenseLinExpr.scale_terms_fst (-1) (l.others v)]; exact DenseLinExpr.toExpr_vars _ x hx)
  · by_cases h2 : l.coeff v = -1
    · rw [DenseLinExpr.trySolve_eq_of_negOne l v h1 h2] at h
      injection h with h'; subst h'
      intro x hx
      exact l.others_terms_fst_mem v x (DenseLinExpr.toExpr_vars _ x hx)
    · rw [DenseLinExpr.trySolve_eq_none l v (by rintro (h | h); exacts [h1 h, h2 h])] at h
      exact absurd h (by simp)

/-- A `trySolveUnit` solution's variables are variables of the linear form. -/
theorem denseTrySolveUnit_vars_subset (l : DenseLinExpr p) (v : VarId) (w : VarId × DenseExpr p)
    (h : l.trySolveUnit v = some w) : ∀ x ∈ w.2.vars, x ∈ l.terms.map Prod.fst := by
  by_cases h1 : l.coeff v * (l.coeff v)⁻¹ = 1
  · rw [DenseLinExpr.trySolveUnit_eq_of l v h1] at h
    injection h with h'; subst h'
    intro x hx
    exact l.others_terms_fst_mem v x
      (by rw [← DenseLinExpr.scale_terms_fst (-(l.coeff v)⁻¹) (l.others v)]
          exact DenseLinExpr.toExpr_vars _ x hx)
  · rw [DenseLinExpr.trySolveUnit_eq_none l v h1] at h
    exact absurd h (by simp)

/-! ## The dense Gauss-elimination pass

The `VarId`-native mirror of `gaussElimPass`: build the occurrence map / protected set, run
`denseGaussLoop` over two sweeps of the algebraic constraints, and — unless no pivot was adopted —
substitute the whole solution map through the system. Correctness is proved **natively** as a
`DensePassCorrect` in `GaussProof.lean` (no dependency on the spec `gaussElimPass`). -/

/-- The dense batch linear-elimination transform, mirroring `gaussElimPass`. -/
def denseGaussElim (bs : BusSemantics p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let dσ := denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
    (d.algebraicConstraints ++ d.algebraicConstraints) DenseSolved.empty
  if dσ.map.isEmpty then d else d.substF dσ.fn

/-- `denseGaussElim` as an explicit `if` (the `let` zeta-reduces). -/
theorem denseGaussElim_eq (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    denseGaussElim bs d =
      if (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
          (d.algebraicConstraints ++ d.algebraicConstraints) DenseSolved.empty).map.isEmpty
      then d
      else d.substF (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
          (d.algebraicConstraints ++ d.algebraicConstraints) DenseSolved.empty).fn := rfl

/-! `denseGaussElimPass` (the wired pass) is built and proved **natively** in
`OptimizerPasses/GaussProof.lean` via `DenseVerifiedPassW.ofNative` — no commutation with the
reference `gaussElimPass`. -/

end ApcOptimizer.Dense
