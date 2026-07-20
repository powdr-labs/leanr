import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Gauss

set_option autoImplicit false

/-! # Dense Gauss scoring / fast pivot selection (Task 3, WP-E — Gauss foundation, part 3)

The dense mirror of the descriptor-based, `argmin`-free pivot scoring in
`OptimizerPasses/Gauss.lean` (`occurrenceMap`/`protectedVars`/`pivotScore`, the `coeffIdx` index,
the `pm1Desc`/`unitDesc` descriptors and `fastBest`). Everything here is keyed on `VarId` and
`DenseExpr`; each construction decodes, under a covering registry, to its spec counterpart.

The runtime win the spec `fastBest` buys — scanning lightweight `(VarId, score)` descriptors and
building the winning solution only — is preserved: `denseFastBest` is the descriptor version
(`denseFastBest_eq` proves it equal to the naive `argmin` over the built candidates), **not** the
naive `denseSolvableFrom |>.argmin`.

`denseFastBest_decode` (the correspondence the Gauss-loop chunk consumes) is proved by inheriting the
spec's `fastBest_eq`: `denseFastBest` equals the dense naive `argmin` (`denseFastBest_eq`), which
decodes — member-wise, since the score correspondence only holds on registered ids — to
`(pm1PivotsOf ++ unitPivotsOf).argmin (pivotScore …)`, which the spec's `fastBest_eq` identifies with
`fastBest`. The occurrence-map / protected-set correspondences are stated as hypotheses of
`denseFastBest_decode` and discharged by the standalone `denseOccurrenceMap_decode` /
`denseProtectedVars_decode` lemmas (the DigitFold "HashMap-under-`resolve`" fold pattern). -/

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

/-- Decoding preserves the variable-occurrence count. -/
theorem VarRegistry.decodeExpr_varCount (reg : VarRegistry) (e : DenseExpr p) :
    (reg.decodeExpr e).varCount = e.varCount := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [decodeExpr, Expression.varCount, DenseExpr.varCount, iha, ihb]
  | mul a b iha ihb => simp [decodeExpr, Expression.varCount, DenseExpr.varCount, iha, ihb]

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

/-! ## `argmin` congruence over a member-restricted key correspondence

The score correspondence `densePivotScore ↔ pivotScore` holds only on *registered* ids, so the
`∀ a` `argmin_map_key` is unusable — this member-restricted variant is the tool for decoding a dense
`argmin` (all of whose candidates come from a covered constraint, hence are registered). -/

theorem argmin_map_key_mem {α γ : Type*} (g : α → γ) (kα : α → Nat) (kγ : γ → Nat) :
    ∀ (l : List α), (∀ a ∈ l, kγ (g a) = kα a) → (l.map g).argmin kγ = (l.argmin kα).map g := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha : kγ (g a) = kα a := h a (List.mem_cons_self ..)
      rw [List.map_cons, List.argmin_cons, List.argmin_cons,
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      cases hc : t.argmin kα with
      | none => simp
      | some c =>
          have hcmem : c ∈ t := List.argmin_mem (by rw [hc]; exact Option.mem_some_self c)
          have hcc : kγ (g c) = kα c := h c (List.mem_cons_of_mem _ hcmem)
          simp only [Option.map_some, hcc, ha]
          by_cases hlt : kα c < kα a <;> simp [hlt]

/-! ## Validity of pivot keys (for the member-restricted score correspondence) -/

theorem densePm1PivotsOf_valid (reg : VarRegistry) (c : DenseExpr p) (hc : c.CoveredBy reg)
    (w : VarId × DenseExpr p) (h : w ∈ densePm1PivotsOf c) : reg.Valid w.1 := by
  unfold densePm1PivotsOf at h
  cases hL : denseLinearize c with
  | none => rw [hL] at h; simp at h
  | some l =>
      rw [hL] at h
      obtain ⟨v, hv, hvw⟩ := List.mem_filterMap.1 h
      rw [DenseLinExpr.trySolve_fst l v w hvw]
      exact hc v (denseLinearize_mem_vars c l hL v hv)

theorem denseUnitPivotsOf_valid (reg : VarRegistry) (c : DenseExpr p) (hc : c.CoveredBy reg)
    (w : VarId × DenseExpr p) (h : w ∈ denseUnitPivotsOf c) : reg.Valid w.1 := by
  unfold denseUnitPivotsOf at h
  cases hL : denseLinearize c with
  | none => rw [hL] at h; simp at h
  | some l =>
      rw [hL] at h
      obtain ⟨v, hv, hvw⟩ := List.mem_filterMap.1 h
      have hw1 : w.1 = v := by
        cases hts : l.trySolve v with
        | some r => rw [hts] at hvw; simp at hvw
        | none => rw [hts] at hvw; exact DenseLinExpr.trySolveUnit_fst l v w hvw
      rw [hw1]
      exact hc v (denseLinearize_mem_vars c l hL v hv)

/-! ## Score correspondence (validity-gated) -/

/-- `densePivotScore` decodes to `pivotScore`, given the occurrence-map and protected-set
    correspondences and a registered pivot key. -/
theorem densePivotScore_decode (reg : VarRegistry)
    (docc : Std.HashMap VarId Nat) (occ : Std.HashMap Variable Nat)
    (dprot : Std.HashSet VarId) (prot : Std.HashSet Variable)
    (hocc : ∀ i, reg.Valid i → docc[i]? = occ[reg.resolve i]?)
    (hprot : ∀ i, reg.Valid i → dprot.contains i = prot.contains (reg.resolve i))
    (xt : VarId × DenseExpr p) (hx : reg.Valid xt.1) :
    densePivotScore docc dprot xt = pivotScore occ prot (reg.decodePivot xt) := by
  obtain ⟨x, t⟩ := xt
  have hgetD : docc.getD x 1 = occ.getD (reg.resolve x) 1 := by
    rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getD_eq_getD_getElem?, hocc x hx]
  simp only [densePivotScore, pivotScore, VarRegistry.decodePivot,
    reg.decodeExpr_varCount, reg.decodeExpr_isVar, hprot x hx, hgetD]

/-! ## Occurrence map (mirrors `occurrenceMap`) and its correspondence

The correspondence is the DigitFold "HashMap-under-`resolve`" fold pattern: prove the invariant
`∀ k, Valid k → dense[k]? = spec[resolve k]?` is preserved by each count-bump, each per-expression
variable fold, and each per-interaction step. -/

/-- Occurrence counts of every variable across the dense system (one traversal). -/
def denseOccurrenceMap (d : DenseConstraintSystem p) : Std.HashMap VarId Nat :=
  let addE := fun (m : Std.HashMap VarId Nat) (e : DenseExpr p) =>
    e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m
  let m := d.algebraicConstraints.foldl addE ∅
  d.busInteractions.foldl (fun m bi => bi.payload.foldl addE (addE m bi.multiplicity)) m

/-- One count-bump preserves the resolve-correspondence invariant. -/
theorem denseBump_decode (reg : VarRegistry) {x : VarId} (hx : reg.Valid x)
    (md : Std.HashMap VarId Nat) (ms : Std.HashMap Variable Nat)
    (hinv : ∀ k, reg.Valid k → md[k]? = ms[reg.resolve k]?) :
    ∀ k, reg.Valid k →
      (md.insert x (md.getD x 0 + 1))[k]?
        = (ms.insert (reg.resolve x) (ms.getD (reg.resolve x) 0 + 1))[reg.resolve k]? := by
  intro k hk
  have hval : md.getD x 0 = ms.getD (reg.resolve x) 0 := by
    rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getD_eq_getD_getElem?, hinv x hx]
  rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert, hval]
  by_cases hxk : x = k
  · subst hxk; simp
  · have hxk' : ¬ reg.resolve x = reg.resolve k := fun he => hxk (reg.resolve_inj hx hk he)
    rw [if_neg (by simpa using hxk), if_neg (by simpa using hxk')]
    exact hinv k hk

/-- A per-expression variable fold preserves the correspondence invariant (over `vs` vs
    `vs.map resolve`). -/
theorem denseBumpFold_decode (reg : VarRegistry) :
    ∀ (vs : List VarId), (∀ x ∈ vs, reg.Valid x) →
      ∀ (md : Std.HashMap VarId Nat) (ms : Std.HashMap Variable Nat),
      (∀ k, reg.Valid k → md[k]? = ms[reg.resolve k]?) →
      ∀ k, reg.Valid k →
        (vs.foldl (fun m x => m.insert x (m.getD x 0 + 1)) md)[k]?
          = ((vs.map reg.resolve).foldl (fun m x => m.insert x (m.getD x 0 + 1)) ms)[reg.resolve k]? := by
  intro vs
  induction vs with
  | nil => intro _ md ms hinv k hk; exact hinv k hk
  | cons x rest ih =>
      intro hvv md ms hinv k hk
      have hxv : reg.Valid x := hvv x (List.mem_cons_self ..)
      have hrestv : ∀ x' ∈ rest, reg.Valid x' := fun x' hx' => hvv x' (List.mem_cons_of_mem _ hx')
      simp only [List.foldl_cons, List.map_cons]
      exact ih hrestv _ _ (denseBump_decode reg hxv md ms hinv) k hk

/-- `addE` (fold the count-bump over an expression's variables) preserves the invariant. -/
theorem denseAddE_decode (reg : VarRegistry) {e : DenseExpr p} (hec : e.CoveredBy reg)
    (md : Std.HashMap VarId Nat) (ms : Std.HashMap Variable Nat)
    (hinv : ∀ k, reg.Valid k → md[k]? = ms[reg.resolve k]?) :
    ∀ k, reg.Valid k →
      (e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) md)[k]?
        = ((reg.decodeExpr e).vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) ms)[reg.resolve k]? := by
  rw [reg.decodeExpr_vars e]
  exact denseBumpFold_decode reg e.vars hec md ms hinv

/-- Folding `addE` over an expression list preserves the invariant (over `es` vs
    `es.map decodeExpr`). -/
theorem denseAddEFold_decode (reg : VarRegistry) :
    ∀ (es : List (DenseExpr p)), (∀ e ∈ es, e.CoveredBy reg) →
      ∀ (md : Std.HashMap VarId Nat) (ms : Std.HashMap Variable Nat),
      (∀ k, reg.Valid k → md[k]? = ms[reg.resolve k]?) →
      ∀ k, reg.Valid k →
        (es.foldl (fun m e => e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m) md)[k]?
          = ((es.map reg.decodeExpr).foldl
              (fun m e => e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m) ms)[reg.resolve k]? := by
  intro es
  induction es with
  | nil => intro _ md ms hinv k hk; exact hinv k hk
  | cons e rest ih =>
      intro hcov md ms hinv k hk
      have hec : e.CoveredBy reg := hcov e (List.mem_cons_self ..)
      have hrestc : ∀ e' ∈ rest, e'.CoveredBy reg := fun e' he' => hcov e' (List.mem_cons_of_mem _ he')
      simp only [List.foldl_cons, List.map_cons]
      exact ih hrestc _ _ (denseAddE_decode reg hec md ms hinv) k hk

/-- Folding the per-interaction step preserves the invariant (over `bis` vs `bis.map decodeBI`). -/
theorem denseBIFold_decode (reg : VarRegistry) :
    ∀ (bis : List (BusInteraction (DenseExpr p))), (∀ bi ∈ bis, denseBICovered reg bi) →
      ∀ (md : Std.HashMap VarId Nat) (ms : Std.HashMap Variable Nat),
      (∀ k, reg.Valid k → md[k]? = ms[reg.resolve k]?) →
      ∀ k, reg.Valid k →
        (bis.foldl (fun m bi =>
            bi.payload.foldl (fun m e => e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m)
              (bi.multiplicity.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m)) md)[k]?
          = ((bis.map reg.decodeBI).foldl (fun m bi =>
              bi.payload.foldl (fun m e => e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m)
                (bi.multiplicity.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m)) ms)[reg.resolve k]? := by
  intro bis
  induction bis with
  | nil => intro _ md ms hinv k hk; exact hinv k hk
  | cons bi rest ih =>
      intro hcov md ms hinv k hk
      have hbc : denseBICovered reg bi := hcov bi (List.mem_cons_self ..)
      have hrestc : ∀ b ∈ rest, denseBICovered reg b := fun b hb => hcov b (List.mem_cons_of_mem _ hb)
      simp only [List.foldl_cons, List.map_cons]
      refine ih hrestc _ _ ?_ k hk
      exact denseAddEFold_decode reg bi.payload hbc.2 _ _ (denseAddE_decode reg hbc.1 md ms hinv)

/-- **The occurrence map decodes to `occurrenceMap` under `resolve`** (value-for-value on registered
    ids). -/
theorem denseOccurrenceMap_decode (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    ∀ i, reg.Valid i → (denseOccurrenceMap d)[i]? = (occurrenceMap (reg.decodeCS d))[reg.resolve i]? := by
  intro i hi
  simp only [denseOccurrenceMap, occurrenceMap, VarRegistry.decodeCS]
  exact denseBIFold_decode reg d.busInteractions hcov.2 _ _
    (fun k hk => denseAddEFold_decode reg d.algebraicConstraints hcov.1 ∅ ∅
      (fun _ _ => by simp) k hk) i hi

/-! ## Protected variables (mirrors `protectedVars`) and its correspondence -/

/-- Variables occurring as a *raw* payload slot of a stateless interaction (mirrors
    `protectedVars`). -/
def denseProtectedVars (d : DenseConstraintSystem p) (bs : BusSemantics p) : Std.HashSet VarId :=
  d.busInteractions.foldl (init := ∅) fun s bi =>
    if bs.isStateful bi.busId then s
    else bi.payload.foldl (fun s e => match e with | .var x => s.insert x | _ => s) s

/-- One set-insert preserves the resolve-correspondence invariant. -/
theorem denseSetInsert_decode (reg : VarRegistry) {x : VarId} (hx : reg.Valid x)
    (sd : Std.HashSet VarId) (ss : Std.HashSet Variable)
    (hinv : ∀ k, reg.Valid k → sd.contains k = ss.contains (reg.resolve k)) :
    ∀ k, reg.Valid k →
      (sd.insert x).contains k = (ss.insert (reg.resolve x)).contains (reg.resolve k) := by
  intro k hk
  rw [Std.HashSet.contains_insert, Std.HashSet.contains_insert, hinv k hk]
  by_cases hxk : x = k
  · subst hxk; simp
  · have hxk' : ¬ reg.resolve x = reg.resolve k := fun he => hxk (reg.resolve_inj hx hk he)
    rw [show (x == k) = false from by simpa using hxk,
        show (reg.resolve x == reg.resolve k) = false from by simpa using hxk']

/-- A per-payload variable-insert fold preserves the correspondence invariant. -/
theorem denseSetFold_decode (reg : VarRegistry) :
    ∀ (es : List (DenseExpr p)), (∀ e ∈ es, e.CoveredBy reg) →
      ∀ (sd : Std.HashSet VarId) (ss : Std.HashSet Variable),
      (∀ k, reg.Valid k → sd.contains k = ss.contains (reg.resolve k)) →
      ∀ k, reg.Valid k →
        (es.foldl (fun s e => match e with | .var x => s.insert x | _ => s) sd).contains k
          = ((es.map reg.decodeExpr).foldl
              (fun s e => match e with | .var x => s.insert x | _ => s) ss).contains (reg.resolve k) := by
  intro es
  induction es with
  | nil => intro _ sd ss hinv k hk; exact hinv k hk
  | cons e rest ih =>
      intro hcov sd ss hinv k hk
      have hrestc : ∀ e' ∈ rest, e'.CoveredBy reg := fun e' he' => hcov e' (List.mem_cons_of_mem _ he')
      simp only [List.foldl_cons, List.map_cons]
      refine ih hrestc _ _ ?_ k hk
      intro k' hk'
      cases e with
      | var x =>
          have hxv : reg.Valid x := (hcov (.var x) (List.mem_cons_self ..)) x (by simp [DenseExpr.vars])
          exact denseSetInsert_decode reg hxv sd ss hinv k' hk'
      | const n => exact hinv k' hk'
      | add a b => exact hinv k' hk'
      | mul a b => exact hinv k' hk'

/-- The per-interaction stateless-payload step preserves the correspondence invariant. -/
theorem denseProtBIFold_decode (reg : VarRegistry) (bs : BusSemantics p) :
    ∀ (bis : List (BusInteraction (DenseExpr p))), (∀ bi ∈ bis, denseBICovered reg bi) →
      ∀ (sd : Std.HashSet VarId) (ss : Std.HashSet Variable),
      (∀ k, reg.Valid k → sd.contains k = ss.contains (reg.resolve k)) →
      ∀ k, reg.Valid k →
        (bis.foldl (fun s bi => if bs.isStateful bi.busId then s
            else bi.payload.foldl (fun s e => match e with | .var x => s.insert x | _ => s) s) sd).contains k
          = ((bis.map reg.decodeBI).foldl (fun s bi => if bs.isStateful bi.busId then s
              else bi.payload.foldl (fun s e => match e with | .var x => s.insert x | _ => s) s) ss).contains (reg.resolve k) := by
  intro bis
  induction bis with
  | nil => intro _ sd ss hinv k hk; exact hinv k hk
  | cons bi rest ih =>
      intro hcov sd ss hinv k hk
      have hbc : denseBICovered reg bi := hcov bi (List.mem_cons_self ..)
      have hrestc : ∀ b ∈ rest, denseBICovered reg b := fun b hb => hcov b (List.mem_cons_of_mem _ hb)
      simp only [List.foldl_cons, List.map_cons]
      refine ih hrestc _ _ ?_ k hk
      intro k' hk'
      by_cases hst : bs.isStateful bi.busId
      · rw [if_pos hst, show (reg.decodeBI bi).busId = bi.busId from rfl, if_pos hst]
        exact hinv k' hk'
      · rw [if_neg hst, show (reg.decodeBI bi).busId = bi.busId from rfl, if_neg hst,
            show (reg.decodeBI bi).payload = bi.payload.map reg.decodeExpr from rfl]
        exact denseSetFold_decode reg bi.payload hbc.2 sd ss hinv k' hk'

/-- **The protected set decodes to `protectedVars` under `resolve`** (membership-for-membership on
    registered ids). -/
theorem denseProtectedVars_decode (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (hcov : d.CoveredBy reg) :
    ∀ i, reg.Valid i →
      (denseProtectedVars d bs).contains i = (protectedVars (reg.decodeCS d) bs).contains (reg.resolve i) := by
  intro i hi
  simp only [denseProtectedVars, protectedVars, VarRegistry.decodeCS]
  exact denseProtBIFold_decode reg bs d.busInteractions hcov.2 ∅ ∅ (fun _ _ => by simp) i hi

/-! ## `denseFastBest` decodes to `fastBest` -/

/-- **`denseFastBest` decodes to `fastBest`.** Proved by inheriting the spec's `fastBest_eq`: the
    dense descriptor selector equals the dense naive `argmin` (`denseFastBest_eq`), which decodes —
    member-wise, since the score correspondence only holds on registered keys — to the spec naive
    `argmin`, i.e. `fastBest`.

    The occurrence-map / protected-set correspondences are hypotheses (the caller, `gaussLoop`,
    discharges them via `denseOccurrenceMap_decode` / `denseProtectedVars_decode`). -/
theorem denseFastBest_decode (reg : VarRegistry) (c : DenseExpr p) (hc : c.CoveredBy reg)
    (docc : Std.HashMap VarId Nat) (occ : Std.HashMap Variable Nat)
    (dprot : Std.HashSet VarId) (prot : Std.HashSet Variable)
    (hocc : ∀ i, reg.Valid i → docc[i]? = occ[reg.resolve i]?)
    (hprot : ∀ i, reg.Valid i → dprot.contains i = prot.contains (reg.resolve i)) :
    (denseFastBest c docc dprot).map reg.decodePivot = fastBest (reg.decodeExpr c) occ prot := by
  rw [denseFastBest_eq c docc dprot, fastBest_eq (reg.decodeExpr c) occ prot]
  have hscore : ∀ a ∈ densePm1PivotsOf c ++ denseUnitPivotsOf c,
      pivotScore occ prot (reg.decodePivot a) = densePivotScore docc dprot a := by
    intro a ha
    have hav : reg.Valid a.1 := by
      rcases List.mem_append.1 ha with h | h
      · exact densePm1PivotsOf_valid reg c hc a h
      · exact denseUnitPivotsOf_valid reg c hc a h
    exact (densePivotScore_decode reg docc occ dprot prot hocc hprot a hav).symm
  rw [← argmin_map_key_mem reg.decodePivot (densePivotScore docc dprot) (pivotScore occ prot)
    (densePm1PivotsOf c ++ denseUnitPivotsOf c) hscore]
  congr 1
  rw [List.map_append, reg.densePm1PivotsOf_decode c hc, reg.denseUnitPivotsOf_decode c hc]

/-! ## Generic HashMap / HashSet fold lemmas (shared by the dense and spec `insertAll`)

`Solved.insertAll` and `DenseSolved.insertAll` both fold a list of `(key, value)` pairs into their
`map` (a `HashMap.insert` fold) and into their `revDeps` (a nested `HashSet.insert` fold, one bucket
per variable of each value). The lemmas here characterize those folds by *membership*, so they are
insensitive to the iteration order of the `HashSet.toList` that seeds the `touched` list — the point
that makes the dense/spec correspondence provable despite dense and spec hashing to different orders.
-/

/-- If a `filterMap` producing pairs always echoes its input as the first component, the mapped keys
    stay `Nodup`. Used to show the `touched` list built from a `HashSet.toList` has distinct keys. -/
theorem nodup_filterMap_fst {α β : Type*} (f : α → Option (α × β))
    (hf : ∀ y r, f y = some r → r.1 = y) :
    ∀ (L : List α), L.Nodup → ((L.filterMap f).map Prod.fst).Nodup := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons y rest ih =>
      intro hnd
      simp only [List.nodup_cons] at hnd
      obtain ⟨hyni, hrestnd⟩ := hnd
      have hmemkey : ∀ k ∈ (rest.filterMap f).map Prod.fst, k ∈ rest := by
        intro k hk
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
        obtain ⟨y', hy', hfr⟩ := List.mem_filterMap.1 hr
        rw [hf y' r hfr]; exact hy'
      cases hfy : f y with
      | none => simp only [List.filterMap_cons_none hfy]; exact ih hrestnd
      | some r =>
          simp only [List.filterMap_cons_some hfy, List.map_cons, List.nodup_cons]
          refine ⟨?_, ih hrestnd⟩
          rw [hf y r hfy]
          exact fun hy => hyni (hmemkey y hy)

section GenericFold

variable {α : Type*} [BEq α] [Hashable α] [LawfulBEq α] [EquivBEq α] [LawfulHashable α]

/-- A left fold of inserts, queried at a key absent from all folded keys, is the base lookup. -/
theorem foldInsert_absent {β : Type*} (i : α) :
    ∀ (ps : List (α × β)) (m0 : Std.HashMap α β), (∀ p ∈ ps, p.1 ≠ i) →
      (ps.foldl (fun m p => m.insert p.1 p.2) m0)[i]? = m0[i]? := by
  intro ps
  induction ps with
  | nil => intro m0 _; rfl
  | cons hd tl ih =>
      intro m0 hne
      have hhd : hd.1 ≠ i := hne hd (List.mem_cons_self ..)
      have htl : ∀ p ∈ tl, p.1 ≠ i := fun p hp => hne p (List.mem_cons_of_mem _ hp)
      simp only [List.foldl_cons]
      rw [ih (m0.insert hd.1 hd.2) htl, Std.HashMap.getElem?_insert, if_neg (by simpa using hhd)]

/-- A left fold of inserts, queried at a key present exactly once (distinct keys), returns its value.
    Order-independent: whatever order the pairs are folded, the unique pair with key `y` wins. -/
theorem foldInsert_present {β : Type*} (y : α) (v : β) :
    ∀ (ps : List (α × β)), (y, v) ∈ ps → (ps.map Prod.fst).Nodup →
      ∀ (m0 : Std.HashMap α β), (ps.foldl (fun m p => m.insert p.1 p.2) m0)[y]? = some v := by
  intro ps
  induction ps with
  | nil => intro hmem _ _; simp at hmem
  | cons hd tl ih =>
      intro hmem hnodup m0
      simp only [List.map_cons, List.nodup_cons] at hnodup
      obtain ⟨hnotin, htlnodup⟩ := hnodup
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 hmem with heq | hmemtl
      · subst heq
        have hne : ∀ p ∈ tl, p.1 ≠ y :=
          fun p hp hpy => hnotin (hpy ▸ List.mem_map.2 ⟨p, hp, rfl⟩)
        rw [foldInsert_absent y tl (m0.insert y v) hne, Std.HashMap.getElem?_insert_self]
      · exact ih hmemtl htlnodup (m0.insert hd.1 hd.2)

/-- Membership in a nested `HashSet.insert` fold over one value's variables: querying bucket `z` for
    `k'`, the fold adds `k` to bucket `z` exactly when `z` is one of the variables. Order-free. -/
theorem revBucket_mem (k z k' : α) :
    ∀ (vs : List α) (rd : Std.HashMap α (Std.HashSet α)),
      (k' ∈ ((vs.foldl (fun rd w => rd.insert w (((rd[w]?).getD ∅).insert k)) rd)[z]?).getD ∅)
        ↔ (k' ∈ ((rd[z]?).getD ∅)) ∨ (z ∈ vs ∧ k = k') := by
  intro vs
  induction vs with
  | nil => intro rd; simp
  | cons w rest ih =>
      intro rd
      simp only [List.foldl_cons]
      rw [ih (rd.insert w (((rd[w]?).getD ∅).insert k))]
      have key : (k' ∈ ((rd.insert w (((rd[w]?).getD ∅).insert k))[z]?).getD ∅)
          ↔ (k' ∈ ((rd[z]?).getD ∅)) ∨ (w = z ∧ k = k') := by
        rw [Std.HashMap.getElem?_insert]
        by_cases hwz : w = z
        · subst hwz
          rw [if_pos (by simp)]
          simp only [Option.getD_some, Std.HashSet.mem_insert, beq_iff_eq]
          tauto
        · rw [if_neg (by simpa using hwz)]
          simp only [hwz, false_and, or_false]
      rw [key]
      constructor
      · rintro ((h | ⟨rfl, rfl⟩) | ⟨hz, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_self .., rfl⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ hz, rfl⟩
      · rintro (h | ⟨hz, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hz with rfl | hz'
          · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
          · exact Or.inr ⟨hz', rfl⟩

/-- Membership in the full `revDeps` fold over a pair list: bucket `z` gains `k'` iff it already had
    it or some pair `(k', v)` has `z` among `v`'s variables. Order-free (an `∃` over the pairs). -/
theorem revDepsFold_mem {β : Type*} (varsOf : β → List α) (z k' : α) :
    ∀ (ps : List (α × β)) (rd : Std.HashMap α (Std.HashSet α)),
      (k' ∈ ((ps.foldl (fun rd p => (varsOf p.2).foldl
                (fun rd w => rd.insert w (((rd[w]?).getD ∅).insert p.1)) rd) rd)[z]?).getD ∅)
        ↔ (k' ∈ ((rd[z]?).getD ∅)) ∨ (∃ p ∈ ps, z ∈ varsOf p.2 ∧ p.1 = k') := by
  intro ps
  induction ps with
  | nil => intro rd; simp
  | cons pr rest ih =>
      intro rd
      simp only [List.foldl_cons]
      rw [ih ((varsOf pr.2).foldl (fun rd w => rd.insert w (((rd[w]?).getD ∅).insert pr.1)) rd),
        revBucket_mem pr.1 z k' (varsOf pr.2) rd]
      constructor
      · rintro ((h | ⟨hz, rfl⟩) | ⟨p, hp, hzp, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨pr, List.mem_cons_self .., hz, rfl⟩
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hzp, rfl⟩
      · rintro (h | ⟨p, hp, hzp, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hp with rfl | hp'
          · exact Or.inl (Or.inr ⟨hzp, rfl⟩)
          · exact Or.inr ⟨p, hp', hzp, rfl⟩

end GenericFold

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

/-- `insertAll`'s `revDeps` is the nested `HashSet.insert` fold. -/
theorem insertAll_revDeps :
    ∀ (pairs : List (VarId × DenseExpr p)) (dσ : DenseSolved p),
      (dσ.insertAll pairs).revDeps
        = pairs.foldl (fun rd p => p.2.vars.foldl
            (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert p.1)) rd) dσ.revDeps := by
  intro pairs
  induction pairs with
  | nil => intro dσ; rfl
  | cons hd tl ih =>
      intro dσ; obtain ⟨x, t⟩ := hd
      simp only [insertAll, List.foldl_cons]
      rw [ih]

end DenseSolved

/-! ## Closed forms of the spec `Solved.insertAll` data (proof-agnostic)

The spec loop threads soundness/vars proofs into `insertAll`, but its `map`/`revDeps` **data** are
the same folds as the dense side. These lemmas extract that data ignoring the proofs, so the
bisimulation can compare the two `insertAll` results field-for-field. -/

theorem Solved.insertAll_map {cs : ConstraintSystem p} {bs : BusSemantics p} :
    ∀ (pairs : List (Variable × Expression p)) (σ : Solved p cs bs)
      (H : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env)
      (Hv : ∀ yt ∈ pairs, ∀ z ∈ yt.2.vars, z ∈ cs.vars),
      (σ.insertAll pairs H Hv).map = pairs.foldl (fun m p => m.insert p.1 p.2) σ.map := by
  intro pairs
  induction pairs with
  | nil => intro σ H Hv; rfl
  | cons hd tl ih =>
      intro σ H Hv; obtain ⟨x, t⟩ := hd
      simp only [Solved.insertAll, List.foldl_cons]
      rw [ih]

theorem Solved.insertAll_revDeps {cs : ConstraintSystem p} {bs : BusSemantics p} :
    ∀ (pairs : List (Variable × Expression p)) (σ : Solved p cs bs)
      (H : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env)
      (Hv : ∀ yt ∈ pairs, ∀ z ∈ yt.2.vars, z ∈ cs.vars),
      (σ.insertAll pairs H Hv).revDeps
        = pairs.foldl (fun rd p => p.2.vars.foldl
            (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert p.1)) rd) σ.revDeps := by
  intro pairs
  induction pairs with
  | nil => intro σ H Hv; rfl
  | cons hd tl ih =>
      intro σ H Hv; obtain ⟨x, t⟩ := hd
      simp only [Solved.insertAll, List.foldl_cons]
      rw [ih]

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

/-! ## The `touched` list: membership, distinct keys, and fold lookups

Both loops build `touched` by scanning a `HashSet.toList` (the reverse-dependency bucket) and keeping
the stored solutions that mention the pivot, then rewriting each by the pivot. These generic lemmas
characterize that list by membership, so the subsequent fold-into-map is order-free. `men` is the
`mentions`-pivot test and `tr` the pivot-rewrite. -/

section Touched

variable {α β : Type*} [BEq α] [Hashable α] [LawfulBEq α] [EquivBEq α] [LawfulHashable α]

/-- `(k', w)` is in the transformed `touched` list iff `k'` is a bucket member with a mentioning
    stored solution `s`, and `w` is its rewrite `tr s`. -/
theorem mem_touchedPairs (S : Std.HashSet α) (m : Std.HashMap α β) (men : β → Bool) (tr : β → β)
    (k' : α) (w : β) :
    (k', w) ∈ (S.toList.filterMap (fun y => (m[y]?).bind
        (fun s => if men s then some (y, s) else none))).map (fun ys => (ys.1, tr ys.2))
      ↔ ∃ s, k' ∈ S ∧ m[k']? = some s ∧ men s = true ∧ w = tr s := by
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨y0, s0⟩, hmemf, heq⟩
    obtain ⟨y1, hy1, hf⟩ := List.mem_filterMap.1 hmemf
    obtain ⟨s', hs', hif⟩ := Option.bind_eq_some_iff.1 hf
    by_cases hmen : men s' = true
    · rw [if_pos hmen] at hif
      obtain ⟨rfl, rfl⟩ : y1 = y0 ∧ s' = s0 := by simpa [Prod.ext_iff] using hif
      obtain ⟨hyk, hw⟩ : y1 = k' ∧ tr s' = w := by simpa [Prod.ext_iff] using heq
      subst hyk; subst hw
      exact ⟨s', Std.HashSet.mem_of_mem_toList hy1, hs', hmen, rfl⟩
    · rw [if_neg hmen] at hif; exact absurd hif (by simp)
  · rintro ⟨s, hS, hm, hmen, rfl⟩
    refine ⟨(k', s), ?_, rfl⟩
    refine List.mem_filterMap.2 ⟨k', ?_, ?_⟩
    · rw [← Std.HashSet.mem_toList] at hS; exact hS
    · rw [hm]; simp [hmen]

/-- The transformed `touched` list has distinct keys (its keys are a sublist of the bucket's
    `toList`, which is `Nodup`). -/
theorem touchedPairs_nodup (S : Std.HashSet α) (m : Std.HashMap α β) (men : β → Bool) (tr : β → β) :
    (((S.toList.filterMap (fun y => (m[y]?).bind
        (fun s => if men s then some (y, s) else none))).map (fun ys => (ys.1, tr ys.2))).map
        Prod.fst).Nodup := by
  rw [List.map_map]
  have hcomp : (Prod.fst ∘ fun ys : α × β => (ys.1, tr ys.2)) = Prod.fst := by funext ys; rfl
  rw [hcomp]
  refine nodup_filterMap_fst _ ?_ S.toList
    (Std.HashSet.distinct_toList.imp (fun {a b} h => by simpa using h))
  intro y r hr
  obtain ⟨s', _, hif⟩ := Option.bind_eq_some_iff.1 hr
  by_cases hmen : men s' = true
  · rw [if_pos hmen] at hif
    obtain rfl : r = (y, s') := by simpa using hif.symm
    rfl
  · rw [if_neg hmen] at hif; exact absurd hif (by simp)

/-- Fold-insert lookup at a bucket-member key with a mentioning solution: the rewrite `tr s`. -/
theorem foldInsert_touched_hit (S : Std.HashSet α) (m : Std.HashMap α β) (men : β → Bool)
    (tr : β → β) (m0 : Std.HashMap α β) (k' : α) (s : β)
    (hS : k' ∈ S) (hm : m[k']? = some s) (hmen : men s = true) :
    (((S.toList.filterMap (fun y => (m[y]?).bind
          (fun s => if men s then some (y, s) else none))).map (fun ys => (ys.1, tr ys.2))).foldl
        (fun mm p => mm.insert p.1 p.2) m0)[k']? = some (tr s) :=
  foldInsert_present k' (tr s) _ ((mem_touchedPairs S m men tr k' (tr s)).2 ⟨s, hS, hm, hmen, rfl⟩)
    (touchedPairs_nodup S m men tr) m0

/-- Fold-insert lookup at a key that is not a mentioning bucket member: the base lookup. -/
theorem foldInsert_touched_miss (S : Std.HashSet α) (m : Std.HashMap α β) (men : β → Bool)
    (tr : β → β) (m0 : Std.HashMap α β) (k' : α)
    (hmiss : ¬ ∃ s, k' ∈ S ∧ m[k']? = some s ∧ men s = true) :
    (((S.toList.filterMap (fun y => (m[y]?).bind
          (fun s => if men s then some (y, s) else none))).map (fun ys => (ys.1, tr ys.2))).foldl
        (fun mm p => mm.insert p.1 p.2) m0)[k']? = m0[k']? := by
  refine foldInsert_absent k' _ m0 (fun p hp hpk => hmiss ?_)
  obtain ⟨s, hS, hm, hmen, _⟩ := (mem_touchedPairs S m men tr p.1 p.2).1 (by simpa using hp)
  exact ⟨s, hpk ▸ hS, hpk ▸ hm, hmen⟩

end Touched

/-! ## Small `resolve` helpers -/

/-- Appending a single pair to a fold of inserts is one final insert. -/
theorem foldl_insert_append_pair {α β : Type*} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (A : List (α × β)) (x : α) (t : β) (m0 : Std.HashMap α β) :
    (A ++ [(x, t)]).foldl (fun m p => m.insert p.1 p.2) m0
      = (A.foldl (fun m p => m.insert p.1 p.2) m0).insert x t := by
  rw [List.foldl_append]; rfl

/-- On valid ids, `resolve z` is in a list's `resolve`-image iff `z` is in the list. -/
theorem mem_map_resolve (reg : VarRegistry) {z : VarId} (hz : reg.Valid z)
    (l : List VarId) (hl : ∀ i ∈ l, reg.Valid i) :
    reg.resolve z ∈ l.map reg.resolve ↔ z ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨w, hw, he⟩; rwa [reg.resolve_inj (hl w hw) hz he] at hw
  · intro hz'; exact ⟨z, hz', rfl⟩

/-! ## The bisimulation invariant

`Corr reg dσ σ` captures everything the Gauss output depends on: the dense solution map decodes,
value-for-value, to the spec map (at every valid id, on the resolved key), every dense key is valid,
every stored value is covered, the emptiness tests agree, and the reverse-dependency buckets
correspond membership-for-membership. The last is what makes the per-step `touched` set match, hence
the map update, hence the output. Everything is order-free — no dependence on `HashSet.toList`
iteration order (which differs between the `VarId`- and `Variable`-keyed sets). -/

structure Corr (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    (dσ : DenseSolved p) (σ : Solved p cs bs) : Prop where
  /-- Dense map value decodes to spec map value at the resolved key. -/
  mapVal : ∀ i, reg.Valid i → (dσ.map[i]?).map reg.decodeExpr = σ.map[reg.resolve i]?
  /-- Every dense map key is valid. -/
  mapKeyValid : ∀ (i : VarId) (s : DenseExpr p), dσ.map[i]? = some s → reg.Valid i
  /-- Every stored dense value is covered. -/
  mapCov : ∀ (i : VarId) (s : DenseExpr p), dσ.map[i]? = some s → s.CoveredBy reg
  /-- The emptiness tests agree (the pass branches on `σ.map.isEmpty`). -/
  isEmptyEq : dσ.map.isEmpty = σ.map.isEmpty
  /-- Reverse-dependency buckets correspond, membership-for-membership under `resolve`. -/
  revDeps : ∀ z, reg.Valid z → ∀ k, reg.Valid k →
    (k ∈ ((dσ.revDeps[z]?).getD ∅) ↔ reg.resolve k ∈ ((σ.revDeps[reg.resolve z]?).getD ∅))

/-- The empty maps correspond. -/
theorem corr_empty (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p} :
    Corr reg (DenseSolved.empty : DenseSolved p) (Solved.empty : Solved p cs bs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i _; simp [DenseSolved.empty, Solved.empty]
  · intro i s h; simp [DenseSolved.empty] at h
  · intro i s h; simp [DenseSolved.empty] at h
  · simp [DenseSolved.empty, Solved.empty, Std.HashMap.isEmpty_empty]
  · intro z _ k _
    simp [DenseSolved.empty, Solved.empty]

/-- The per-key `touched`-membership test corresponds under `resolve`: `k` is a bucket member of `x`
    with a stored solution mentioning `x`, iff `resolve k` is a bucket member of `resolve x` with a
    stored solution mentioning `resolve x`. The core of the `touched` set matching. -/
theorem hit_iff (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    {dσ : DenseSolved p} {σ : Solved p cs bs} (hcorr : Corr reg dσ σ) {x : VarId} (hxv : reg.Valid x)
    {i : VarId} (hiv : reg.Valid i) :
    (i ∈ ((dσ.revDeps[x]?).getD ∅) ∧ ∃ s, dσ.map[i]? = some s ∧ s.mentions x = true)
      ↔ (reg.resolve i ∈ ((σ.revDeps[reg.resolve x]?).getD ∅)
          ∧ ∃ s', σ.map[reg.resolve i]? = some s' ∧ s'.mentions (reg.resolve x) = true) := by
  constructor
  · rintro ⟨hmem, s, hms, hmen⟩
    refine ⟨(hcorr.revDeps x hxv i hiv).1 hmem, reg.decodeExpr s, ?_, ?_⟩
    · have h := hcorr.mapVal i hiv
      rw [hms] at h; simpa using h.symm
    · rw [← reg.decodeExpr_mentions hxv s (hcorr.mapCov i s hms)]; exact hmen
  · rintro ⟨hmem, s', hms', hmen'⟩
    have hmv := hcorr.mapVal i hiv
    rw [hms'] at hmv
    obtain ⟨s0, hs0, hdec⟩ := Option.map_eq_some_iff.1 hmv
    refine ⟨(hcorr.revDeps x hxv i hiv).2 hmem, s0, hs0, ?_⟩
    rw [reg.decodeExpr_mentions hxv s0 (hcorr.mapCov i s0 hs0), hdec]; exact hmen'

/-- Map-value correspondence is preserved by one loop step. -/
theorem corr_step_mapVal (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    {dσ : DenseSolved p} {σ : Solved p cs bs} (hcorr : Corr reg dσ σ)
    (x : VarId) (t : DenseExpr p) (hxv : reg.Valid x) (htcov : t.CoveredBy reg)
    (σ' : Solved p cs bs)
    (hmap : σ'.map
      = ((((σ.revDeps[reg.resolve x]?).getD ∅).toList.filterMap (fun y =>
          (σ.map[y]?).bind (fun s => if s.mentions (reg.resolve x) then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst (reg.resolve x) (reg.decodeExpr t)).normalize))
          ++ [(reg.resolve x, reg.decodeExpr t)]).foldl (fun m p => m.insert p.1 p.2) σ.map) :
    ∀ i, reg.Valid i →
      ((dσ.insertAll ((((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
          (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)])).map[i]?).map reg.decodeExpr
        = σ'.map[reg.resolve i]? := by
  intro i hiv
  rw [DenseSolved.insertAll_map, foldl_insert_append_pair, hmap, foldl_insert_append_pair,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
  by_cases hxi : x = i
  · subst hxi
    rw [if_pos (by simp), if_pos (by simp), Option.map_some]
  · rw [if_neg (by simpa using hxi),
      if_neg (by simpa using (fun h => hxi (reg.resolve_inj hxv hiv h)))]
    by_cases hhit : i ∈ ((dσ.revDeps[x]?).getD ∅) ∧ ∃ s, dσ.map[i]? = some s ∧ s.mentions x = true
    · obtain ⟨hSi, s, hms, hmen⟩ := hhit
      obtain ⟨hSi', s', hms', hmen'⟩ := (hit_iff reg hcorr hxv hiv).1 ⟨hSi, s, hms, hmen⟩
      have hmv := hcorr.mapVal i hiv
      rw [hms, hms'] at hmv
      simp only [Option.map_some, Option.some.injEq] at hmv
      rw [foldInsert_touched_hit ((dσ.revDeps[x]?).getD ∅) dσ.map (fun s => s.mentions x)
          (fun s => (s.subst x t).normalize) dσ.map i s hSi hms hmen,
        foldInsert_touched_hit ((σ.revDeps[reg.resolve x]?).getD ∅) σ.map
          (fun s => s.mentions (reg.resolve x))
          (fun s => (s.subst (reg.resolve x) (reg.decodeExpr t)).normalize) σ.map
          (reg.resolve i) s' hSi' hms' hmen']
      simp only [Option.map_some, Option.some.injEq]
      have hsub_cov : (s.subst x t).CoveredBy reg :=
        DenseExpr.subst_covered (hcorr.mapCov i s hms) htcov
      rw [reg.decodeExpr_normalize (s.subst x t) hsub_cov,
        reg.decodeExpr_subst hxv t s (hcorr.mapCov i s hms), hmv]
    · have hnsHit : ¬ (reg.resolve i ∈ ((σ.revDeps[reg.resolve x]?).getD ∅)
          ∧ ∃ s', σ.map[reg.resolve i]? = some s' ∧ s'.mentions (reg.resolve x) = true) :=
        fun h => hhit ((hit_iff reg hcorr hxv hiv).2 h)
      rw [foldInsert_touched_miss ((dσ.revDeps[x]?).getD ∅) dσ.map (fun s => s.mentions x)
          (fun s => (s.subst x t).normalize) dσ.map i
          (fun ⟨s, hS, hm, hmen⟩ => hhit ⟨hS, s, hm, hmen⟩),
        foldInsert_touched_miss ((σ.revDeps[reg.resolve x]?).getD ∅) σ.map
          (fun s => s.mentions (reg.resolve x))
          (fun s => (s.subst (reg.resolve x) (reg.decodeExpr t)).normalize) σ.map (reg.resolve i)
          (fun ⟨s', hS, hm, hmen⟩ => hnsHit ⟨hS, s', hm, hmen⟩)]
      exact hcorr.mapVal i hiv

/-- Map-key validity is preserved by one loop step (new keys are `x` and mentioning bucket members,
    all valid). -/
theorem corr_step_mapKeyValid (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    {dσ : DenseSolved p} {σ : Solved p cs bs} (hcorr : Corr reg dσ σ)
    (x : VarId) (t : DenseExpr p) (hxv : reg.Valid x) :
    ∀ (i : VarId) (s : DenseExpr p),
      (dσ.insertAll ((((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
          (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)])).map[i]? = some s →
      reg.Valid i := by
  intro i s h
  rw [DenseSolved.insertAll_map, foldl_insert_append_pair, Std.HashMap.getElem?_insert] at h
  by_cases hxi : x = i
  · exact hxi ▸ hxv
  · rw [if_neg (by simpa using hxi)] at h
    by_cases hhit : i ∈ ((dσ.revDeps[x]?).getD ∅) ∧ ∃ s0, dσ.map[i]? = some s0 ∧ s0.mentions x = true
    · obtain ⟨_, s0, hms, _⟩ := hhit; exact hcorr.mapKeyValid i s0 hms
    · rw [foldInsert_touched_miss ((dσ.revDeps[x]?).getD ∅) dσ.map (fun s => s.mentions x)
          (fun s => (s.subst x t).normalize) dσ.map i
          (fun ⟨s0, hS, hm, hmen⟩ => hhit ⟨hS, s0, hm, hmen⟩)] at h
      exact hcorr.mapKeyValid i s h

/-- Value coverage is preserved by one loop step (new values are `t` and pivot-rewrites of covered
    stored solutions, all covered). -/
theorem corr_step_mapCov (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    {dσ : DenseSolved p} {σ : Solved p cs bs} (hcorr : Corr reg dσ σ)
    (x : VarId) (t : DenseExpr p) (htcov : t.CoveredBy reg) :
    ∀ (i : VarId) (s : DenseExpr p),
      (dσ.insertAll ((((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
          (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)])).map[i]? = some s →
      s.CoveredBy reg := by
  intro i s h
  rw [DenseSolved.insertAll_map, foldl_insert_append_pair, Std.HashMap.getElem?_insert] at h
  by_cases hxi : x = i
  · rw [if_pos (by simpa using hxi), Option.some.injEq] at h
    exact h ▸ htcov
  · rw [if_neg (by simpa using hxi)] at h
    by_cases hhit : i ∈ ((dσ.revDeps[x]?).getD ∅) ∧ ∃ s0, dσ.map[i]? = some s0 ∧ s0.mentions x = true
    · obtain ⟨hSi, s0, hms, hmen⟩ := hhit
      rw [foldInsert_touched_hit ((dσ.revDeps[x]?).getD ∅) dσ.map (fun s => s.mentions x)
          (fun s => (s.subst x t).normalize) dσ.map i s0 hSi hms hmen, Option.some.injEq] at h
      subst h
      intro k hk
      exact (DenseExpr.subst_covered (hcorr.mapCov i s0 hms) htcov) k (DenseExpr.normalize_vars _ k hk)
    · rw [foldInsert_touched_miss ((dσ.revDeps[x]?).getD ∅) dσ.map (fun s => s.mentions x)
          (fun s => (s.subst x t).normalize) dσ.map i
          (fun ⟨s0, hS, hm, hmen⟩ => hhit ⟨hS, s0, hm, hmen⟩)] at h
      exact hcorr.mapCov i s h

/-- The emptiness test is preserved by one loop step (both maps gain the pivot, so both are
    non-empty). -/
theorem corr_step_isEmpty (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    {dσ : DenseSolved p} {σ : Solved p cs bs}
    (x : VarId) (t : DenseExpr p) (σ' : Solved p cs bs)
    (hmap : σ'.map
      = ((((σ.revDeps[reg.resolve x]?).getD ∅).toList.filterMap (fun y =>
          (σ.map[y]?).bind (fun s => if s.mentions (reg.resolve x) then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst (reg.resolve x) (reg.decodeExpr t)).normalize))
          ++ [(reg.resolve x, reg.decodeExpr t)]).foldl (fun m p => m.insert p.1 p.2) σ.map) :
    (dσ.insertAll ((((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
        (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))).map
        (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)])).map.isEmpty
      = σ'.map.isEmpty := by
  rw [DenseSolved.insertAll_map, foldl_insert_append_pair, hmap, foldl_insert_append_pair,
    Std.HashMap.isEmpty_insert, Std.HashMap.isEmpty_insert]

/-- Reverse-dependency correspondence is preserved by one loop step. Both loops add the same
    (bucket, key) pairs — the pivot's variables get the pivot key, and each rewritten stored solution
    contributes its variables — and set membership is order-free, so the buckets stay in step. -/
theorem corr_step_revDeps (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    {dσ : DenseSolved p} {σ : Solved p cs bs} (hcorr : Corr reg dσ σ)
    (x : VarId) (t : DenseExpr p) (hxv : reg.Valid x) (htcov : t.CoveredBy reg)
    (σ' : Solved p cs bs)
    (hrev : σ'.revDeps
      = ((((σ.revDeps[reg.resolve x]?).getD ∅).toList.filterMap (fun y =>
          (σ.map[y]?).bind (fun s => if s.mentions (reg.resolve x) then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst (reg.resolve x) (reg.decodeExpr t)).normalize))
          ++ [(reg.resolve x, reg.decodeExpr t)]).foldl
          (fun rd p => p.2.vars.foldl
            (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert p.1)) rd) σ.revDeps) :
    ∀ z, reg.Valid z → ∀ k, reg.Valid k →
      (k ∈ (((dσ.insertAll ((((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
          (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)])).revDeps[z]?).getD ∅)
        ↔ reg.resolve k ∈ ((σ'.revDeps[reg.resolve z]?).getD ∅)) := by
  intro z hz k hk
  -- The pivot-rewrite of a covered stored solution decodes as expected; its variables transfer.
  have hvarsEq : ∀ (s : DenseExpr p), s.CoveredBy reg →
      (z ∈ ((s.subst x t).normalize).vars ↔
        reg.resolve z ∈ (((reg.decodeExpr s).subst (reg.resolve x) (reg.decodeExpr t)).normalize).vars) := by
    intro s hcov_s
    have hcov_val : ((s.subst x t).normalize).CoveredBy reg := fun kk hkk =>
      (DenseExpr.subst_covered hcov_s htcov) kk (DenseExpr.normalize_vars _ kk hkk)
    have hdec : reg.decodeExpr ((s.subst x t).normalize)
        = ((reg.decodeExpr s).subst (reg.resolve x) (reg.decodeExpr t)).normalize := by
      rw [reg.decodeExpr_normalize (s.subst x t) (DenseExpr.subst_covered hcov_s htcov),
        reg.decodeExpr_subst hxv t s hcov_s]
    rw [← hdec, reg.decodeExpr_vars]
    exact (mem_map_resolve reg hz ((s.subst x t).normalize).vars hcov_val).symm
  have htvars : z ∈ t.vars ↔ reg.resolve z ∈ (reg.decodeExpr t).vars := by
    rw [reg.decodeExpr_vars]; exact (mem_map_resolve reg hz t.vars htcov).symm
  rw [DenseSolved.insertAll_revDeps, revDepsFold_mem DenseExpr.vars z k, hrev,
    revDepsFold_mem Expression.vars (reg.resolve z) (reg.resolve k),
    hcorr.revDeps z hz k hk]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨p, hp, hzp, hpk⟩
    rcases List.mem_append.1 hp with hpt | hpb
    · obtain ⟨s, hSi, hms, hmen, hp2⟩ :=
        (mem_touchedPairs ((dσ.revDeps[x]?).getD ∅) dσ.map (fun s => s.mentions x)
          (fun s => (s.subst x t).normalize) p.1 p.2).1 (by simpa using hpt)
      have hp1v : reg.Valid p.1 := hcorr.mapKeyValid p.1 s hms
      have hmapv := hcorr.mapVal p.1 hp1v
      rw [hms] at hmapv
      refine ⟨(reg.resolve p.1,
          ((reg.decodeExpr s).subst (reg.resolve x) (reg.decodeExpr t)).normalize), ?_, ?_, ?_⟩
      · refine List.mem_append.2 (Or.inl ?_)
        refine (mem_touchedPairs ((σ.revDeps[reg.resolve x]?).getD ∅) σ.map
          (fun s => s.mentions (reg.resolve x))
          (fun s => (s.subst (reg.resolve x) (reg.decodeExpr t)).normalize)
          (reg.resolve p.1) _).2 ⟨reg.decodeExpr s, ?_, ?_, ?_, rfl⟩
        · exact (hcorr.revDeps x hxv p.1 hp1v).1 hSi
        · simpa using hmapv.symm
        · rw [← reg.decodeExpr_mentions hxv s (hcorr.mapCov p.1 s hms)]; exact hmen
      · exact (hvarsEq s (hcorr.mapCov p.1 s hms)).1 (hp2 ▸ hzp)
      · rw [hpk]
    · rw [List.mem_singleton] at hpb
      subst hpb
      refine ⟨(reg.resolve x, reg.decodeExpr t), List.mem_append.2 (Or.inr (by simp)), ?_, ?_⟩
      · exact htvars.1 hzp
      · exact congrArg reg.resolve hpk
  · rintro ⟨q, hq, hzq, hqk⟩
    rcases List.mem_append.1 hq with hqt | hqb
    · obtain ⟨s', hSi', hms', hmen', hq2⟩ :=
        (mem_touchedPairs ((σ.revDeps[reg.resolve x]?).getD ∅) σ.map
          (fun s => s.mentions (reg.resolve x))
          (fun s => (s.subst (reg.resolve x) (reg.decodeExpr t)).normalize) q.1 q.2).1
          (by simpa using hqt)
      -- q.1 = resolve k, so the spec bucket member is resolve k; pull back to a dense witness.
      have hspecHit : reg.resolve k ∈ ((σ.revDeps[reg.resolve x]?).getD ∅)
          ∧ ∃ s', σ.map[reg.resolve k]? = some s' ∧ s'.mentions (reg.resolve x) = true := by
        rw [← hqk]; exact ⟨hSi', s', hms', hmen'⟩
      obtain ⟨hSk, s, hmk, hmenk⟩ := (hit_iff reg hcorr hxv hk).2 hspecHit
      refine ⟨(k, (s.subst x t).normalize), List.mem_append.2 (Or.inl ?_), ?_, rfl⟩
      · exact (mem_touchedPairs ((dσ.revDeps[x]?).getD ∅) dσ.map (fun s => s.mentions x)
          (fun s => (s.subst x t).normalize) k _).2 ⟨s, hSk, hmk, hmenk, rfl⟩
      · -- resolve z ∈ q.2.vars, and q.2 = spec-rewrite of s' = decode s
        have hmapk := hcorr.mapVal k hk
        rw [hmk] at hmapk
        have hqk' : σ.map[reg.resolve k]? = some s' := by rw [← hqk]; exact hms'
        rw [hqk'] at hmapk
        have hss : reg.decodeExpr s = s' := by simpa using hmapk
        have hzq' : reg.resolve z
            ∈ (((reg.decodeExpr s).subst (reg.resolve x) (reg.decodeExpr t)).normalize).vars := by
          rw [hss, ← hq2]; exact hzq
        exact (hvarsEq s (hcorr.mapCov k s hmk)).2 hzq'
    · rw [List.mem_singleton] at hqb
      subst hqb
      have hxk : x = k := reg.resolve_inj hxv hk hqk
      exact ⟨(x, t), List.mem_append.2 (Or.inr (by simp)), htvars.2 hzq, hxk⟩

/-- **One loop step preserves `Corr`.** `σ'` is any spec solution whose `map`/`revDeps` are the folds
    the spec `insertAll` produces (so the proof arguments are irrelevant); the five fields are the
    lemmas above. -/
theorem corr_step (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    {dσ : DenseSolved p} {σ : Solved p cs bs} (hcorr : Corr reg dσ σ)
    (x : VarId) (t : DenseExpr p) (hxv : reg.Valid x) (htcov : t.CoveredBy reg)
    (σ' : Solved p cs bs)
    (hmap : σ'.map
      = ((((σ.revDeps[reg.resolve x]?).getD ∅).toList.filterMap (fun y =>
          (σ.map[y]?).bind (fun s => if s.mentions (reg.resolve x) then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst (reg.resolve x) (reg.decodeExpr t)).normalize))
          ++ [(reg.resolve x, reg.decodeExpr t)]).foldl (fun m p => m.insert p.1 p.2) σ.map)
    (hrev : σ'.revDeps
      = ((((σ.revDeps[reg.resolve x]?).getD ∅).toList.filterMap (fun y =>
          (σ.map[y]?).bind (fun s => if s.mentions (reg.resolve x) then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst (reg.resolve x) (reg.decodeExpr t)).normalize))
          ++ [(reg.resolve x, reg.decodeExpr t)]).foldl
          (fun rd p => p.2.vars.foldl
            (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert p.1)) rd) σ.revDeps) :
    Corr reg
      (dσ.insertAll ((((dσ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
          (dσ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))).map
          (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)])) σ' :=
  ⟨corr_step_mapVal reg hcorr x t hxv htcov σ' hmap,
   corr_step_mapKeyValid reg hcorr x t hxv,
   corr_step_mapCov reg hcorr x t htcov,
   corr_step_isEmpty reg x t σ' hmap,
   corr_step_revDeps reg hcorr x t hxv htcov σ' hrev⟩

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

/-- Every `±1`-pivot solution of a covered constraint is covered. -/
theorem densePm1PivotsOf_covered (reg : VarRegistry) (c : DenseExpr p) (hc : c.CoveredBy reg)
    (w : VarId × DenseExpr p) (h : w ∈ densePm1PivotsOf c) : w.2.CoveredBy reg := by
  unfold densePm1PivotsOf at h
  cases hL : denseLinearize c with
  | none => rw [hL] at h; simp at h
  | some l =>
      rw [hL] at h
      obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
      intro k hk
      exact reg.denseLinearize_covered_terms hc hL k (denseTrySolve_vars_subset l v w hv k hk)

/-- Every unit-pivot solution of a covered constraint is covered. -/
theorem denseUnitPivotsOf_covered (reg : VarRegistry) (c : DenseExpr p) (hc : c.CoveredBy reg)
    (w : VarId × DenseExpr p) (h : w ∈ denseUnitPivotsOf c) : w.2.CoveredBy reg := by
  unfold denseUnitPivotsOf at h
  cases hL : denseLinearize c with
  | none => rw [hL] at h; simp at h
  | some l =>
      rw [hL] at h
      obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
      cases hts : l.trySolve v with
      | some r => rw [hts] at hv; simp at hv
      | none =>
          rw [hts] at hv
          intro k hk
          exact reg.denseLinearize_covered_terms hc hL k (denseTrySolveUnit_vars_subset l v w hv k hk)

/-- The pivot `denseFastBest` adopts has a valid key and a covered right-hand side. -/
theorem denseFastBest_pivot (reg : VarRegistry) (c : DenseExpr p) (hc : c.CoveredBy reg)
    (occ : Std.HashMap VarId Nat) (prot : Std.HashSet VarId) (x : VarId) (t : DenseExpr p)
    (h : denseFastBest c occ prot = some (x, t)) : reg.Valid x ∧ t.CoveredBy reg := by
  rw [denseFastBest_eq] at h
  have hmem : (x, t) ∈ densePm1PivotsOf c ++ denseUnitPivotsOf c :=
    List.argmin_mem (by rw [h]; exact Option.mem_some_self _)
  rcases List.mem_append.1 hmem with hp | hu
  · exact ⟨densePm1PivotsOf_valid reg c hc (x, t) hp, densePm1PivotsOf_covered reg c hc (x, t) hp⟩
  · exact ⟨denseUnitPivotsOf_valid reg c hc (x, t) hu, denseUnitPivotsOf_covered reg c hc (x, t) hu⟩

/-! ## The Gauss-loop bisimulation

**Main theorem.** With the occurrence-map / protected-set correspondences fixed, and the dense
pending list decoding elementwise (with every dense pending constraint covered) to the spec pending
list, `denseGaussLoop` and `gaussLoop` preserve `Corr`. Structural induction on the dense pending
list mirrors `gaussLoop`'s recursion: the reduced constraint `c'` decodes (map correspondence via
`decodeExpr_substF` + normalize commutation), so `denseFastBest c'` decodes to `fastBest`
(`denseFastBest_decode`); on `none` both loops skip, on `some` the adopted pivot decodes and
`corr_step` carries `Corr` through the shared `insertAll`. -/
theorem denseGaussLoop_corr (reg : VarRegistry) {cs : ConstraintSystem p} {bs : BusSemantics p}
    (occ' : Std.HashMap Variable Nat) (prot' : Std.HashSet Variable)
    (docc : Std.HashMap VarId Nat) (dprot : Std.HashSet VarId)
    (hocc : ∀ i, reg.Valid i → docc[i]? = occ'[reg.resolve i]?)
    (hprot : ∀ i, reg.Valid i → dprot.contains i = prot'.contains (reg.resolve i)) :
    ∀ (densePending : List (DenseExpr p)) (pending : List (Expression p)),
      densePending.map reg.decodeExpr = pending →
      (∀ c ∈ densePending, c.CoveredBy reg) →
      ∀ (hmem : ∀ c ∈ pending, c ∈ cs.algebraicConstraints)
        (dσ : DenseSolved p) (σ : Solved p cs bs),
        Corr reg dσ σ →
        Corr reg (denseGaussLoop docc dprot densePending dσ)
          (gaussLoop cs bs occ' prot' pending hmem σ) := by
  intro densePending
  induction densePending with
  | nil =>
      intro pending hpd _ hmem dσ σ hcorr
      simp only [List.map_nil] at hpd
      subst hpd
      simpa only [denseGaussLoop, gaussLoop] using hcorr
  | cons c rest ih =>
      intro pending hpd hcov hmem dσ σ hcorr
      simp only [List.map_cons] at hpd
      subst hpd
      have hchead : c.CoveredBy reg := hcov c (List.mem_cons_self ..)
      have hcovrest : ∀ c' ∈ rest, c'.CoveredBy reg :=
        fun c' hc' => hcov c' (List.mem_cons_of_mem _ hc')
      have hcsub_cov : (c.substF dσ.fn).CoveredBy reg :=
        DenseExpr.substF_covered hchead (fun i _ tt htt => hcorr.mapCov i tt htt)
      have hc'cov : ((c.substF dσ.fn).normalize).CoveredBy reg :=
        fun kk hkk => hcsub_cov kk (DenseExpr.normalize_vars _ kk hkk)
      have hc'dec : reg.decodeExpr ((c.substF dσ.fn).normalize)
          = ((reg.decodeExpr c).substF σ.fn).normalize := by
        rw [reg.decodeExpr_normalize (c.substF dσ.fn) hcsub_cov,
          reg.decodeExpr_substF dσ.fn σ.fn (fun i hi => hcorr.mapVal i hi) c hchead]
      have hfb := denseFastBest_decode reg ((c.substF dσ.fn).normalize) hc'cov docc occ' dprot prot'
        hocc hprot
      rw [hc'dec] at hfb
      cases hdfb : denseFastBest ((c.substF dσ.fn).normalize) docc dprot with
      | none =>
          rw [hdfb] at hfb
          simp only [Option.map_none] at hfb
          have hsfb : fastBest (((reg.decodeExpr c).substF σ.fn).normalize) occ' prot' = none :=
            hfb.symm
          simp only [denseGaussLoop, gaussLoop, hdfb]
          split
          · exact ih (rest.map reg.decodeExpr) rfl hcovrest _ dσ σ hcorr
          · rename_i x_s t_s heq
            rw [hsfb] at heq; exact absurd heq (by simp)
      | some xt =>
          obtain ⟨x, t⟩ := xt
          rw [hdfb] at hfb
          simp only [Option.map_some, VarRegistry.decodePivot] at hfb
          have hsfb : fastBest (((reg.decodeExpr c).substF σ.fn).normalize) occ' prot'
              = some (reg.resolve x, reg.decodeExpr t) := hfb.symm
          obtain ⟨hxv, htcov⟩ :=
            denseFastBest_pivot reg ((c.substF dσ.fn).normalize) hc'cov docc dprot x t hdfb
          simp only [denseGaussLoop, gaussLoop, hdfb]
          split
          · rename_i heq
            rw [hsfb] at heq; exact absurd heq (by simp)
          · rename_i x_s t_s heq
            rw [hsfb] at heq
            obtain ⟨rfl, rfl⟩ : x_s = reg.resolve x ∧ t_s = reg.decodeExpr t := by
              simp only [Option.some.injEq, Prod.mk.injEq] at heq; exact ⟨heq.1.symm, heq.2.symm⟩
            refine ih (rest.map reg.decodeExpr) rfl hcovrest _ _ _ ?_
            exact corr_step reg hcorr x t hxv htcov _
              (Solved.insertAll_map _ σ _ _) (Solved.insertAll_revDeps _ σ _ _)

/-! ## The dense Gauss-elimination pass

The `VarId`-native mirror of `gaussElimPass`: build the occurrence map / protected set, run
`denseGaussLoop` over two sweeps of the algebraic constraints, and — unless no pivot was adopted —
substitute the whole solution map through the system. The `Corr` bisimulation
(`denseGaussElim_corr`) makes the dense loop result correspond to the spec `σ`, so the two `if`
branches agree (`Corr.isEmptyEq`) and the substituted output decodes to the spec output
(`decodeCS_substF` via `Corr.mapVal`). The pass inherits `gaussElimPass`'s `PassCorrect` through
`ofTransform`. -/

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

/-- The spec `gaussElimPass`'s output as an explicit `if` (its `let`s zeta-reduce; the two branches'
    `.out` project to `cs` / `cs.substF σ.fn`). -/
theorem gaussElimPass_out (cs : ConstraintSystem p) (bs : BusSemantics p) :
    (gaussElimPass cs bs).out =
      if (gaussLoop cs bs (occurrenceMap cs) (protectedVars cs bs)
          (cs.algebraicConstraints ++ cs.algebraicConstraints)
          (fun _c hc => (List.mem_append.1 hc).elim id id) Solved.empty).map.isEmpty
      then cs
      else cs.substF (gaussLoop cs bs (occurrenceMap cs) (protectedVars cs bs)
          (cs.algebraicConstraints ++ cs.algebraicConstraints)
          (fun _c hc => (List.mem_append.1 hc).elim id id) Solved.empty).fn := by
  simp only [gaussElimPass]
  split <;> rfl

/-- The dense Gauss loop result corresponds (`Corr`) to the spec `gaussElimPass`'s `σ`: discharge
    `denseGaussLoop_corr`'s hypotheses from the occurrence-map / protected-set decode lemmas, the
    pending-list decode, system coverage, and the empty-map correspondence. -/
theorem denseGaussElim_corr (reg : VarRegistry) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (hc : d.CoveredBy reg) :
    Corr reg
      (denseGaussLoop (denseOccurrenceMap d) (denseProtectedVars d bs)
        (d.algebraicConstraints ++ d.algebraicConstraints) DenseSolved.empty)
      (gaussLoop (reg.decodeCS d) bs (occurrenceMap (reg.decodeCS d))
        (protectedVars (reg.decodeCS d) bs)
        ((reg.decodeCS d).algebraicConstraints ++ (reg.decodeCS d).algebraicConstraints)
        (fun _c hc => (List.mem_append.1 hc).elim id id) Solved.empty) := by
  refine denseGaussLoop_corr reg (occurrenceMap (reg.decodeCS d)) (protectedVars (reg.decodeCS d) bs)
    (denseOccurrenceMap d) (denseProtectedVars d bs)
    (denseOccurrenceMap_decode reg d hc) (denseProtectedVars_decode reg d bs hc)
    (d.algebraicConstraints ++ d.algebraicConstraints)
    ((reg.decodeCS d).algebraicConstraints ++ (reg.decodeCS d).algebraicConstraints)
    ?_ ?_ _ DenseSolved.empty Solved.empty (corr_empty reg)
  · show (d.algebraicConstraints ++ d.algebraicConstraints).map reg.decodeExpr
        = (reg.decodeCS d).algebraicConstraints ++ (reg.decodeCS d).algebraicConstraints
    rw [List.map_append]; rfl
  · intro c hc'
    exact hc.1 c ((List.mem_append.1 hc').elim id id)

/-! `denseGaussElimPass` (the wired pass) is now built and proved **natively** in
`OptimizerPasses/GaussProof.lean` via `DenseVerifiedPassW.ofNative` — no commutation with the
reference `gaussElimPass`. The commutation-era `Corr` cluster above is dead once that lands. -/

end ApcOptimizer.Dense
