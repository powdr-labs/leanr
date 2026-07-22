import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelLive
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense witness/form indices for `busPairCancel`

The per-invocation position indices the acceptance test consults for bound-deriving witnesses
(`denseBuildBoundIdx`/`denseDropWits`) and range-checked-form witnesses
(`denseBuildFormIdx`/`denseDropFormWits`), plus the `_mem` layer proving every returned witness is a
live interaction other than the dropped pair (the `hwits`/`hfwits` shape `denseCheckCancel_sound`
takes).

The builders are **untrusted**: a stale or wrong entry costs time, never soundness, because the
lookups re-check at every use that the position is in range, still live, distinct from the pair, and
(for the bound witness) still derives a `denseInteractionBound`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `denseInteractionBound` with the multiplicity constant and constant-payload pattern hoisted out
    of the caller's per-payload-variable loop (they are per-interaction values). Definitionally the
    same function at the canonical arguments (`denseInteractionBoundPat_eq`). -/
def denseInteractionBoundPat (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (mval? : Option (ZMod p))
    (pat : List (Option (ZMod p))) (i : VarId) : Option Nat :=
  match mval? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval pat slot

/-- Candidate positions of bound-deriving interactions, per variable (ascending), built once per
    invocation. Untrusted — `denseDropWitsIdxGo` re-checks liveness, the dropped pair, and the bound
    at every use. -/
def denseBuildBoundIdx (bs : BusSemantics p) (facts : BusFacts p bs)
    (arr : Array (BusInteraction (DenseExpr p))) : Std.HashMap VarId (List Nat) :=
  (arr.toList.zipIdx).foldr (fun bik m =>
    let bi := bik.1
    let mval? := bi.multiplicity.constValue?
    let pat := bi.payload.map DenseExpr.constValue?
    bi.payload.foldl (fun m e =>
      match e with
      | .var v =>
        -- skip repeated occurrences of the same variable within one payload
        if (m.getD v []).head? = some bik.2 then m
        else
          match denseInteractionBoundPat bs facts bi mval? pat v with
          | some _ => m.insert v (bik.2 :: m.getD v [])
          | none => m
      | _ => m) m) ∅

/-- The scan behind `denseDropWits`: the first of `v`'s indexed candidate positions (ascending,
    skipping dead entries and the dropped pair) that still derives a `denseInteractionBound` for
    `v`. -/
def denseDropWitsIdxGo {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (v : VarId) : List Nat → Option (BusInteraction (DenseExpr p))
  | [] => none
  | k :: ks =>
    if h : k < arr.size then
      if alive[k]?.getD false && !decide (arr[k] = S) && !decide (arr[k] = R) then
        match denseInteractionBound bs facts arr[k] v with
        | some _ => some arr[k]
        | none => denseDropWitsIdxGo facts arr alive S R v ks
      else denseDropWitsIdxGo facts arr alive S R v ks
    else denseDropWitsIdxGo facts arr alive S R v ks

/-- First interaction of a plain list deriving a `denseInteractionBound` for `v` — used to consult
    the emitted byte checks `checksOld`, which live outside the stable array. -/
def denseFirstBoundIn {bs : BusSemantics p} (facts : BusFacts p bs) (v : VarId) :
    List (BusInteraction (DenseExpr p)) → Option (BusInteraction (DenseExpr p))
  | [] => none
  | bi :: rest =>
    match denseInteractionBound bs facts bi v with
    | some _ => some bi
    | none => denseFirstBoundIn facts v rest

/-- The witness lookup for a candidate drop: the first bound-deriving interaction other than the
    dropped pair — first among the live stable-array entries (via `bidx`), then among the
    previously-emitted checks `checksOld` — followed by this drop's emitted checks. -/
def denseDropWits {bs : BusSemantics p} (facts : BusFacts p bs)
    (bidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (checksOld emitted : List (BusInteraction (DenseExpr p))) (v : VarId) :
    List (BusInteraction (DenseExpr p)) :=
  match denseDropWitsIdxGo facts arr alive S R v (bidx.getD v []) with
  | some bi => bi :: emitted
  | none =>
    match denseFirstBoundIn facts v checksOld with
    | some bi => bi :: emitted
    | none => emitted

/-- Candidate positions for range-checked forms, per variable: interactions on a *stateless* bus
    carrying a compound payload slot mentioning the variable, at most four per variable. Untrusted —
    `denseDropFormWits` re-checks liveness and the dropped pair at every use. -/
def denseBuildFormIdx (bs : BusSemantics p) (arr : Array (BusInteraction (DenseExpr p))) :
    Std.HashMap VarId (List Nat) :=
  (arr.toList.zipIdx).foldl (fun m bik =>
    if bs.isStateful bik.1.busId then m
    else
      bik.1.payload.foldl (fun m e =>
        if e.isSingleVar then m
        else
          e.vars.dedup.foldl (fun m v =>
            let cur := m.getD v []
            if cur.length < 4 then m.insert v (bik.2 :: cur) else m) m) m) ∅

/-- The range-checked-form witness lookup for a candidate drop: the indexed candidate positions
    for `v`, re-checked live and distinct from the dropped pair — the interactions
    `denseBasisJustified` mines for bounded linear forms. -/
def denseDropFormWits (fidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p)) (v : VarId) :
    List (BusInteraction (DenseExpr p)) :=
  (fidx.getD v []).filterMap (fun k =>
    if h : k < arr.size then
      if alive[k]?.getD false && !decide (arr[k] = S) && !decide (arr[k] = R) then
        some arr[k]
      else none
    else none)

/-! ### The `_mem` proof layer

Every returned witness is a live interaction at a position `≠ S`/`≠ R`, mapped into
`A ++ B ++ C ++ emitted` — the `hwits`/`hfwits` hypotheses `denseCheckCancel_sound` consumes. -/

/-- Every witness the indexed scan returns is a live entry other than the dropped pair. -/
theorem denseDropWitsIdxGo_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (v : VarId) :
    ∀ (ks : List Nat) {bi : BusInteraction (DenseExpr p)},
      denseDropWitsIdxGo facts arr alive S R v ks = some bi →
      bi ∈ denseLiveSeg arr alive 0 arr.size ∧ bi ≠ S ∧ bi ≠ R := by
  intro ks
  induction ks with
  | nil =>
    intro bi h
    exact absurd h (by simp [denseDropWitsIdxGo])
  | cons k rest ih =>
    intro bi h
    rw [denseDropWitsIdxGo] at h
    split_ifs at h with hk hcond
    ·
      revert h
      cases hb : denseInteractionBound bs facts arr[k] v with
      | some b =>
        intro h
        obtain rfl := Option.some.inj h
        rw [Bool.and_eq_true, Bool.and_eq_true] at hcond
        obtain ⟨⟨hal, hnS⟩, hnR⟩ := hcond
        refine ⟨denseLiveSeg_mem arr alive 0 arr.size k arr[k] (Nat.zero_le _) (by omega) hal
            (Array.getElem?_eq_getElem hk), ?_, ?_⟩
        · exact fun he => by simp [he] at hnS
        · exact fun he => by simp [he] at hnR
      | none =>
        intro h
        exact ih h
    · exact ih h
    · exact ih h

/-- Every interaction `denseFirstBoundIn` returns is a member of the scanned list. -/
theorem denseFirstBoundIn_mem {bs : BusSemantics p} (facts : BusFacts p bs) (v : VarId) :
    ∀ (l : List (BusInteraction (DenseExpr p))) {bi : BusInteraction (DenseExpr p)},
      denseFirstBoundIn facts v l = some bi → bi ∈ l := by
  intro l
  induction l with
  | nil => intro bi h; simp [denseFirstBoundIn] at h
  | cons hd tl ih =>
    intro bi h
    rw [denseFirstBoundIn] at h
    cases hb : denseInteractionBound bs facts hd v with
    | some b => rw [hb] at h; obtain rfl := Option.some.inj h; exact List.mem_cons.2 (Or.inl rfl)
    | none => rw [hb] at h; exact List.mem_cons_of_mem _ (ih h)

/-- Every witness the lookup returns is in the remaining region, given that the live stable-array
    entries other than the dropped pair are in `A ++ B ++ C`, and so are the previously-emitted
    checks `checksOld`. -/
theorem denseDropWits_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (bidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (checksOld emitted : List (BusInteraction (DenseExpr p)))
    {A B C : List (BusInteraction (DenseExpr p))}
    (horig : ∀ bi ∈ denseLiveSeg arr alive 0 arr.size, bi ≠ S → bi ≠ R → bi ∈ A ++ B ++ C)
    (hchecks : ∀ bi ∈ checksOld, bi ∈ A ++ B ++ C) :
    ∀ v, ∀ bi ∈ denseDropWits facts bidx arr alive S R checksOld emitted v,
      bi ∈ A ++ B ++ C ++ emitted := by
  intro v bi hbi
  unfold denseDropWits at hbi
  cases hgo : denseDropWitsIdxGo facts arr alive S R v (bidx.getD v []) with
  | some bi' =>
    rw [hgo] at hbi
    rcases List.mem_cons.1 hbi with rfl | hbi
    · obtain ⟨hmem, hne1, hne2⟩ := denseDropWitsIdxGo_mem facts arr alive S R v _ hgo
      exact List.mem_append_left _ (horig bi hmem hne1 hne2)
    · exact List.mem_append_right _ hbi
  | none =>
    rw [hgo] at hbi
    cases hfb : denseFirstBoundIn facts v checksOld with
    | some bi' =>
      rw [hfb] at hbi
      rcases List.mem_cons.1 hbi with rfl | hbi
      · exact List.mem_append_left _ (hchecks bi (denseFirstBoundIn_mem facts v checksOld hfb))
      · exact List.mem_append_right _ hbi
    | none =>
      rw [hfb] at hbi
      exact List.mem_append_right _ hbi

/-- Every form witness is in the remaining region (the index entry is re-checked at use). -/
theorem denseDropFormWits_mem (fidx : Std.HashMap VarId (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    {A B C : List (BusInteraction (DenseExpr p))}
    (horig : ∀ bi ∈ denseLiveSeg arr alive 0 arr.size, bi ≠ S → bi ≠ R → bi ∈ A ++ B ++ C)
    (emitted : List (BusInteraction (DenseExpr p))) :
    ∀ v, ∀ bi ∈ denseDropFormWits fidx arr alive S R v, bi ∈ A ++ B ++ C ++ emitted := by
  intro v bi hbi
  rw [denseDropFormWits, List.mem_filterMap] at hbi
  obtain ⟨k, _, heq⟩ := hbi
  split_ifs at heq with hk hcond
  · obtain rfl := Option.some.inj heq
    rw [Bool.and_eq_true, Bool.and_eq_true] at hcond
    obtain ⟨⟨hal, hnS⟩, hnR⟩ := hcond
    refine List.mem_append_left _ (horig arr[k]
      (denseLiveSeg_mem arr alive 0 arr.size k _ (Nat.zero_le _) (by omega) hal
        (Array.getElem?_eq_getElem hk)) ?_ ?_)
    · exact fun he => by simp [he] at hnS
    · exact fun he => by simp [he] at hnR

end ApcOptimizer.Dense
