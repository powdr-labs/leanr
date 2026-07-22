import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelLive
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense witness/form indices for `busPairCancel` (Task 3, chunk C6)

Dense, `VarId`-native transliteration of the *witness-index* slice of
`OptimizerPasses/BusPairCancel.lean` (:2105-2310), the per-invocation position indices the
acceptance test consults for bound-deriving witnesses (`buildBoundIdx`/`dropWitsIdxGo`/
`firstBoundIn`/`dropWits`) and range-checked-form witnesses (`buildFormIdx`/`dropFormWits`), plus
the thin `_mem` proof layer that guarantees every returned witness is a live interaction other than
the dropped pair — the exact shape C7's `cancelLoop` feeds into C5's `denseCheckCancel_sound`
`hwits`/`hfwits` hypotheses. Impl + its (small) proof layer live together here.

## `denseInteractionBoundPat` — the payload-pattern-hoisted variant (spec #164)

`interactionBoundPat` (`OptimizerPasses/DomainProp.lean:325`) is `interactionBound` with the
per-*interaction* multiplicity constant and constant-payload pattern hoisted out of the per-payload-
*variable* loop of `buildBoundIdx` (callers querying every payload variable would otherwise recompute
the full-payload pattern fold once per variable). Definitionally the same function at the canonical
arguments (`interactionBoundPat_eq`, `rfl`). We mirror that hoisting relationship exactly on the
dense side: `denseInteractionBoundPat` (defined here) relates to `denseInteractionBound`
(`Dense/DigitFold.lean:118`) precisely as `interactionBoundPat` relates to `interactionBound` —
`denseInteractionBoundPat_eq` is likewise `rfl`. It is placed in this file (rather than beside
`denseInteractionBound`) because `buildBoundIdx` is its only current consumer; **flagged for a future
`domainBatch` delta re-port**: should a dense `domainBatch` need the pattern-hoisted variant (as the
spec's #164 rework threads it), reuse `denseInteractionBoundPat` here rather than re-deriving it,
matching the precedent `Dense/BusPairCancelCheck.lean` set for `denseMkByteCheck`.

## Untrusted indices, re-checked at use

`denseBuildBoundIdx`/`denseBuildFormIdx` build candidate-position lists **once** over the initial
`arr`. They are *untrusted*: a stale or wrong entry costs time, never soundness, because
`denseDropWitsIdxGo`/`denseDropFormWits` re-check, at every use, that the position is in range, still
**live** (`alive[k]?`), distinct from the dropped pair (`≠ S`, `≠ R`), and — for the bound witness —
that it *still* derives a `denseInteractionBound`. Hence no `_mem`/correctness lemma is ported for the
two builders (mirroring the spec, which proves none): the `_mem` guarantees below rest entirely on
the re-checks in the lookups. Fold order and the dedup-head skip
(`(m.getD v []).head? = some bik.2`) are preserved byte-for-byte from the spec.

## The `_mem` layer and its C5/C7 connection

`denseDropWitsIdxGo_mem`/`denseDropFormWits_mem` (and the helper `denseFirstBoundIn_mem`) prove every
returned witness lies in `denseLiveSeg arr alive 0 arr.size` and differs from `S`/`R` — via C4's
`denseLiveSeg_mem` (`Dense/BusPairCancelLive.lean`), the connector between a re-checked live position
and the ghost live projection. `denseDropWits_mem`/`denseDropFormWits_mem` then lift that to
`bi ∈ A ++ B ++ C ++ emitted`, given the caller's split of the live entries other than the pair into
`A ++ B ++ C` (`horig`) and of the previously-emitted checks (`hchecks`). C7's `cancelLoop` supplies
`horig`/`hchecks` from `denseLiveSeg_split`, instantiates `emitted := checks`, and hands the results
straight to C5's `denseCheckCancel_sound` as `hwits`/`hfwits`
(`∀ v, ∀ bi ∈ wits v, bi ∈ A ++ B ++ C ++ checks`). The lemmas are stated generically in `A B C` in
exactly that shape. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ### `denseInteractionBoundPat` (pattern-hoisted `denseInteractionBound`) -/

/-- `denseInteractionBound` with the multiplicity constant and the constant-payload pattern computed
    once by the caller — they are per-*interaction* values, and callers that query every payload
    variable of an interaction would otherwise recompute the pattern (a full payload fold) per
    variable. Definitionally the same function at the canonical arguments
    (`denseInteractionBoundPat_eq`). Native mirror of `interactionBoundPat`
    (`OptimizerPasses/DomainProp.lean:325`). -/
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

/-! ### The bound-witness position index -/

/-- Candidate positions of bound-deriving interactions, per variable: every array position whose
    interaction derives a `denseInteractionBound` for the variable, ascending. Built once per
    invocation (the per-interaction multiplicity constant and constant-payload pattern are hoisted
    via `denseInteractionBoundPat`); **untrusted** — `denseDropWitsIdxGo` re-checks liveness, the
    dropped pair, and the bound itself at every use, so a stale or wrong entry costs time, never
    soundness. Mirrors `buildBoundIdx` (`OptimizerPasses/BusPairCancel.lean:2112`). -/
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
    skipping dead entries and any value equal to the dropped pair) that still derives a
    `denseInteractionBound` for `v` — exactly the interaction the full array scan found first, at
    bucket cost. Mirrors `dropWitsIdxGo` (`OptimizerPasses/BusPairCancel.lean:2133`). -/
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
    the emitted byte checks, which live outside the stable array (`checksOld`), preserving the old
    compact-array behaviour where the emitted checks sat in the array's tail and could witness an
    earlier pair's byte bound. Mirrors `firstBoundIn`
    (`OptimizerPasses/BusPairCancel.lean:2151`). -/
def denseFirstBoundIn {bs : BusSemantics p} (facts : BusFacts p bs) (v : VarId) :
    List (BusInteraction (DenseExpr p)) → Option (BusInteraction (DenseExpr p))
  | [] => none
  | bi :: rest =>
    match denseInteractionBound bs facts bi v with
    | some _ => some bi
    | none => denseFirstBoundIn facts v rest

/-- The witness lookup for a candidate drop: the first bound-deriving interaction other than the
    dropped pair — first among the live stable-array entries (through the per-variable position
    index `bidx`, ascending, exactly the order the old full-array scan visited), then among the
    previously-emitted checks `checksOld` — followed by this drop's emitted checks. Every returned
    interaction is a member of the remaining region (`denseDropWits_mem`). Mirrors `dropWits`
    (`OptimizerPasses/BusPairCancel.lean:2165`). -/
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

/-! ### The range-checked-form witness index -/

/-- Candidate positions for range-checked forms, per variable: interactions on a *stateless* bus
    (this pass only ever tombstones stateful memory pairs) carrying a compound payload slot that
    mentions the variable, at most four per variable. Built once per invocation; **untrusted** —
    `denseDropFormWits` re-checks liveness and the dropped pair at every use, so a stale or wrong
    entry costs time, never soundness. Mirrors `buildFormIdx`
    (`OptimizerPasses/BusPairCancel.lean:2264`). -/
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
    `denseBasisJustified` mines for bounded linear forms. Mirrors `dropFormWits`
    (`OptimizerPasses/BusPairCancel.lean:2279`). -/
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

/-! ### The `_mem` proof layer (native)

Every returned witness is a live interaction at a position `≠ S`/`≠ R` — i.e. a member of the
post-drop `denseLiveSeg` projection, mapped into `A ++ B ++ C ++ emitted`. These are the
`hwits`/`hfwits` membership hypotheses C5's `denseCheckCancel_sound` consumes; C7 threads
`denseLiveSeg`-projected `A`/`B`/`C` and this drop's `checks` as `emitted`. -/

/-- Every witness the indexed scan returns is a live entry other than the dropped pair — via C4's
    `denseLiveSeg_mem`. Native mirror of `dropWitsIdxGo_mem`
    (`OptimizerPasses/BusPairCancel.lean:2178`). -/
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
    · -- in range, live, not the dropped pair
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

/-- Every interaction `denseFirstBoundIn` returns is a member of the scanned list. Native mirror of
    `firstBoundIn_mem` (`OptimizerPasses/BusPairCancel.lean:2212`). -/
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
    checks `checksOld`. Native mirror of `dropWits_mem`
    (`OptimizerPasses/BusPairCancel.lean:2228`). -/
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

/-- Every form witness is in the remaining region (the index entry is re-checked at use). Native
    mirror of `dropFormWits_mem` (`OptimizerPasses/BusPairCancel.lean:2291`). -/
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
