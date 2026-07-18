import ApcOptimizer.Implementation.Dense.Adapter
import ApcOptimizer.Implementation.OptimizerPasses.Dedup

set_option autoImplicit false

/-! # Dense syntactic-duplicate removal (Task 3)

The dense mirror of `OptimizerPasses/Dedup.lean`: drop structurally-duplicate algebraic constraints
(`List.dedup`) and stateless bus interactions (keep-first, hash-bucketed), keeping the first
occurrence. Unlike the eval-preserving folds, dedup *compares whole values structurally* (equality
of `DenseExpr`/`BusInteraction (DenseExpr p)`), so its decode-commutation is **validity-gated**:
`resolve` is injective only on valid ids, so two dense values are structurally equal iff their
decodes are only when every leaf id is valid. The injectivity lemmas `decodeExpr_inj` /
`decodeBI_inj` therefore carry coverage hypotheses, and the pass discharges them from the threaded
coverage invariant.

Correctness rests on the exact structural comparison (`denseDedupStateless`, `List.dedup`); the
hash-bucketed `denseDedupStatelessFast` — the VarId-based mirror of the spec's `dedupStatelessFast`
— is proven equal to it (`denseDedupStatelessFast_eq`), so the pass runs the fast version yet
inherits the slow version's proof, exactly as the spec pass does. The pass is built with
`ofTransform`, inheriting `dedupPass`'s `PassCorrect`: the dense output decodes to exactly
`(decode d).dedupFast bs`, the spec pass's output. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

-- `DenseExpr` has decidable equality (needed for `List.dedup` and the `∈ seen` membership test);
-- it also induces `DecidableEq (BusInteraction (DenseExpr p))` via the generic instance.
deriving instance DecidableEq for DenseExpr

/-! ## Structural injectivity of decode under coverage

`resolve` is injective on valid ids, so `decodeExpr`/`decodeBI` are injective on *covered* values —
the fact that lets structural comparison commute with decode. -/

/-- **`decodeExpr` is injective on covered dense expressions.** -/
theorem VarRegistry.decodeExpr_inj (reg : VarRegistry) :
    ∀ {a b : DenseExpr p}, a.CoveredBy reg → b.CoveredBy reg →
      reg.decodeExpr a = reg.decodeExpr b → a = b := by
  intro a
  induction a with
  | const m =>
      intro b _ _ h
      cases b with
      | const n => simp only [VarRegistry.decodeExpr, Expression.const.injEq] at h; rw [h]
      | var j => simp [VarRegistry.decodeExpr] at h
      | add a2 b2 => simp [VarRegistry.decodeExpr] at h
      | mul a2 b2 => simp [VarRegistry.decodeExpr] at h
  | var i =>
      intro b hca hcb h
      cases b with
      | const n => simp [VarRegistry.decodeExpr] at h
      | var j =>
          simp only [VarRegistry.decodeExpr, Expression.var.injEq] at h
          have hvi : reg.Valid i := hca i (by simp [DenseExpr.vars])
          have hvj : reg.Valid j := hcb j (by simp [DenseExpr.vars])
          rw [reg.resolve_inj hvi hvj h]
      | add a2 b2 => simp [VarRegistry.decodeExpr] at h
      | mul a2 b2 => simp [VarRegistry.decodeExpr] at h
  | add a1 b1 iha ihb =>
      intro b hca hcb h
      cases b with
      | const n => simp [VarRegistry.decodeExpr] at h
      | var j => simp [VarRegistry.decodeExpr] at h
      | add a2 b2 =>
          simp only [VarRegistry.decodeExpr, Expression.add.injEq] at h
          obtain ⟨ha1, hb1⟩ := DenseExpr.coveredBy_add.mp hca
          obtain ⟨ha2, hb2⟩ := DenseExpr.coveredBy_add.mp hcb
          rw [iha ha1 ha2 h.1, ihb hb1 hb2 h.2]
      | mul a2 b2 => simp [VarRegistry.decodeExpr] at h
  | mul a1 b1 iha ihb =>
      intro b hca hcb h
      cases b with
      | const n => simp [VarRegistry.decodeExpr] at h
      | var j => simp [VarRegistry.decodeExpr] at h
      | add a2 b2 => simp [VarRegistry.decodeExpr] at h
      | mul a2 b2 =>
          simp only [VarRegistry.decodeExpr, Expression.mul.injEq] at h
          obtain ⟨ha1, hb1⟩ := DenseExpr.coveredBy_mul.mp hca
          obtain ⟨ha2, hb2⟩ := DenseExpr.coveredBy_mul.mp hcb
          rw [iha ha1 ha2 h.1, ihb hb1 hb2 h.2]

/-- `decodeExpr` is injective on lists of covered dense expressions (elementwise). -/
theorem VarRegistry.decodeExprs_inj (reg : VarRegistry) :
    ∀ {l1 l2 : List (DenseExpr p)}, (∀ e ∈ l1, e.CoveredBy reg) → (∀ e ∈ l2, e.CoveredBy reg) →
      l1.map reg.decodeExpr = l2.map reg.decodeExpr → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 _ _ h
      cases l2 with
      | nil => rfl
      | cons b r => simp at h
  | cons a rest ih =>
      intro l2 hc1 hc2 h
      cases l2 with
      | nil => simp at h
      | cons b rest2 =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hab, hrest⟩ := h
          rw [reg.decodeExpr_inj (hc1 a (List.mem_cons_self ..)) (hc2 b (List.mem_cons_self ..)) hab,
            ih (fun e he => hc1 e (List.mem_cons_of_mem _ he))
              (fun e he => hc2 e (List.mem_cons_of_mem _ he)) hrest]

/-- **`decodeBI` is injective on covered dense bus interactions.** -/
theorem VarRegistry.decodeBI_inj (reg : VarRegistry) {a b : BusInteraction (DenseExpr p)}
    (hca : denseBICovered reg a) (hcb : denseBICovered reg b)
    (h : reg.decodeBI a = reg.decodeBI b) : a = b := by
  obtain ⟨hma, hpa⟩ := hca
  obtain ⟨hmb, hpb⟩ := hcb
  simp only [VarRegistry.decodeBI, BusInteraction.mk.injEq] at h
  obtain ⟨hbus, hmult, hpay⟩ := h
  cases a with
  | mk ba ma pa =>
    cases b with
    | mk bb mb pb =>
      obtain rfl := hbus
      obtain rfl := reg.decodeExpr_inj hma hmb hmult
      obtain rfl := reg.decodeExprs_inj hpa hpb hpay
      rfl

/-! ## Dense algebraic dedup commutation (validity-gated) -/

/-- **`List.dedup` commutes with `decodeExpr`** on a covered list: dedup-then-decode equals
    decode-then-dedup, because `decodeExpr` is injective on the covered elements (so it neither
    merges nor splits duplicates). -/
theorem VarRegistry.map_dedup_decodeExpr (reg : VarRegistry) :
    ∀ (l : List (DenseExpr p)), (∀ e ∈ l, e.CoveredBy reg) →
      (l.dedup).map reg.decodeExpr = (l.map reg.decodeExpr).dedup := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro hc
      have hca : a.CoveredBy reg := hc a (List.mem_cons_self ..)
      have hcrest : ∀ e ∈ rest, e.CoveredBy reg := fun e he => hc e (List.mem_cons_of_mem _ he)
      by_cases h : a ∈ rest
      · rw [List.dedup_cons_of_mem h, List.map_cons,
          List.dedup_cons_of_mem (List.mem_map.2 ⟨a, h, rfl⟩), ih hcrest]
      · have hnm : reg.decodeExpr a ∉ rest.map reg.decodeExpr := by
          intro hcon
          rw [List.mem_map] at hcon
          obtain ⟨e, he, heq⟩ := hcon
          exact h (reg.decodeExpr_inj (hcrest e he) hca heq ▸ he)
        rw [List.dedup_cons_of_notMem h, List.map_cons, List.map_cons,
          List.dedup_cons_of_notMem hnm, ih hcrest]

/-! ## Dense keep-first stateless dedup (reference version) -/

/-- Drop a stateless interaction if an identical one was already kept; keep every stateful
    interaction unconditionally (mirrors `dedupStateless`). -/
def denseDedupStateless (bs : BusSemantics p) :
    (seen : List (BusInteraction (DenseExpr p))) → List (BusInteraction (DenseExpr p)) →
    List (BusInteraction (DenseExpr p))
  | _, [] => []
  | seen, bi :: rest =>
    if bs.isStateful bi.busId then bi :: denseDedupStateless bs seen rest
    else if bi ∈ seen then denseDedupStateless bs seen rest
    else bi :: denseDedupStateless bs (bi :: seen) rest

/-- Every kept interaction was in the input (mirrors `dedupStateless_subset`). -/
theorem denseDedupStateless_subset (bs : BusSemantics p) :
    ∀ (seen l : List (BusInteraction (DenseExpr p))),
      ∀ bi ∈ denseDedupStateless bs seen l, bi ∈ l := by
  intro seen l
  induction l generalizing seen with
  | nil => intro bi h; simp [denseDedupStateless] at h
  | cons b rest ih =>
    intro bi h
    rw [denseDedupStateless] at h
    split_ifs at h with h1 h2
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih seen bi h')
    · exact List.mem_cons_of_mem _ (ih seen bi h)
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (b :: seen) bi h')

/-- **Stateless dedup commutes with decode** (validity-gated through `decodeBI_inj`): the dense
    keep-first dedup, decoded, is the spec keep-first dedup on the decoded interactions, with the
    seen-set decoded pointwise. -/
theorem VarRegistry.denseDedupStateless_map (reg : VarRegistry) (bs : BusSemantics p) :
    ∀ (l seen : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ l, denseBICovered reg bi) → (∀ bi ∈ seen, denseBICovered reg bi) →
      (denseDedupStateless bs seen l).map reg.decodeBI
        = dedupStateless bs (seen.map reg.decodeBI) (l.map reg.decodeBI) := by
  intro l
  induction l with
  | nil => intro seen _ _; rfl
  | cons bi rest ih =>
      intro seen hcl hcseen
      have hcbi : denseBICovered reg bi := hcl bi (List.mem_cons_self ..)
      have hcrest : ∀ b ∈ rest, denseBICovered reg b :=
        fun b hb => hcl b (List.mem_cons_of_mem _ hb)
      by_cases hst : bs.isStateful bi.busId = true
      · have e1 : denseDedupStateless bs seen (bi :: rest)
              = bi :: denseDedupStateless bs seen rest := by
          rw [denseDedupStateless, if_pos hst]
        have e2 : dedupStateless bs (seen.map reg.decodeBI) ((bi :: rest).map reg.decodeBI)
              = reg.decodeBI bi
                :: dedupStateless bs (seen.map reg.decodeBI) (rest.map reg.decodeBI) := by
          rw [List.map_cons, dedupStateless,
            if_pos (show bs.isStateful (reg.decodeBI bi).busId = true from hst)]
        rw [e1, e2, List.map_cons, ih seen hcrest hcseen]
      · by_cases hmem : bi ∈ seen
        · have e1 : denseDedupStateless bs seen (bi :: rest)
                = denseDedupStateless bs seen rest := by
            rw [denseDedupStateless, if_neg hst, if_pos hmem]
          have e2 : dedupStateless bs (seen.map reg.decodeBI) ((bi :: rest).map reg.decodeBI)
                = dedupStateless bs (seen.map reg.decodeBI) (rest.map reg.decodeBI) := by
            rw [List.map_cons, dedupStateless,
              if_neg (show ¬ bs.isStateful (reg.decodeBI bi).busId = true from hst),
              if_pos (List.mem_map.2 ⟨bi, hmem, rfl⟩)]
          rw [e1, e2, ih seen hcrest hcseen]
        · have hnm : reg.decodeBI bi ∉ seen.map reg.decodeBI := by
            intro hcon
            rw [List.mem_map] at hcon
            obtain ⟨s, hs, hseq⟩ := hcon
            exact hmem (reg.decodeBI_inj (hcseen s hs) hcbi hseq ▸ hs)
          have hcseen' : ∀ b ∈ (bi :: seen), denseBICovered reg b := by
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hcbi
            · exact hcseen b hb'
          have e1 : denseDedupStateless bs seen (bi :: rest)
                = bi :: denseDedupStateless bs (bi :: seen) rest := by
            rw [denseDedupStateless, if_neg hst, if_neg hmem]
          have e2 : dedupStateless bs (seen.map reg.decodeBI) ((bi :: rest).map reg.decodeBI)
                = reg.decodeBI bi
                  :: dedupStateless bs (reg.decodeBI bi :: seen.map reg.decodeBI)
                      (rest.map reg.decodeBI) := by
            rw [List.map_cons, dedupStateless,
              if_neg (show ¬ bs.isStateful (reg.decodeBI bi).busId = true from hst), if_neg hnm]
          rw [e1, e2, List.map_cons, ih (bi :: seen) hcrest hcseen', List.map_cons]

/-! ## Hash-bucketed stateless dedup (VarId-based, mirrors `dedupStatelessFast`) -/

/-- A structural hash of a dense expression (for bucketing; VarId-based at the leaves). -/
def DenseExpr.bHash : DenseExpr p → UInt64
  | .const n => mixHash 11 (hash n.val)
  | .var i => mixHash 13 (hash i)
  | .add a b => mixHash 17 (mixHash a.bHash b.bHash)
  | .mul a b => mixHash 19 (mixHash a.bHash b.bHash)

/-- A structural hash of a dense interaction (bus id, multiplicity, payload). -/
def denseBIbHash (bi : BusInteraction (DenseExpr p)) : UInt64 :=
  mixHash (hash bi.busId)
    (mixHash bi.multiplicity.bHash (bi.payload.foldl (fun h e => mixHash h e.bHash) 7))

/-- `denseDedupStateless` with the `seen` set bucketed by `denseBIbHash`: each membership test
    scans only the matching bucket (mirrors `dedupStatelessFast`). -/
def denseDedupStatelessFast (bs : BusSemantics p)
    (seen : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))) :
    List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p))
  | [] => []
  | bi :: rest =>
    if bs.isStateful bi.busId then bi :: denseDedupStatelessFast bs seen rest
    else if bi ∈ seen.getD (denseBIbHash bi) [] then denseDedupStatelessFast bs seen rest
    else bi :: denseDedupStatelessFast bs
      (seen.insert (denseBIbHash bi) (bi :: seen.getD (denseBIbHash bi) [])) rest

/-- The bucketed dedup returns the identical list to `denseDedupStateless`, given a `seen` hash-map
    that agrees with the `seen` list on membership (mirrors `dedupStatelessFast_eq`). -/
theorem denseDedupStatelessFast_eq (bs : BusSemantics p)
    (bis : List (BusInteraction (DenseExpr p))) :
    ∀ (seenL : List (BusInteraction (DenseExpr p)))
      (seenH : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))),
      (∀ bi, bi ∈ seenL ↔ bi ∈ seenH.getD (denseBIbHash bi) []) →
      denseDedupStatelessFast bs seenH bis = denseDedupStateless bs seenL bis := by
  induction bis with
  | nil => intro _ _ _; rfl
  | cons bi rest ih =>
    intro seenL seenH h
    rw [denseDedupStatelessFast, denseDedupStateless]
    by_cases hst : bs.isStateful bi.busId = true
    · rw [if_pos hst, if_pos hst, ih seenL seenH h]
    · rw [if_neg hst, if_neg hst]
      by_cases hmem : bi ∈ seenL
      · rw [if_pos ((h bi).mp hmem), if_pos hmem, ih seenL seenH h]
      · rw [if_neg (fun hc => hmem ((h bi).mpr hc)), if_neg hmem,
          ih (bi :: seenL) (seenH.insert (denseBIbHash bi) (bi :: seenH.getD (denseBIbHash bi) []))
            (by
              intro x
              rw [Std.HashMap.getD_insert]
              by_cases hbh : denseBIbHash bi = denseBIbHash x
              · rw [if_pos (by simpa using hbh), List.mem_cons, List.mem_cons]
                have hx := h x
                rw [← hbh] at hx
                exact or_congr_right hx
              · have hxne : x ≠ bi := fun he => hbh (by rw [he])
                rw [if_neg (by simpa using hbh), List.mem_cons]
                exact (or_iff_right hxne).trans (h x))]

/-- The bucketed dedup, started empty, equals `denseDedupStateless` started empty. -/
theorem denseDedupStatelessFast_eq_nil (bs : BusSemantics p)
    (bis : List (BusInteraction (DenseExpr p))) :
    denseDedupStatelessFast bs ∅ bis = denseDedupStateless bs [] bis :=
  denseDedupStatelessFast_eq bs bis [] ∅ (by intro bi; simp [Std.HashMap.getD_empty])

/-! ## The deduplicated dense system -/

/-- The deduplicated dense system (reference: keep-first stateless dedup). -/
def DenseConstraintSystem.dedup (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.dedup,
    busInteractions := denseDedupStateless bs [] d.busInteractions }

/-- The deduplicated dense system, computed with the hash-bucketed stateless dedup. Equal to
    `DenseConstraintSystem.dedup` (`dedupFast_eq`). -/
def DenseConstraintSystem.dedupFast (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.dedup,
    busInteractions := denseDedupStatelessFast bs ∅ d.busInteractions }

theorem DenseConstraintSystem.dedupFast_eq (d : DenseConstraintSystem p) (bs : BusSemantics p) :
    d.dedupFast bs = d.dedup bs := by
  simp only [DenseConstraintSystem.dedupFast, DenseConstraintSystem.dedup,
    denseDedupStatelessFast_eq_nil]

/-- Dedup only drops interactions and constraints, so it preserves coverage. -/
theorem DenseConstraintSystem.dedup_covered {reg : VarRegistry} {d : DenseConstraintSystem p}
    {bs : BusSemantics p} (hc : d.CoveredBy reg) : (d.dedup bs).CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hc
  constructor
  · intro e he
    simp only [DenseConstraintSystem.dedup] at he
    exact hac e (List.mem_dedup.1 he)
  · intro bi hbimem
    simp only [DenseConstraintSystem.dedup] at hbimem
    exact hbi bi (denseDedupStateless_subset bs [] d.busInteractions bi hbimem)

/-- **The dedup commutes with decode** on a covered system: the dense deduplicated system decodes to
    the spec deduplicated system of the decoded input. -/
theorem VarRegistry.decodeCS_dedup (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (hc : d.CoveredBy reg) :
    reg.decodeCS (d.dedup bs) = (reg.decodeCS d).dedup bs := by
  obtain ⟨hac, hbi⟩ := hc
  simp only [DenseConstraintSystem.dedup, ConstraintSystem.dedup, VarRegistry.decodeCS]
  congr 1
  · exact reg.map_dedup_decodeExpr d.algebraicConstraints hac
  · have hmap := reg.denseDedupStateless_map bs d.busInteractions [] hbi (by intro bi hbi; simp at hbi)
    simpa using hmap

/-! ## The dense dedup pass -/

/-- The dense duplicate-removal pass (runs the hash-bucketed dedup). Its `PassCorrect` is inherited
    from the spec `dedupPass` — the dense output decodes to exactly `(decode d).dedupFast bs`, the
    spec pass's output. -/
def denseDedupPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofTransform
    (fun bs d => d.dedupFast bs)
    dedupPass.withFacts
    (fun reg bs d hc => by
      show (d.dedupFast bs).CoveredBy reg
      rw [DenseConstraintSystem.dedupFast_eq]
      exact DenseConstraintSystem.dedup_covered hc)
    (fun reg bs facts d hc => by
      show reg.decodeCS (d.dedupFast bs) = (dedupPass.withFacts (reg.decodeCS d) bs facts).out
      have hR : (dedupPass.withFacts (reg.decodeCS d) bs facts).out = (reg.decodeCS d).dedup bs := by
        show (reg.decodeCS d).dedupFast bs = (reg.decodeCS d).dedup bs
        exact ConstraintSystem.dedupFast_eq _ _
      rw [hR, DenseConstraintSystem.dedupFast_eq]
      exact reg.decodeCS_dedup bs d hc)
    (fun _ _ _ => rfl)

end ApcOptimizer.Dense
