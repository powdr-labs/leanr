import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.Dense.DigitFold
import ApcOptimizer.Implementation.Dense.Normalize
import ApcOptimizer.Implementation.Dense.Gauss
import ApcOptimizer.Implementation.Dense.Rewrite

set_option autoImplicit false

/-! # Dense finite-domain-table construction (Task 3 — DomainBatch, part 1)

Dense, `VarId`-native port of the domain-derivation layer of
`OptimizerPasses/DomainBatch.lean`: the table of finite domains derived from product-of-affine-factor
constraints (`rootsIn`) and from fact-bounded bus payload slots (`interactionDomainF`).

`FiniteDomain p` is variable-free, so it is reused verbatim (values are *equal*, not decoded). The
runtime dense table is a plain `Std.HashMap VarId (FiniteDomain p)` (no soundness field); its
correctness flows through the correspondence proved here: the dense table decodes, value-for-value
under `resolve`, to the spec `DomainTable`'s `map` on the decoded system. The fact-consuming
`interactionDomainF` reuses the *unchanged* `facts : BusFacts p bs` (keyed by bus IDs + field
patterns, VM-neutral) via `denseInteractionBound` from `Dense/DigitFold.lean` — the DigitFold
fact-layer template.

Only the domain-derivation layer is ported here; the joint enumeration (`collectForced`/`forcedOver`/
`compileE`/`scanBox`) and the pass itself are later chunks. Nothing is wired into the pipeline. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense `rootsIn`

`rootsIn` returns a variable-free `List (ZMod p)`, so the dense mirror produces the *same* value; the
correspondence is `rootsIn (resolve i) (decodeExpr e) = denseRootsIn i e`. The only variable
comparison is `y = x` in the single-term case, decided identically by `resolve`-injectivity on valid
ids. -/

/-- Dense `rootsOfTerms` (mirrors `rootsOfTerms`). -/
def denseRootsOfTerms (i : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → Option (List (ZMod p))
  | [] => if c = 0 then none else some []
  | [(j, a)] =>
      let r := -(a⁻¹ * c)
      if j = i ∧ a ≠ 0 ∧ a * r + c = 0 then some [r] else none
  | _ :: _ :: _ => none

theorem denseRootsOfTerms_decode (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) (c : ZMod p)
    (ts : List (VarId × ZMod p)) (hts : ∀ t ∈ ts, reg.Valid t.1) :
    rootsOfTerms (reg.resolve i) c (ts.map (fun t => (reg.resolve t.1, t.2)))
      = denseRootsOfTerms i c ts := by
  rcases ts with _ | ⟨⟨j, a⟩, _ | ⟨t2, rest⟩⟩
  · rfl
  · have hjv : reg.Valid j := hts (j, a) (by simp)
    have hcond : (reg.resolve j = reg.resolve i) = (j = i) :=
      propext ⟨fun h => reg.resolve_inj hjv hi h, fun h => by rw [h]⟩
    simp only [List.map_cons, List.map_nil, rootsOfTerms, denseRootsOfTerms, hcond]
  · rfl

/-- Dense `affineRootsIn` (mirrors `affineRootsIn`), through `denseLinearize` + `DenseLinExpr.norm`. -/
def denseAffineRootsIn (i : VarId) (e : DenseExpr p) : Option (List (ZMod p)) :=
  (denseLinearize e).bind (fun l => denseRootsOfTerms i l.norm.const l.norm.terms)

theorem denseAffineRootsIn_decode (reg : VarRegistry) {i : VarId} (hi : reg.Valid i)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    affineRootsIn (reg.resolve i) (reg.decodeExpr e) = denseAffineRootsIn i e := by
  unfold affineRootsIn denseAffineRootsIn
  rw [← reg.denseLinearize_decode e]
  cases hdl : denseLinearize e with
  | none => rfl
  | some l =>
      show rootsOfTerms (reg.resolve i) (reg.decodeLin l).norm.const (reg.decodeLin l).norm.terms
        = denseRootsOfTerms i l.norm.const l.norm.terms
      have hltv : ∀ i' ∈ l.terms.map Prod.fst, reg.Valid i' :=
        reg.denseLinearize_covered_terms hc hdl
      rw [← reg.decodeLin_norm l hltv]
      show rootsOfTerms (reg.resolve i) l.norm.const
          (l.norm.terms.map (fun t => (reg.resolve t.1, t.2)))
        = denseRootsOfTerms i l.norm.const l.norm.terms
      exact denseRootsOfTerms_decode reg hi l.norm.const l.norm.terms
        (fun t ht => hltv t.1 (l.norm_terms_fst t.1 (List.mem_map.2 ⟨t, ht, rfl⟩)))

/-- Dense `rootsIn` (mirrors `rootsIn`): affine roots, recursing into a product's factors. -/
def denseRootsIn (i : VarId) : DenseExpr p → Option (List (ZMod p))
  | .const n => denseAffineRootsIn i (.const n)
  | .var j => denseAffineRootsIn i (.var j)
  | .add a b => denseAffineRootsIn i (.add a b)
  | .mul a b =>
    match denseAffineRootsIn i (.mul a b) with
    | some r => some r
    | none =>
      match denseRootsIn i a, denseRootsIn i b with
      | some ra, some rb => some (ra ++ rb)
      | _, _ => none

theorem denseRootsIn_decode (reg : VarRegistry) {i : VarId} (hi : reg.Valid i)
    (e : DenseExpr p) (hc : e.CoveredBy reg) :
    rootsIn (reg.resolve i) (reg.decodeExpr e) = denseRootsIn i e := by
  induction e with
  | const n => exact denseAffineRootsIn_decode reg hi _ hc
  | var j => exact denseAffineRootsIn_decode reg hi _ hc
  | add a b _ _ => exact denseAffineRootsIn_decode reg hi _ hc
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      show (match affineRootsIn (reg.resolve i) (reg.decodeExpr (a.mul b)) with
            | some r => some r
            | none =>
              match rootsIn (reg.resolve i) (reg.decodeExpr a),
                    rootsIn (reg.resolve i) (reg.decodeExpr b) with
              | some ra, some rb => some (ra ++ rb)
              | _, _ => none)
        = (match denseAffineRootsIn i (a.mul b) with
            | some r => some r
            | none =>
              match denseRootsIn i a, denseRootsIn i b with
              | some ra, some rb => some (ra ++ rb)
              | _, _ => none)
      rw [denseAffineRootsIn_decode reg hi (a.mul b) hc, iha ha, ihb hb]

/-! ## The dense domain table

A plain runtime structure wrapping `Std.HashMap VarId (FiniteDomain p)`; correctness comes from the
correspondence, not a carried invariant. -/

/-- Finite domains for `VarId`s (runtime-only; no soundness field). -/
structure DenseDomainTable (p : ℕ) where
  map : Std.HashMap VarId (FiniteDomain p)

/-- The empty dense domain table. -/
def DenseDomainTable.empty : DenseDomainTable p := ⟨∅⟩

/-- Insert an entailed domain, keeping the smaller of two candidate domains (mirrors
    `DomainTable.insertEntry`'s keep-smaller data logic). -/
def DenseDomainTable.insertEntry (T : DenseDomainTable p) (i : VarId) (d : FiniteDomain p) :
    DenseDomainTable p :=
  let keep : Bool := match T.map[i]? with
    | some d0 => decide (d.size < d0.size)
    | none => true
  if keep then ⟨T.map.insert i d⟩ else T

/-- The table's domains for a `VarId` list, all-or-nothing (mirrors `DomainTable.doms`). -/
def DenseDomainTable.doms (T : DenseDomainTable p) :
    List VarId → Option (List (VarId × FiniteDomain p))
  | [] => some []
  | i :: is =>
    match T.map[i]?, T.doms is with
    | some d, some rest => some ((i, d) :: rest)
    | _, _ => none

/-! ## `.map`-extraction helpers and the insert correspondence -/

/-- The `.map` field of the dense `insertEntry`. -/
theorem DenseDomainTable.insertEntry_map (T : DenseDomainTable p) (i : VarId) (d : FiniteDomain p) :
    (T.insertEntry i d).map
      = (if (match T.map[i]? with | some d0 => decide (d.size < d0.size) | none => (true : Bool))
             = true
         then T.map.insert i d else T.map) := by
  unfold DenseDomainTable.insertEntry
  rw [apply_ite DenseDomainTable.map]

/-- The `.map` field of the spec `DomainTable.insertEntry` (proof-agnostic). -/
theorem DomainTable_insertEntry_map {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (x : Variable) (d : FiniteDomain p)
    (h : ∀ env, cs.satisfies bs env → env x ∈ d.toList) :
    (T.insertEntry x d h).map
      = (if (match T.map[x]? with | some d0 => decide (d.size < d0.size) | none => (true : Bool))
             = true
         then T.map.insert x d else T.map) := by
  unfold DomainTable.insertEntry
  rw [apply_ite DomainTable.map]
  rfl

/-- `insertEntry` preserves the `denseT[i]? = specT.map[resolve i]?` correspondence invariant.
    (The `FiniteDomain` value `d` is variable-free, hence *equal* on both sides.) -/
theorem DenseDomainTable.insertEntry_decode {cs : ConstraintSystem p} {bs : BusSemantics p}
    (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) (d : FiniteDomain p)
    (Tspec : DomainTable p cs bs) (Tdense : DenseDomainTable p)
    (h : ∀ env, cs.satisfies bs env → env (reg.resolve i) ∈ d.toList)
    (hinv : ∀ k, reg.Valid k → Tdense.map[k]? = Tspec.map[reg.resolve k]?) :
    ∀ k, reg.Valid k →
      (Tdense.insertEntry i d).map[k]?
        = (Tspec.insertEntry (reg.resolve i) d h).map[reg.resolve k]? := by
  intro k hk
  rw [DenseDomainTable.insertEntry_map, DomainTable_insertEntry_map]
  simp only [hinv i hi]
  by_cases hkeep : (match Tspec.map[reg.resolve i]? with
      | some d0 => decide (d.size < d0.size) | none => (true : Bool)) = true
  · rw [if_pos hkeep, if_pos hkeep, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    by_cases hik : i = k
    · subst hik; simp
    · have hik' : ¬ reg.resolve i = reg.resolve k := fun he => hik (reg.resolve_inj hi hk he)
      rw [if_neg (by simpa using hik), if_neg (by simpa using hik')]
      exact hinv k hk
  · rw [if_neg hkeep, if_neg hkeep]
    exact hinv k hk

/-! ## `dedup` commutes with `resolve` on a covered id list -/

/-- **`List.dedup` commutes with `resolve`** on a list of valid ids: `resolve` is injective there, so
    it neither merges nor splits duplicates (mirrors `map_dedup_decodeExpr`). -/
theorem VarRegistry.map_dedup_resolve (reg : VarRegistry) :
    ∀ (l : List VarId), (∀ i ∈ l, reg.Valid i) →
      (l.dedup).map reg.resolve = (l.map reg.resolve).dedup := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro hv
      have hva : reg.Valid a := hv a (List.mem_cons_self ..)
      have hvrest : ∀ i ∈ rest, reg.Valid i := fun i hi => hv i (List.mem_cons_of_mem _ hi)
      by_cases h : a ∈ rest
      · have hmem : reg.resolve a ∈ rest.map reg.resolve := List.mem_map.2 ⟨a, h, rfl⟩
        rw [List.dedup_cons_of_mem h, List.map_cons, List.dedup_cons_of_mem hmem, ih hvrest]
      · have hnm : reg.resolve a ∉ rest.map reg.resolve := by
          intro hcon
          obtain ⟨w, hw, he⟩ := List.mem_map.1 hcon
          exact h (reg.resolve_inj (hvrest w hw) hva he ▸ hw)
        rw [List.dedup_cons_of_notMem h, List.map_cons, List.map_cons,
          List.dedup_cons_of_notMem hnm, ih hvrest]

/-! ## Constraint-sourced domains -/

/-- Dense inner `addVars` for constraints (mirrors `addConstraintDoms.addVars`). -/
def denseAddConstraintVars (c : DenseExpr p) :
    List VarId → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | i :: is, T =>
    match denseRootsIn i c with
    | some d => denseAddConstraintVars c is (T.insertEntry i (.explicit d))
    | none => denseAddConstraintVars c is T

/-- Dense constraint-sourced domains (mirrors `addConstraintDoms`). -/
def denseAddConstraintDoms : List (DenseExpr p) → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | c :: rest, T =>
    let vs := c.vars.dedup
    denseAddConstraintDoms rest (if vs.length ≤ 3 then denseAddConstraintVars c vs T else T)

theorem denseAddConstraintVars_decode [Fact p.Prime] {cs : ConstraintSystem p}
    {bs : BusSemantics p} (reg : VarRegistry) (c : DenseExpr p) (hcc : c.CoveredBy reg)
    (hc : reg.decodeExpr c ∈ cs.algebraicConstraints) :
    ∀ (xs : List VarId), (∀ i ∈ xs, reg.Valid i) →
      ∀ (Tspec : DomainTable p cs bs) (Tdense : DenseDomainTable p),
      (∀ k, reg.Valid k → Tdense.map[k]? = Tspec.map[reg.resolve k]?) →
      ∀ k, reg.Valid k →
        (denseAddConstraintVars c xs Tdense).map[k]?
          = (addConstraintDoms.addVars (reg.decodeExpr c) hc (xs.map reg.resolve) Tspec).map[reg.resolve k]? := by
  intro xs
  induction xs with
  | nil => intro _ Tspec Tdense hinv k hk; exact hinv k hk
  | cons i is ih =>
      intro hxv Tspec Tdense hinv k hk
      have hiv : reg.Valid i := hxv i (List.mem_cons_self ..)
      have hisv : ∀ i' ∈ is, reg.Valid i' := fun i' hi' => hxv i' (List.mem_cons_of_mem _ hi')
      have hroots := denseRootsIn_decode reg hiv c hcc
      show (denseAddConstraintVars c (i :: is) Tdense).map[k]?
        = (addConstraintDoms.addVars (reg.decodeExpr c) hc
            (reg.resolve i :: is.map reg.resolve) Tspec).map[reg.resolve k]?
      unfold denseAddConstraintVars addConstraintDoms.addVars
      split
      · rename_i d hr_d
        have hr_s : rootsIn (reg.resolve i) (reg.decodeExpr c) = some d := hroots.trans hr_d
        split
        · rename_i d' hr_s'
          rw [hr_s] at hr_s'; obtain rfl := Option.some.inj hr_s'
          exact ih hisv _ _
            (DenseDomainTable.insertEntry_decode reg hiv (.explicit d) Tspec Tdense _ hinv) k hk
        · rename_i hr_s'; rw [hr_s] at hr_s'; exact absurd hr_s' (by simp)
      · rename_i hr_d
        have hr_s : rootsIn (reg.resolve i) (reg.decodeExpr c) = none := hroots.trans hr_d
        split
        · rename_i d' hr_s'; rw [hr_s] at hr_s'; exact absurd hr_s' (by simp)
        · exact ih hisv _ _ hinv k hk

/-! ## Bus-sourced range domains -/

/-- The raw-variable payload entries of a dense interaction (mirrors `payloadRawVars`). -/
def densePayloadRawVars (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.payload.filterMap (fun e => match e with | .var i => some i | _ => none)

theorem densePayloadRawVars_decode (reg : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    payloadRawVars (reg.decodeBI bi) = (densePayloadRawVars bi).map reg.resolve := by
  unfold payloadRawVars densePayloadRawVars
  show (bi.payload.map reg.decodeExpr).filterMap _ = _
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext e
  cases e <;> rfl

theorem densePayloadRawVars_valid {reg : VarRegistry} {bi : BusInteraction (DenseExpr p)}
    (hc : denseBICovered reg bi) : ∀ i ∈ densePayloadRawVars bi, reg.Valid i := by
  intro i hi
  unfold densePayloadRawVars at hi
  rw [List.mem_filterMap] at hi
  obtain ⟨e, hemem, he⟩ := hi
  cases e with
  | var j => simp only [Option.some.injEq] at he; subst he; exact hc.2 _ hemem j (by simp [DenseExpr.vars])
  | const n => simp at he
  | add a b => simp at he
  | mul a b => simp at he

/-- A bus obligation's range domain for `i`, kept symbolically (mirrors `interactionDomainF`), using
    the DigitFold fact-layer `denseInteractionBound` on the unchanged `facts`. -/
def denseInteractionDomainF (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) : Option (FiniteDomain p) :=
  match denseInteractionBound bs facts bi i with
  | none => none
  | some bound => if bound ≤ maxDomainBound then some (.range bound) else none

theorem denseInteractionDomainF_decode (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) {i : VarId} (hi : reg.Valid i) (bi : BusInteraction (DenseExpr p))
    (hc : denseBICovered reg bi) :
    interactionDomainF bs facts (reg.decodeBI bi) (reg.resolve i)
      = denseInteractionDomainF bs facts bi i := by
  unfold interactionDomainF denseInteractionDomainF
  rw [denseInteractionBound_decode bs facts reg hi bi hc]
  cases denseInteractionBound bs facts bi i <;> rfl

/-- Dense inner `addVars` for bus obligations (mirrors `addBusDoms.addVars`). -/
def denseAddBusVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    List VarId → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | i :: is, T =>
    match denseInteractionDomainF bs facts bi i with
    | some d => denseAddBusVars bs facts bi is (T.insertEntry i d)
    | none => denseAddBusVars bs facts bi is T

/-- Dense bus-sourced domains (mirrors `addBusDoms`). -/
def denseAddBusDoms (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | bi :: rest, T =>
    denseAddBusDoms bs facts rest (denseAddBusVars bs facts bi (densePayloadRawVars bi).dedup T)

/-! ## Dense enumeration engine (Task 3 — DomainBatch, part 2)

The joint box-scan enumeration, re-instantiated over `VarId` keys / `List (VarId × ZMod p)` points.
The compiled predicates (`IExpr`/`CBi`) and the symbolic `FiniteDomain` enumeration are
*variable-free* and reused verbatim from the spec; only the *key type* of the enumerated points and
the environment/compile leaves change. Every dense def here is ID-native (no `Variable` materialized
on the scan's hot path). Its correspondence to the spec engine — the survivor point's *values* agree
and its *keys map by `resolve`* — is proved for chunk 3's `forcedOver` to consume.

Throughout, a dense point `pt : List (VarId × ZMod p)` decodes to the spec point
`pt.map (fun kv => (reg.resolve kv.1, kv.2))` (keys resolved, values unchanged). -/

/-- The `Variable`-`powdrId?`/`name` fast-equality of two resolved valid IDs decides `VarId`
    equality: `resolve` is injective on valid IDs, so it neither merges nor splits them. -/
theorem denseFastEq_resolve (reg : VarRegistry) {x y : VarId} (hx : reg.Valid x) (hy : reg.Valid y) :
    ((reg.resolve y).powdrId? == (reg.resolve x).powdrId?
        && (reg.resolve y).name == (reg.resolve x).name) = (y == x) := by
  by_cases hyx : y = x
  · subst hyx; simp
  · have h1 : ((reg.resolve y).powdrId? == (reg.resolve x).powdrId?
        && (reg.resolve y).name == (reg.resolve x).name) = false := by
      rw [Bool.eq_false_iff]; intro hc
      exact hyx (reg.resolve_inj hy hx ((varFastEq_iff _ _).mp hc))
    have h2 : (y == x) = false := by
      rw [Bool.eq_false_iff]; intro hc; exact hyx (eq_of_beq hc)
    rw [h1, h2]

/-- Enumeration-time `VarId` lookup, mirroring `envOfFast`; compares `VarId`s directly. -/
def denseEnvOfFast : List (VarId × ZMod p) → VarId → ZMod p
  | [], _ => 0
  | (x, v) :: rest, y => if (y == x) = true then v else denseEnvOfFast rest y

/-- `denseEnvOfFast` on a point equals `envOfFast` on the decoded point (keys resolved). -/
theorem denseEnvOfFast_decode (reg : VarRegistry) :
    ∀ (pt : List (VarId × ZMod p)), (∀ kv ∈ pt, reg.Valid kv.1) →
      ∀ (y : VarId), reg.Valid y →
        envOfFast (pt.map (fun kv => (reg.resolve kv.1, kv.2))) (reg.resolve y)
          = denseEnvOfFast pt y := by
  intro pt
  induction pt with
  | nil => intro _ y _; rfl
  | cons kv rest ih =>
      intro hv y hy
      obtain ⟨x, v⟩ := kv
      have hxv : reg.Valid x := hv (x, v) (List.mem_cons_self ..)
      have hrv : ∀ kv ∈ rest, reg.Valid kv.1 := fun kv h => hv kv (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, envOfFast, denseEnvOfFast, denseFastEq_resolve reg hxv hy]
      by_cases hb : (y == x) = true
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb]; exact ih hrv y hy

/-- `containsFast`, over `VarId`s (the `envOfFast` discriminator trick), for the covered-item scans. -/
def denseContainsFast (xs : List VarId) (y : VarId) : Bool :=
  match xs with
  | [] => false
  | x :: rest => (y == x) || denseContainsFast rest y

/-- `denseContainsFast` on `VarId`s equals `containsFast` on the resolved keys. -/
theorem denseContainsFast_decode (reg : VarRegistry) :
    ∀ (xs : List VarId), (∀ x ∈ xs, reg.Valid x) → ∀ (y : VarId), reg.Valid y →
      containsFast (xs.map reg.resolve) (reg.resolve y) = denseContainsFast xs y := by
  intro xs
  induction xs with
  | nil => intro _ y _; rfl
  | cons x rest ih =>
      intro hxv y hy
      have hxvh : reg.Valid x := hxv x (List.mem_cons_self ..)
      have hrv : ∀ x' ∈ rest, reg.Valid x' := fun x' h => hxv x' (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, containsFast, denseContainsFast, denseFastEq_resolve reg hxvh hy]
      rw [ih hrv y hy]

/-! ### Index-compiled evaluation over dense points

`IExpr`/`CBi` are variable-free, so the *same* compiled term is produced dense and spec; only its
*evaluation* changes key type. `lookupIx` ignores keys, so the dense evaluators agree with the spec
ones on the decoded point (`denseLookupIx_map` and its lifts). -/

/-- Positional lookup in a dense assignment (mirrors `lookupIx`; ignores keys). -/
def denseLookupIx : List (VarId × ZMod p) → Nat → ZMod p
  | [], _ => 0
  | (_, v) :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIx rest i

theorem denseLookupIx_map (reg : VarRegistry) (pt : List (VarId × ZMod p)) (n : Nat) :
    lookupIx (pt.map (fun kv => (reg.resolve kv.1, kv.2))) n = denseLookupIx pt n := by
  induction pt generalizing n with
  | nil => cases n <;> rfl
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      cases n with
      | zero => rfl
      | succ m => simpa using ih m

/-- `IExpr.evalWith` over a dense point (mirrors `IExpr.evalWith`; positional). -/
def denseIExprEvalWith (add mul : ZMod p → ZMod p → ZMod p) (pt : List (VarId × ZMod p)) :
    IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIx pt i
  | .add a b => add (denseIExprEvalWith add mul pt a) (denseIExprEvalWith add mul pt b)
  | .mul a b => mul (denseIExprEvalWith add mul pt a) (denseIExprEvalWith add mul pt b)

theorem denseIExprEvalWith_map (reg : VarRegistry) (add mul : ZMod p → ZMod p → ZMod p)
    (pt : List (VarId × ZMod p)) (ie : IExpr p) :
    IExpr.evalWith add mul (pt.map (fun kv => (reg.resolve kv.1, kv.2))) ie
      = denseIExprEvalWith add mul pt ie := by
  induction ie with
  | const n => rfl
  | ix i => exact denseLookupIx_map reg pt i
  | add a b iha ihb => simp only [IExpr.evalWith, denseIExprEvalWith, iha, ihb]
  | mul a b iha ihb => simp only [IExpr.evalWith, denseIExprEvalWith, iha, ihb]

/-- `CBi.evalWith` over a dense point (mirrors `CBi.evalWith`). -/
def denseCBiEvalWith (add mul : ZMod p → ZMod p → ZMod p) (cbi : CBi p)
    (pt : List (VarId × ZMod p)) : BusInteraction (ZMod p) :=
  { busId := cbi.busId,
    multiplicity := denseIExprEvalWith add mul pt cbi.mult,
    payload := cbi.payload.map (fun ie => denseIExprEvalWith add mul pt ie) }

theorem denseCBiEvalWith_map (reg : VarRegistry) (add mul : ZMod p → ZMod p → ZMod p)
    (cbi : CBi p) (pt : List (VarId × ZMod p)) :
    CBi.evalWith add mul cbi (pt.map (fun kv => (reg.resolve kv.1, kv.2)))
      = denseCBiEvalWith add mul cbi pt := by
  simp only [CBi.evalWith, denseCBiEvalWith, denseIExprEvalWith_map reg]

/-- `survivesAllCW` over a dense point (mirrors `survivesAllCW`). -/
def denseSurvivesAllCW (add mul : ZMod p → ZMod p → ZMod p) (isZero : ZMod p → Bool)
    (bs : BusSemantics p) (ces : List (IExpr p)) (cbis : List (CBi p))
    (pt : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWith add mul pt ie)) &&
    cbis.all (fun cbi =>
      let v := denseCBiEvalWith add mul cbi pt
      isZero v.multiplicity || !bs.violatesConstraint v)

theorem denseSurvivesAllCW_map (reg : VarRegistry) (add mul : ZMod p → ZMod p → ZMod p)
    (isZero : ZMod p → Bool) (bs : BusSemantics p) (ces : List (IExpr p)) (cbis : List (CBi p))
    (pt : List (VarId × ZMod p)) :
    survivesAllCW add mul isZero bs ces cbis (pt.map (fun kv => (reg.resolve kv.1, kv.2)))
      = denseSurvivesAllCW add mul isZero bs ces cbis pt := by
  simp only [survivesAllCW, denseSurvivesAllCW, denseIExprEvalWith_map reg,
    denseCBiEvalWith_map reg]

/-! ### Compiling dense items to `IExpr`/`CBi`

The compiled term is *identical* to the spec's on the decoded item, provided the keys are valid: the
only variable-typed step is `denseVarIx`, which finds the same position as `varIx` on the resolved
keys by `resolve`-injectivity. -/

/-- First position of `y` in dense `keys` (mirrors `varIx`). -/
def denseVarIx (keys : List VarId) (y : VarId) : Option Nat :=
  match keys with
  | [] => none
  | x :: rest => if (y == x) = true then some 0 else (denseVarIx rest y).map (· + 1)

theorem denseVarIx_decode (reg : VarRegistry) :
    ∀ (keys : List VarId), (∀ x ∈ keys, reg.Valid x) → ∀ (y : VarId), reg.Valid y →
      varIx (keys.map reg.resolve) (reg.resolve y) = denseVarIx keys y := by
  intro keys
  induction keys with
  | nil => intro _ y _; rfl
  | cons x rest ih =>
      intro hkv y hy
      have hxv : reg.Valid x := hkv x (List.mem_cons_self ..)
      have hrv : ∀ x' ∈ rest, reg.Valid x' := fun x' h => hkv x' (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, varIx, denseVarIx, denseFastEq_resolve reg hxv hy]
      by_cases hb : (y == x) = true
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb, ih hrv y hy]

/-- Compile a dense expression against dense `keys` (mirrors `compileE`). -/
def denseCompileE (keys : List VarId) : DenseExpr p → Option (IExpr p)
  | .const n => some (.const n)
  | .var y => (denseVarIx keys y).map .ix
  | .add a b =>
    match denseCompileE keys a, denseCompileE keys b with
    | some ia, some ib => some (.add ia ib)
    | _, _ => none
  | .mul a b =>
    match denseCompileE keys a, denseCompileE keys b with
    | some ia, some ib => some (.mul ia ib)
    | _, _ => none

theorem denseCompileE_decode (reg : VarRegistry) (keys : List VarId)
    (hkv : ∀ x ∈ keys, reg.Valid x) (e : DenseExpr p) (hc : e.CoveredBy reg) :
    compileE (keys.map reg.resolve) (reg.decodeExpr e) = denseCompileE keys e := by
  induction e with
  | const n => rfl
  | var i =>
      have hiv : reg.Valid i := hc i (by simp [DenseExpr.vars])
      show compileE (keys.map reg.resolve) (.var (reg.resolve i)) = (denseVarIx keys i).map .ix
      rw [compileE, denseVarIx_decode reg keys hkv i hiv]
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      show compileE (keys.map reg.resolve) ((reg.decodeExpr a).add (reg.decodeExpr b))
        = denseCompileE keys (a.add b)
      rw [compileE, denseCompileE, iha ha, ihb hb]
      cases denseCompileE keys a <;> cases denseCompileE keys b <;> rfl
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      show compileE (keys.map reg.resolve) ((reg.decodeExpr a).mul (reg.decodeExpr b))
        = denseCompileE keys (a.mul b)
      rw [compileE, denseCompileE, iha ha, ihb hb]
      cases denseCompileE keys a <;> cases denseCompileE keys b <;> rfl

/-- Compile a list of dense expressions, all-or-nothing (mirrors `compileEs`). -/
def denseCompileEs (keys : List VarId) : List (DenseExpr p) → Option (List (IExpr p))
  | [] => some []
  | e :: rest =>
    match denseCompileE keys e, denseCompileEs keys rest with
    | some ie, some irest => some (ie :: irest)
    | _, _ => none

theorem denseCompileEs_decode (reg : VarRegistry) (keys : List VarId)
    (hkv : ∀ x ∈ keys, reg.Valid x) :
    ∀ (es : List (DenseExpr p)), (∀ e ∈ es, e.CoveredBy reg) →
      compileEs (keys.map reg.resolve) (es.map reg.decodeExpr) = denseCompileEs keys es := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e rest ih =>
      intro hcov
      have hce : e.CoveredBy reg := hcov e (List.mem_cons_self ..)
      have hcr : ∀ e' ∈ rest, e'.CoveredBy reg := fun e' h => hcov e' (List.mem_cons_of_mem _ h)
      show compileEs (keys.map reg.resolve) (reg.decodeExpr e :: rest.map reg.decodeExpr)
        = denseCompileEs keys (e :: rest)
      rw [compileEs, denseCompileEs, denseCompileE_decode reg keys hkv e hce, ih hcr]
      cases denseCompileE keys e <;> cases denseCompileEs keys rest <;> rfl

/-- Compile a dense bus interaction (mirrors `compileBi`). -/
def denseCompileBi (keys : List VarId) (bi : BusInteraction (DenseExpr p)) : Option (CBi p) :=
  match denseCompileE keys bi.multiplicity, denseCompileEs keys bi.payload with
  | some m, some pl => some ⟨bi.busId, m, pl⟩
  | _, _ => none

theorem denseCompileBi_decode (reg : VarRegistry) (keys : List VarId)
    (hkv : ∀ x ∈ keys, reg.Valid x) (bi : BusInteraction (DenseExpr p))
    (hc : denseBICovered reg bi) :
    compileBi (keys.map reg.resolve) (reg.decodeBI bi) = denseCompileBi keys bi := by
  obtain ⟨hm, hp⟩ := hc
  unfold compileBi denseCompileBi VarRegistry.decodeBI
  rw [denseCompileE_decode reg keys hkv bi.multiplicity hm,
    denseCompileEs_decode reg keys hkv bi.payload hp]
  cases denseCompileE keys bi.multiplicity <;> cases denseCompileEs keys bi.payload <;> rfl

/-- Compile a list of dense interactions, all-or-nothing (mirrors `compileBis`). -/
def denseCompileBis (keys : List VarId) : List (BusInteraction (DenseExpr p)) →
    Option (List (CBi p))
  | [] => some []
  | bi :: rest =>
    match denseCompileBi keys bi, denseCompileBis keys rest with
    | some cbi, some crest => some (cbi :: crest)
    | _, _ => none

theorem denseCompileBis_decode (reg : VarRegistry) (keys : List VarId)
    (hkv : ∀ x ∈ keys, reg.Valid x) :
    ∀ (bis : List (BusInteraction (DenseExpr p))), (∀ bi ∈ bis, denseBICovered reg bi) →
      compileBis (keys.map reg.resolve) (bis.map reg.decodeBI) = denseCompileBis keys bis := by
  intro bis
  induction bis with
  | nil => intro _; rfl
  | cons bi rest ih =>
      intro hcov
      have hcb : denseBICovered reg bi := hcov bi (List.mem_cons_self ..)
      have hcr : ∀ bi' ∈ rest, denseBICovered reg bi' :=
        fun bi' h => hcov bi' (List.mem_cons_of_mem _ h)
      show compileBis (keys.map reg.resolve) (reg.decodeBI bi :: rest.map reg.decodeBI)
        = denseCompileBis keys (bi :: rest)
      rw [compileBis, denseCompileBis, denseCompileBi_decode reg keys hkv bi hcb, ih hcr]
      cases denseCompileBi keys bi <;> cases denseCompileBis keys rest <;> rfl

/-! ### The uncompiled fallback predicate `denseSurvivesAllM`

Used only when compilation fails (never, for covered items); still ported so the dense compiled
survivor is total and its correspondence unconditional. Evaluation goes through `DenseExpr.eval`
under `denseEnvOfFast`; its bus-obligation check inlines the decoded `BusInteraction.eval`. -/

/-- `DenseExpr.eval` depends only on the values of the variables that occur. -/
theorem DenseExpr.eval_congr (e : DenseExpr p) (f g : VarId → ZMod p)
    (h : ∀ i ∈ e.vars, f i = g i) : e.eval f = e.eval g := by
  induction e with
  | const n => rfl
  | var i => exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at h
      simp only [DenseExpr.eval, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]
  | mul a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at h
      simp only [DenseExpr.eval, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]

/-- Evaluating the decoded expression under `envOfFast` on the decoded point equals evaluating the
    dense expression under `denseEnvOfFast` on the dense point. -/
theorem denseExpr_eval_decode (reg : VarRegistry) (e : DenseExpr p) (hc : e.CoveredBy reg)
    (pt : List (VarId × ZMod p)) (hpt : ∀ kv ∈ pt, reg.Valid kv.1) :
    (reg.decodeExpr e).eval (envOfFast (pt.map (fun kv => (reg.resolve kv.1, kv.2))))
      = e.eval (denseEnvOfFast pt) := by
  rw [reg.decodeExpr_eval e]
  apply DenseExpr.eval_congr
  intro i hi
  exact denseEnvOfFast_decode reg pt hpt i (hc i hi)

/-- Fallback survivor predicate over dense items (mirrors `survivesAllM`; inlines the decoded
    `BusInteraction.eval`). -/
def denseSurvivesAllM (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (a : List (VarId × ZMod p)) : Bool :=
  es.all (fun e => decide (e.eval (denseEnvOfFast a) = 0)) &&
    bis.all (fun bi =>
      let v : BusInteraction (ZMod p) :=
        { busId := bi.busId,
          multiplicity := bi.multiplicity.eval (denseEnvOfFast a),
          payload := bi.payload.map (fun e => e.eval (denseEnvOfFast a)) }
      decide (v.multiplicity = 0) || !bs.violatesConstraint v)

theorem denseSurvAllM_es (reg : VarRegistry) (pt : List (VarId × ZMod p))
    (hpt : ∀ kv ∈ pt, reg.Valid kv.1) :
    ∀ (es : List (DenseExpr p)), (∀ e ∈ es, e.CoveredBy reg) →
      (es.map reg.decodeExpr).all
          (fun e => decide (e.eval (envOfFast (pt.map (fun kv => (reg.resolve kv.1, kv.2)))) = 0))
        = es.all (fun e => decide (e.eval (denseEnvOfFast pt) = 0)) := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e rest ih =>
      intro hcov
      have hce : e.CoveredBy reg := hcov e (List.mem_cons_self ..)
      have hcr : ∀ e' ∈ rest, e'.CoveredBy reg := fun e' h => hcov e' (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, List.all_cons, denseExpr_eval_decode reg e hce pt hpt, ih hcr]

theorem denseSurvAllM_bis (reg : VarRegistry) (bs : BusSemantics p)
    (pt : List (VarId × ZMod p)) (hpt : ∀ kv ∈ pt, reg.Valid kv.1) :
    ∀ (bis : List (BusInteraction (DenseExpr p))), (∀ bi ∈ bis, denseBICovered reg bi) →
      (bis.map reg.decodeBI).all
          (fun bi =>
            let v := bi.eval (envOfFast (pt.map (fun kv => (reg.resolve kv.1, kv.2))))
            decide (v.multiplicity = 0) || !bs.violatesConstraint v)
        = bis.all (fun bi =>
            let v : BusInteraction (ZMod p) :=
              { busId := bi.busId,
                multiplicity := bi.multiplicity.eval (denseEnvOfFast pt),
                payload := bi.payload.map (fun e => e.eval (denseEnvOfFast pt)) }
            decide (v.multiplicity = 0) || !bs.violatesConstraint v) := by
  intro bis
  induction bis with
  | nil => intro _; rfl
  | cons bi rest ih =>
      intro hcov
      have hcb : denseBICovered reg bi := hcov bi (List.mem_cons_self ..)
      have hcr : ∀ bi' ∈ rest, denseBICovered reg bi' :=
        fun bi' h => hcov bi' (List.mem_cons_of_mem _ h)
      obtain ⟨hm, hp⟩ := hcb
      have hbe : (reg.decodeBI bi).eval (envOfFast (pt.map (fun kv => (reg.resolve kv.1, kv.2))))
          = ({ busId := bi.busId,
               multiplicity := bi.multiplicity.eval (denseEnvOfFast pt),
               payload := bi.payload.map (fun e => e.eval (denseEnvOfFast pt)) }
              : BusInteraction (ZMod p)) := by
        unfold BusInteraction.eval VarRegistry.decodeBI
        congr 1
        · exact denseExpr_eval_decode reg bi.multiplicity hm pt hpt
        · rw [List.map_map]
          exact List.map_congr_left (fun e he => denseExpr_eval_decode reg e (hp e he) pt hpt)
      simp only [List.map_cons, List.all_cons, hbe, ih hcr]

theorem denseSurvivesAllM_decode (reg : VarRegistry) (bs : BusSemantics p)
    (es : List (DenseExpr p)) (hes : ∀ e ∈ es, e.CoveredBy reg)
    (bis : List (BusInteraction (DenseExpr p))) (hbis : ∀ bi ∈ bis, denseBICovered reg bi)
    (pt : List (VarId × ZMod p)) (hpt : ∀ kv ∈ pt, reg.Valid kv.1) :
    survivesAllM bs (es.map reg.decodeExpr) (bis.map reg.decodeBI)
        (pt.map (fun kv => (reg.resolve kv.1, kv.2)))
      = denseSurvivesAllM bs es bis pt := by
  unfold survivesAllM denseSurvivesAllM
  rw [denseSurvAllM_es reg pt hpt es hes, denseSurvAllM_bis reg bs pt hpt bis hbis]

/-! ### The dense compiled survivor predicate

Structurally mirrors `compiledSurv`, but returns a *plain* predicate (chunk 3 inherits soundness via
`ofTransform`; no subtype property is carried). Its correspondence to `(compiledSurv …).val` on a
decoded right-keyed point routes through each side's uncompiled `survivesAllM` form: the spec side by
its own carried `.property`, the dense side by `denseCompiledSurv_property` below (which reuses the
*spec* `survivesAllCW_eq`/`survivesAllC_eq` on the identical compiled `IExpr`/`CBi`s). -/

/-- Per-point survivor predicate for a target over dense items (mirrors `compiledSurv`, plain fn). -/
def denseCompiledSurv (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) :
    List (VarId × ZMod p) → Bool :=
  match denseCompileEs keys es, denseCompileBis keys bis with
  | some ces, some cbis =>
    let addI : Add (ZMod p) := inferInstance
    let mulI : Mul (ZMod p) := inferInstance
    let dec : DecidableEq (ZMod p) := inferInstance
    let add := addI.add
    let mul := mulI.mul
    let isZero : ZMod p → Bool := fun v => @decide (v = 0) (dec v 0)
    fun pt => denseSurvivesAllCW add mul isZero bs ces cbis pt
  | _, _ => denseSurvivesAllM bs es bis

/-- `denseCompiledSurv` unfolded and applied, with the field operations reduced. -/
theorem denseCompiledSurv_eq_match (bs : BusSemantics p) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (pt : List (VarId × ZMod p)) :
    denseCompiledSurv bs es bis keys pt
      = (match denseCompileEs keys es, denseCompileBis keys bis with
          | some ces, some cbis =>
              denseSurvivesAllCW Add.add Mul.mul (fun v => decide (v = 0)) bs ces cbis pt
          | _, _ => denseSurvivesAllM bs es bis pt) := by
  unfold denseCompiledSurv
  cases denseCompileEs keys es <;> cases denseCompileBis keys bis <;> rfl

/-- On a right-keyed point, `denseCompiledSurv` decides exactly `denseSurvivesAllM` (dense analog of
    `compiledSurv`'s carried property; reuses the *spec* compile-eval lemmas on the shared
    compiled `IExpr`/`CBi`s). -/
theorem denseCompiledSurv_property (reg : VarRegistry) (bs : BusSemantics p)
    (es : List (DenseExpr p)) (hes : ∀ e ∈ es, e.CoveredBy reg)
    (bis : List (BusInteraction (DenseExpr p))) (hbis : ∀ bi ∈ bis, denseBICovered reg bi)
    (keys : List VarId) (hkv : ∀ x ∈ keys, reg.Valid x)
    (pt : List (VarId × ZMod p)) (hpt : ∀ kv ∈ pt, reg.Valid kv.1) (hptk : pt.map Prod.fst = keys) :
    denseCompiledSurv bs es bis keys pt = denseSurvivesAllM bs es bis pt := by
  have hptk_s : (pt.map (fun kv => (reg.resolve kv.1, kv.2))).map Prod.fst = keys.map reg.resolve := by
    rw [← hptk]; simp only [List.map_map, Function.comp_def]
  rw [denseCompiledSurv_eq_match]
  cases hde : denseCompileEs keys es with
  | none => simp
  | some ces =>
    cases hdb : denseCompileBis keys bis with
    | none => simp
    | some cbis =>
      have hce' : compileEs (keys.map reg.resolve) (es.map reg.decodeExpr) = some ces :=
        (denseCompileEs_decode reg keys hkv es hes).trans hde
      have hcb' : compileBis (keys.map reg.resolve) (bis.map reg.decodeBI) = some cbis :=
        (denseCompileBis_decode reg keys hkv bis hbis).trans hdb
      show denseSurvivesAllCW Add.add Mul.mul (fun v => decide (v = 0)) bs ces cbis pt
        = denseSurvivesAllM bs es bis pt
      rw [← denseSurvivesAllCW_map reg,
        survivesAllCW_eq Add.add Mul.mul (fun v => decide (v = 0))
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) bs ces cbis _,
        survivesAllC_eq bs (es.map reg.decodeExpr) (bis.map reg.decodeBI) (keys.map reg.resolve)
          ces cbis hce' hcb' _ hptk_s]
      exact denseSurvivesAllM_decode reg bs es hes bis hbis pt hpt

/-- **`denseCompiledSurv` decodes to `(compiledSurv …).val`** on a decoded right-keyed point: both
    reduce to their uncompiled `survivesAllM` form there, which correspond by
    `denseSurvivesAllM_decode`. This is the survivor-predicate agreement `denseScanBox_decode`
    consumes. -/
theorem denseCompiledSurv_decode (reg : VarRegistry) (bs : BusSemantics p)
    (es : List (DenseExpr p)) (hes : ∀ e ∈ es, e.CoveredBy reg)
    (bis : List (BusInteraction (DenseExpr p))) (hbis : ∀ bi ∈ bis, denseBICovered reg bi)
    (keys : List VarId) (hkv : ∀ x ∈ keys, reg.Valid x)
    (pt : List (VarId × ZMod p)) (hpt : ∀ kv ∈ pt, reg.Valid kv.1) (hptk : pt.map Prod.fst = keys) :
    denseCompiledSurv bs es bis keys pt
      = (compiledSurv bs (es.map reg.decodeExpr) (bis.map reg.decodeBI) (keys.map reg.resolve)).val
          (pt.map (fun kv => (reg.resolve kv.1, kv.2))) := by
  have hptk_s : (pt.map (fun kv => (reg.resolve kv.1, kv.2))).map Prod.fst = keys.map reg.resolve := by
    rw [← hptk]; simp only [List.map_map, Function.comp_def]
  rw [denseCompiledSurv_property reg bs es hes bis hbis keys hkv pt hpt hptk,
    (compiledSurv bs (es.map reg.decodeExpr) (bis.map reg.decodeBI) (keys.map reg.resolve)).property
      _ hptk_s]
  exact (denseSurvivesAllM_decode reg bs es hes bis hbis pt hpt).symm

/-! ### Lazy box enumeration, dense, and the fold bisimulation

`foldlStop`, `rangeFoldFrom`, `FiniteDomain.foldElts` are *variable-free* (generic in the fold state)
and reused verbatim. Only `boxFold` fixes the point key type, so it gets a dense mirror
`denseBoxFold`. The bisimulation `boxFold_rel` relates the dense and spec folds through a relation on
their (possibly different) states, given: the step functions agree on decoded points, and the
enumerated points — assembled from the domain keys — are always fully keyed by `doms`. -/

/-- Fold bisimulation over a shared list with an early stop. -/
theorem foldlStop_rel {α βd βs : Type} (R : βd → βs → Prop)
    (fd : βd → α → βd) (fs : βs → α → βs) (stopd : βd → Bool) (stops : βs → Bool)
    (hstop : ∀ ad as, R ad as → stopd ad = stops as)
    (hf : ∀ ad as a, R ad as → R (fd ad a) (fs as a)) :
    ∀ (l : List α) (ad : βd) (as : βs), R ad as →
      R (foldlStop fd stopd l ad) (foldlStop fs stops l as) := by
  intro l
  induction l with
  | nil => intro ad as h; exact h
  | cons a rest ih =>
      intro ad as h
      rw [foldlStop, foldlStop]
      by_cases hs : stopd ad = true
      · rw [if_pos hs, if_pos (by rw [← hstop ad as h]; exact hs)]; exact h
      · rw [if_neg hs, if_neg (by rw [← hstop ad as h]; exact hs)]
        exact ih (fd ad a) (fs as a) (hf ad as a h)

/-- Fold bisimulation over a shared `FiniteDomain`'s elements. -/
theorem foldElts_rel {βd βs : Type} (R : βd → βs → Prop)
    (fd : βd → ZMod p → βd) (fs : βs → ZMod p → βs) (stopd : βd → Bool) (stops : βs → Bool)
    (hstop : ∀ ad as, R ad as → stopd ad = stops as)
    (hf : ∀ ad as v, R ad as → R (fd ad v) (fs as v))
    (d : FiniteDomain p) (ad : βd) (as : βs) (h : R ad as) :
    R (d.foldElts fd stopd ad) (d.foldElts fs stops as) := by
  rw [FiniteDomain.foldElts_eq, FiniteDomain.foldElts_eq]
  exact foldlStop_rel R fd fs stopd stops hstop hf d.toList ad as h

/-- Stream the Cartesian product of dense domains into `f` (mirrors `boxFold`; `VarId` keys). -/
def denseBoxFold {β : Type} (f : β → List (VarId × ZMod p) → β) (stop : β → Bool) :
    List (VarId × FiniteDomain p) → β → β
  | [], acc => if stop acc then acc else f acc []
  | (x, d) :: rest, acc =>
    denseBoxFold (fun acc' a => d.foldElts (fun acc'' v => f acc'' ((x, v) :: a)) stop acc') stop
      rest acc

/-- **Box-fold bisimulation.** The dense and spec box folds over corresponding domains (keys mapped by
    `resolve`, `FiniteDomain`s equal) end in `R`-related states, given the steps agree on decoded,
    fully-keyed, valid points. -/
theorem boxFold_rel {βd βs : Type} (reg : VarRegistry) (R : βd → βs → Prop)
    (fd : βd → List (VarId × ZMod p) → βd) (fs : βs → List (Variable × ZMod p) → βs)
    (stopd : βd → Bool) (stops : βs → Bool)
    (hstop : ∀ ad as, R ad as → stopd ad = stops as) :
    ∀ (doms_d : List (VarId × FiniteDomain p)), (∀ kd ∈ doms_d, reg.Valid kd.1) →
      (∀ ad as ptd, R ad as → ptd.map Prod.fst = doms_d.map Prod.fst →
        (∀ kv ∈ ptd, reg.Valid kv.1) →
        R (fd ad ptd) (fs as (ptd.map (fun kv => (reg.resolve kv.1, kv.2))))) →
    ∀ (acc_d : βd) (acc_s : βs), R acc_d acc_s →
      R (denseBoxFold fd stopd doms_d acc_d)
        (boxFold fs stops (doms_d.map (fun kd => (reg.resolve kd.1, kd.2))) acc_s) := by
  intro doms_d
  induction doms_d generalizing fd fs with
  | nil =>
      intro _ hf acc_d acc_s hacc
      show R (if stopd acc_d then acc_d else fd acc_d [])
        (if stops acc_s then acc_s else fs acc_s [])
      by_cases hs : stopd acc_d = true
      · rw [if_pos hs, if_pos (by rw [← hstop acc_d acc_s hacc]; exact hs)]; exact hacc
      · rw [if_neg hs, if_neg (by rw [← hstop acc_d acc_s hacc]; exact hs)]
        have := hf acc_d acc_s [] hacc rfl (by simp)
        simpa using this
  | cons kd rest ih =>
      intro hdv hf acc_d acc_s hacc
      obtain ⟨x, d⟩ := kd
      have hxv : reg.Valid x := hdv (x, d) (List.mem_cons_self ..)
      have hrv : ∀ kd' ∈ rest, reg.Valid kd'.1 := fun kd' h => hdv kd' (List.mem_cons_of_mem _ h)
      show R (denseBoxFold
              (fun acc' a => d.foldElts (fun acc'' v => fd acc'' ((x, v) :: a)) stopd acc') stopd
              rest acc_d)
        (boxFold (fun acc' a => d.foldElts (fun acc'' v => fs acc'' ((reg.resolve x, v) :: a)) stops
              acc') stops (rest.map (fun kd => (reg.resolve kd.1, kd.2))) acc_s)
      refine ih _ _ hrv ?_ acc_d acc_s hacc
      intro ad as ptd' hR hkeys' hvptd'
      refine foldElts_rel R _ _ stopd stops hstop ?_ d ad as hR
      intro ad' as' v hR'
      have hkeys'' : ((x, v) :: ptd').map Prod.fst = ((x, d) :: rest).map Prod.fst := by
        simp only [List.map_cons, hkeys']
      have hvptd'' : ∀ kv ∈ (x, v) :: ptd', reg.Valid kv.1 := by
        intro kv hkv
        rcases List.mem_cons.1 hkv with h | h
        · rw [h]; exact hxv
        · exact hvptd' kv h
      have := hf ad' as' ((x, v) :: ptd') hR' hkeys'' hvptd''
      simpa using this

/-! ### From the domain table to the scan input

`forcedOver` scans `T.doms xs`. Chunk 1 gives the table's `getElem?` correspondence; this lifts it to
`doms`: the dense `doms` list decodes (keys resolved, `FiniteDomain`s equal) to the spec one, which
supplies chunk 3's `denseScanBox_decode` hypotheses (`hkeys`, `hdv`, and the decoded `fdoms`). -/

/-- The dense domain-table `doms` decodes to the spec `doms` (keys resolved, values equal). -/
theorem DenseDomainTable.doms_decode {cs : ConstraintSystem p} {bs : BusSemantics p}
    (reg : VarRegistry) (Tdense : DenseDomainTable p) (Tspec : DomainTable p cs bs)
    (hinv : ∀ k, reg.Valid k → Tdense.map[k]? = Tspec.map[reg.resolve k]?) :
    ∀ (xs : List VarId), (∀ x ∈ xs, reg.Valid x) →
      Tspec.doms (xs.map reg.resolve)
        = (Tdense.doms xs).map (fun l => l.map (fun kd => (reg.resolve kd.1, kd.2))) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x rest ih =>
      intro hxv
      have hxvh : reg.Valid x := hxv x (List.mem_cons_self ..)
      have hrv : ∀ x' ∈ rest, reg.Valid x' := fun x' h => hxv x' (List.mem_cons_of_mem _ h)
      show Tspec.doms (reg.resolve x :: rest.map reg.resolve)
        = (Tdense.doms (x :: rest)).map (fun l => l.map (fun kd => (reg.resolve kd.1, kd.2)))
      rw [DomainTable.doms, DenseDomainTable.doms, ← hinv x hxvh, ih hrv]
      cases Tdense.map[x]? <;> cases Tdense.doms rest <;> rfl

/-! ### The dense box scan and its correspondence

`denseScanStep`/`denseScanStop`/`denseScanBox` mirror `scanStep`/`scanStop`/`scanBox` over `VarId`
points. The correspondence relation `scanRel` says a dense candidate list decodes (keys resolved,
values equal) to the spec one and is fully valid; `denseScanBox_decode` establishes it via
`boxFold_rel`. This is exactly what chunk 3's `forcedOver` consumes: the survivor point returned by
`denseScanBox` decodes, value-for-value with keys mapped by `resolve`, to `scanBox`'s. -/

/-- One dense scan step (mirrors `scanStep`). -/
def denseScanStep (surv : List (VarId × ZMod p) → Bool) (keys : List VarId) :
    Option (List (VarId × ZMod p)) → List (VarId × ZMod p) → Option (List (VarId × ZMod p))
  | none, pt => if surv pt = true then some (keys.map (fun x => (x, denseEnvOfFast pt x))) else none
  | some cands, pt =>
    if surv pt = true then some (cands.filter (fun xc => decide (denseEnvOfFast pt xc.1 = xc.2)))
    else some cands

/-- The dense scan aborts once a tracked candidate set empties (mirrors `scanStop`). -/
def denseScanStop : Option (List (VarId × ZMod p)) → Bool
  | none => false
  | some cands => cands.isEmpty

/-- The dense box scan, streamed lazily over the symbolic domains (mirrors `scanBox`). -/
def denseScanBox (surv : List (VarId × ZMod p) → Bool) (keys : List VarId)
    (doms : List (VarId × FiniteDomain p)) : Option (List (VarId × ZMod p)) :=
  denseBoxFold (denseScanStep surv keys) denseScanStop doms none

/-- The scan-result correspondence: a dense candidate list decodes (keys resolved, values equal) to
    the spec one and every key is valid. `none` corresponds only to `none`. -/
def scanRel (reg : VarRegistry) :
    Option (List (VarId × ZMod p)) → Option (List (Variable × ZMod p)) → Prop
  | none, none => True
  | some cd, some cs =>
      cs = cd.map (fun kv => (reg.resolve kv.1, kv.2)) ∧ ∀ kv ∈ cd, reg.Valid kv.1
  | _, _ => False

/-- The `scanWith`/`scanStep` filter commutes with the key-decode: filtering a dense candidate list
    by `denseEnvOfFast` agreement then decoding equals decoding then filtering by `envOfFast`. -/
theorem denseScanFilter (reg : VarRegistry) (ptd : List (VarId × ZMod p))
    (hvptd : ∀ kv ∈ ptd, reg.Valid kv.1) :
    ∀ (cd : List (VarId × ZMod p)), (∀ kv ∈ cd, reg.Valid kv.1) →
      (cd.map (fun kv => (reg.resolve kv.1, kv.2))).filter
          (fun xc => decide (envOfFast (ptd.map (fun kv => (reg.resolve kv.1, kv.2))) xc.1 = xc.2))
        = (cd.filter (fun xc => decide (denseEnvOfFast ptd xc.1 = xc.2))).map
            (fun kv => (reg.resolve kv.1, kv.2)) := by
  intro cd
  induction cd with
  | nil => intro _; rfl
  | cons xc rest ih =>
      intro hcv
      have hxv : reg.Valid xc.1 := hcv xc (List.mem_cons_self ..)
      have hrv : ∀ kv ∈ rest, reg.Valid kv.1 := fun kv h => hcv kv (List.mem_cons_of_mem _ h)
      have hpred : decide (envOfFast (ptd.map (fun kv => (reg.resolve kv.1, kv.2)))
              (reg.resolve xc.1) = xc.2)
          = decide (denseEnvOfFast ptd xc.1 = xc.2) := by
        rw [denseEnvOfFast_decode reg ptd hvptd xc.1 hxv]
      simp only [List.map_cons, List.filter_cons, hpred]
      by_cases hc : decide (denseEnvOfFast ptd xc.1 = xc.2) = true
      · rw [if_pos hc, if_pos hc, List.map_cons, ih hrv]
      · rw [if_neg hc, if_neg hc, ih hrv]

/-- **The dense box scan decodes to the spec box scan** (`scanRel`), the enumeration correspondence
    chunk 3's `forcedOver` consumes. Requires `keys_d` to be the domain keys, the domain keys valid,
    and the two survivor predicates to agree on decoded, fully-keyed, valid points. -/
theorem denseScanBox_decode (reg : VarRegistry)
    (surv_d : List (VarId × ZMod p) → Bool) (surv_s : List (Variable × ZMod p) → Bool)
    (keys_d : List VarId) (doms_d : List (VarId × FiniteDomain p))
    (hkeys : keys_d = doms_d.map Prod.fst)
    (hdv : ∀ kd ∈ doms_d, reg.Valid kd.1)
    (hsurv : ∀ ptd, (∀ kv ∈ ptd, reg.Valid kv.1) → ptd.map Prod.fst = keys_d →
      surv_d ptd = surv_s (ptd.map (fun kv => (reg.resolve kv.1, kv.2)))) :
    scanRel reg (denseScanBox surv_d keys_d doms_d)
      (scanBox surv_s (keys_d.map reg.resolve)
        (doms_d.map (fun kd => (reg.resolve kd.1, kd.2)))) := by
  have hkvd : ∀ x ∈ keys_d, reg.Valid x := by
    intro x hx; rw [hkeys] at hx
    obtain ⟨kd, hkd, he⟩ := List.mem_map.1 hx; rw [← he]; exact hdv kd hkd
  unfold denseScanBox scanBox
  refine boxFold_rel reg (scanRel reg) (denseScanStep surv_d keys_d)
    (scanStep surv_s (keys_d.map reg.resolve)) denseScanStop scanStop ?_ doms_d hdv ?_ none none
    (by simp [scanRel])
  · -- hstop
    intro ad as h
    cases ad with
    | none => cases as with
        | none => rfl
        | some cs => exact absurd h (by simp [scanRel])
    | some cd => cases as with
        | none => exact absurd h (by simp [scanRel])
        | some cs =>
            obtain ⟨heq, -⟩ := h; subst heq
            cases cd <;> rfl
  · -- hf
    intro ad as ptd hR hkeysptd hvptd
    have hpk : ptd.map Prod.fst = keys_d := by rw [hkeysptd, hkeys]
    have hs : surv_d ptd = surv_s (ptd.map (fun kv => (reg.resolve kv.1, kv.2))) :=
      hsurv ptd hvptd hpk
    cases ad with
    | none =>
        cases as with
        | some _ => exact absurd hR (by simp [scanRel])
        | none =>
            show scanRel reg (denseScanStep surv_d keys_d none ptd)
              (scanStep surv_s (keys_d.map reg.resolve) none
                (ptd.map (fun kv => (reg.resolve kv.1, kv.2))))
            simp only [denseScanStep, scanStep, hs]
            by_cases hsv : surv_s (ptd.map (fun kv => (reg.resolve kv.1, kv.2))) = true
            · rw [if_pos hsv, if_pos hsv]
              refine ⟨?_, ?_⟩
              · rw [List.map_map, List.map_map]
                apply List.map_congr_left
                intro x hx
                simp only [Function.comp_def]
                rw [denseEnvOfFast_decode reg ptd hvptd x (hkvd x hx)]
              · intro kv hkv
                obtain ⟨x, hx, he⟩ := List.mem_map.1 hkv; rw [← he]; exact hkvd x hx
            · rw [if_neg hsv, if_neg hsv]; trivial
    | some cd =>
        cases as with
        | none => exact absurd hR (by simp [scanRel])
        | some cs =>
            obtain ⟨heq, hcdv⟩ := hR
            show scanRel reg (denseScanStep surv_d keys_d (some cd) ptd)
              (scanStep surv_s (keys_d.map reg.resolve) (some cs)
                (ptd.map (fun kv => (reg.resolve kv.1, kv.2))))
            simp only [denseScanStep, scanStep, hs]
            by_cases hsv : surv_s (ptd.map (fun kv => (reg.resolve kv.1, kv.2))) = true
            · rw [if_pos hsv, if_pos hsv]
              subst heq
              exact ⟨denseScanFilter reg ptd hvptd cd hcdv, fun kv hkv =>
                hcdv kv (List.mem_filter.1 hkv).1⟩
            · rw [if_neg hsv, if_neg hsv]; exact ⟨heq, hcdv⟩

/-! ### `allBox`, dense (for chunk 3's `constraintRedundant`)

A `Bool`-valued lazy box `.all`, mirroring `allBox`; its correspondence is the `boxFold_rel`
instance at `R := (· = ·)` on `Bool`, given the two predicates agree on decoded, fully-keyed,
valid points. -/

/-- `(assignments (matList doms)).all pred`, streamed lazily over dense domains (mirrors `allBox`). -/
def denseAllBox (pred : List (VarId × ZMod p) → Bool) (doms : List (VarId × FiniteDomain p)) :
    Bool :=
  denseBoxFold (fun acc pt => acc && pred pt) (fun acc => !acc) doms true

/-- **`denseAllBox` decodes to `allBox`** on corresponding domains, given the predicates agree on
    decoded, fully-keyed, valid points. -/
theorem denseAllBox_decode (reg : VarRegistry) (pred_d : List (VarId × ZMod p) → Bool)
    (pred_s : List (Variable × ZMod p) → Bool) (doms_d : List (VarId × FiniteDomain p))
    (hdv : ∀ kd ∈ doms_d, reg.Valid kd.1)
    (hpred : ∀ ptd, (∀ kv ∈ ptd, reg.Valid kv.1) → ptd.map Prod.fst = doms_d.map Prod.fst →
      pred_d ptd = pred_s (ptd.map (fun kv => (reg.resolve kv.1, kv.2)))) :
    denseAllBox pred_d doms_d
      = allBox pred_s (doms_d.map (fun kd => (reg.resolve kd.1, kd.2))) := by
  unfold denseAllBox allBox
  refine boxFold_rel reg Eq (fun acc pt => acc && pred_d pt) (fun acc pt => acc && pred_s pt)
    (fun acc => !acc) (fun acc => !acc) ?_ doms_d hdv ?_ true true rfl
  · intro ad as h; show (!ad) = (!as); rw [h]
  · intro ad as ptd h hk hv
    show (ad && pred_d ptd) = (as && pred_s (ptd.map (fun kv => (reg.resolve kv.1, kv.2))))
    rw [h, hpred ptd hv hk]

/-! ## Dense `varsInF` (Task 3 — DomainBatch, part 3)

The covered-set predicates that `forcedOver` filters items by. Their only variable comparisons go
through `denseContainsFast`, so a decoded item's `varsInF` on the resolved target set agrees with the
dense item's `varsInF` on the dense target set. -/

/-- `Expression.varsInF`, over `VarId`s (mirrors `Expression.varsInF`). -/
def DenseExpr.varsInF (xs : List VarId) : DenseExpr p → Bool
  | .const _ => true
  | .var y => denseContainsFast xs y
  | .add a b => a.varsInF xs && b.varsInF xs
  | .mul a b => a.varsInF xs && b.varsInF xs

theorem denseExpr_varsInF_decode (reg : VarRegistry) (xs : List VarId)
    (hxv : ∀ x ∈ xs, reg.Valid x) (e : DenseExpr p) (hc : e.CoveredBy reg) :
    (reg.decodeExpr e).varsInF (xs.map reg.resolve) = e.varsInF xs := by
  induction e with
  | const n => rfl
  | var i =>
      have hiv : reg.Valid i := hc i (by simp [DenseExpr.vars])
      show Expression.varsInF (xs.map reg.resolve) (.var (reg.resolve i)) = denseContainsFast xs i
      exact denseContainsFast_decode reg xs hxv i hiv
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      show Expression.varsInF (xs.map reg.resolve) ((reg.decodeExpr a).add (reg.decodeExpr b))
        = (a.add b).varsInF xs
      rw [Expression.varsInF, DenseExpr.varsInF, iha ha, ihb hb]
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      show Expression.varsInF (xs.map reg.resolve) ((reg.decodeExpr a).mul (reg.decodeExpr b))
        = (a.mul b).varsInF xs
      rw [Expression.varsInF, DenseExpr.varsInF, iha ha, ihb hb]

/-- `BusInteraction.varsInF`, over `VarId`s (mirrors `BusInteraction.varsInF`). -/
def denseBIVarsInF (xs : List VarId) (bi : BusInteraction (DenseExpr p)) : Bool :=
  bi.multiplicity.varsInF xs && bi.payload.all (fun e => e.varsInF xs)

theorem denseBIVarsInF_payload (reg : VarRegistry) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x) :
    ∀ (pl : List (DenseExpr p)), (∀ e ∈ pl, e.CoveredBy reg) →
      (pl.map reg.decodeExpr).all (fun e => e.varsInF (xs.map reg.resolve))
        = pl.all (fun e => e.varsInF xs) := by
  intro pl
  induction pl with
  | nil => intro _; rfl
  | cons e rest ih =>
      intro hcov
      have hce : e.CoveredBy reg := hcov e (List.mem_cons_self ..)
      have hcr : ∀ e' ∈ rest, e'.CoveredBy reg := fun e' h => hcov e' (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, List.all_cons, denseExpr_varsInF_decode reg xs hxv e hce, ih hcr]

theorem denseBIVarsInF_decode (reg : VarRegistry) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (bi : BusInteraction (DenseExpr p)) (hc : denseBICovered reg bi) :
    (reg.decodeBI bi).varsInF (xs.map reg.resolve) = denseBIVarsInF xs bi := by
  obtain ⟨hm, hp⟩ := hc
  have h1 : (reg.decodeBI bi).multiplicity.varsInF (xs.map reg.resolve) = bi.multiplicity.varsInF xs :=
    denseExpr_varsInF_decode reg xs hxv bi.multiplicity hm
  have h2 : (reg.decodeBI bi).payload.all (fun e => e.varsInF (xs.map reg.resolve))
      = bi.payload.all (fun e => e.varsInF xs) :=
    denseBIVarsInF_payload reg xs hxv bi.payload hp
  show ((reg.decodeBI bi).multiplicity.varsInF (xs.map reg.resolve)
      && (reg.decodeBI bi).payload.all (fun e => e.varsInF (xs.map reg.resolve)))
    = (bi.multiplicity.varsInF xs && bi.payload.all (fun e => e.varsInF xs))
  rw [h1, h2]

/-! ## Dense `biInformative` (mirrors `biInformative`)

The informativeness gate on a covered obligation, through `DenseExpr.isVar`/`.constValue?` (both
decode-invariant, unconditionally) and the DigitFold fact-layer `denseInteractionBound`. -/

/-- Dense `biInformative` (mirrors `biInformative`). -/
def denseBiInformative (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  bi.payload.any (fun e => !(e.isVar || e.constValue?.isSome)) ||
  bi.payload.any (fun e => match e with
    | .var i => (denseInteractionBound bs facts bi i).isNone
    | _ => false)

theorem denseBiInformative_snd (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (hbc : denseBICovered reg bi) :
    ∀ (pl : List (DenseExpr p)), (∀ e ∈ pl, e.CoveredBy reg) →
      (pl.map reg.decodeExpr).any (fun e => match e with
          | .var x => (interactionBound bs facts (reg.decodeBI bi) x).isNone | _ => false)
        = pl.any (fun e => match e with
          | .var i => (denseInteractionBound bs facts bi i).isNone | _ => false) := by
  intro pl
  induction pl with
  | nil => intro _; rfl
  | cons e rest ih =>
      intro hcov
      have hce : e.CoveredBy reg := hcov e (List.mem_cons_self ..)
      have hcr : ∀ e' ∈ rest, e'.CoveredBy reg := fun e' h => hcov e' (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, List.any_cons]
      rw [ih hcr]
      congr 1
      cases e with
      | var i =>
          have hiv : reg.Valid i := hce i (by simp [DenseExpr.vars])
          show (interactionBound bs facts (reg.decodeBI bi) (reg.resolve i)).isNone
            = (denseInteractionBound bs facts bi i).isNone
          rw [denseInteractionBound_decode bs facts reg hiv bi hbc]
      | const n => rfl
      | add a b => rfl
      | mul a b => rfl

theorem denseBiInformative_decode (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (hc : denseBICovered reg bi) :
    biInformative bs facts (reg.decodeBI bi) = denseBiInformative bs facts bi := by
  show ((reg.decodeBI bi).payload.any (fun e => !(e.isVar || e.constValue?.isSome))
        || (reg.decodeBI bi).payload.any (fun e => match e with
              | .var x => (interactionBound bs facts (reg.decodeBI bi) x).isNone | _ => false))
    = (bi.payload.any (fun e => !(e.isVar || e.constValue?.isSome))
        || bi.payload.any (fun e => match e with
              | .var i => (denseInteractionBound bs facts bi i).isNone | _ => false))
  congr 1
  · show (bi.payload.map reg.decodeExpr).any (fun e => !(e.isVar || e.constValue?.isSome))
        = bi.payload.any (fun e => !(e.isVar || e.constValue?.isSome))
    simp only [List.any_map, Function.comp_def, reg.decodeExpr_isVar, reg.decodeExpr_constValue?]
  · exact denseBiInformative_snd reg bs facts bi hc bi.payload hc.2

/-! ## Dense inverted index (mirrors `CoveredIndex`)

The `VarId`-keyed inverted index `forcedOver` uses to find covered items in O(local). Its correctness
flows through the correspondence proved here: the dense candidate list (buckets under a target's
variables, plus the variable-less positions) is the *same* `List Nat` as the spec's on the resolved
target, so the dedup `HashSet` and its `toList` are identical, and the per-position `Q` re-check maps
decode-for-decode. Bucket/varless correspondence is the DigitFold/Gauss "HashMap-fold-under-`resolve`"
pattern over the `build` fold. -/

/-- The dense inverted index (mirrors `CoveredIndex.CovIndex`). -/
structure DenseCovIndex where
  buckets : Std.HashMap VarId (List Nat)
  varless : List Nat

/-- One dense index-build step (mirrors `CoveredIndex.buildStep`). -/
def denseBuildStep {α : Type} (varsOf : α → List VarId) (ai : α × Nat) (idx : DenseCovIndex) :
    DenseCovIndex :=
  match varsOf ai.1 with
  | [] => ⟨idx.buckets, ai.2 :: idx.varless⟩
  | vs => ⟨vs.foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets, idx.varless⟩

/-- Build the dense inverted index (mirrors `CoveredIndex.build`). -/
def denseCovBuild {α : Type} (varsOf : α → List VarId) (items : List α) : DenseCovIndex :=
  items.zipIdx.foldr (denseBuildStep varsOf) ⟨∅, []⟩

/-- The dense candidate positions for target `xs` (mirrors `CoveredIndex.candidates`). -/
def denseCandidates (idx : DenseCovIndex) (xs : List VarId) : List Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])) ++ idx.varless

/-- The dense covered items for target `xs`, unordered (mirrors `CoveredIndex.coveredIdxUnord`). -/
def denseCoveredIdxUnord {α : Type} (idx : DenseCovIndex) (arr : Array α) (Q : α → Bool)
    (xs : List VarId) : List α :=
  (((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList).filterMap
    (fun i => if h : i < arr.size then (if Q arr[i] then some arr[i] else none) else none)

/-! ### `buildStep` projection helpers (dense + spec varless) -/

theorem denseBuildStep_buckets_nil {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (h : varsOf ai.1 = []) : (denseBuildStep varsOf ai idx).buckets = idx.buckets := by
  simp only [denseBuildStep, h]

theorem denseBuildStep_buckets_cons {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (w0 : VarId) (ws : List VarId) (h : varsOf ai.1 = w0 :: ws) :
    (denseBuildStep varsOf ai idx).buckets
      = (w0 :: ws).foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets := by
  simp only [denseBuildStep, h]

theorem denseBuildStep_varless_nil {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (h : varsOf ai.1 = []) :
    (denseBuildStep varsOf ai idx).varless = ai.2 :: idx.varless := by
  simp only [denseBuildStep, h]

theorem denseBuildStep_varless_cons {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) (w0 : VarId) (ws : List VarId) (h : varsOf ai.1 = w0 :: ws) :
    (denseBuildStep varsOf ai idx).varless = idx.varless := by
  simp only [denseBuildStep, h]

theorem specBuildStep_varless_nil {α : Type} (varsOf : α → List Variable) (ai : α × Nat)
    (idx : CoveredIndex.CovIndex) (h : varsOf ai.1 = []) :
    (CoveredIndex.buildStep varsOf ai idx).varless = ai.2 :: idx.varless := by
  simp only [CoveredIndex.buildStep, h]

theorem specBuildStep_varless_cons {α : Type} (varsOf : α → List Variable) (ai : α × Nat)
    (idx : CoveredIndex.CovIndex) (w0 : Variable) (ws : List Variable) (h : varsOf ai.1 = w0 :: ws) :
    (CoveredIndex.buildStep varsOf ai idx).varless = idx.varless := by
  simp only [CoveredIndex.buildStep, h]

/-! ### The build correspondence -/

/-- `List.zipIdx` commutes with `List.map` on the elements (positions unchanged). -/
theorem map_zipIdx_dec {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat),
    (l.map f).zipIdx n = (l.zipIdx n).map (fun ai => (f ai.1, ai.2)) := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons a rest ih => intro n; simp only [List.map_cons, List.zipIdx_cons, ih]

/-- Folding the dense bucket-insert over `vs` and the spec bucket-insert over `vs.map resolve`
    preserves the bucket correspondence (`resolve` injective on valid ids). -/
theorem denseBucketFold_corr (reg : VarRegistry) (pos : Nat) :
    ∀ (vs : List VarId), (∀ v ∈ vs, reg.Valid v) →
      ∀ (md : Std.HashMap VarId (List Nat)) (ms : Std.HashMap Variable (List Nat)),
      (∀ i, reg.Valid i → md.getD i [] = ms.getD (reg.resolve i) []) →
      ∀ i, reg.Valid i →
        (vs.foldl (fun m v => m.insert v (pos :: m.getD v [])) md).getD i []
          = ((vs.map reg.resolve).foldl (fun m v => m.insert v (pos :: m.getD v [])) ms).getD (reg.resolve i) [] := by
  intro vs
  induction vs with
  | nil => intro _ md ms hinv i hi; exact hinv i hi
  | cons v rest ih =>
      intro hvv md ms hinv i hi
      have hvvh : reg.Valid v := hvv v (List.mem_cons_self ..)
      have hrv : ∀ v' ∈ rest, reg.Valid v' := fun v' h => hvv v' (List.mem_cons_of_mem _ h)
      simp only [List.map_cons, List.foldl_cons]
      refine ih hrv _ _ ?_ i hi
      intro i' hi'
      rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert]
      by_cases hvi : v = i'
      · subst hvi
        simp only [beq_self_eq_true, if_true]
        rw [hinv v hvvh]
      · have hvi' : ¬ reg.resolve v = reg.resolve i' := fun he => hvi (reg.resolve_inj hvvh hi' he)
        rw [if_neg (by simpa using hvi), if_neg (by simpa using hvi')]
        exact hinv i' hi'

/-- The dense/spec build folds over a shared zipIdx list agree on `varless` (equal lists) and on
    every bucket (equal `List Nat`) under `resolve`. -/
theorem denseBuildStep_fold_corr {α β : Type} (reg : VarRegistry) (dec : α → β)
    (varsOf_d : α → List VarId) (varsOf_s : β → List Variable)
    (hvo : ∀ a, varsOf_s (dec a) = (varsOf_d a).map reg.resolve) :
    ∀ (l : List (α × Nat)), (∀ ai ∈ l, ∀ v ∈ varsOf_d ai.1, reg.Valid v) →
      (l.foldr (denseBuildStep varsOf_d) ⟨∅, []⟩).varless
          = ((l.map (fun ai => (dec ai.1, ai.2))).foldr (CoveredIndex.buildStep varsOf_s) ⟨∅, []⟩).varless
        ∧ (∀ i, reg.Valid i →
            (l.foldr (denseBuildStep varsOf_d) ⟨∅, []⟩).buckets.getD i []
              = ((l.map (fun ai => (dec ai.1, ai.2))).foldr (CoveredIndex.buildStep varsOf_s) ⟨∅, []⟩).buckets.getD (reg.resolve i) []) := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨rfl, fun i _ => by simp only [List.foldr_nil, List.map_nil, Std.HashMap.getD_empty]⟩
  | cons ai0 rest ih =>
      intro hv
      have hvrest : ∀ ai ∈ rest, ∀ v ∈ varsOf_d ai.1, reg.Valid v :=
        fun ai h => hv ai (List.mem_cons_of_mem _ h)
      have hv0 : ∀ v ∈ varsOf_d ai0.1, reg.Valid v := hv ai0 (List.mem_cons_self ..)
      obtain ⟨ihvarless, ihbuckets⟩ := ih hvrest
      have hvo0 : varsOf_s (dec ai0.1) = (varsOf_d ai0.1).map reg.resolve := hvo ai0.1
      simp only [List.foldr_cons, List.map_cons]
      cases hvs : varsOf_d ai0.1 with
      | nil =>
          have hvs' : varsOf_s (dec ai0.1) = [] := by rw [hvo0, hvs]; rfl
          refine ⟨?_, ?_⟩
          · rw [denseBuildStep_varless_nil varsOf_d ai0 _ hvs,
                specBuildStep_varless_nil varsOf_s (dec ai0.1, ai0.2) _ hvs', ihvarless]
          · intro i hi
            rw [denseBuildStep_buckets_nil varsOf_d ai0 _ hvs,
                CoveredIndex.buildStep_buckets_nil varsOf_s (dec ai0.1, ai0.2) _ hvs']
            exact ihbuckets i hi
      | cons w0 ws =>
          have hvs' : varsOf_s (dec ai0.1) = reg.resolve w0 :: ws.map reg.resolve := by
            rw [hvo0, hvs]; rfl
          refine ⟨?_, ?_⟩
          · rw [denseBuildStep_varless_cons varsOf_d ai0 _ w0 ws hvs,
                specBuildStep_varless_cons varsOf_s (dec ai0.1, ai0.2) _ (reg.resolve w0) (ws.map reg.resolve) hvs']
            exact ihvarless
          · intro i hi
            rw [denseBuildStep_buckets_cons varsOf_d ai0 _ w0 ws hvs,
                CoveredIndex.buildStep_buckets_cons varsOf_s (dec ai0.1, ai0.2) _ (reg.resolve w0) (ws.map reg.resolve) hvs']
            exact denseBucketFold_corr reg ai0.2 (w0 :: ws) (by rw [← hvs]; exact hv0) _ _ ihbuckets i hi

/-- **The dense inverted index decodes to `CoveredIndex.build`**: `varless` equal, and every bucket
    equal (as `List Nat`) under `resolve`, given the item vars decode and are valid. -/
theorem denseCovBuild_corr {α β : Type} (reg : VarRegistry) (dec : α → β)
    (varsOf_d : α → List VarId) (varsOf_s : β → List Variable)
    (hvo : ∀ a, varsOf_s (dec a) = (varsOf_d a).map reg.resolve)
    (items_d : List α) (hitems : ∀ a ∈ items_d, ∀ v ∈ varsOf_d a, reg.Valid v) :
    (denseCovBuild varsOf_d items_d).varless = (CoveredIndex.build varsOf_s (items_d.map dec)).varless
      ∧ (∀ i, reg.Valid i → (denseCovBuild varsOf_d items_d).buckets.getD i []
          = (CoveredIndex.build varsOf_s (items_d.map dec)).buckets.getD (reg.resolve i) []) := by
  unfold denseCovBuild CoveredIndex.build
  rw [map_zipIdx_dec dec items_d 0]
  refine denseBuildStep_fold_corr reg dec varsOf_d varsOf_s hvo items_d.zipIdx ?_
  intro ai hai v hv
  have hmem : ai.1 ∈ items_d := by
    have h1 : ai.1 ∈ (items_d.zipIdx).map Prod.fst := List.mem_map.2 ⟨ai, hai, rfl⟩
    rwa [List.zipIdx_map_fst] at h1
  exact hitems ai.1 hmem v hv

/-- The dense candidate list is the *same* `List Nat` as the spec candidate list on the resolved
    target (varless + buckets equal). -/
theorem denseFlatMapGetD (reg : VarRegistry) (idx_d : DenseCovIndex) (idx_s : CoveredIndex.CovIndex)
    (hbuckets : ∀ i, reg.Valid i → idx_d.buckets.getD i [] = idx_s.buckets.getD (reg.resolve i) []) :
    ∀ (xs : List VarId), (∀ x ∈ xs, reg.Valid x) →
      xs.flatMap (fun v => idx_d.buckets.getD v [])
        = (xs.map reg.resolve).flatMap (fun v => idx_s.buckets.getD v []) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x rest ih =>
      intro hxv
      have hxvh : reg.Valid x := hxv x (List.mem_cons_self ..)
      have hrv : ∀ x' ∈ rest, reg.Valid x' := fun x' h => hxv x' (List.mem_cons_of_mem _ h)
      rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, hbuckets x hxvh, ih hrv]

theorem denseCandidates_corr (reg : VarRegistry) (idx_d : DenseCovIndex)
    (idx_s : CoveredIndex.CovIndex) (xs : List VarId) (hxv : ∀ x ∈ xs, reg.Valid x)
    (hvarless : idx_d.varless = idx_s.varless)
    (hbuckets : ∀ i, reg.Valid i → idx_d.buckets.getD i [] = idx_s.buckets.getD (reg.resolve i) []) :
    denseCandidates idx_d xs = CoveredIndex.candidates idx_s (xs.map reg.resolve) := by
  unfold denseCandidates CoveredIndex.candidates
  rw [hvarless]
  congr 1
  exact denseFlatMapGetD reg idx_d idx_s hbuckets xs hxv

/-- **`denseCoveredIdxUnord` decodes to `CoveredIndex.coveredIdxUnord`.** Given identical candidate
    lists (`hcand`) and a decode-corresponding predicate on the items, the dense covered list maps
    element-for-element to the spec covered list. -/
theorem denseCoveredIdxUnord_corr {α β : Type} (reg : VarRegistry) (dec : α → β)
    (idx_d : DenseCovIndex) (idx_s : CoveredIndex.CovIndex) (items_d : List α)
    (Q_d : α → Bool) (Q_s : β → Bool) (xs : List VarId)
    (hcand : denseCandidates idx_d xs = CoveredIndex.candidates idx_s (xs.map reg.resolve))
    (hQ : ∀ a ∈ items_d, Q_d a = Q_s (dec a)) :
    (denseCoveredIdxUnord idx_d items_d.toArray Q_d xs).map dec
      = CoveredIndex.coveredIdxUnord idx_s (items_d.map dec).toArray Q_s (xs.map reg.resolve) := by
  unfold denseCoveredIdxUnord
  simp only [CoveredIndex.coveredIdxUnord]
  rw [hcand, List.map_filterMap]
  refine CoveredIndex.filterMap_congr' _ (fun i _ => ?_)
  by_cases hlt : i < items_d.length
  · rw [dif_pos (show i < items_d.toArray.size by simpa using hlt),
        dif_pos (show i < (items_d.map dec).toArray.size by
          simp only [List.size_toArray, List.length_map]; exact hlt)]
    simp only [List.getElem_toArray, List.getElem_map]
    have hqeq : Q_s (dec items_d[i]) = Q_d items_d[i] := (hQ items_d[i] (items_d.getElem_mem hlt)).symm
    by_cases hq : Q_d items_d[i] = true
    · rw [if_pos hq, if_pos (hqeq.trans hq), Option.map_some]
    · rw [if_neg hq, if_neg (by rw [hqeq]; exact hq), Option.map_none]
  · rw [dif_neg (by simpa using hlt),
        dif_neg (by simp only [List.size_toArray, List.length_map]; exact hlt), Option.map_none]

/-! ### Dense `ForcedIdx` and its correspondence -/

/-- The dense analog of `ForcedIdx` (plain data — no soundness witnesses; correctness rides on the
    correspondence + inherited `PassCorrect`). -/
structure DenseForcedIdx (p : ℕ) where
  csIdx : DenseCovIndex
  arrCs : Array (DenseExpr p)
  bisIdx : DenseCovIndex
  arrBis : Array (BusInteraction (DenseExpr p))
  activeIdx : DenseCovIndex
  arrActive : Array (DenseExpr p)

/-- The dense domain-table `doms` list has keys `xs` (mirrors `DomainTable.doms_fst`). -/
theorem DenseDomainTable.doms_fst (T : DenseDomainTable p) :
    ∀ (xs : List VarId) (ds : List (VarId × FiniteDomain p)),
      T.doms xs = some ds → ds.map Prod.fst = xs := by
  intro xs
  induction xs with
  | nil => intro ds h; simp only [DenseDomainTable.doms, Option.some.injEq] at h; subst h; rfl
  | cons x rest ih =>
      intro ds h
      rw [DenseDomainTable.doms] at h
      cases hd : T.map[x]? with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some d =>
          cases hr : T.doms rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds' =>
              rw [hd, hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp [ih ds' hr]

/-! ### Dense covered-index soundness (membership of an enumerated item is a real covered item) -/

theorem denseCoveredIdxUnord_mem {α : Type} (idx : DenseCovIndex) (arr : Array α) (Q : α → Bool)
    (xs : List VarId) {e : α} (he : e ∈ denseCoveredIdxUnord idx arr Q xs) :
    ∃ i, ∃ _h : i < arr.size, arr[i] = e ∧ Q e = true := by
  rw [denseCoveredIdxUnord, List.mem_filterMap] at he
  obtain ⟨i, _hi, hfe⟩ := he
  by_cases h : i < arr.size
  · rw [dif_pos h] at hfe
    by_cases hq : Q arr[i]
    · rw [if_pos hq] at hfe
      have hei : arr[i] = e := Option.some.inj hfe
      exact ⟨i, h, hei, by rw [← hei]; exact hq⟩
    · rw [if_neg hq] at hfe; exact absurd hfe (by simp)
  · rw [dif_neg h] at hfe; exact absurd hfe (by simp)

theorem denseCoveredIdxUnord_mem_of_eq {α : Type} (idx : DenseCovIndex) (l : List α) (arr : Array α)
    (harr : arr = l.toArray) (Q : α → Bool) (xs : List VarId)
    {e : α} (he : e ∈ denseCoveredIdxUnord idx arr Q xs) : e ∈ l ∧ Q e = true := by
  subst harr
  obtain ⟨i, hi, hei, hq⟩ := denseCoveredIdxUnord_mem idx l.toArray Q xs he
  subst hei
  have hi' : i < l.length := by simpa using hi
  exact ⟨by simp [l.getElem_mem hi'], hq⟩

/-- Canonical dedup key of a dense variable set: the spec `varSetKey` on the resolved variables. -/
def denseVarSetKey (reg : VarRegistry) (xs : List VarId) : String := varSetKey (xs.map reg.resolve)

/-- Apply a dense solution map to a system, unless it is empty (mirrors the spec pass's
    `if σ.map.isEmpty then cs else cs.substF σ.fn`). Kept as a standalone function so the solution
    map is computed exactly once (as the argument). -/
def applyσ (dσ : DenseSolved p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if dσ.map.isEmpty then d else d.substF dσ.fn
