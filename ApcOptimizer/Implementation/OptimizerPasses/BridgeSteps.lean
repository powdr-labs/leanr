import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Certified-step loop combinators and bus-rewrite vocabulary

Reusable proof infrastructure that makes pass proofs compose *mechanically*, packaging two shapes
that have already been hand-rolled more than once:

* **The certified-step induction.** `denseReencodeLoop_correct` (`ReencodeProof.lean`) hand-rolls
  the composition of per-step `DensePassCorrect` certificates along `denseReencodeLoop`, threading
  `Extends` + coverage + pointwise-`isInput` through an induction and transporting each step's
  certificate to the final registry via `funext`; `busPairCancel`'s `denseCancelLoop`
  (`BusPairCancel.lean`) hand-rolls the same shape via a proof-carrying `DenseDropResult`.
  `bytePack`'s drain loop is about to need it a third time. The `DenseNativeStep` record travels the
  invariants *with the value*, and `DenseNativeStep.trans`/`.foldList`/`.drain` package the
  induction once.

* **The bus-rewrite vocabulary.** `denseBIMapExpr` applies an expression rewrite to every field of a
  `BusInteraction (DenseExpr p)`, with a canonical public lemma cluster
  (`denseBIMapExpr_eval_of_agree` / `denseBIMapExpr_eq_self` / `denseBIMapExpr_vars_subset`).

## Proof-architecture defaults (see also `Bridge.lean`)

Proof-carrying structures use **`Prop`-carrying dense twins** — `Prop` fields about dense data
only, which erase — rather than externalising invariants into a threaded induction (precedent:
`DenseDropResult`, and now `DenseNativeStep`). Data-only dense records remain correct only where a
*carried* proof would force representation correspondence (`DenseTwoRootMap.Sound`-style lookup
invariants). Loops compose via the `DenseNativeStep` combinators here; passes lift once, at the
optimizer boundary, through `DensePassCorrect.lift`.

The key `isInput`-composition fact baked in (from `ReencodeProof.register_isInput_eq`): registering
a `powdrId? = none` `Variable` leaves `VarRegistry.isInput` **pointwise unchanged as a function**
(invalid IDs resolve to the metadata-free default, already `isInput = false`), so a pass minting only
derived (`none`) variables preserves `isInput` exactly — certificates compose at literally the same
`isInput` function, with no support-based transport (only the pointwise-stability lemma). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `DenseNativeStep`: a certified step, invariants travelling with the value

One step of a dense transform, from registry `reg`/system `d` to `reg'`/`out`, minting the
dense derivations `dd`. The data fields (`reg'`/`out`/`dd`) are the runtime output; the five
`Prop` fields erase. `hii` is the pointwise-`isInput` preservation in `funext` form (the form that
composes cleanly under `trans`: certificates are transported by a single `rw`). -/
structure DenseNativeStep (p : ℕ) (bs : BusSemantics p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) where
  /-- The (possibly extended) output registry. -/
  reg' : VarRegistry
  /-- The transformed dense system. -/
  out : DenseConstraintSystem p
  /-- The dense derivations minted by this step. -/
  dd : DenseDerivations p
  /-- The registry only grows. -/
  ext : reg.Extends reg'
  /-- Minting only derived (`powdrId? = none`) columns preserves `isInput` pointwise. -/
  hii : reg'.isInput = reg.isInput
  /-- The output is covered by the output registry. -/
  cov : out.CoveredBy reg'
  /-- The minted derivations are covered by the output registry. -/
  dcov : dd.CoveredBy reg'
  /-- Correctness at the output registry's `isInput`. -/
  correct : DensePassCorrect reg'.isInput d out dd bs

/-- **Reflexivity / identity step.** Same registry and system, no new derivations. The base case of a
    fold/drain; the input coverage is what fills the `cov` field. -/
def DenseNativeStep.refl (bs : BusSemantics p) {reg : VarRegistry} {d : DenseConstraintSystem p}
    (hcov : d.CoveredBy reg) : DenseNativeStep p bs reg d where
  reg' := reg
  out := d
  dd := []
  ext := VarRegistry.Extends.refl reg
  hii := rfl
  cov := hcov
  dcov := by intro x hx; simp at hx
  correct := DensePassCorrect.refl reg.isInput d bs

/-- **Non-extending step.** Keep the registry (`reg' = reg`, `hii = rfl`), change the system to `out`
    with no new derivations — the shape of a `busPairCancel`/`bytePack` drop or pack step. The single
    step's correctness `hcorrect` and the output coverage `hcov` are supplied by the caller. -/
def DenseNativeStep.ofSame (bs : BusSemantics p) {reg : VarRegistry} {d out : DenseConstraintSystem p}
    (hcov : out.CoveredBy reg) (hcorrect : DensePassCorrect reg.isInput d out [] bs) :
    DenseNativeStep p bs reg d where
  reg' := reg
  out := out
  dd := []
  ext := VarRegistry.Extends.refl reg
  hii := rfl
  cov := hcov
  dcov := by intro x hx; simp at hx
  correct := hcorrect

/-- **Sequential composition of two certified steps.** Given `s1 : reg → s1.reg'` and a step `s2`
    *from* `s1`'s output, produce the composite `reg → s2.reg'`, concatenating derivations
    (`s1.dd ++ s2.dd`). This is exactly the reencode/busPairCancel loop body, packaged once: the first
    step's certificate is transported forward to the final registry's `isInput` by a single
    `rw [s2.hii]` (the pointwise-stability the loop threads), then composed with `DensePassCorrect.andThen`. -/
def DenseNativeStep.trans {bs : BusSemantics p} {reg : VarRegistry} {d : DenseConstraintSystem p}
    (s1 : DenseNativeStep p bs reg d) (s2 : DenseNativeStep p bs s1.reg' s1.out) :
    DenseNativeStep p bs reg d where
  reg' := s2.reg'
  out := s2.out
  dd := s1.dd ++ s2.dd
  ext := s1.ext.trans s2.ext
  hii := s2.hii.trans s1.hii
  cov := s2.cov
  dcov := DenseDerivations.coveredBy_append (DenseDerivations.CoveredBy.mono s2.ext s1.dcov) s2.dcov
  correct := by
    have h1 : DensePassCorrect s2.reg'.isInput d s1.out s1.dd bs := by
      rw [s2.hii]; exact s1.correct
    exact h1.andThen s2.correct

/-! ## Fold and drain combinators

Both fold a family of per-step certificates into a single `DenseNativeStep` via `trans`, threading an
opaque state `σ` (reencode threads `csIdx`/`arrCs`/`varSet`/`idx`; bytePack threads nothing) and the
running coverage (each step receives its input coverage; the next step gets the current step's output
coverage, seeded by the pass's input coverage). Nothing in the proof looks inside `σ`. -/

/-- **List fold.** Compose the per-step certificates produced by `step` along `xs`, left to right,
    into one certified step (final registry, final system, concatenated derivations, composed
    certificate) and the final `σ`. Structural on `xs`. -/
def DenseNativeStep.foldList {α σ : Type} (bs : BusSemantics p)
    (step : α → σ → (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
      σ × DenseNativeStep p bs reg d) :
    List α → σ → (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
      σ × DenseNativeStep p bs reg d
  | [], s, _reg, _d, hcov => (s, DenseNativeStep.refl bs hcov)
  | x :: xs, s, reg, d, hcov =>
    let r1 := step x s reg d hcov
    let r2 := DenseNativeStep.foldList bs step xs r1.1 r1.2.reg' r1.2.out r1.2.cov
    (r2.1, r1.2.trans r2.2)

/-- **Drain.** Iterate `step` (which reports `none` at the fixpoint) up to `fuel` times, composing the
    per-step certificates into one certified step and returning the final `σ`. Structural on `fuel`;
    `fuel` matches the runtime drain shape (e.g. the live-interaction count is a safe bound). -/
def DenseNativeStep.drain {σ : Type} (bs : BusSemantics p)
    (step : σ → (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
      Option (σ × DenseNativeStep p bs reg d)) :
    Nat → σ → (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
      σ × DenseNativeStep p bs reg d
  | 0, s, _reg, _d, hcov => (s, DenseNativeStep.refl bs hcov)
  | fuel + 1, s, reg, d, hcov =>
    match step s reg d hcov with
    | none => (s, DenseNativeStep.refl bs hcov)
    | some r1 =>
      let r2 := DenseNativeStep.drain bs step fuel r1.1 r1.2.reg' r1.2.out r1.2.cov
      (r2.1, r1.2.trans r2.2)

/-! ## Glue into `DensePassResult` / the pass builders

`toDensePassResult` closes a certified step directly into the existing `DensePassResult` (what
`of`/`ofExtending` produce), applying `DensePassCorrect.lift` at the extended registry and
restating the input decode at the original registry via `Extends.decodeCS_eq` — the same discharge as
`ofExtending`'s `correct` field. `ofDenseStep` wires it into a `DenseVerifiedPassW`: a pass
author builds a `DenseNativeStep` (via `foldList`/`drain`/`ofSame`) and gets the pass for free. -/

/-- Close a certified step into the framework `DensePassResult`. The `correct` field is discharged by
    `DensePassCorrect.lift` (re-covering the input at the extended registry with
    `denseCS_coveredBy_mono`, then `Extends.decodeCS_eq` to restate at the original registry). -/
def DenseNativeStep.toDensePassResult {bs : BusSemantics p} {reg : VarRegistry}
    {d : DenseConstraintSystem p} (s : DenseNativeStep p bs reg d) (hcov : d.CoveredBy reg) :
    DensePassResult reg d bs where
  reg' := s.reg'
  out := s.out
  derivs := s.dd
  ext := s.ext
  covered := s.cov
  dcovered := s.dcov
  correct := by
    have hcovd' : d.CoveredBy s.reg' := denseCS_coveredBy_mono s.ext hcov
    have hlift := DensePassCorrect.lift hcovd' s.cov s.dcov s.correct
    rwa [s.ext.decodeCS_eq hcov] at hlift

/-- Build a `DenseVerifiedPassW` from a per-invocation certified-step builder (typically a
    `foldList`/`drain` projection). The runtime output is the step's data (`reg'`/`out`/`dd`); the
    framework obligations are the step's erased `Prop` fields, lifted once. -/
def DenseVerifiedPassW.ofDenseStep
    (build : (reg : VarRegistry) → (bs : BusSemantics p) → (facts : BusFacts p bs) →
      (d : DenseConstraintSystem p) → d.CoveredBy reg → DenseNativeStep p bs reg d) :
    DenseVerifiedPassW p :=
  fun reg d hcov bs facts => (build reg bs facts d hcov).toDensePassResult hcov

/-- `ofDenseStep` respects the degree bound whenever the built step's decoded output stays within
    bound (the per-build degree obligation). -/
theorem DenseVerifiedPassW.ofDenseStep_respectsDeg {b : DegreeBound}
    {build : (reg : VarRegistry) → (bs : BusSemantics p) → (facts : BusFacts p bs) →
      (d : DenseConstraintSystem p) → d.CoveredBy reg → DenseNativeStep p bs reg d}
    (hdeg : ∀ (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
      (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg),
      (reg.decodeCS d).withinDegree b →
      ((build reg bs facts d hcov).reg'.decodeCS (build reg bs facts d hcov).out).withinDegree b) :
    DenseRespectsDeg b (ofDenseStep build) := by
  intro reg d hcov bs facts hin
  exact hdeg reg bs facts d hcov hin

/-! ## Projection glue for `ofExtending`

For pass authors who split the runtime data transform from the proof: package a certified step as the
`(reg', out, dd)` tuple `ofExtending`'s `transform` returns, and discharge the four obligations
by projection. Each lemma's statement is exactly the shape `ofExtending` demands
(`hext`/`hcov`/`hdcov`/`hcorrect`) — the tuple projections reduce definitionally to the fields, so the
discharge is `.proj_ext`/`.proj_cov`/… with zero rewriting (`hcorrect` lines up because `.correct` is
already stated at `reg'.isInput = toTuple.1.isInput`). -/

/-- The `(reg', out, dd)` tuple an `ofExtending` transform returns. -/
@[reducible] def DenseNativeStep.toTuple {bs : BusSemantics p} {reg : VarRegistry}
    {d : DenseConstraintSystem p} (s : DenseNativeStep p bs reg d) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p := (s.reg', s.out, s.dd)

theorem DenseNativeStep.proj_ext {bs : BusSemantics p} {reg : VarRegistry}
    {d : DenseConstraintSystem p} (s : DenseNativeStep p bs reg d) :
    reg.Extends s.toTuple.1 := s.ext

theorem DenseNativeStep.proj_cov {bs : BusSemantics p} {reg : VarRegistry}
    {d : DenseConstraintSystem p} (s : DenseNativeStep p bs reg d) :
    s.toTuple.2.1.CoveredBy s.toTuple.1 := s.cov

theorem DenseNativeStep.proj_dcov {bs : BusSemantics p} {reg : VarRegistry}
    {d : DenseConstraintSystem p} (s : DenseNativeStep p bs reg d) :
    s.toTuple.2.2.CoveredBy s.toTuple.1 := s.dcov

theorem DenseNativeStep.proj_correct {bs : BusSemantics p} {reg : VarRegistry}
    {d : DenseConstraintSystem p} (s : DenseNativeStep p bs reg d) :
    DensePassCorrect s.toTuple.1.isInput d s.toTuple.2.1 s.toTuple.2.2 bs := s.correct

/-- The four projections deliver exactly the `ofExtending` obligation shapes for the transform
    `fun … => s.toTuple`. -/
private example {bs : BusSemantics p} {reg : VarRegistry} {d : DenseConstraintSystem p}
    (s : DenseNativeStep p bs reg d) :
    reg.Extends s.toTuple.1 ∧ s.toTuple.2.1.CoveredBy s.toTuple.1
      ∧ s.toTuple.2.2.CoveredBy s.toTuple.1
      ∧ DensePassCorrect s.toTuple.1.isInput d s.toTuple.2.1 s.toTuple.2.2 bs :=
  ⟨s.proj_ext, s.proj_cov, s.proj_dcov, s.proj_correct⟩

/-! ## Sanity check: a two-step toy pass through `foldList`

One step **extends** the registry (mints a `powdrId? = none` column, keeping the system), the other
is the identity — composed by `foldList`, closed into a `DenseVerifiedPassW` through `ofDenseStep`.
The extending step's `hii` uses the baked-in pointwise-stability lemma below (a `private` restatement
of `ReencodeProof.register_isInput_eq`, kept file-local to avoid a duplicate global). -/

private theorem register_isInput_stable (reg : VarRegistry) (v : Variable) (hv : v.powdrId? = none)
    (i : VarId) : (reg.register v).1.isInput i = reg.isInput i := by
  by_cases hvalid : reg.Valid i
  · rw [VarRegistry.isInput, VarRegistry.isInput,
        (VarRegistry.register_extends reg v).resolve_eq hvalid]
  · have hge : reg.byId.size ≤ i.index := Nat.not_lt.mp hvalid
    have hreg : reg.isInput i = false := by
      show ((reg.byId[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_eq_none hge]; rfl
    rw [hreg]
    show (((reg.register v).1.byId[i.index]?).getD default).powdrId?.isSome = false
    unfold VarRegistry.register
    split
    · show ((reg.byId[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_eq_none hge]; rfl
    · show (((reg.byId.push v)[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_push]
      split
      · rw [Option.getD_some]; show (v.powdrId?).isSome = false; rw [hv]; rfl
      · rw [Array.getElem?_eq_none hge]; rfl

private def toyFreshVar : Variable := { name := "bridgesteps_toy", powdrId? := none }

private def toyStep (bs : BusSemantics p) :
    Bool → Unit → (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
      Unit × DenseNativeStep p bs reg d :=
  fun b _ reg d hcov =>
    if b then
      ((),
       { reg' := (reg.register toyFreshVar).1
         out := d
         dd := []
         ext := VarRegistry.register_extends reg toyFreshVar
         hii := funext (fun i => register_isInput_stable reg toyFreshVar rfl i)
         cov := denseCS_coveredBy_mono (VarRegistry.register_extends reg toyFreshVar) hcov
         dcov := by intro x hx; simp at hx
         correct := DensePassCorrect.refl (reg.register toyFreshVar).1.isInput d bs })
    else ((), DenseNativeStep.refl bs hcov)

private def toyPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofDenseStep (fun reg bs _facts d hcov =>
    (DenseNativeStep.foldList bs (toyStep bs) [true, false] () reg d hcov).2)

/-! ## Bus-rewrite vocabulary: the dense `BusInteraction.mapExpr`

`denseBIMapExpr` applies an expression-level rewrite to every field of a dense bus interaction, with
a canonical public lemma cluster (`denseBIMapExpr_eval_of_agree` / `denseBIMapExpr_eq_self` /
`denseBIMapExpr_vars_subset`). This is additive: existing per-pass inline copies
(`denseBIEval_mapExpr_of_agree`, `denseMapExpr_eq_self`, `denseMapExpr_vars_subset` in
`DomainFoldProof.lean`, stated over the inline `{ bi with … }` form) stay untouched. -/

/-- Apply `g` to every expression of a dense bus interaction (dense payload). -/
def denseBIMapExpr (bi : BusInteraction (DenseExpr p)) (g : DenseExpr p → DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := bi.busId, multiplicity := g bi.multiplicity, payload := bi.payload.map g }

/-- A rewritten interaction evaluates identically given expression-level agreement. -/
theorem denseBIMapExpr_eval_of_agree (g : DenseExpr p → DenseExpr p) (denv : VarId → ZMod p)
    (hag : ∀ e : DenseExpr p, (g e).eval denv = e.eval denv) (bi : BusInteraction (DenseExpr p)) :
    denseBIEval (denseBIMapExpr bi g) denv = denseBIEval bi denv := by
  unfold denseBIMapExpr denseBIEval
  simp only [hag bi.multiplicity, List.map_map]
  congr 1
  exact List.map_congr_left (fun e _ => by simp only [Function.comp_apply]; exact hag e)

/-- A rewrite fixing each of an interaction's expressions leaves the interaction unchanged. -/
theorem denseBIMapExpr_eq_self {bi : BusInteraction (DenseExpr p)} {g : DenseExpr p → DenseExpr p}
    (hm : g bi.multiplicity = bi.multiplicity) (hp : ∀ e ∈ bi.payload, g e = e) :
    denseBIMapExpr bi g = bi := by
  unfold denseBIMapExpr
  have hpl : bi.payload.map g = bi.payload :=
    (List.map_congr_left (g := id) hp).trans (List.map_id _)
  rw [hm, hpl]

/-- A rewrite introducing no variables per expression keeps an interaction's variables. -/
theorem denseBIMapExpr_vars_subset (g : DenseExpr p → DenseExpr p)
    (hg : ∀ (e : DenseExpr p) (i : VarId), i ∈ (g e).vars → i ∈ e.vars)
    (bi : BusInteraction (DenseExpr p)) :
    ∀ i ∈ denseBIVars (denseBIMapExpr bi g), i ∈ denseBIVars bi := by
  intro i hi
  unfold denseBIMapExpr at hi
  simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hi ⊢
  rcases hi with hi | ⟨e, he, hi⟩
  · exact Or.inl (hg _ i hi)
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact Or.inr ⟨e0, he0, hg e0 i hi⟩

end ApcOptimizer.Dense
