import ApcOptimizer.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false

/-! # A shared, threaded fact store (implementation)

The optimizer's passes each derive the same kinds of data — variable→item occurrence indices,
value-bound maps, two-root decompositions, entailed finite domains, materialized range lists — and
today each pass rebuilds its own from scratch on every cleanup cycle, then discards it. This module
adds a **`FactStore`**: one value threaded through the whole cleanup cycle (prelude → cleanup
fixpoint → coda) so those derived structures can be built once and reused across passes and cycles.

The store is deliberately **`Prop`-free**: it carries only raw data (hash maps / lists over the
spec-level types `Variable`, `Expression`, `ZMod p`, `Nat`), never a soundness proof. Every consumer
**re-validates what it reads against the current system** — exactly the candidate-then-reverify
pattern already used by `CoveredIndex` (`coveredIdx_mem`), `busPairCancel`'s `recvIndex`, and the
`VarCsIdx`. So a store entry that has gone stale (a cached position that now names a different item,
a bound whose witnessing interaction was dropped) can at most cause a consumer to *miss* an
optimization; it can never license an unsound one. This is the "untrusted candidate generator"
discipline: correctness never depends on the store being fresh or even correct.

Because the store carries no proof, threading it needs no proof either: a `VerifiedPassS` returns
the same proof-carrying `PassResult` as a `VerifiedPassW` (so `PassCorrect` composes exactly as
before, via `PassCorrect.andThen`) plus an updated store on the side. The degree-respecting
machinery mirrors `FactPass.lean` one-for-one. The top-level `pipeline` seeds the store with
`FactStore.empty`, threads it, and discards it — so `optimizerWithBusFacts` and the audited
`ApcOptimizer/Optimizer.lean` are unchanged. -/

variable {p : ℕ}

/-- The shared derived-data store threaded through the cleanup cycle. `Prop`-free: only raw data,
    no soundness proof — consumers re-validate against the current system. Starts empty
    (`FactStore.empty`); members are added incrementally. -/
structure FactStore (p : ℕ) where
  -- members added in later phases
  deriving Inhabited

/-- The empty store: no cached facts. -/
def FactStore.empty : FactStore p := {}

/-- A proof-carrying pass that additionally threads the shared `FactStore`: given the current
    system, semantics, proven facts, and the incoming store, it returns the usual proof-carrying
    `PassResult` **plus** an updated store. The store is data only; the `PassResult` is exactly the
    obligation a `VerifiedPassW` discharges, so correctness composes unchanged. -/
abbrev VerifiedPassS (p : ℕ) :=
  (cs : ConstraintSystem p) → (bs : BusSemantics p) → (facts : BusFacts p bs) →
    FactStore p → PassResult cs bs × FactStore p

/-- Any fact-aware (non-store) pass is a store pass that passes the store through untouched. Safe
    because consumers re-validate: passing a store across a pass that changed the system can at most
    make a later reuse miss. -/
def VerifiedPassW.toS (f : VerifiedPassW p) : VerifiedPassS p :=
  fun cs bs facts s => (f cs bs facts, s)

/-- Sequential composition (same proof shape as `VerifiedPassW.andThen`): the `PassResult`s compose
    via `PassCorrect.andThen`, derivations concatenate, and the store threads through. -/
def VerifiedPassS.andThen (f g : VerifiedPassS p) : VerifiedPassS p :=
  fun cs bs facts s =>
    let r1 := f cs bs facts s
    let r2 := g r1.1.out bs facts r1.2
    (⟨r2.1.out, r1.1.derivs ++ r2.1.derivs, r1.1.correct.andThen r2.1.correct⟩, r2.2)

/-- Wrap a store pass with a degree guard: if the output would exceed the bound, keep the input
    system (correct by reflexivity) but retain the pass's store work (sound regardless of which
    system we keep). -/
def VerifiedPassS.guardDegree (f : VerifiedPassS p) : VerifiedPassS p :=
  fun cs bs facts s =>
    let r := f cs bs facts s
    if r.1.out.withinDegreeB bs.degreeBound then r
    else (⟨cs, [], PassCorrect.refl cs bs⟩, r.2)

/-! ## Degree guarding for store passes

Mirrors `FactPass.lean`'s `RespectsDeg` machinery: the store output is irrelevant to the degree
bound, so every lemma is the fact-aware one with the extra store argument threaded through. -/

/-- A store pass never pushes a within-bound system past the semantics' degree bound. Identical to
    `RespectsDeg` up to the extra (ignored, for degree purposes) store argument. -/
def RespectsDegS (f : VerifiedPassS p) : Prop :=
  ∀ (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) (s : FactStore p),
    cs.withinDegree bs.degreeBound → (f cs bs facts s).1.out.withinDegree bs.degreeBound

/-- A degree-respecting fact-aware pass lifts to a degree-respecting store pass. -/
theorem VerifiedPassW.toS_respectsDeg {f : VerifiedPassW p} (hf : RespectsDeg f) :
    RespectsDegS f.toS :=
  fun cs bs facts _ h => hf cs bs facts h

theorem VerifiedPassS.guardDegree_respectsDeg (f : VerifiedPassS p) :
    RespectsDegS f.guardDegree := by
  intro cs bs facts s h
  by_cases hok : (f cs bs facts s).1.out.withinDegreeB bs.degreeBound = true
  · simp only [VerifiedPassS.guardDegree, hok, if_true]
    exact (ConstraintSystem.withinDegreeB_iff _ _).1 hok
  · simp only [VerifiedPassS.guardDegree, hok]
    exact h

theorem VerifiedPassS.andThen_respectsDeg {f g : VerifiedPassS p}
    (hf : RespectsDegS f) (hg : RespectsDegS g) : RespectsDegS (f.andThen g) := by
  intro cs bs facts s h
  exact hg _ bs facts _ (hf cs bs facts s h)

/-! ## Chaining and the store-threaded fixpoint -/

/-- The identity store pass: system unchanged, store unchanged, correct by reflexivity. -/
def VerifiedPassS.id : VerifiedPassS p :=
  fun cs bs _ s => (⟨cs, [], PassCorrect.refl cs bs⟩, s)

theorem VerifiedPassS.id_respectsDeg : RespectsDegS (VerifiedPassS.id (p := p)) :=
  fun _ _ _ _ h => h

/-- Fold a list of store passes into one sequential store pass (identity on `[]`). -/
def chainPassesS (l : List (VerifiedPassS p)) : VerifiedPassS p :=
  l.foldl VerifiedPassS.andThen VerifiedPassS.id

theorem foldl_andThenS_respectsDeg :
    ∀ (l : List (VerifiedPassS p)) (init : VerifiedPassS p),
      RespectsDegS init → (∀ f ∈ l, RespectsDegS f) →
      RespectsDegS (l.foldl VerifiedPassS.andThen init)
  | [], _, hinit, _ => by simpa using hinit
  | g :: rest, init, hinit, hall => by
      rw [List.foldl_cons]
      exact foldl_andThenS_respectsDeg rest (init.andThen g)
        (VerifiedPassS.andThen_respectsDeg hinit (hall g (List.mem_cons_self ..)))
        (fun f hf => hall f (List.mem_cons_of_mem _ hf))

theorem chainPassesS_respectsDeg {l : List (VerifiedPassS p)} (h : ∀ f ∈ l, RespectsDegS f) :
    RespectsDegS (chainPassesS l) := by
  unfold chainPassesS
  exact foldl_andThenS_respectsDeg _ _ VerifiedPassS.id_respectsDeg h

/-- Iterate a store pass to a fixpoint, threading the store, with **no** iteration budget — the exact
    recursion of `iterateToFixpoint`, on the same well-founded `sizeKey` measure (the store does not
    enter the measure). Correct by construction: each kept step is `PassCorrect`, derivations
    concatenate, and the stopping case returns the input system unchanged (keeping the store work,
    which is sound regardless of which system we keep). -/
def iterateToFixpointS (f : VerifiedPassS p) (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (s : FactStore p) : PassResult cs bs × FactStore p :=
  let r := f cs bs facts s
  if _h : r.1.out.sizeKey < cs.sizeKey then
    let r2 := iterateToFixpointS f r.1.out bs facts r.2
    (⟨r2.1.out, r.1.derivs ++ r2.1.derivs, r.1.correct.andThen r2.1.correct⟩, r2.2)
  else
    (⟨cs, [], PassCorrect.refl cs bs⟩, r.2)
  termination_by cs.sizeKey
  decreasing_by exact _h

theorem iterateToFixpointS_respectsDeg {f : VerifiedPassS p} (hf : RespectsDegS f) :
    RespectsDegS (iterateToFixpointS f) := by
  intro cs
  induction cs using sizeKey_wf.induction with
  | _ cs ih =>
    intro bs facts s hcs
    rw [iterateToFixpointS]
    split
    · rename_i h
      exact ih _ h bs facts _ (hf cs bs facts s hcs)
    · exact hcs
