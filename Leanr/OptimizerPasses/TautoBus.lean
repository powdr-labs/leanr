import Leanr.OptimizerPasses.ConstantFold

set_option autoImplicit false

/-! # Satisfied-constant-lookup (tautology) removal

Drops a *stateless* bus interaction whose evaluated message is the **same for every environment**
(multiplicity and all payload entries fold to constants) and provably satisfies the bus's table
(`violatesConstraint` probed once, on that constant message, returns `false`). Such an interaction
imposes no obligation on any assignment and contributes nothing to the (stateful-only) side
effects, so removing it is equivalence- and invariant-preserving.

Two subtleties are load-bearing:

* the **multiplicity must fold to a constant too**, not just the payload: `violatesConstraint`
  receives the full evaluated `BusInteraction` including its multiplicity, so a variable
  multiplicity would make the probed message differ from the runtime message;
* only **stateless** interactions qualify: a stateful one is observable in `sideEffects`
  regardless of its message.

This is generic in the bus semantics — the pass only *calls* `violatesConstraint` on one concrete
message (e.g. it removes an OpenVM PC-lookup row whose tuple became fully constant, and would
remove constant range checks that are in range). Field-free. -/

variable {p : ℕ}

/-! ## Constant messages -/

/-- The constant value of an expression, if its fold is a literal constant. -/
def Expression.constValue? (e : Expression p) : Option (ZMod p) :=
  match e.fold with
  | .const c => some c
  | _ => none

theorem Expression.constValue?_sound (e : Expression p) (c : ZMod p)
    (h : e.constValue? = some c) (env : String → ZMod p) : e.eval env = c := by
  unfold Expression.constValue? at h
  split at h
  · rename_i c' hfold
    simp only [Option.some.injEq] at h
    subst h
    rw [← e.fold_eval env, hfold]
    rfl
  · exact absurd h (by simp)

/-- Constant values of a list of expressions, all-or-nothing. -/
def constValues? : List (Expression p) → Option (List (ZMod p))
  | [] => some []
  | e :: rest =>
    match e.constValue?, constValues? rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

theorem constValues?_sound (es : List (Expression p)) (vs : List (ZMod p))
    (h : constValues? es = some vs) (env : String → ZMod p) :
    es.map (fun e => e.eval env) = vs := by
  induction es generalizing vs with
  | nil => simp only [constValues?, Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    rw [constValues?] at h
    cases hv : e.constValue? with
    | none => rw [hv] at h; exact absurd h (by simp)
    | some v =>
      cases hvs : constValues? rest with
      | none => rw [hv, hvs] at h; exact absurd h (by simp)
      | some vs' =>
        rw [hv, hvs] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [Expression.constValue?_sound e v hv env, ih vs' hvs]

/-- The evaluated message of a bus interaction, if it is the same under every environment. -/
def BusInteraction.constMessage? (bi : BusInteraction (Expression p)) :
    Option (BusInteraction (ZMod p)) :=
  match bi.multiplicity.constValue?, constValues? bi.payload with
  | some m, some vs => some { busId := bi.busId, multiplicity := m, payload := vs }
  | _, _ => none

theorem BusInteraction.constMessage?_sound (bi : BusInteraction (Expression p))
    (msg : BusInteraction (ZMod p)) (h : bi.constMessage? = some msg)
    (env : String → ZMod p) : bi.eval env = msg := by
  unfold BusInteraction.constMessage? at h
  cases hm : bi.multiplicity.constValue? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
    cases hvs : constValues? bi.payload with
    | none => rw [hm, hvs] at h; exact absurd h (by simp)
    | some vs =>
      rw [hm, hvs] at h
      simp only [Option.some.injEq] at h
      subst h
      simp [BusInteraction.eval, bi.multiplicity.constValue?_sound m hm env,
            constValues?_sound bi.payload vs hvs env]

/-! ## The correctness core: dropping universally-satisfied stateless interactions -/

/-- Dropping interactions only from buses with no declared memory discipline preserves the
    memory discipline: every declared bus's message list is untouched. -/
theorem ConstraintSystem.memoryDiscipline_filterBus_undeclared (cs : ConstraintSystem p)
    (bs : BusSemantics p) (keep : BusInteraction (Expression p) → Bool)
    (a : String → ZMod p)
    (hundecl : ∀ bi ∈ cs.busInteractions, keep bi = false → bs.memoryBus bi.busId = none) :
    ((cs.filterBus keep).memoryDiscipline bs a ↔ cs.memoryDiscipline bs a) := by
  unfold ConstraintSystem.memoryDiscipline
  have hmsgs : ∀ (busId : Nat) (shape : MemoryBusShape), bs.memoryBus busId = some shape →
      ∀ (l : List (BusInteraction (Expression p))),
        (∀ bi ∈ l, keep bi = false → bs.memoryBus bi.busId = none) →
        (l.filter keep).filter (fun bi => bi.busId = busId)
          = l.filter (fun bi => bi.busId = busId) := by
    intro busId shape hdecl l hl
    induction l with
    | nil => rfl
    | cons bi rest ih =>
      have hrest := ih (fun bi' hbi' hk' => hl bi' (List.mem_cons_of_mem _ hbi') hk')
      by_cases hb : bi.busId = busId
      · have hkeep : keep bi = true := by
          by_contra hk
          have := hl bi (List.mem_cons_self ..) (by simpa using hk)
          rw [hb, hdecl] at this
          exact absurd this (by simp)
        rw [List.filter_cons_of_pos hkeep,
            List.filter_cons_of_pos (by simpa using hb),
            List.filter_cons_of_pos (by simpa using hb), hrest]
      · by_cases hk : keep bi = true
        · rw [List.filter_cons_of_pos hk,
              List.filter_cons_of_neg (by simpa using hb),
              List.filter_cons_of_neg (by simpa using hb), hrest]
        · rw [List.filter_cons_of_neg (by simpa using hk),
              List.filter_cons_of_neg (by simpa using hb), hrest]
  constructor
  · intro h busId shape hdecl
    have hd := h busId shape hdecl
    simp only [ConstraintSystem.filterBus] at hd
    rwa [hmsgs busId shape hdecl cs.busInteractions hundecl] at hd
  · intro h busId shape hdecl
    simp only [ConstraintSystem.filterBus]
    rw [hmsgs busId shape hdecl cs.busInteractions hundecl]
    exact h busId shape hdecl

/-- Dropping bus interactions that are (a) stateless, (b) on buses without memory discipline,
    and (c) never violating a constraint is equivalence- and invariant-preserving: their
    `violatesConstraint` obligation holds under every assignment, and stateless interactions
    never enter `sideEffects` (which here stay *equal*, not just `≈`). -/
theorem ConstraintSystem.filterBusStateless_correct (cs : ConstraintSystem p)
    (bs : BusSemantics p) (keep : BusInteraction (Expression p) → Bool)
    (hstateless : ∀ bi ∈ cs.busInteractions, keep bi = false →
      bs.isStateful bi.busId = false)
    (hundecl : ∀ bi ∈ cs.busInteractions, keep bi = false → bs.memoryBus bi.busId = none)
    (hok : ∀ bi ∈ cs.busInteractions, keep bi = false → ∀ env,
      bs.violatesConstraint (bi.eval env) = false) :
    PassCorrect cs (cs.filterBus keep) bs := by
  have hiff : ∀ env, (cs.filterBus keep).satisfies bs env ↔ cs.satisfies bs env := by
    intro env
    have hdisc := cs.memoryDiscipline_filterBus_undeclared bs keep env hundecl
    simp only [ConstraintSystem.satisfies]
    constructor
    · rintro ⟨hc, hb, hd⟩
      refine ⟨hc, fun bi hbimem => ?_, hdisc.1 hd⟩
      by_cases hk : keep bi = true
      · exact hb bi (List.mem_filter.2 ⟨hbimem, hk⟩)
      · intro _; exact hok bi hbimem (by simpa using hk) env
    · rintro ⟨hc, hb, hd⟩
      exact ⟨hc, fun bi hbimem => hb bi (List.mem_filter.1 hbimem).1, hdisc.2 hd⟩
  have hfilter : ∀ (bis : List (BusInteraction (Expression p))),
      (∀ bi ∈ bis, keep bi = false → bs.isStateful bi.busId = false) →
      (bis.filter keep).filter (fun bi => bs.isStateful bi.busId)
        = bis.filter (fun bi => bs.isStateful bi.busId) := by
    intro bis
    induction bis with
    | nil => intro _; rfl
    | cons bi rest ih =>
      intro hall
      have hrest := ih (fun b hb hkf => hall b (List.mem_cons_of_mem _ hb) hkf)
      by_cases hk : keep bi = true
      · rw [List.filter_cons_of_pos hk]
        by_cases hst : bs.isStateful bi.busId = true
        · rw [List.filter_cons_of_pos (by simpa using hst),
              List.filter_cons_of_pos (by simpa using hst), hrest]
        · rw [List.filter_cons_of_neg (by simpa using hst),
              List.filter_cons_of_neg (by simpa using hst), hrest]
      · have hst : bs.isStateful bi.busId = false :=
          hall bi (List.mem_cons_self ..) (by simpa using hk)
        rw [List.filter_cons_of_neg hk,
            List.filter_cons_of_neg (by simp [hst]), hrest]
  have hside : ∀ env, (cs.filterBus keep).sideEffects bs env = cs.sideEffects bs env := by
    intro env
    simp only [ConstraintSystem.sideEffects, ConstraintSystem.filterBus]
    rw [hfilter cs.busInteractions hstateless]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro env hsat
    exact ⟨env, (hiff env).1 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro env hsat
    exact ⟨env, (hiff env).2 hsat, by rw [hside]; exact BusState.equiv_refl _⟩
  · intro hinv env hsat bi hbi
    have hbimem : bi ∈ cs.busInteractions :=
      (List.mem_filter.1 (by simpa only [ConstraintSystem.filterBus] using hbi)).1
    exact hinv env ((hiff env).1 hsat) bi hbimem

/-! ## The pass -/

/-- Is this interaction a tautology: stateless, with a constant message the bus accepts? -/
def isTautoLookup (bs : BusSemantics p) (bi : BusInteraction (Expression p)) : Bool :=
  !bs.isStateful bi.busId && (bs.memoryBus bi.busId).isNone &&
    (match bi.constMessage? with
     | some msg => !bs.violatesConstraint msg
     | none => false)

/-- The tautology-lookup removal pass: drop stateless interactions whose constant message is
    accepted by the bus's table. -/
def tautoBusDropPass : VerifiedPass p := fun cs bs =>
  ⟨cs.filterBus (fun bi => !isTautoLookup bs bi),
   cs.filterBusStateless_correct bs _
     (by
       intro bi _ hkf
       have htauto : isTautoLookup bs bi = true := by simpa using hkf
       rw [isTautoLookup, Bool.and_eq_true, Bool.and_eq_true] at htauto
       simpa using htauto.1.1)
     (by
       intro bi _ hkf
       have htauto : isTautoLookup bs bi = true := by simpa using hkf
       rw [isTautoLookup, Bool.and_eq_true, Bool.and_eq_true] at htauto
       simpa [Option.isNone_iff_eq_none] using htauto.1.2)
     (by
       intro bi _ hkf env
       have htauto : isTautoLookup bs bi = true := by simpa using hkf
       rw [isTautoLookup, Bool.and_eq_true, Bool.and_eq_true] at htauto
       have hmsg := htauto.2
       cases hcm : bi.constMessage? with
       | none => rw [hcm] at hmsg; exact absurd hmsg (by simp)
       | some msg =>
         rw [hcm] at hmsg
         rw [bi.constMessage?_sound msg hcm env]
         simpa using hmsg)⟩
