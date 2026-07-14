import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.FlagFold

set_option autoImplicit false

/-! # Subsumed range-check removal (idea 4(c))

After unification and packing, blocks keep a variable range check `[x, w]` on the variable range
checker whose bound `2^w` is *already implied* by a **stronger or equal** stateless check retained
elsewhere in the system: most commonly the same `x` also sits in a tuple-range slot (e.g.
`mem_ptr_limbs__1` is checked `< 8192` by a `[x, 13]` range check *and* carried in a
`TupleRangeChecker[256, 8192]` slot 1), or is a byte-guaranteed memory-receive limb. Such a
range check is *entailed* — every assignment satisfying the rest of the system already forces
`x` into range — so dropping it is sound, variable-neutral, and removes one bus interaction.

The drop reuses two proven ingredients, exactly as `RedundantByteDrop`:

1. `ConstraintSystem.filterBusEntailed_correct` — a stateless interaction may be dropped when it
   is accepted under *every assignment satisfying the filtered system*.
2. A **non-circular justification base**: the checked variable's bound is looked up only among the
   interactions this pass can never drop (those *not* recognized as single-variable range checks),
   via the proven `findVarBound` (`slotBound`-derived bounds: tuple slots, byte-limb memory
   receives, and any retained range check). Otherwise two range checks of equal width on the same
   variable could each justify the other and both would be dropped unsoundly.

A recognized check `[x, w]` is dropped when the base bounds `x` by some `b' ≤ 2^w`: the retained
source forces `x.val < b' ≤ 2^w`, and `w ≤ 25` (a wider check always violates and is never
recognized), so the message `[x, w]` is accepted. No new `BusFacts`; the bound comparison is a
plain `Nat` `≤`, so the direction is exactly "the retained check is at least as strong".

Runs in the cleanup cycle (a bus win, `filterBus`-based, variable-neutral); the fixpoint reruns
it after each shrink. -/

namespace SubsumedRange

variable {p : ℕ}

/-- Recognize a single-variable range check `[x, width]` (multiplicity `1`) on a `varRangeBus`
    bus whose width is a *satisfiable* constant (`width.val ≤ 25`), returning the checked variable
    and the width constant. A width `> 25` check always violates, so dropping it would be unsound;
    it is deliberately not recognized. -/
def rangeCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Variable × ZMod p) :=
  match bi.payload with
  | [v, c] =>
    match v with
    | Expression.var x =>
      match c.constValue? with
      | some cv =>
        if facts.varRangeBus bi.busId = true ∧ bi.multiplicity = Expression.const 1
            ∧ cv.val ≤ 25 then some (x, cv) else none
      | none => none
    | _ => none
  | _ => none

/-- Structure of a recognized check: it lives on a `varRangeBus`, has multiplicity `1`, a
    satisfiable width, and payload `[x, c]` with `c` the constant `cv`. -/
theorem rangeCheck?_spec (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (cv : ZMod p)
    (h : rangeCheck? bs facts bi = some (x, cv)) :
    facts.varRangeBus bi.busId = true ∧ bi.multiplicity = Expression.const 1 ∧ cv.val ≤ 25 ∧
      ∃ c, bi.payload = [Expression.var x, c] ∧ c.constValue? = some cv := by
  unfold rangeCheck? at h
  split at h
  case h_2 => exact absurd h (by simp)
  case h_1 v c hpay =>
    split at h
    case h_2 => exact absurd h (by simp)
    case h_1 x' hv =>
      split at h
      case h_2 => exact absurd h (by simp)
      case h_1 cv' hcv =>
        split_ifs at h with hcond
        obtain ⟨hvr, hm, hle⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hvr, hm, hle, c, hpay, hcv⟩

/-- A recognized range check lives on a stateless bus. -/
theorem rangeCheck?_stateless (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (cv : ZMod p)
    (h : rangeCheck? bs facts bi = some (x, cv)) : bs.isStateful bi.busId = false :=
  (facts.varRangeBus_sound bi.busId (rangeCheck?_spec bs facts bi x cv h).1).1

/-- If the checked variable is in range (`< 2^width`), the recognized message is accepted. -/
theorem rangeCheck?_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x : Variable) (cv : ZMod p)
    (h : rangeCheck? bs facts bi = some (x, cv)) (env : Variable → ZMod p)
    (hlt : (env x).val < 2 ^ cv.val) : bs.violatesConstraint (bi.eval env) = false := by
  obtain ⟨hvr, hm, hle, c, hpay, hcv⟩ := rangeCheck?_spec bs facts bi x cv h
  have hev : bi.eval env = { busId := bi.busId, multiplicity := 1, payload := [env x, cv] } := by
    unfold BusInteraction.eval
    rw [hm, hpay]
    simp only [List.map_cons, List.map_nil, Expression.eval, c.constValue?_sound cv hcv env]
  rw [hev]
  exact ((facts.varRangeBus_sound bi.busId hvr).2 (env x) cv 1).2 ⟨hle, hlt⟩

/-! ## The pass -/

/-- The justification base: interactions this pass can never drop (not recognized as
    single-variable range checks). Bounding variables only against these makes the drop
    non-circular. -/
def dropBase (bs : BusSemantics p) (facts : BusFacts p bs) (cs : ConstraintSystem p) :
    List (BusInteraction (Expression p)) :=
  cs.busInteractions.filter (fun bi => (rangeCheck? bs facts bi).isNone)

/-- Keep `bi` unless it is a recognized range check `[x, w]` whose variable is already bounded
    `< 2^w` by a retained (base) interaction. -/
def dropKeep (bs : BusSemantics p) (facts : BusFacts p bs)
    (base : List (BusInteraction (Expression p))) (bi : BusInteraction (Expression p)) : Bool :=
  match rangeCheck? bs facts bi with
  | some (x, cv) =>
    match findVarBound bs facts base x with
    | some b' => !decide (b' ≤ 2 ^ cv.val)
    | none => true
  | none => true

/-- Drop every variable range check whose bound is already entailed by a stronger-or-equal
    retained stateless check on the same variable. -/
def subsumedRangeDropPass : VerifiedPassW p := fun cs bs facts =>
  ⟨cs.filterBus (dropKeep bs facts (dropBase bs facts cs)), [],
   cs.filterBusEntailed_correct bs _
     (by
       intro bi _ hkf
       cases hr : rangeCheck? bs facts bi with
       | none => exact absurd hkf (by simp [dropKeep, hr])
       | some xcv =>
         obtain ⟨x, cv⟩ := xcv
         exact rangeCheck?_stateless bs facts bi x cv hr)
     (by
       intro bi hbimem hkf env hsat _
       cases hr : rangeCheck? bs facts bi with
       | none => exact absurd hkf (by simp [dropKeep, hr])
       | some xcv =>
         obtain ⟨x, cv⟩ := xcv
         cases hb : findVarBound bs facts (dropBase bs facts cs) x with
         | none => exact absurd hkf (by simp [dropKeep, hr, hb])
         | some b' =>
           -- `hkf` reduces to the bound comparison
           have hble : b' ≤ 2 ^ cv.val := by
             simp only [dropKeep, hr, hb, Bool.not_eq_false', decide_eq_true_eq] at hkf
             exact hkf
           -- every base interaction survives the filter, so `hsat` accepts it
           have hbase : (env x).val < b' := by
             refine findVarBound_sound bs facts (dropBase bs facts cs) x b' hb env
               (fun bi' hbi' hmult => ?_)
             have hbimem' : bi' ∈ cs.busInteractions := (List.mem_filter.1 hbi').1
             have hnone : rangeCheck? bs facts bi' = none := by
               have := (List.mem_filter.1 hbi').2
               simpa using this
             have hkeep : dropKeep bs facts (dropBase bs facts cs) bi' = true := by
               simp only [dropKeep, hnone]
             exact hsat.2 bi' (List.mem_filter.2 ⟨hbimem', hkeep⟩) hmult
           exact rangeCheck?_accepted bs facts bi x cv hr env (lt_of_lt_of_le hbase hble))⟩

end SubsumedRange
