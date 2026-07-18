import ApcOptimizer.Implementation.Dense.Rewrite
import ApcOptimizer.Implementation.Dense.Adapter
import ApcOptimizer.Implementation.OptimizerPasses.ZeroMultBus
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus

set_option autoImplicit false

/-! # Dense drop passes (Task 3): trivial-constraint and zero-multiplicity-bus removal

Two dense filter passes built with `ofTransform`, inheriting their spec `PassCorrect`. The keep
predicates decode identically (`fold`/`isConstZero` commute with decode), so the dense filter
decodes to the spec filter. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `!c.fold.isConstZero` decodes correctly (folding then the const-zero test commute with decode). -/
theorem VarRegistry.notConstZeroFold_decode (reg : VarRegistry) (c : DenseExpr p) :
    (!(c.fold.isConstZero)) = (!((reg.decodeExpr c).fold.isConstZero)) := by
  rw [← reg.decodeExpr_isConstZero c.fold, reg.decodeExpr_fold]

/-- Dense trivial-constraint removal: drop every algebraic constraint whose fold is literal `0`. -/
def denseTrivialConstraintDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofTransform
    (fun _ d => d.filterConstraints (fun c => !c.fold.isConstZero))
    trivialConstraintDropPass.withFacts
    (fun _ _ _ hc => DenseConstraintSystem.filterConstraints_covered hc)
    (fun reg _ _ d _ =>
      reg.decodeCS_filterConstraints (sk := fun c => !c.fold.isConstZero) d
        (fun c _ => reg.notConstZeroFold_decode c))
    (fun _ _ _ => rfl)

/-- Dense zero-multiplicity-bus removal: drop bus interactions whose multiplicity folds to `0`
    (identity in the degenerate `1 = 0` ring, matching the spec pass). -/
def denseZeroMultBusDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofTransform
    (fun _ d =>
      if (1 : ZMod p) = 0 then d
      else d.filterBus (fun bi => !bi.multiplicity.fold.isConstZero))
    zeroMultBusDropPass.withFacts
    (fun _ _ _ hc => by
      by_cases hp1 : (1 : ZMod p) = 0
      · simpa [hp1] using hc
      · simpa [hp1] using DenseConstraintSystem.filterBus_covered hc)
    (fun reg bs facts d _ => by
      by_cases hp1 : (1 : ZMod p) = 0
      · show reg.decodeCS (if (1 : ZMod p) = 0 then d else _)
          = (zeroMultBusDropPass.withFacts (reg.decodeCS d) bs facts).out
        rw [if_pos hp1]
        simp only [VerifiedPass.withFacts, zeroMultBusDropPass, dif_pos hp1]
      · show reg.decodeCS (if (1 : ZMod p) = 0 then d
            else d.filterBus (fun bi => !bi.multiplicity.fold.isConstZero))
          = (zeroMultBusDropPass.withFacts (reg.decodeCS d) bs facts).out
        rw [if_neg hp1,
          reg.decodeCS_filterBus (sk := fun bi => !bi.multiplicity.fold.isConstZero) d
            (fun bi _ => reg.notConstZeroFold_decode bi.multiplicity)]
        simp only [VerifiedPass.withFacts, zeroMultBusDropPass, dif_neg hp1])
    (fun _ _ _ => by simp only [VerifiedPass.withFacts, zeroMultBusDropPass]; split <;> rfl)

/-! ## Tautology-lookup removal (dense) -/

/-- Constant value of a dense expression (fold then require a literal). -/
def DenseExpr.constValue? (e : DenseExpr p) : Option (ZMod p) :=
  match e.fold with
  | .const c => some c
  | _ => none

/-- Constant values of a dense payload list. -/
def denseConstValues? : List (DenseExpr p) → Option (List (ZMod p))
  | [] => some []
  | e :: rest =>
    match e.constValue?, denseConstValues? rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Constant message of a dense bus interaction, if fully constant. -/
def denseConstMessage? (bi : BusInteraction (DenseExpr p)) : Option (BusInteraction (ZMod p)) :=
  match bi.multiplicity.constValue?, denseConstValues? bi.payload with
  | some m, some vs => some { busId := bi.busId, multiplicity := m, payload := vs }
  | _, _ => none

/-- Is this dense interaction a tautology: stateless, with a constant message the bus accepts? -/
def denseIsTautoLookup (bs : BusSemantics p) (bi : BusInteraction (DenseExpr p)) : Bool :=
  !bs.isStateful bi.busId &&
    (match denseConstMessage? bi with
     | some msg => !bs.violatesConstraint msg
     | none => false)

theorem VarRegistry.decodeExpr_constValue? (reg : VarRegistry) (e : DenseExpr p) :
    (reg.decodeExpr e).constValue? = e.constValue? := by
  have h := reg.decodeExpr_fold e
  simp only [Expression.constValue?, DenseExpr.constValue?, ← h]
  cases e.fold <;> rfl

@[simp] theorem VarRegistry.decodeBI_busId (reg : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    (reg.decodeBI bi).busId = bi.busId := rfl

theorem VarRegistry.constValues_decode (reg : VarRegistry) (l : List (DenseExpr p)) :
    constValues? (l.map reg.decodeExpr) = denseConstValues? l := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map_cons, constValues?, denseConstValues?, reg.decodeExpr_constValue?, ih]
      cases e.constValue? <;> cases denseConstValues? rest <;> rfl

theorem VarRegistry.decodeBI_constMessage? (reg : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    (reg.decodeBI bi).constMessage? = denseConstMessage? bi := by
  simp only [BusInteraction.constMessage?, denseConstMessage?, VarRegistry.decodeBI,
    reg.decodeExpr_constValue?, reg.constValues_decode]
  cases bi.multiplicity.constValue? <;> cases denseConstValues? bi.payload <;> rfl

theorem VarRegistry.isTautoLookup_decode (reg : VarRegistry) (bs : BusSemantics p)
    (bi : BusInteraction (DenseExpr p)) :
    isTautoLookup bs (reg.decodeBI bi) = denseIsTautoLookup bs bi := by
  simp only [isTautoLookup, denseIsTautoLookup, reg.decodeBI_constMessage?,
    VarRegistry.decodeBI_busId]
  cases denseConstMessage? bi <;> rfl

/-- Dense tautology-lookup removal: drop stateless interactions with an accepted constant message. -/
def denseTautoBusDropPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofTransform
    (fun bs d => d.filterBus (fun bi => !denseIsTautoLookup bs bi))
    tautoBusDropPass.withFacts
    (fun _ _ _ hc => DenseConstraintSystem.filterBus_covered hc)
    (fun reg bs _ d _ =>
      reg.decodeCS_filterBus (sk := fun bi => !isTautoLookup bs bi) d
        (fun bi _ => by simp only [reg.isTautoLookup_decode bs bi]))
    (fun _ _ _ => rfl)

end ApcOptimizer.Dense
