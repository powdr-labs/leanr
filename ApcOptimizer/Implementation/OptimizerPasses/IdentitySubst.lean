import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Dense late identity-result substitution (runtime defs; proof in `Proofs/IdentitySubst.lean`)

The map is keyed by first occurrence in `d.busInteractions` list order — no sort or key
enumeration, plain hash-map point lookups. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The `VarId` of a bare-variable dense expression, else `none`. -/
def denseAsVar (e : DenseExpr p) : Option VarId :=
  match e with | .var v => some v | _ => none

/-- The operand `VarId` of an OR-identity `(op, o1, o2, r)`: the non-zero operand when the other is
    the constant `0` (so `r = o1 | o2` collapses to that operand). -/
def denseOrIdentityOperand (o1 o2 : DenseExpr p) : Option VarId :=
  if o2 = DenseExpr.const 0 then denseAsVar o1
  else if o1 = DenseExpr.const 0 then denseAsVar o2
  else none

/-- The `(result, operand)` pair of an OR-identity interaction decoding to `(orOp, o1, o2, result)`
    where one operand is `0` and the surviving operand is a bare variable distinct from the result. -/
def denseIdentityPairAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (VarId × VarId) :=
  match facts.byteXorSpec bi.busId with
  | some spec =>
    match spec.orOp with
    | some oop =>
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        match r with
        | .var rv =>
          if bi.multiplicity = DenseExpr.const 1 ∧ op = DenseExpr.const oop then
            match denseOrIdentityOperand o1 o2 with
            | some o1v => if rv = o1v then none else some (rv, o1v)
            | none => none
          else none
        | _ => none
      | none => none
    | none => none
  | none => none

/-- All recognised `(result, operand)` identity pairs in the system, computed once. -/
def denseIdentityPairs {bs : BusSemantics p} (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (VarId × VarId) :=
  d.busInteractions.filterMap (denseIdentityPairAt facts)

/-- First-wins key→value map of a pair list: the value stored for `y` is the first pair keyed `y`. -/
def denseFirstWins : List (VarId × VarId) → Std.HashMap VarId VarId → Std.HashMap VarId VarId
  | [], m => m
  | pr :: rest, m => denseFirstWins rest (if m.contains pr.1 then m else m.insert pr.1 pr.2)

/-- Resolve a mapped variable through operand→operand chains, fuel-bounded (a cycle burns fuel and
    stops harmlessly). -/
def denseResolveGo (m : Std.HashMap VarId VarId) : Nat → VarId → VarId
  | 0, v => v
  | fuel + 1, v =>
    match m[v]? with
    | some w => denseResolveGo m fuel w
    | none => v

/-- The mapped pairs, with the operand side path-compressed. -/
def denseIdentityMap {bs : BusSemantics p} (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    Std.HashMap VarId VarId :=
  denseFirstWins (denseIdentityPairs facts d) ∅

/-- The identity substitution over a prebuilt map: `result ↦ operand` (first per key), the operand
    resolved through chains (`denseResolveGo`). The map is a parameter (computed once by the pass
    body) to avoid re-evaluation per query by arity expansion. -/
def denseIdentityFm (m : Std.HashMap VarId VarId) (fuel : Nat) : VarId → Option (DenseExpr p) :=
  fun y => m[y]?.map (fun w => DenseExpr.var (denseResolveGo m fuel w))

/-- Recognizes OR-identity bus lookups asserting `r = x | 0` (one operand the constant `0`) and
    substitutes each such result by its surviving operand everywhere — e.g. `r = x | 0` becomes
    `r := x`. The empty-pairs branch returns the system untouched (no recognised identities, e.g.
    any OpenVM circuit whose bitwise bus declares no `orOp`). -/
def denseIdentitySubstF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  match denseIdentityPairs facts d with
  | [] => d
  | _ :: _ =>
    if (1 : ZMod p) ≠ 0 then
      -- Bind the map fully applied here; see `denseIdentityFm` (arity-expansion trap).
      let m := denseIdentityMap facts d
      d.substF (denseIdentityFm m m.size)
    else d

end ApcOptimizer.Dense
