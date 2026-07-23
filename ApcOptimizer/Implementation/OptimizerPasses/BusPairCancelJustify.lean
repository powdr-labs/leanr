import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.ListSplit
import ApcOptimizer.Implementation.OptimizerPasses.SearchBudgets

set_option autoImplicit false

/-! # Dense byte-justification certificates for `busPairCancel`

Runtime-only certificates for deciding whether an expression is provably a byte (`< 256`) or
otherwise bounded, used by the byte-justified drops. A leaf file — definitions only, no soundness
lemma (that lives in `Proofs/BusPairCancelJustify.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The expression's single distinct variable: `some (some v)` when exactly `v` occurs, `some none`
    when no variable occurs, `none` when several distinct variables occur. -/
def DenseExpr.singleVarAux : DenseExpr p → Option (Option VarId)
  | .const _ => some none
  | .var y => some (some y)
  | .add a b | .mul a b =>
    match a.singleVarAux, b.singleVarAux with
    | some none, r => r
    | r, some none => r
    | some (some u), some (some v) => if u == v then some (some u) else none
    | _, _ => none

/-- Is the expression a single-variable expression (exactly one distinct variable)? -/
def DenseExpr.isSingleVar (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some _) => true
  | _ => false

/-- Per-point core of the deep justification: with the `keys` of `c` pinned by `pt`, the substituted
    and folded constraint must be linear and, once normalized, either pin `x` to a re-checked byte
    constant or equate it to a variable in the precomputed `byteVars`. -/
def densePointByteOk (x : VarId) (c : DenseExpr p) (byteVars : List VarId)
    (keys : List VarId) (pt : List (VarId × ZMod p)) : Bool :=
  match denseLinearize ((c.substF (fun v =>
      if keys.contains v then some (.const (denseEnvOfFast pt v)) else none)).fold) with
  | none => false
  | some l =>
    let ln := DenseLinExpr.norm l
    match ln.terms with
    | [(v, a)] =>
      decide (v = x) && decide (a ≠ 0) &&
        decide (a * (-(a⁻¹ * ln.const)) + ln.const = 0) &&
        decide ((-(a⁻¹ * ln.const) : ZMod p).val < 256)
    | [(v1, a1), (v2, a2)] =>
      decide (ln.const = 0) &&
      (if v1 = x then
        decide (a2 = -a1) && decide (a1 ≠ 0) && byteVars.contains v2
       else if v2 = x then
        decide (a1 = -a2) && decide (a2 ≠ 0) && byteVars.contains v1
       else false)
    | _ => false

/-- The variables of `c` (other than `x`) with a proven byte bound from the remaining interactions —
    computed once per candidate, not once per enumeration point. -/
def denseDeepByteVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) (c : DenseExpr p) :
    List VarId :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filter (fun v =>
    match denseFindVarBound bs facts (wits v) v with
    | some b => decide (b ≤ 256)
    | none => false)

/-- The variables of `c` other than `x` that carry a small proven *constraint-derived* finite domain
    (selector flags) — the candidates for enumeration in the deep justification. -/
def denseDeepEnumDoms (domCs : List (DenseExpr p)) (x : VarId) (c : DenseExpr p) :
    List (VarId × List (ZMod p)) :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filterMap (fun v =>
    match denseFindDomainAlg domCs v with
    | some d => if d.length ≤ maxDeepDomain then some (v, d) else none
    | none => none)

/-- Deep byte bound for `x` from one constraint `c`: enumerate the small proven finite domains of
    `c`'s other variables (e.g. one-hot selector flags) and require `densePointByteOk` at every
    point. -/
def denseDeepBoundOk (domCs : List (DenseExpr p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) (c : DenseExpr p) :
    Bool :=
  let enum := denseDeepEnumDoms domCs x c
  if (c.vars.dedup.filter (fun v => v ≠ x)).length ≤ maxDeepVars &&
      (enum.map (fun vd => vd.2.length)).prod ≤ maxDeepPoints then
    (denseAssignments enum).all
      (densePointByteOk x c (denseDeepByteVars bs facts wits x c) (enum.map Prod.fst))
  else false

/-- Deep byte justification for `x`: one of the first `maxDeepConstraints` constraints mentioning `x`
    (the caller passes them as `cands`) pins it via `denseDeepBoundOk`. -/
def denseDeepByteJustified (domCs cands : List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) : Bool :=
  (cands.take maxDeepConstraints).any (fun c => denseDeepBoundOk domCs bs facts wits x c)

/-- Evaluate the single-variable expression `e` with its variable fixed to `d` and check the result
    is a byte constant. -/
def denseExprPointByte (e : DenseExpr p) (x : VarId) (d : ZMod p) : Bool :=
  match (e.substF (fun v => if v = x then some (.const d) else none)).fold.constValue? with
  | some c => decide (c.val < 256)
  | none => false

/-- Is `e` a byte because its single variable `x` ranges over a small constraint-derived finite
    domain at every point of which `e` evaluates to a byte? -/
def denseDomainByteJustified (domCs : List (DenseExpr p)) (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some x) =>
    match denseFindDomainAlg domCs x with
    | some d => decide (d.length ≤ maxDeepDomain) && d.all (denseExprPointByte e x)
    | none => false
  | _ => false

/-- Natural upper bound of a term list `Σ cᵥ·v` under per-variable value bounds `bnd` (`bnd v`
    bounds `(denv v).val` strictly): `Σ cᵥ.val·(bnd v − 1)`; `none` if any variable is unbounded. -/
def denseLinTermsNatBound (bnd : VarId → Option Nat) : List (VarId × ZMod p) → Option Nat
  | [] => some 0
  | (v, c) :: rest =>
    match bnd v, denseLinTermsNatBound bnd rest with
    | some b, some acc => some (c.val * (b - 1) + acc)
    | _, _ => none

/-- Natural upper bound of `L.eval`: `L.const.val + Σ cᵥ.val·(bnd v − 1)`. -/
def DenseLinExpr.natBound (bnd : VarId → Option Nat) (L : DenseLinExpr p) : Option Nat :=
  (denseLinTermsNatBound bnd L.terms).map (fun s => L.const.val + s)

/-- Affine byte/limb justification: `e` linearizes to a form whose per-variable-bounded natural
    value is `< bound` (and `< p`, so it does not wrap). -/
def denseAffineJustified (bound : Nat) (bnd : VarId → Option Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L =>
    match L.natBound bnd with
    | some M => decide (M < bound) && decide (M < p)
    | none => false
  | none => false

/-! ## Basis justification -/

/-- The linearized (merged) form and bound of payload slot `i` of `bi`, when the multiplicity is
    a nonzero constant and the slot carries a `slotBound`. -/
def denseFormBoundAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : Nat) : Option (DenseLinExpr p × Nat) :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match bi.payload[i]?,
            facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
      | some e, some B =>
        match denseLinearize e with
        | some L => some (L.norm, B)
        | none => none
      | _, _ => none

/-- Fuel-bounded basis reduction: is `L`'s value provably `< bound − used` via per-variable bounds
    (finish arm) after subtracting integer multiples of range-checked slot forms from `fwits`? -/
def denseBasisReduceGo (bound : Nat) (bnd : VarId → Option Nat) {bs : BusSemantics p}
    (facts : BusFacts p bs) (fwits : VarId → List (BusInteraction (DenseExpr p))) :
    Nat → Nat → DenseLinExpr p → Bool
  | 0, _, _ => false
  | fuel + 1, used, L =>
    (match L.natBound bnd with
     | some M => decide (used + M < bound) && decide (used + M < p)
     | none => false) ||
    (L.terms.map Prod.fst).any (fun v =>
      (fwits v).any (fun bi =>
        (List.range bi.payload.length).any (fun i =>
          match denseFormBoundAt facts bi i with
          | none => false
          | some (Lf, Bf) =>
            let cF := IntervalForce.srep (Lf.coeff v)
            let μi := IntervalForce.srep (L.coeff v) / cF
            if cF ≠ 0 ∧ 0 < μi ∧ cF * μi = IntervalForce.srep (L.coeff v) then
              denseBasisReduceGo bound bnd facts fwits fuel (used + μi.toNat * (Bf - 1))
                ((L.add (Lf.scale (-(μi.toNat : ZMod p)))).norm)
            else false)))

/-- Basis justification: `e` linearizes to a form the fuel-bounded reduction proves `< bound`. -/
def denseBasisJustified (bound : Nat) (bnd : VarId → Option Nat) {bs : BusSemantics p}
    (facts : BusFacts p bs) (fwits : VarId → List (BusInteraction (DenseExpr p)))
    (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L => denseBasisReduceGo bound bnd facts fwits basisFuel 0 L.norm
  | none => false

/-! ## Bitwise-lookup AND/OR-output justification -/

/-- The form `2·x + r − o1 − o2`, whose vanishing witnesses `2·x = o1 + o2 − r` (`x = o1 & o2`). -/
def denseXorAndForm (x : VarId) (o1 o2 r : DenseExpr p) : DenseExpr p :=
  .add (.mul (.const 2) (.var x))
    (.add r (.add (.mul (.const (-1)) o1) (.mul (.const (-1)) o2)))

/-- The form `2·x − r − o1 − o2`, whose vanishing witnesses `2·x = o1 + o2 + r` (`x = o1 | o2`). -/
def denseXorOrForm (x : VarId) (o1 o2 r : DenseExpr p) : DenseExpr p :=
  .add (.mul (.const 2) (.var x))
    (.add (.mul (.const (-1)) r) (.add (.mul (.const (-1)) o1) (.mul (.const (-1)) o2)))

/-- Does a dense expression linearize to the zero form (`= 0` under every assignment)? -/
def denseLinIsZero (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L => decide ((DenseLinExpr.norm L).const = 0) && (DenseLinExpr.norm L).terms.isEmpty
  | none => false

/-- Does one surviving interaction pin `x` as the AND (or, when `allowOr`, OR) output of a
    byte-forced XOR pair? On a `byteXorSpec` bus (byte bound `≤ 256`), an active (nonzero constant
    multiplicity) message decoding to `(op, o1, o2, r)` with `op = xorOp` forces `o1, o2 ∈ [0,256)`
    and `r = o1 ⊕ o2`; if the result slot additionally obeys `r = o1 + o2 − 2·x` (then `x = o1 & o2`)
    or, when `allowOr`, `r = 2·x − o1 − o2` (then `x = o1 | o2`), then `x ∈ [0,256)` under every
    assignment satisfying the interaction. E.g. the surviving XOR `[b, c, -2·x + b + c, 1]` pins the
    AND output `x < 256`. The OR arm is gated by `allowOr` because it is only enabled where it is
    variable-safe (see the dispatcher). Soundness in `Proofs/BusPairCancelJustify.lean`. -/
def denseXorAndByteWit (allowOr : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (x : VarId) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match facts.byteXorSpec bi.busId with
  | none => false
  | some spec =>
    decide (spec.bound ≤ 256) &&
    (match bi.multiplicity.constValue? with
     | some mv => decide (mv ≠ 0)
     | none => false) &&
    (match spec.decode bi.payload with
     | some (op, o1, o2, r) =>
       decide (op = (.const spec.xorOp : DenseExpr p)) &&
       (denseLinIsZero (denseXorAndForm x o1 o2 r) ||
         (allowOr && denseLinIsZero (denseXorOrForm x o1 o2 r)))
     | none => false)

/-- Is `x` byte-justified by some surviving XOR interaction in `wl` (`denseXorAndByteWit`)? -/
def denseXorAndByteJustified (allowOr : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (x : VarId) (wl : List (BusInteraction (DenseExpr p))) : Bool :=
  wl.any (denseXorAndByteWit allowOr bs facts x)

/-- Is `e` provably a byte under every assignment satisfying the remaining system? Tries, in order:
    a constant `< bound`; a variable with a bus-fact bound `≤ bound`; (when `deep`) a
    selector-flag-domain deep justification, or a bitwise-lookup AND/OR-output justification
    (`denseXorAndByteWit`), or a single-variable finite-domain justification; an affine recomposition
    of bounded limbs; or a basis reduction against range-checked slot forms (`fwits`). Remaining
    interactions are consulted through `wits`; `domCs`/`candsOf` are precomputed by the caller. The
    AND/OR arm allows the OR form only via `wits` (never `fwits`): the memory-limb XOR that would
    unlock it in the pair-cancel caller is a `fwits` form-witness, and enabling OR there perturbs the
    memory-ordering gadgets into a variable regression, so it is kept to the variable-safe AND form. -/
def denseByteJustifiedW (bound : Nat) (deep : Bool) (domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (e : DenseExpr p) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < bound)
  | none =>
    (match e with
     | .var x =>
       (match denseFindVarBound bs facts (wits x) x with
        | some b => decide (b ≤ bound)
        | none => false) ||
       (deep && decide (256 ≤ bound) &&
         denseDeepByteJustified domCs (candsOf x) bs facts wits x) ||
       (deep && decide (256 ≤ bound) &&
         (denseXorAndByteJustified true bs facts x (wits x) ||
           denseXorAndByteJustified false bs facts x (fwits x)))
     | _ => false) ||
    (deep && decide (256 ≤ bound) && denseDomainByteJustified domCs e) ||
    denseAffineJustified bound (fun x => denseFindVarBound bs facts (wits x) x) e ||
    denseBasisJustified bound (fun x => denseFindVarBound bs facts (wits x) x) facts fwits e

/-- The plain full-scan form (used by the coda's `RedundantByteDrop`): naive per-query filters, with
    the basis arm disabled (`fwits = []`). -/
def denseByteJustified (bound : Nat) (deep : Bool) (all : List (DenseExpr p))
    (bs : BusSemantics p) (facts : BusFacts p bs)
    (rest : List (BusInteraction (DenseExpr p))) (e : DenseExpr p) : Bool :=
  denseByteJustifiedW bound deep (all.filter DenseExpr.isSingleVar)
    (fun x => all.filter (DenseExpr.mentions x)) bs facts (fun _ => rest) (fun _ => []) e

/-- Are all of `R`'s payload entries at the declared byte slots justified (through the witness
    lookup `wits` and precomputed `domCs`/`candsOf`, see `denseByteJustifiedW`)? -/
def denseRecvSlotsJustified (bound : Nat) (deep : Bool) (domCs : List (DenseExpr p))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : Bool :=
  slots.all (fun slot =>
    match R.payload[slot]? with
    | some e => denseByteJustifiedW bound deep domCs candsOf bs facts wits fwits e
    | none => true)

end ApcOptimizer.Dense
