import ApcOptimizer.Implementation.Dense.Normalize
import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Dense two-root address disequality (Task 3, busUnify-cluster foundation, chunk M1)

Dense, `VarId`-native runtime mirror of `OptimizerPasses/AddrDiseq.lean` — the shared certificate
library `busUnifyPass`/`busPairCancelPass` consult to refute a memory-address match. This module
is a **library**: it exports no pass, only the certificate-building and certificate-checking
functions the upcoming dense `busUnify` (and later `busPairCancel`) ports will consume.

Every spec proof-carrying wrapper (`TwoRootMap.sound`, `NonzeroWits.sound`) is **dropped**: the
dense structures keep exactly the data field(s) and lose the `Prop` field, matching the established
"proof-carrying spec struct → plain dense runtime state" pattern (`DenseSolved`, `DenseCandsV`,
`DenseSurvV`, …). Correctness is the prover's job, established natively downstream. Every `dif`
(dependent if used only to extract a proof witness for the certificate, e.g. `if hu : k*k⁻¹=1
then … ⟨…, hu, …⟩ …`) becomes a plain `if` on the same decidable condition — same control flow,
same branch taken, no proof term built. Primality/unit gating that is **behaviorally** relevant
(the map comes out empty on composite `p`; an entry is only inserted when its coefficient is a
unit) is preserved exactly, since it changes which candidates end up in the map.

`twoRootOf?` (recognizing a two-root decomposition) is technically owned by
`OptimizerPasses/RootPairUnify.lean`, but `AddrDiseq` is its only consumer so far; the dense mirror
`denseTwoRootOf?` is placed here (not duplicated) so the later dense `rootPairUnify` port (S1) can
import and reuse it directly. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## RootPairUnify-origin helper: recognizing a two-root constraint (dense)

Dense mirror of `RootPairUnify.twoRootOf?` (`OptimizerPasses/RootPairUnify.lean:74`). Placed here
(not in a not-yet-existing `Dense/RootPairUnify.lean`) because `AddrDiseq`'s `TwoRootMap` is its
only current consumer; reuse this definition (do not re-derive) when porting `rootPairUnify`. -/

/-- The two-root decomposition of a dense constraint relative to `x`: `some (k, A, δ)` when the
    constraint is a product of two affine factors, both linear in `x` with the same nonzero
    coefficient `k`, whose `x`-free parts differ by the constant `δ`. Mirrors `twoRootOf?`. -/
def denseTwoRootOf? (c : DenseExpr p) (x : VarId) : Option (ZMod p × DenseLinExpr p × ZMod p) :=
  match c with
  | .mul f1 f2 =>
    match denseLinearize f1, denseLinearize f2 with
    | some l1, some l2 =>
      let k := l1.coeff x
      let A := (l1.others x).norm
      let A2 := (l2.others x).norm
      if k ≠ 0 ∧ l2.coeff x = k ∧ A2.terms = A.terms then some (k, A, A2.const - A.const)
      else none
    | _, _ => none
  | _ => none

/-! ## Substituting a two-root branch into a linear form -/

/-- The two affine forms obtained by replacing the variable with coefficient `cx` in `rest + cx·x`
    by the two roots `x = -(k⁻¹·A)` and `x = -(k⁻¹·A) - k⁻¹·δ` of a `denseTwoRootOf?` decomposition
    `(k, A, δ)`. Mirrors `ptrBranchesOf`. -/
def densePtrBranchesOf (k : ZMod p) (A : DenseLinExpr p) (δ cx : ZMod p) (rest : DenseLinExpr p) :
    DenseLinExpr p × DenseLinExpr p :=
  let r1 := A.scale (-(k⁻¹))
  let r2 := r1.add ⟨-(k⁻¹ * δ), []⟩
  ((rest.add (r1.scale cx)).norm, (rest.add (r2.scale cx)).norm)

/-! ## Reducing a pointer expression through its limb decompositions -/

/-! ### A dense two-root map (memoized `denseTwoRootOf?`, no proof carried)

Mirrors `TwoRootMap`, dropping the `sound` proof field (the prover reconstructs correctness
natively downstream). Scanning every constraint per variable per candidate pair is quadratic on
keccak's interleaved window, so the two-root data `(k, A, δ)` for each variable is precomputed once
per pass into a hash map, exactly as the spec does. -/

/-- Per-variable two-root decomposition data (data only — mirrors `TwoRootMap` minus `sound`). -/
structure DenseTwoRootMap (p : ℕ) where
  map : Std.HashMap VarId (ZMod p × DenseLinExpr p × ZMod p)

namespace DenseTwoRootMap

def empty : DenseTwoRootMap p where
  map := ∅

/-- Insert an entry (last write wins). Mirrors `TwoRootMap.insertEntry`, dropping the soundness
    witness argument. -/
def insertEntry (T : DenseTwoRootMap p) (v : VarId) (k : ZMod p) (A : DenseLinExpr p) (δ : ZMod p) :
    DenseTwoRootMap p where
  map := T.map.insert v (k, A, δ)

/-- Insert the two-root entry (if any, with a unit coefficient) for each of `c`'s variables. The
    unit-coefficient `dif` of `TwoRootMap.addVars` becomes a plain `if` on the same decidable
    condition (behaviorally relevant: an entry is only inserted when the coefficient is a unit),
    dropping the certificate witness `TwoRootMap.addVars` built for it. Mirrors `TwoRootMap.addVars`. -/
def addVars (c : DenseExpr p) : DenseTwoRootMap p → List VarId → DenseTwoRootMap p
  | T, [] => T
  | T, v :: vs =>
    match denseTwoRootOf? c v with
    | some (k, A, δ) =>
      if k * k⁻¹ = 1 then addVars c (T.insertEntry v k A δ) vs
      else addVars c T vs
    | none => addVars c T vs

/-- Fold `addVars` over a constraint list. Mirrors `TwoRootMap.addAll`, dropping the membership
    witness threaded through the spec recursion. -/
def addAll : DenseTwoRootMap p → (pending : List (DenseExpr p)) → DenseTwoRootMap p
  | T, [] => T
  | T, c :: rest => addAll (addVars c T c.vars.eraseDups) rest

/-- Build the map for a constraint list (empty on composite `p`, exactly as the spec does — this
    primality gate is behaviorally relevant, not proof scaffolding, so it is preserved as a plain
    `if` on the same decidable condition in place of the spec's proof-extracting `dif`). Mirrors
    `TwoRootMap.build`. -/
def build (constraints : List (DenseExpr p)) : DenseTwoRootMap p :=
  if Nat.Prime p then addAll empty constraints else empty

end DenseTwoRootMap

/-- All affine two-root reductions of a dense expression `E`: for each variable of the linearized
    form that carries a two-root entry, the pair of branch forms `densePtrBranchesOf`. Mirrors
    `ptrReductions`. -/
def densePtrReductions (T : DenseTwoRootMap p) (E : DenseExpr p) :
    List (DenseLinExpr p × DenseLinExpr p) :=
  match denseLinearize E with
  | none => []
  | some L =>
    (L.terms.map Prod.fst).eraseDups.filterMap (fun v =>
      match T.map[v]? with
      | some (k, A, δ) => some (densePtrBranchesOf k A δ (L.coeff v) (L.others v))
      | none => none)

/-! ## Nonzero-constant differences -/

/-- The two forms differ by a nonzero field constant (checked structurally after normalization).
    Mirrors `constDiffNZ`. -/
def denseConstDiffNZ (a b : DenseLinExpr p) : Bool :=
  let d := (a.add (b.scale (-1))).norm
  d.terms.isEmpty && decide (d.const ≠ 0)

/-! ## The expression- and address-level certificates -/

/-- Two dense expressions provably evaluate differently: some two-root reduction of each yields
    four branch-pair differences that are all nonzero field constants. Mirrors `exprTwoRootNeq`. -/
def denseExprTwoRootNeq (T : DenseTwoRootMap p) (e e' : DenseExpr p) : Bool :=
  (densePtrReductions T e).any (fun red =>
    (densePtrReductions T e').any (fun red' =>
      denseConstDiffNZ red.1 red'.1 && denseConstDiffNZ red.1 red'.2 &&
      denseConstDiffNZ red.2 red'.1 && denseConstDiffNZ red.2 red'.2))

/-- Some address slot of `S` and `bi` provably evaluates differently: the two interactions have
    different addresses. Mirrors `addrTwoRootNeq`. -/
def denseAddrTwoRootNeq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S bi : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' => denseExprTwoRootNeq T e e'
    | _, _ => false)

/-! ## The affine (same-base) address-disequality certificate -/

/-- Some address slot of `S` and `bi` linearizes to two affine forms differing by a nonzero field
    constant: the two interactions provably have different addresses. Mirrors `addrAffineNeq`. -/
def denseAddrAffineNeq (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' =>
      (match denseLinearize e, denseLinearize e' with
       | some L, some L' => denseConstDiffNZ L L'
       | _, _ => false)
    | _, _ => false)

/-! ## The nonzero-witness (register-vs-RAM) address-disequality certificate -/

/-- A dense linear form is identically zero (empty terms and zero constant after normalization).
    Mirrors `isZeroLin`. -/
def denseIsZeroLin (l : DenseLinExpr p) : Bool :=
  l.norm.terms.isEmpty && decide (l.norm.const = 0)

/-- Nonzero linear factors of a single reciprocal product `a * b + r` with `r` a nonzero constant:
    `a·b = −r ≠ 0`, so each factor that linearizes is a nonzero witness. Mirrors
    `reciprocalWitsProd`. -/
def denseReciprocalWitsProd (a b r : DenseExpr p) : List (DenseLinExpr p) :=
  match denseLinearize r with
  | some lr =>
    if lr.terms.isEmpty && decide (lr.const ≠ 0) then
      (match denseLinearize a with | some la => [la] | none => []) ++
      (match denseLinearize b with | some lb => [lb] | none => [])
    else []
  | none => []

/-- Nonzero linear witnesses recognized from a constraint of the form `a·b + r = 0` (in either
    additive order), with `r` a nonzero constant. Mirrors `reciprocalWits?`. -/
def denseReciprocalWits? (c : DenseExpr p) : List (DenseLinExpr p) :=
  match c with
  | .add e1 e2 =>
    match e1 with
    | .mul a b => denseReciprocalWitsProd a b e2
    | _ => match e2 with
           | .mul a b => denseReciprocalWitsProd a b e1
           | _ => []
  | _ => []

/-- Linear forms provably nonzero under a constraint list (data only — mirrors `NonzeroWits`
    minus `sound`). -/
structure DenseNonzeroWits (p : ℕ) where
  wits : List (DenseLinExpr p)

/-- Collect every reciprocal-witness linear form from the constraint list. Mirrors
    `NonzeroWits.build`. -/
def DenseNonzeroWits.build (constraints : List (DenseExpr p)) : DenseNonzeroWits p where
  wits := constraints.flatMap denseReciprocalWits?

/-- `Σ_{f ∈ fields} (m.payload[f] − S.payload[f])` as a dense linear form; `none` if any listed
    slot is absent from either payload or is nonlinear. Mirrors `diffSumOver`. -/
def denseDiffSumOver (S m : BusInteraction (DenseExpr p)) : List Nat → Option (DenseLinExpr p)
  | [] => some ⟨0, []⟩
  | f :: fs =>
    match denseDiffSumOver S m fs with
    | none => none
    | some acc =>
      match S.payload[f]?, m.payload[f]? with
      | some eS, some eM =>
        match denseLinearize eS, denseLinearize eM with
        | some lS, some lM => some ((lM.add (lS.scale (-1))).add acc)
        | _, _ => none
      | _, _ => none

/-- The address slots of `S` and `m` provably differ: some subset `T` of the shape's address
    fields has limb-difference sum `Σ_{i∈T}(mᵢ − Sᵢ)` equal (up to sign) to a nonzero witness `g`.
    Mirrors `addrNonzeroNeq`. -/
def denseAddrNonzeroNeq (shape : MemoryBusShape) (nw : DenseNonzeroWits p)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.sublists.any (fun T =>
    match denseDiffSumOver S m T with
    | some D => nw.wits.any (fun g => denseIsZeroLin (D.add (g.scale (-1))) || denseIsZeroLin (D.add g))
    | none => false)

/-- The address-disequality certificates a memory-telescoping pass consults, bundled so both the
    two-root and the reciprocal-nonzero data thread through the pass as one memoized value
    (plain 2-field struct — mirrors `AddrCerts`). -/
structure DenseAddrCerts (p : ℕ) where
  tworoot : DenseTwoRootMap p
  nonzero : DenseNonzeroWits p

/-- Build both certificate tables from the constraint list. Mirrors `AddrCerts.build`. -/
def DenseAddrCerts.build (constraints : List (DenseExpr p)) : DenseAddrCerts p :=
  ⟨DenseTwoRootMap.build constraints, DenseNonzeroWits.build constraints⟩

end ApcOptimizer.Dense
