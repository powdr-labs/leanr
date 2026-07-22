import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense two-root decomposition unification

Recognizes pairs of two-root-decomposed constraints sharing a root gap and unifies them via a
substitution. Impl-only: the top transform `denseRootPairUnifyF` is shaped like `denseBusUnifyF`
(`BusUnifyNative.lean`), so `RootPairUnifyProof.lean` wraps it with `DenseVerifiedPassW.of`.

`ZMod p`'s `Inv` is total for every `p`, so nothing here needs `[Fact p.Prime]` to compute; only
soundness does. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Constant-coefficient decomposition (`DenseExpr.splitAt`, shared dense helper)

Unlike `denseLinearize`, the remainder may be nonlinear, so this succeeds where the affine machinery
gives up. -/

/-- Decompose `e` as `k·x + r`: `k` a field constant, `r` not mentioning `x` (by construction). -/
def DenseExpr.splitAt (x : VarId) : DenseExpr p → Option (ZMod p × DenseExpr p)
  | .const n => some (0, .const n)
  | .var y => if y = x then some (1, .const 0) else some (0, .var y)
  | .add a b =>
      match a.splitAt x, b.splitAt x with
      | some (ca, ra), some (cb, rb) => some (ca + cb, .add ra rb)
      | _, _ => none
  | .mul a b =>
      if a.mentions x || b.mentions x then
        match a.constValue? with
        | some k =>
            match b.splitAt x with
            | some (cb, rb) => some (k * cb, .mul a rb)
            | none => none
        | none =>
            match b.constValue? with
            | some k =>
                match a.splitAt x with
                | some (ca, ra) => some (k * ca, .mul ra b)
                | none => none
            | none => none
      else some (0, .mul a b)

/-! ## Bounds through scaled range checks

The low mem-ptr limb's range check carries not the raw limb but a scaled slot `4⁻¹·(x − F)` for a
small flag polynomial `F`. The slot value is still fact-bounded, so `x = k⁻¹·slot − k⁻¹·R` is
bounded once the offset part `R` enumerates over its (tiny, provable) flag domains. -/

/-- Bound `x` through one interaction: find a slot whose expression is affine in `x` with a unit
    coefficient and a bus-fact value bound; enumerate the remaining variables' proven finite domains
    for the offset part. Returns `B` with `x.val < B` under acceptance. -/
def denseScaledSlotBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (bi : BusInteraction (DenseExpr p)) (x : VarId) :
    Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none else
    (List.range bi.payload.length).findSome? (fun slot =>
      match bi.payload[slot]? with
      | none => none
      | some O =>
        match facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot with
        | none => none
        | some bound =>
          match O.splitAt x with
          | none => none
          | some (k, R) =>
            let m := k⁻¹
            let others := R.vars.eraseDups
            let doms := others.filterMap (fun v =>
              (denseFindDomainAlg domCs v).map (fun d => (v, d)))
            if k * m = 1 ∧ doms.map Prod.fst = others ∧
                (doms.map (fun vd => vd.2.length)).prod ≤ 16 then
              if m.val * (bound - 1) + ((denseAssignments doms).map
                    (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 < p then
                some (m.val * (bound - 1) + ((denseAssignments doms).map
                  (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 + 1)
              else none
            else none)

/-! ## Value bound lookup -/

/-- The value bound of `x` derived from the first bus obligation that bounds it. -/
def denseFindVarBound (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → VarId → Option Nat
  | [], _ => none
  | bi :: rest, x =>
    match denseInteractionBound bs facts bi x with
    | some bound => some bound
    | none => denseFindVarBound bs facts rest x

/-- Bound `x` from a raw slot (`denseFindVarBound`) or, failing that, through a scaled slot
    (`denseScaledSlotBound`). -/
def denseAnyVarBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (x : VarId) : Option Nat :=
  match denseFindVarBound bs facts bis x with
  | some B => some B
  | none => bis.findSome? (fun bi => denseScaledSlotBound bs facts domCs bi x)

/-! ## The pair certificate (dense) -/

/-- Decidable certificate that constraints `cX` (in `x`) and `cY` (in `y`) are two-root twins and
    both variables are range-bounded below the root gap. -/
def denseRpCheckPair (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (cX cY : DenseExpr p) (x y : VarId) : Bool :=
  match denseTwoRootOf? cX x, denseTwoRootOf? cY y with
  | some (k, A, δ), some (k', A', δ') =>
    decide (k' = k) && decide (A'.terms = A.terms) && decide (A'.const = A.const) &&
    decide (δ' = δ) && decide (k * k⁻¹ = 1) &&
    decide (x ∈ cX.vars) && decide (y ∈ cY.vars) &&
    (match denseAnyVarBound bs facts bis domCs x, denseAnyVarBound bs facts bis domCs y with
     | some Bx, some By =>
       decide (max Bx By ≤ (k⁻¹ * δ).val) && decide (max Bx By ≤ p - (k⁻¹ * δ).val)
     | _, _ => false)
  | _, _ => false

/-! ## The scan loop and the pass (dense) -/

/-- A previously seen two-root constraint: the constraint, its variable, and the matching key
    `(k, A.terms, A.const, δ)`. Keys are compared before the expensive certificate is attempted. -/
structure DenseRPSeen (p : ℕ) where
  c : DenseExpr p
  x : VarId
  key : ZMod p × List (VarId × ZMod p) × ZMod p × ZMod p

/-- The two-root candidates of one constraint, with their matching keys. Candidates whose root gap
    `g = k⁻¹·δ` is tiny are dropped up front: the pair condition `B ≤ min(g.val, p − g.val)` can
    never hold for a useful bound `B`, and booleanity constraints `b(b−1) = 0` would otherwise make
    every boolean variable a (never-unifiable, expensive-to-reject) candidate. -/
def denseRpCandidates (c : DenseExpr p) :
    List (VarId × (ZMod p × List (VarId × ZMod p) × ZMod p × ZMod p)) :=
  -- Both factors are linearized once (not per candidate variable); each `x` reads its coefficient
  -- and x-free part off the shared linear forms — exactly `denseTwoRootOf?`'s values.
  match c with
  | .mul f1 f2 =>
    (match denseLinearize f1, denseLinearize f2 with
     | some l1, some l2 =>
       (HashedDedup.hashedEraseDups (hash ·) c.vars).filterMap (fun x =>
         let k := l1.coeff x
         let A := (l1.others x).norm
         let A2 := (l2.others x).norm
         if k ≠ 0 ∧ l2.coeff x = k ∧ A2.terms = A.terms then
           let δ := A2.const - A.const
           if 256 ≤ min (k⁻¹ * δ).val (p - (k⁻¹ * δ).val) then
             some (x, (k, A.terms, A.const, δ))
           else none
         else none)
     | _, _ => [])
  | _ => []

/-- Hash of a candidate key, used to bucket the `seen` accumulator (bucketing never hides a twin;
    the exact `key == key'` check inside the scan separates any hash collision). -/
def denseRpKeyHash (key : ZMod p × List (VarId × ZMod p) × ZMod p × ZMod p) : UInt64 :=
  mixHash (hash key.1.val)
    (mixHash (hash key.2.2.1.val) (mixHash (hash key.2.2.2.val) (hash key.2.1.length)))

/-- Prepend seen-entries into their key-hash buckets, preserving per-bucket insertion order. -/
def denseRpInsertAll (m : Std.HashMap UInt64 (List (DenseRPSeen p)))
    (es : List (DenseRPSeen p)) : Std.HashMap UInt64 (List (DenseRPSeen p)) :=
  es.foldr (fun e acc => acc.insert (denseRpKeyHash e.key) (e :: acc.getD (denseRpKeyHash e.key) []))
    m

/-- Scan the constraints: for each two-root candidate, look for an earlier twin with the same key
    whose pair certificate passes, and adopt the entailed equality into the solution map. -/
def denseRpLoop (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p)) :
    List (DenseExpr p) → Std.HashMap UInt64 (List (DenseRPSeen p)) → DenseSolved p → DenseSolved p
  | [], _, σ => σ
  | c :: rest, seen, σ =>
    let cands := denseRpCandidates c
    match cands.findSome? (fun xk =>
        (seen.getD (denseRpKeyHash xk.2) []).findSome? (fun e =>
          if e.key == xk.2 && e.x != xk.1 &&
              denseRpCheckPair bs facts bis domCs e.c c e.x xk.1
          then some (e, xk.1) else none)) with
    | some ex =>
        denseRpLoop bs facts bis domCs rest
          (denseRpInsertAll seen ((cands.filter (fun xk => xk.1 != ex.2)).map
            (fun xk => (⟨c, xk.1, xk.2⟩ : DenseRPSeen p))))
          (σ.insertAll [(ex.2, DenseExpr.var ex.1.x)])
    | none =>
        denseRpLoop bs facts bis domCs rest
          (denseRpInsertAll seen (cands.map (fun xk => (⟨c, xk.1, xk.2⟩ : DenseRPSeen p)))) σ

/-- For twin constraints `(a+k·x)(a+δ+k·x)=0` and `(a+k·y)(a+δ+k·y)=0` — each pinning its variable
    to one of two roots a fixed gap `g = k⁻¹·δ` apart — when both variables are range-bounded below
    the gap they must land on the same root, so `x = y`; the pass substitutes `y := x` everywhere.
    Identity unless `p` is prime; each substitution is a bare variable, so degree never grows. -/
def denseRootPairUnifyF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseRpLoop bs facts d.busInteractions d.algebraicConstraints
      d.algebraicConstraints ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

end ApcOptimizer.Dense
