import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify
import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Two-root address disequality (symbolic-timestamp forwarding enabler)

`addrConstsNeq` (`BusUnify.lean`) can only refute an in-window memory message as a
*different-address* one when both address slots are literal constants. On keccak's heap the
address slot is a pointer *expression* `mem_ptr_limbs__0 + 2¹⁶·mem_ptr_limbs__1`, so no two
distinct heap pointers are ever refuted, and `busUnifyPass`'s consumer scan aborts on the first
interleaved other-pointer access — the whole "forward the read/`prev_data` limbs across the
symbolic-timestamp access, pin the decomp" chain never fires.

This module provides the missing certificate. Each pointer limb is pinned by a **two-root**
decomposition constraint `(A + k·x)(A + δ + k·x) = 0` (the address-wraparound branch, recognised
by `twoRootOf?`). Substituting the high limb's two roots into the address expression
`limb₀ + 2¹⁶·limb₁` **cancels the low limb algebraically** — over BabyBear `1 + 2¹⁶·30720 ≡ 0`,
so the `limb₀` coefficient vanishes — leaving an affine form in the base register plus a constant,
in each of the two branches. For two accesses off the *same* base register the branch forms differ
only in their constant (the immediate), so every one of the four branch-pair differences is a
nonzero field constant and the addresses provably differ — with **no bounds reasoning at all**,
purely the two-root disjunction and linear arithmetic.

Everything is a decidable, re-checkable certificate consumed by `busUnifyPass` / `busPairCancel`
via `addrTwoRootNeq`; the field-membership step (`twoRootOf?_sound`) needs an integral domain, so
the top-level certificate self-gates on `decide (Nat.Prime p)` and needs no change to the passes'
own primality handling. -/

variable {p : ℕ}

/-! ## Substituting a two-root branch into a linear form -/

/-- The two affine forms obtained by replacing the variable with coefficient `cx` in `rest + cx·x`
    by the two roots `x = -(k⁻¹·A)` and `x = -(k⁻¹·A) - k⁻¹·δ` of a `twoRootOf?` decomposition
    `(k, A, δ)`. Returned normalized (so a cancelled limb drops out). -/
def ptrBranchesOf (k : ZMod p) (A : LinExpr p) (δ cx : ZMod p) (rest : LinExpr p) :
    LinExpr p × LinExpr p :=
  let r1 := A.scale (-(k⁻¹))
  let r2 := r1.add ⟨-(k⁻¹ * δ), []⟩
  ((rest.add (r1.scale cx)).norm, (rest.add (r2.scale cx)).norm)

theorem ptrBranchesOf_eval (k : ZMod p) (A : LinExpr p) (δ cx : ZMod p) (rest : LinExpr p)
    (env : Variable → ZMod p) :
    ((ptrBranchesOf k A δ cx rest).1).eval env = rest.eval env + cx * (-(k⁻¹) * A.eval env) ∧
    ((ptrBranchesOf k A δ cx rest).2).eval env
      = rest.eval env + cx * (-(k⁻¹) * A.eval env - k⁻¹ * δ) := by
  have hc0 : (⟨-(k⁻¹ * δ), []⟩ : LinExpr p).eval env = -(k⁻¹ * δ) := by simp [LinExpr.eval]
  refine ⟨?_, ?_⟩
  · simp only [ptrBranchesOf, LinExpr.norm_eval, LinExpr.add_eval, LinExpr.scale_eval]
  · simp only [ptrBranchesOf, LinExpr.norm_eval, LinExpr.add_eval, LinExpr.scale_eval, hc0]
    ring

/-! ## Reducing a pointer expression through its limb decompositions -/

/-! ### A proof-carrying two-root map (memoized `twoRootOf?`)

Scanning every constraint per variable per candidate pair is quadratic on
keccak's interleaved window. The two-root data `(k, A, δ)` for each variable is instead precomputed
once per pass into a hash map bundled with its soundness. Each entry also carries `Nat.Prime p`
(needed for the field-membership step) — the map is built empty on composite `p` — so the
downstream certificate needs no per-call primality `decide`. -/

variable {constraints : List (Expression p)}

/-- Per-variable two-root decomposition data, each entry sound and witnessed by an actual
    constraint (and `p` prime, needed for the root-membership step). -/
structure TwoRootMap (p : ℕ) (constraints : List (Expression p)) where
  map : Std.HashMap Variable (ZMod p × LinExpr p × ZMod p)
  sound : ∀ v k A δ, map[v]? = some (k, A, δ) →
    Nat.Prime p ∧ k * k⁻¹ = 1 ∧ ∃ c ∈ constraints, twoRootOf? c v = some (k, A, δ)

namespace TwoRootMap

def empty : TwoRootMap p constraints where
  map := ∅
  sound := by
    intro v k A δ h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)

/-- Insert a sound entry (last write wins). -/
def insertEntry (T : TwoRootMap p constraints) (v : Variable) (k : ZMod p) (A : LinExpr p)
    (δ : ZMod p) (h : Nat.Prime p ∧ k * k⁻¹ = 1 ∧ ∃ c ∈ constraints, twoRootOf? c v = some (k, A, δ)) :
    TwoRootMap p constraints where
  map := T.map.insert v (k, A, δ)
  sound := by
    intro w k' A' δ' hw
    rw [Std.HashMap.getElem?_insert] at hw
    by_cases hvw : (v == w) = true
    · rw [if_pos hvw] at hw
      have hvw' : v = w := by simpa using hvw
      have heq : (k, A, δ) = (k', A', δ') := by simpa using hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      subst hvw'
      exact h
    · rw [if_neg hvw] at hw
      exact T.sound w k' A' δ' hw

/-- Insert the two-root entry (if any, with a unit coefficient) for each of `c`'s variables. -/
def addVars (hp : Nat.Prime p) (c : Expression p) (hc : c ∈ constraints) :
    TwoRootMap p constraints → List Variable → TwoRootMap p constraints
  | T, [] => T
  | T, v :: vs =>
    match htr : twoRootOf? c v with
    | some (k, A, δ) =>
      if hu : k * k⁻¹ = 1 then
        addVars hp c hc (T.insertEntry v k A δ ⟨hp, hu, c, hc, htr⟩) vs
      else addVars hp c hc T vs
    | none => addVars hp c hc T vs

/-- Fold `addVars` over a constraint list. -/
def addAll (hp : Nat.Prime p) :
    TwoRootMap p constraints → (pending : List (Expression p)) →
    (∀ c ∈ pending, c ∈ constraints) → TwoRootMap p constraints
  | T, [], _ => T
  | T, c :: rest, hmem =>
    addAll hp (addVars hp c (hmem c (List.mem_cons_self ..)) T c.vars.eraseDups) rest
      (fun c' h => hmem c' (List.mem_cons_of_mem _ h))

/-- Build the map for a constraint list (empty on composite `p`). -/
def build (constraints : List (Expression p)) : TwoRootMap p constraints :=
  if hp : Nat.Prime p then addAll hp empty constraints (fun _ h => h)
  else empty

end TwoRootMap

/-- All affine two-root reductions of an expression `E`: for each variable of the linearized form
    that carries a two-root entry, the pair of branch forms `ptrBranchesOf`. Every returned pair
    `(b₁, b₂)` satisfies `E.eval ∈ {b₁.eval, b₂.eval}` under the constraints
    (`ptrReductions_sound`). -/
def ptrReductions (T : TwoRootMap p constraints) (E : Expression p) :
    List (LinExpr p × LinExpr p) :=
  match linearize E with
  | none => []
  | some L =>
    (L.terms.map Prod.fst).eraseDups.filterMap (fun v =>
      match T.map[v]? with
      | some (k, A, δ) => some (ptrBranchesOf k A δ (L.coeff v) (L.others v))
      | none => none)

theorem ptrReductions_sound (T : TwoRootMap p constraints) (E : Expression p)
    (b1 b2 : LinExpr p) (hmem : (b1, b2) ∈ ptrReductions T E)
    (env : Variable → ZMod p) (hcon : ∀ c ∈ constraints, c.eval env = 0) :
    E.eval env = b1.eval env ∨ E.eval env = b2.eval env := by
  unfold ptrReductions at hmem
  cases hL : linearize E with
  | none => rw [hL] at hmem; simp at hmem
  | some L =>
    rw [hL] at hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨v, _hv, hmatch⟩ := hmem
    cases htm : T.map[v]? with
    | none => rw [htm] at hmatch; simp at hmatch
    | some kAδ =>
      obtain ⟨k, A, δ⟩ := kAδ
      rw [htm] at hmatch
      dsimp only at hmatch
      simp only [Option.some.injEq] at hmatch
      obtain ⟨hp, hunit, c, hc, htr⟩ := T.sound v k A δ htm
      haveI : Fact p.Prime := ⟨hp⟩
      have hroot := twoRootOf?_sound c v k A δ htr hunit env (hcon c hc)
      have hEL : E.eval env = L.eval env := linearize_eval E L hL env
      have hsplit : L.eval env = L.coeff v * env v + (L.others v).eval env := L.eval_split v env
      obtain ⟨he1, he2⟩ := ptrBranchesOf_eval k A δ (L.coeff v) (L.others v) env
      have hb1 : b1 = (ptrBranchesOf k A δ (L.coeff v) (L.others v)).1 :=
        (congrArg Prod.fst hmatch).symm
      have hb2 : b2 = (ptrBranchesOf k A δ (L.coeff v) (L.others v)).2 :=
        (congrArg Prod.snd hmatch).symm
      rcases hroot with hr | hr
      · left; rw [hEL, hsplit, hr, hb1, he1]; ring
      · right; rw [hEL, hsplit, hr, hb2, he2]; ring

/-! ## Nonzero-constant differences -/

/-- The two forms differ by a nonzero field constant (checked structurally after normalization). -/
def constDiffNZ (a b : LinExpr p) : Bool :=
  let d := (a.add (b.scale (-1))).norm
  d.terms.isEmpty && decide (d.const ≠ 0)

theorem constDiffNZ_sound (a b : LinExpr p) (h : constDiffNZ a b = true)
    (env : Variable → ZMod p) : a.eval env ≠ b.eval env := by
  unfold constDiffNZ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hterms, hconst⟩ := h
  have hd : ((a.add (b.scale (-1))).norm).eval env = a.eval env - b.eval env := by
    rw [LinExpr.norm_eval, LinExpr.add_eval, LinExpr.scale_eval]; ring
  have hd2 : ((a.add (b.scale (-1))).norm).eval env = ((a.add (b.scale (-1))).norm).const := by
    simp only [LinExpr.eval, List.isEmpty_iff.1 hterms, List.map_nil, List.sum_nil, add_zero]
  intro heq
  have hz : ((a.add (b.scale (-1))).norm).const = 0 := by rw [← hd2, hd, heq, sub_self]
  exact (of_decide_eq_true hconst) hz

/-! ## The expression- and address-level certificates -/

/-- Two expressions provably evaluate differently: some two-root reduction of each yields four
    branch-pair differences that are all nonzero field constants. -/
def exprTwoRootNeq (T : TwoRootMap p constraints) (e e' : Expression p) : Bool :=
  (ptrReductions T e).any (fun red =>
    (ptrReductions T e').any (fun red' =>
      constDiffNZ red.1 red'.1 && constDiffNZ red.1 red'.2 &&
      constDiffNZ red.2 red'.1 && constDiffNZ red.2 red'.2))

theorem exprTwoRootNeq_sound (T : TwoRootMap p constraints)
    (e e' : Expression p) (h : exprTwoRootNeq T e e' = true) (env : Variable → ZMod p)
    (hcon : ∀ c ∈ constraints, c.eval env = 0) : e.eval env ≠ e'.eval env := by
  unfold exprTwoRootNeq at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨a1, a2⟩, hred, hinner⟩ := h
  rw [List.any_eq_true] at hinner
  obtain ⟨⟨b1, b2⟩, hred', hchk⟩ := hinner
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨h11, h12⟩, h21⟩, h22⟩ := hchk
  have he := ptrReductions_sound T e a1 a2 hred env hcon
  have he' := ptrReductions_sound T e' b1 b2 hred' env hcon
  rcases he with ha | ha <;> rcases he' with hb | hb <;> rw [ha, hb]
  · exact constDiffNZ_sound a1 b1 h11 env
  · exact constDiffNZ_sound a1 b2 h12 env
  · exact constDiffNZ_sound a2 b1 h21 env
  · exact constDiffNZ_sound a2 b2 h22 env

/-- Some address slot of `S` and `bi` provably evaluates differently: the two interactions have
    different addresses. Primality (needed for the two-root membership) is carried by the map's
    entries, so this is a total `Bool` predicate composable with `addrConstsNeq`. -/
def addrTwoRootNeq (shape : MemoryBusShape) (T : TwoRootMap p constraints)
    (S bi : BusInteraction (Expression p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' => exprTwoRootNeq T e e'
    | _, _ => false)

theorem addrTwoRootNeq_sound (shape : MemoryBusShape) (T : TwoRootMap p constraints)
    (S bi : BusInteraction (Expression p))
    (h : addrTwoRootNeq shape T S bi = true) (env : Variable → ZMod p)
    (hcon : ∀ c ∈ constraints, c.eval env = 0) :
    shape.address (S.eval env) ≠ shape.address (bi.eval env) := by
  unfold addrTwoRootNeq at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  intro heq
  obtain ⟨j, hj⟩ : ∃ j, shape.addressFields[j]? = some slot := List.getElem?_of_mem hslot
  -- the address projections agree at `slot`'s position
  have key : (S.eval env).payload[slot]? = (bi.eval env).payload[slot]? := by
    have e1 : (shape.address (S.eval env))[j]? = some ((S.eval env).payload[slot]?) := by
      simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
    have e2 : (shape.address (bi.eval env))[j]? = some ((bi.eval env).payload[slot]?) := by
      simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
    rw [heq, e2] at e1; exact (Option.some.inj e1).symm
  have keyS : (S.eval env).payload[slot]? = (S.payload[slot]?).map (fun e => e.eval env) := by
    show (S.payload.map (fun e => e.eval env))[slot]? = _; rw [List.getElem?_map]
  have keyB : (bi.eval env).payload[slot]? = (bi.payload[slot]?).map (fun e => e.eval env) := by
    show (bi.payload.map (fun e => e.eval env))[slot]? = _; rw [List.getElem?_map]
  rw [keyS, keyB] at key
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : bi.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at hcond key
      simp only [Option.map_some, Option.some.injEq] at key
      exact exprTwoRootNeq_sound T e e' hcond env hcon key

/-! ## The affine (same-base) address-disequality certificate

The two-root certificate above needs the limb-decomposition constraints and primality. A far more
common shape — a wasm frame-pointer-relative stack pointer `c + fp`, or any two accesses off a
*common base* with different immediates — needs neither: linearizing both address slots and
subtracting yields a **nonzero field constant** (`(c₁ + fp) − (c₂ + fp) = c₁ − c₂`), so the
addresses provably differ with pure linear arithmetic — no bounds, no primality, no `TwoRootMap`.
This strictly generalizes `addrConstsNeq` (`const − const` is a constant difference too) and,
unlike the two-root path, consults no constraints, so it is a total `Bool` predicate composable
with the other two certificates. -/

/-- Some address slot of `S` and `bi` linearizes to two affine forms differing by a nonzero field
    constant: the two interactions provably have different addresses. Corpus-agnostic; any
    common-base addressing (a shared symbolic base with distinct immediates) benefits. -/
def addrAffineNeq (shape : MemoryBusShape) (S bi : BusInteraction (Expression p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' =>
      (match linearize e, linearize e' with
       | some L, some L' => constDiffNZ L L'
       | _, _ => false)
    | _, _ => false)

theorem addrAffineNeq_sound (shape : MemoryBusShape) (S bi : BusInteraction (Expression p))
    (h : addrAffineNeq shape S bi = true) (env : Variable → ZMod p) :
    shape.address (S.eval env) ≠ shape.address (bi.eval env) := by
  unfold addrAffineNeq at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  intro heq
  obtain ⟨j, hj⟩ : ∃ j, shape.addressFields[j]? = some slot := List.getElem?_of_mem hslot
  have key : (S.eval env).payload[slot]? = (bi.eval env).payload[slot]? := by
    have e1 : (shape.address (S.eval env))[j]? = some ((S.eval env).payload[slot]?) := by
      simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
    have e2 : (shape.address (bi.eval env))[j]? = some ((bi.eval env).payload[slot]?) := by
      simp only [MemoryBusShape.address, List.getElem?_map, hj, Option.map_some]
    rw [heq, e2] at e1; exact (Option.some.inj e1).symm
  have keyS : (S.eval env).payload[slot]? = (S.payload[slot]?).map (fun e => e.eval env) := by
    show (S.payload.map (fun e => e.eval env))[slot]? = _; rw [List.getElem?_map]
  have keyB : (bi.eval env).payload[slot]? = (bi.payload[slot]?).map (fun e => e.eval env) := by
    show (bi.payload.map (fun e => e.eval env))[slot]? = _; rw [List.getElem?_map]
  rw [keyS, keyB] at key
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : bi.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at key
      simp only [Option.map_some, Option.some.injEq] at key
      simp only [hSp, hbp] at hcond
      cases hL : linearize e with
      | none => simp [hL] at hcond
      | some L =>
        cases hL' : linearize e' with
        | none => simp [hL, hL'] at hcond
        | some L' =>
          simp only [hL, hL'] at hcond
          exact constDiffNZ_sound L L' hcond env
            (by rw [← linearize_eval e L hL env, ← linearize_eval e' L' hL' env]; exact key)
