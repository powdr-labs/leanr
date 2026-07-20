import ApcOptimizer.Implementation.OptimizerPasses.Subst
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Affine

set_option autoImplicit false

/-! # Dense affine forms (Task 3, WP-E — Gauss foundation)

The dense mirror of `LinExpr`/`linearize` (`OptimizerPasses/Affine.lean`), the linear-form layer the
Gauss elimination pass is built on. `linearize` never compares variables (it only appends and
scales term lists), so its decode-commutation needs no validity hypothesis — unlike the solver layer
(`coeff`/`trySolve`, which filter on `t.1 = x`), which comes next.

`decodeLin` decodes a dense linear form by resolving each term's `VarId`; the commutation lemmas
show the dense `eval`/`add`/`scale`/`linearize`/`toExpr` decode to their spec counterparts. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A dense linear form: a constant plus `(VarId, coefficient)` terms. -/
structure DenseLinExpr (p : ℕ) where
  const : ZMod p
  terms : List (VarId × ZMod p)

/-- Evaluate a dense linear form under a dense environment. -/
def DenseLinExpr.eval (l : DenseLinExpr p) (denv : VarId → ZMod p) : ZMod p :=
  l.const + (l.terms.map (fun t => t.2 * denv t.1)).sum

def DenseLinExpr.add (a b : DenseLinExpr p) : DenseLinExpr p :=
  ⟨a.const + b.const, a.terms ++ b.terms⟩

def DenseLinExpr.scale (k : ZMod p) (a : DenseLinExpr p) : DenseLinExpr p :=
  ⟨k * a.const, a.terms.map (fun t => (t.1, k * t.2))⟩

/-- Try to view a dense expression as a linear form (`none` on a variable×variable product). -/
def denseLinearize : DenseExpr p → Option (DenseLinExpr p)
  | .const n => some ⟨n, []⟩
  | .var i => some ⟨0, [(i, 1)]⟩
  | .add a b =>
      match denseLinearize a, denseLinearize b with
      | some la, some lb => some (la.add lb)
      | _, _ => none
  | .mul a b =>
      match denseLinearize a, denseLinearize b with
      | some la, some lb =>
          if la.terms.isEmpty then some (lb.scale la.const)
          else if lb.terms.isEmpty then some (la.scale lb.const)
          else none
      | _, _ => none

/-- Turn a dense linear form back into a dense expression. -/
def DenseLinExpr.toExpr (l : DenseLinExpr p) : DenseExpr p :=
  l.terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) (.const l.const)

/-! ## Decoding a dense linear form -/

/-- Decode a dense linear form by resolving each term's `VarId`. -/
def VarRegistry.decodeLin (reg : VarRegistry) (l : DenseLinExpr p) : LinExpr p :=
  ⟨l.const, l.terms.map (fun t => (reg.resolve t.1, t.2))⟩

@[simp] theorem VarRegistry.decodeLin_const (reg : VarRegistry) (l : DenseLinExpr p) :
    (reg.decodeLin l).const = l.const := rfl

theorem VarRegistry.decodeLin_add (reg : VarRegistry) (a b : DenseLinExpr p) :
    reg.decodeLin (a.add b) = (reg.decodeLin a).add (reg.decodeLin b) := by
  simp only [VarRegistry.decodeLin, DenseLinExpr.add, LinExpr.add, List.map_append]

theorem VarRegistry.decodeLin_scale (reg : VarRegistry) (k : ZMod p) (a : DenseLinExpr p) :
    reg.decodeLin (a.scale k) = (reg.decodeLin a).scale k := by
  simp only [VarRegistry.decodeLin, DenseLinExpr.scale, LinExpr.scale, List.map_map,
    Function.comp_def]

/-- `terms.isEmpty` is preserved by decoding (decode maps over the term list). -/
theorem VarRegistry.decodeLin_terms_isEmpty (reg : VarRegistry) (l : DenseLinExpr p) :
    (reg.decodeLin l).terms.isEmpty = l.terms.isEmpty := by
  simp only [VarRegistry.decodeLin, List.isEmpty_map]

/-- Decoding commutes with evaluation of a linear form. -/
theorem VarRegistry.decodeLin_eval (reg : VarRegistry) (l : DenseLinExpr p) (env : Variable → ZMod p) :
    (reg.decodeLin l).eval env = l.eval (fun i => env (reg.resolve i)) := by
  simp only [VarRegistry.decodeLin, LinExpr.eval, DenseLinExpr.eval, List.map_map,
    Function.comp_def]

/-- **`linearize` commutes with decode.** No validity needed: `linearize` never compares variables. -/
theorem VarRegistry.denseLinearize_decode (reg : VarRegistry) (e : DenseExpr p) :
    (denseLinearize e).map reg.decodeLin = linearize (reg.decodeExpr e) := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb =>
      simp only [denseLinearize, VarRegistry.decodeExpr, linearize, ← iha, ← ihb]
      cases denseLinearize a <;> cases denseLinearize b <;>
        simp [reg.decodeLin_add]
  | mul a b iha ihb =>
      simp only [denseLinearize, VarRegistry.decodeExpr, linearize, ← iha, ← ihb]
      cases denseLinearize a <;> cases denseLinearize b <;>
        simp [reg.decodeLin_terms_isEmpty, reg.decodeLin_scale,
          apply_ite (Option.map reg.decodeLin)]

/-- `toExpr` commutes with decode. -/
theorem VarRegistry.decodeLin_toExpr (reg : VarRegistry) (l : DenseLinExpr p) :
    reg.decodeExpr l.toExpr = (reg.decodeLin l).toExpr := by
  simp only [DenseLinExpr.toExpr, LinExpr.toExpr, VarRegistry.decodeLin]
  suffices H : ∀ (terms : List (VarId × ZMod p)) (init : DenseExpr p),
      reg.decodeExpr (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init)
        = (terms.map (fun t => (reg.resolve t.1, t.2))).foldl
            (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) (reg.decodeExpr init) by
    exact H l.terms (.const l.const)
  intro terms
  induction terms with
  | nil => intro init; rfl
  | cons t rest ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, ih, VarRegistry.decodeExpr]

/-! # Dense affine solver (Task 3, WP-E — Gauss foundation, part 2)

The dense mirror of the affine *solver* layer of `OptimizerPasses/Affine.lean` — `coeff`/`others`,
`trySolve`/`trySolveUnit`, and the occurrence-aware pivot enumerators `pm1PivotsOf`/`unitPivotsOf`.
These *compare variables* (they filter a term list on `t.1 = x`) and are `VarId`-native; the native
Gauss proof (`GaussProof.lean`) consumes them directly (`densePm1PivotsOf`/`denseUnitPivotsOf` and
their `_sound`/`_vars` lemmas). The commutation-era decode lemmas and the unused `solveAffineLin`/
`solveAffine`/`solvableFrom` solver defs the old Gauss port relied on have been removed; the
`decodeLin_*`/`denseLinearize_covered_terms` lemmas that other passes (AddrDiseqProof/Normalize/
DomainBatch) still consume are kept. -/

/-! ## Membership-congruence helpers for `find?`/`filterMap`/`flatMap` -/

/-- `find?` depends only on its predicate's values on list members. -/
theorem find?_congr_mem {α : Type _} {p q : α → Bool} (l : List α)
    (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have ha : p a = q a := h a (by simp)
      have hrest := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      by_cases hp : p a = true
      · rw [List.find?_cons_of_pos hp, List.find?_cons_of_pos (ha ▸ hp)]
      · rw [List.find?_cons_of_neg hp, List.find?_cons_of_neg (ha ▸ hp), hrest]

/-- `filterMap` depends only on its map's values on list members. -/
theorem filterMap_congr_mem {α β : Type _} {f g : α → Option β} (l : List α)
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
          ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- `flatMap` depends only on its map's values on list members. -/
theorem flatMap_congr_mem {α β : Type _} {f g : α → List β} (l : List α)
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
          ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-! ## `denseLinearize` introduces no new variable (coverage transfer)

Reproved locally (independent of `Dense/Normalize.lean`, which sits *downstream* of this file): the
term ids of a linearized dense expression are among the expression's variables, so a covered
expression yields an all-valid term list. -/

/-- Every term variable of `denseLinearize e` occurs in `e`. -/
theorem denseLinearize_mem_vars (e : DenseExpr p) (l : DenseLinExpr p)
    (h : denseLinearize e = some l) : ∀ i ∈ l.terms.map Prod.fst, i ∈ e.vars := by
  induction e generalizing l with
  | const n => simp only [denseLinearize, Option.some.injEq] at h; subst h; simp
  | var y =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      intro x hx; simpa [DenseExpr.vars] using hx
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          intro x hx
          simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hx
          simp only [DenseExpr.vars, List.mem_append]
          exact hx.imp (iha la hla x) (ihb lb hlb x)
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            intro x hx
            have hst : (lb.scale la.const).terms.map Prod.fst = lb.terms.map Prod.fst := by
              simp [DenseLinExpr.scale, List.map_map, Function.comp_def]
            rw [hst] at hx
            exact List.mem_append.2 (Or.inr (ihb lb hlb x hx))
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              intro x hx
              have hst : (la.scale lb.const).terms.map Prod.fst = la.terms.map Prod.fst := by
                simp [DenseLinExpr.scale, List.map_map, Function.comp_def]
              rw [hst] at hx
              exact List.mem_append.2 (Or.inl (iha la hla x hx))
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-- A covered dense expression linearizes to a term list of valid ids. -/
theorem VarRegistry.denseLinearize_covered_terms (reg : VarRegistry) {c : DenseExpr p}
    {l : DenseLinExpr p} (hc : c.CoveredBy reg) (hl : denseLinearize c = some l) :
    ∀ i ∈ l.terms.map Prod.fst, reg.Valid i :=
  fun i hi => hc i (denseLinearize_mem_vars c l hl i hi)

/-! ## Decoding a dense pivot -/

/-! ## Resolving a filtered-by-variable term list (validity-gated) -/

/-- Filtering a term list on `t.1 = x` commutes with `resolve`-decoding, given all compared ids
    valid (`resolve` is injective there, so the `VarId` test decodes to the `Variable` test). -/
theorem VarRegistry.map_resolve_filter_eq (reg : VarRegistry) {x : VarId} (hx : reg.Valid x)
    (ts : List (VarId × ZMod p)) (hv : ∀ i ∈ ts.map Prod.fst, reg.Valid i) :
    (ts.filter (fun t => t.1 = x)).map (fun t => (reg.resolve t.1, t.2))
      = (ts.map (fun t => (reg.resolve t.1, t.2))).filter (fun t => t.1 = reg.resolve x) := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      have ht1 : reg.Valid t.1 := hv t.1 (by simp)
      have hrest : ∀ i ∈ rest.map Prod.fst, reg.Valid i :=
        fun i hi => hv i (List.mem_cons_of_mem _ hi)
      by_cases h : t.1 = x
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.map_cons,
            List.filter_cons_of_pos (by simp [h]), ih hrest]
      · have hne : reg.resolve t.1 ≠ reg.resolve x := fun he => h (reg.resolve_inj ht1 hx he)
        rw [List.filter_cons_of_neg (by simpa using h), List.map_cons,
            List.filter_cons_of_neg (by simpa using hne), ih hrest]

/-- Filtering a term list on `t.1 ≠ x` commutes with `resolve`-decoding (validity-gated). -/
theorem VarRegistry.map_resolve_filter_ne (reg : VarRegistry) {x : VarId} (hx : reg.Valid x)
    (ts : List (VarId × ZMod p)) (hv : ∀ i ∈ ts.map Prod.fst, reg.Valid i) :
    (ts.filter (fun t => t.1 ≠ x)).map (fun t => (reg.resolve t.1, t.2))
      = (ts.map (fun t => (reg.resolve t.1, t.2))).filter (fun t => t.1 ≠ reg.resolve x) := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      have ht1 : reg.Valid t.1 := hv t.1 (by simp)
      have hrest : ∀ i ∈ rest.map Prod.fst, reg.Valid i :=
        fun i hi => hv i (List.mem_cons_of_mem _ hi)
      by_cases h : t.1 = x
      · rw [List.filter_cons_of_neg (by simp [h]), List.map_cons,
            List.filter_cons_of_neg (by simp [h]), ih hrest]
      · have hne : reg.resolve t.1 ≠ reg.resolve x := fun he => h (reg.resolve_inj ht1 hx he)
        rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.map_cons,
            List.filter_cons_of_pos (by simpa using hne), ih hrest]

/-! ## Coefficient / remainder of a dense linear form -/

/-- Total coefficient of `x` in a dense linear form (mirrors `LinExpr.coeff`). -/
def DenseLinExpr.coeff (l : DenseLinExpr p) (x : VarId) : ZMod p :=
  ((l.terms.filter (fun t => t.1 = x)).map Prod.snd).sum

/-- The dense linear form with all `x` terms removed (mirrors `LinExpr.others`). -/
def DenseLinExpr.others (l : DenseLinExpr p) (x : VarId) : DenseLinExpr p :=
  ⟨l.const, l.terms.filter (fun t => t.1 ≠ x)⟩

/-- Partition a dense term-list evaluation by whether the variable is `x` (mirrors
    `eval_terms_split`). Pure — no validity, since it never resolves. -/
theorem denseEval_terms_split (x : VarId) (denv : VarId → ZMod p)
    (terms : List (VarId × ZMod p)) :
    (terms.map (fun t => t.2 * denv t.1)).sum
    = ((terms.filter (fun t => t.1 = x)).map Prod.snd).sum * denv x
      + ((terms.filter (fun t => t.1 ≠ x)).map (fun t => t.2 * denv t.1)).sum := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
      by_cases hx : t.1 = x
      · rw [List.filter_cons_of_pos (by simpa using hx),
            List.filter_cons_of_neg (by simpa using hx),
            List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, hx]
        ring
      · rw [List.filter_cons_of_neg (by simpa using hx),
            List.filter_cons_of_pos (by simpa using hx),
            List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
        ring

/-- Coefficient/remainder decomposition of a dense linear form's evaluation (mirrors
    `LinExpr.eval_split`). -/
theorem DenseLinExpr.eval_split (l : DenseLinExpr p) (x : VarId) (denv : VarId → ZMod p) :
    l.eval denv = l.coeff x * denv x + (l.others x).eval denv := by
  simp only [DenseLinExpr.eval, DenseLinExpr.coeff, DenseLinExpr.others,
    denseEval_terms_split x denv l.terms]
  ring

/-! ## Coefficient / remainder / term-vars commutation -/

/-- **`coeff` commutes with decode** (validity-gated). -/
theorem VarRegistry.decodeLin_coeff (reg : VarRegistry) (l : DenseLinExpr p) {x : VarId}
    (hx : reg.Valid x) (hterms : ∀ i ∈ l.terms.map Prod.fst, reg.Valid i) :
    (reg.decodeLin l).coeff (reg.resolve x) = l.coeff x := by
  simp only [LinExpr.coeff, DenseLinExpr.coeff, VarRegistry.decodeLin]
  rw [← reg.map_resolve_filter_eq hx l.terms hterms]
  simp [List.map_map, Function.comp_def]

/-- **`others` commutes with decode** (validity-gated). -/
theorem VarRegistry.decodeLin_others (reg : VarRegistry) (l : DenseLinExpr p) {x : VarId}
    (hx : reg.Valid x) (hterms : ∀ i ∈ l.terms.map Prod.fst, reg.Valid i) :
    reg.decodeLin (l.others x) = (reg.decodeLin l).others (reg.resolve x) := by
  simp only [VarRegistry.decodeLin, DenseLinExpr.others, LinExpr.others]
  rw [reg.map_resolve_filter_ne hx l.terms hterms]

/-! ## Solving for a unit-coefficient variable -/

/-- Try to solve the dense linear form `= 0` for `v` when `v` has coefficient `±1`
    (mirrors `LinExpr.trySolve`). -/
def DenseLinExpr.trySolve (l : DenseLinExpr p) (v : VarId) : Option (VarId × DenseExpr p) :=
  if l.coeff v = 1 then some (v, ((l.others v).scale (-1)).toExpr)
  else if l.coeff v = -1 then some (v, (l.others v).toExpr)
  else none

/-- Try to solve the dense linear form `= 0` for `v` when `v`'s coefficient is a *unit*
    (mirrors `LinExpr.trySolveUnit`). -/
def DenseLinExpr.trySolveUnit (l : DenseLinExpr p) (v : VarId) : Option (VarId × DenseExpr p) :=
  if l.coeff v * (l.coeff v)⁻¹ = 1 then
    some (v, ((l.others v).scale (-(l.coeff v)⁻¹)).toExpr)
  else none

/-! ## The affine solver -/

/-! ## Occurrence-aware pivot enumeration -/

/-- All `±1`-coefficient pivots of one dense constraint (mirrors `pm1PivotsOf`). -/
def densePm1PivotsOf (c : DenseExpr p) : List (VarId × DenseExpr p) :=
  match denseLinearize c with
  | none => []
  | some l => (l.terms.map Prod.fst).filterMap l.trySolve

/-- Unit-coefficient pivots of one dense constraint, for variables with no `±1` solution
    (mirrors `unitPivotsOf`). -/
def denseUnitPivotsOf (c : DenseExpr p) : List (VarId × DenseExpr p) :=
  match denseLinearize c with
  | none => []
  | some l =>
    (l.terms.map Prod.fst).filterMap (fun v =>
      match l.trySolve v with
      | some _ => none
      | none => l.trySolveUnit v)

/-! ## Native affine-form evaluation (mirrors `LinExpr.add_eval`/`scale_eval`/`linearize_eval`)

The eval-preservation identities for the dense affine layer, proved natively over `VarId → ZMod p`
environments (no `decode`, no prime hypothesis — pure algebra). Consolidated here at their
definitions' home so every downstream native proof (normalization, domain passes, busPairCancel)
shares one copy. -/

theorem DenseLinExpr.add_eval (a b : DenseLinExpr p) (denv : VarId → ZMod p) :
    (a.add b).eval denv = a.eval denv + b.eval denv := by
  simp only [DenseLinExpr.add, DenseLinExpr.eval, List.map_append, List.sum_append]
  ring

theorem DenseLinExpr.scale_eval (k : ZMod p) (a : DenseLinExpr p) (denv : VarId → ZMod p) :
    (a.scale k).eval denv = k * a.eval denv := by
  simp only [DenseLinExpr.scale, DenseLinExpr.eval, List.map_map, mul_add]
  congr 1
  induction a.terms with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih, Function.comp_apply]; ring

theorem denseLinearize_eval (e : DenseExpr p) (l : DenseLinExpr p) (h : denseLinearize e = some l)
    (denv : VarId → ZMod p) : e.eval denv = l.eval denv := by
  induction e generalizing l with
  | const n =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      simp [DenseLinExpr.eval, DenseExpr.eval]
  | var i =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      simp [DenseLinExpr.eval, DenseExpr.eval]
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          rw [DenseExpr.eval, iha la hla, ihb lb hlb, DenseLinExpr.add_eval]
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          have hae : a.eval denv = la.eval denv := iha la hla
          have hbe : b.eval denv = lb.eval denv := ihb lb hlb
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            have hc : la.eval denv = la.const := by
              simp only [DenseLinExpr.eval, List.isEmpty_iff.1 h1, List.map_nil, List.sum_nil,
                add_zero]
            rw [DenseExpr.eval, hae, hbe, DenseLinExpr.scale_eval, hc]
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              have hc : lb.eval denv = lb.const := by
                simp only [DenseLinExpr.eval, List.isEmpty_iff.1 h2, List.map_nil, List.sum_nil,
                  add_zero]
              rw [DenseExpr.eval, hae, hbe, DenseLinExpr.scale_eval, hc, mul_comm]
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-- Evaluating the linear-form-rebuilt expression folds back to the affine sum. Dense mirror of
    `toExpr_foldl_eval` (`OptimizerPasses/Affine.lean:148`). -/
theorem denseToExpr_foldl_eval (denv : VarId → ZMod p) (terms : List (VarId × ZMod p)) :
    ∀ init : DenseExpr p,
      (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).eval denv
      = init.eval denv + (terms.map (fun t => t.2 * denv t.1)).sum := by
  induction terms with
  | nil => intro init; simp
  | cons t rest ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      simp only [DenseExpr.eval]
      ring

/-- `DenseLinExpr.toExpr` is eval-preserving. Dense mirror of `LinExpr.toExpr_eval`
    (`OptimizerPasses/Affine.lean:160`). -/
theorem DenseLinExpr.toExpr_eval (l : DenseLinExpr p) (denv : VarId → ZMod p) :
    l.toExpr.eval denv = l.eval denv := by
  simp only [DenseLinExpr.toExpr, DenseLinExpr.eval, denseToExpr_foldl_eval, DenseExpr.eval]

end ApcOptimizer.Dense
