import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.Subst
import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Batch linear elimination (Gaussian elimination)

`affineSubstPass` eliminates one variable per invocation and pays a full-system rescan and
rewrite for each — on parsed machines with hundreds of linearly-solvable variables that is
quadratic and dominates the runtime. This pass eliminates **all** of them in one invocation:

1. Walk the constraints once (two sweeps, so a constraint whose pivot only becomes solvable
   after an earlier substitution is caught). For each, *reduce* it by the solutions found so
   far (`Expression.substF` + `normalize` — cheap, the constraint is small), and try to solve
   the reduced form for a unit-coefficient pivot (the proven `pm1PivotsOf`/`unitPivotsOf`
   candidates from `Affine.lean`), choosing the candidate that duplicates the least text
   (occurrence counts precomputed once) and avoiding pivots that would rewrite a raw payload
   slot of a stateless bus interaction into a compound expression (those slots feed the
   fact-domain machinery of `DomainProp.lean`; substituting a non-variable into them destroys
   derivable range knowledge).
2. Maintain the solution map **resolved**: when `x := t` is adopted, rewrite `x` out of every
   previously-stored solution (`Expression.subst`, only on entries that mention `x`). Reduced
   constraints therefore never mention solved variables, so neither do new solutions.
3. Apply the whole resolved map in a *single* system traversal (`ConstraintSystem.substF`).

Correctness: the map is carried in `Solved`, a `Std.HashMap` bundled with the proof that every
stored pair is entailed by the system (built with `Std.HashMap.getElem?_insert`); the final
application is `ConstraintSystem.substF_correct`. Purely equational — no field assumptions
(unit pivots re-check `a * a⁻¹ = 1`, as in `Affine.lean`). -/

variable {p : ℕ}

/-! ## Cheap syntactic helpers (no allocation) -/

/-- Does the expression mention variable `x`? -/
def Expression.mentions (x : Variable) : Expression p → Bool
  | .const _ => false
  | .var y => y == x
  | .add a b => a.mentions x || b.mentions x
  | .mul a b => a.mentions x || b.mentions x

/-- Number of variable occurrences (with multiplicity). -/
def Expression.varCount : Expression p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add a b => a.varCount + b.varCount
  | .mul a b => a.varCount + b.varCount

/-- Is the expression literally a variable? -/
def Expression.isVar : Expression p → Bool
  | .var _ => true
  | _ => false

/-- Bridge from the runtime `mentions` predicate to membership in `vars` (the converse of
    `Reencode.mentions_false_not_mem_vars`). Lets the reverse-dependency completeness invariant,
    stated over `t.vars`, discharge the `mentions`-based touched recheck. -/
theorem mem_vars_of_mentions (x : Variable) (e : Expression p) (h : e.mentions x = true) :
    x ∈ e.vars := by
  induction e with
  | const n => simp [Expression.mentions] at h
  | var y =>
      simp only [Expression.mentions] at h
      simp only [Expression.vars, List.mem_singleton]
      exact (beq_iff_eq.1 h).symm
  | add a b iha ihb =>
      simp only [Expression.mentions, Bool.or_eq_true] at h
      simp only [Expression.vars, List.mem_append]
      exact h.imp iha ihb
  | mul a b iha ihb =>
      simp only [Expression.mentions, Bool.or_eq_true] at h
      simp only [Expression.vars, List.mem_append]
      exact h.imp iha ihb

/-! ## The proof-carrying solution map -/

/-- Posting `x` into the reverse-dependency bucket of every variable in a list never removes an
    existing membership (the buckets only grow). Modelled on `CoveredIndex.inner_getD_mono`. -/
theorem revDeps_foldl_mono (x z y : Variable) (vs : List Variable) :
    ∀ (m : Std.HashMap Variable (Std.HashSet Variable)), y ∈ (m[z]?).getD ∅ →
      y ∈ ((vs.foldl (fun rd w => rd.insert w (((rd[w]?).getD ∅).insert x)) m)[z]?).getD ∅ := by
  induction vs with
  | nil => intro m hy; simpa using hy
  | cons w0 rest ih =>
      intro m hy
      simp only [List.foldl_cons]
      apply ih
      rw [Std.HashMap.getElem?_insert]
      by_cases h : (w0 == z) = true
      · rw [if_pos h]
        have hwz : w0 = z := by simpa using h
        subst hwz
        simp only [Option.getD_some]
        exact Std.HashSet.mem_insert.2 (Or.inr hy)
      · rw [if_neg h]; exact hy

/-- After posting `x` into every bucket of `vs`, `x` is in the bucket of each `z ∈ vs`.
    Modelled on `CoveredIndex.inner_getD_self`. -/
theorem revDeps_foldl_self (x z : Variable) (vs : List Variable) :
    ∀ (m : Std.HashMap Variable (Std.HashSet Variable)), z ∈ vs →
      x ∈ ((vs.foldl (fun rd w => rd.insert w (((rd[w]?).getD ∅).insert x)) m)[z]?).getD ∅ := by
  induction vs with
  | nil => intro m hz; simp at hz
  | cons w0 rest ih =>
      intro m hz
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 hz with rfl | hz
      · refine revDeps_foldl_mono x z x rest _ ?_
        rw [Std.HashMap.getElem?_insert, if_pos (by simp), Option.getD_some]
        exact Std.HashSet.mem_insert_self
      · exact ih _ hz

/-- A set of solved variables `x := t`, each entailed by every satisfying assignment of `cs`.
    The `Std.HashMap` makes both lookup during reduction and the final `substF` application
    cheap; the bundled proof is exactly the hypothesis `ConstraintSystem.substF_correct`
    consumes. -/
structure Solved (p : ℕ) (cs : ConstraintSystem p) (bs : BusSemantics p) where
  map : Std.HashMap Variable (Expression p)
  /-- Reverse-dependency index: `revDeps[z]` is a superset of the solution keys `y` whose stored
      right-hand side `map[y]` mentions `z`. Used to resolve a newly-adopted pivot `x := t` into
      only the affected stored solutions (`revDeps[x]`) instead of scanning the whole map (which is
      O(K²) over K pivots). Buckets are `HashSet`s so re-posting a repeatedly-rewritten key is
      idempotent (a `List` bucket would accumulate duplicates and blow up the re-insertion work). -/
  revDeps : Std.HashMap Variable (Std.HashSet Variable)
  sound : ∀ env, cs.satisfies bs env → ∀ y t, map[y]? = some t → env y = t.eval env
  varsIn : ∀ (y : Variable) (t : Expression p), map[y]? = some t → ∀ z ∈ t.vars, z ∈ cs.vars
  /-- The reverse-dependency index is *complete*: if a stored solution `map[y]`'s right-hand side
      mentions `z`, then `y` is in `z`'s bucket. This makes the `revDeps`-driven resolution of a
      pivot equal to the full-map scan (every affected solution is found), so the output stays
      byte-identical — a proof, not just an output test. Erases at runtime. -/
  revComplete : ∀ (y : Variable) (t : Expression p) (z : Variable),
    map[y]? = some t → z ∈ t.vars → y ∈ (revDeps[z]?).getD ∅

namespace Solved

variable {cs : ConstraintSystem p} {bs : BusSemantics p}

def empty : Solved p cs bs where
  map := ∅
  revDeps := ∅
  sound := by
    intro _ _ y t h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)
  varsIn := by
    intro y t h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)
  revComplete := by
    intro y t z h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)

/-- The map as a lookup function (what `substF` consumes). -/
def fn (σ : Solved p cs bs) : Variable → Option (Expression p) := fun y => σ.map[y]?

/-- Under a satisfying assignment, rebinding by the solution map changes nothing. -/
theorem envF_self (σ : Solved p cs bs) (env : Variable → ZMod p)
    (hsat : cs.satisfies bs env) : envF σ.fn env = env :=
  envF_eq_self σ.fn env (fun y t hyt => σ.sound env hsat y t hyt)

/-- Reducing an expression by the solution map preserves its value under satisfying
    assignments. -/
theorem eval_reduce (σ : Solved p cs bs) (e : Expression p) (env : Variable → ZMod p)
    (hsat : cs.satisfies bs env) :
    ((e.substF σ.fn).normalize).eval env = e.eval env := by
  rw [Expression.normalize_eval, Expression.eval_substF, σ.envF_self env hsat]

/-- Insert a list of entailed pairs (later inserts win, which is harmless: every pair is
    entailed individually). -/
def insertAll (σ : Solved p cs bs) (pairs : List (Variable × Expression p))
    (H : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env)
    (Hv : ∀ yt ∈ pairs, ∀ z ∈ yt.2.vars, z ∈ cs.vars) :
    Solved p cs bs :=
  match pairs with
  | [] => σ
  | (x, t) :: rest =>
      let σ' : Solved p cs bs :=
        { map := σ.map.insert x t,
          -- post `x` into the reverse-dependency bucket of every variable `t` mentions (stale
          -- entries from an overwritten `x` are harmless; the `HashSet` keeps re-posting idempotent).
          revDeps := t.vars.foldl (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert x)) σ.revDeps,
          sound := by
            intro env hsat y s hys
            rw [Std.HashMap.getElem?_insert] at hys
            by_cases hxy : (x == y) = true
            · rw [if_pos hxy] at hys
              have hxy' : x = y := by simpa using hxy
              have hts : t = s := by simpa using hys
              subst hxy'; subst hts
              exact H env hsat (x, t) (List.mem_cons_self ..)
            · rw [if_neg hxy] at hys
              exact σ.sound env hsat y s hys
          varsIn := by
            intro y s hys
            rw [Std.HashMap.getElem?_insert] at hys
            by_cases hxy : (x == y) = true
            · rw [if_pos hxy] at hys
              have hts : t = s := by simpa using hys
              subst hts
              exact Hv (x, t) (List.mem_cons_self ..)
            · rw [if_neg hxy] at hys
              exact σ.varsIn y s hys
          revComplete := by
            intro y s z hys hz
            rw [Std.HashMap.getElem?_insert] at hys
            by_cases hxy : (x == y) = true
            · -- new/overwritten key `x`: `s = t`, and `x` was posted to every bucket of `t.vars ∋ z`
              rw [if_pos hxy] at hys
              have hxy' : x = y := by simpa using hxy
              have hts : t = s := by simpa using hys
              subst hxy'; subst hts
              exact revDeps_foldl_self x z t.vars σ.revDeps hz
            · -- untouched key: old completeness gives `y ∈ σ.revDeps[z]`, monotone under posting
              rw [if_neg hxy] at hys
              exact revDeps_foldl_mono x z y t.vars σ.revDeps (σ.revComplete y s z hys hz) }
      σ'.insertAll rest (fun env hsat yt hyt => H env hsat yt (List.mem_cons_of_mem _ hyt))
        (fun yt hyt => Hv yt (List.mem_cons_of_mem _ hyt))

/-! ### The reverse-dependency-indexed touched-solution selection

When adopting a pivot `x := t`, Gauss must rewrite `x` out of every stored solution whose RHS
mentions `x`. `touchedOf` gathers exactly those `(key, rhs)` pairs from `x`'s reverse-dependency
bucket (re-checking `mentions` since buckets may be stale), instead of scanning the whole map.
`mem_touchedOf` proves it emits **exactly** the current solutions mentioning `x` — both directions:
soundness (every emitted pair is a current solution mentioning `x`) and, using `revComplete`,
completeness (every such solution is emitted). It is thus extensionally the same set as the
full-map scan `fullScanTouched` (`mem_touchedOf_iff_fullScan`); `HashSet` bucket uniqueness gives
each pair once. -/

/-- The touched-solution selection for a pivot on `x`: the current solutions whose RHS mentions
    `x`, gathered from `x`'s reverse-dependency bucket. -/
def touchedOf (σ : Solved p cs bs) (x : Variable) : List (Variable × Expression p) :=
  ((σ.revDeps[x]?).getD ∅).toList.filterMap (fun y =>
    (σ.map[y]?).bind (fun s => if s.mentions x then some (y, s) else none))

/-- The full-map-scan reference: every stored solution whose RHS mentions `x`. -/
def fullScanTouched (σ : Solved p cs bs) (x : Variable) : List (Variable × Expression p) :=
  σ.map.toList.filter (fun ys => ys.2.mentions x)

theorem mem_touchedOf (σ : Solved p cs bs) (x y : Variable) (s : Expression p) :
    (y, s) ∈ σ.touchedOf x ↔ σ.map[y]? = some s ∧ s.mentions x = true := by
  unfold touchedOf
  constructor
  · intro hys
    obtain ⟨y', _, hy'⟩ := List.mem_filterMap.1 hys
    obtain ⟨s', hs', hif⟩ := Option.bind_eq_some_iff.1 hy'
    by_cases hm : s'.mentions x
    · rw [if_pos hm] at hif
      simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨hs', hm⟩
    · rw [if_neg hm] at hif; exact absurd hif (by simp)
  · rintro ⟨hmap, hmen⟩
    refine List.mem_filterMap.2 ⟨y, ?_, ?_⟩
    · rw [Std.HashSet.mem_toList]
      exact σ.revComplete y s x hmap (mem_vars_of_mentions x s hmen)
    · rw [hmap]
      show (if s.mentions x then some (y, s) else none) = some (y, s)
      rw [if_pos hmen]

theorem mem_fullScanTouched (σ : Solved p cs bs) (x y : Variable) (s : Expression p) :
    (y, s) ∈ σ.fullScanTouched x ↔ σ.map[y]? = some s ∧ s.mentions x = true := by
  unfold fullScanTouched
  rw [List.mem_filter, Std.HashMap.mem_toList_iff_getElem?_eq_some]

/-- The indexed selection is extensionally the full-map scan. -/
theorem mem_touchedOf_iff_fullScan (σ : Solved p cs bs) (x : Variable)
    (ys : Variable × Expression p) : ys ∈ σ.touchedOf x ↔ ys ∈ σ.fullScanTouched x := by
  obtain ⟨y, s⟩ := ys
  rw [mem_touchedOf, mem_fullScanTouched]

end Solved

/-! ## Pivot choice -/

/-- Occurrence counts of every variable across the system (one traversal). -/
def occurrenceMap (cs : ConstraintSystem p) : Std.HashMap Variable Nat :=
  let addE := fun (m : Std.HashMap Variable Nat) (e : Expression p) =>
    e.vars.foldl (fun m x => m.insert x (m.getD x 0 + 1)) m
  let m := cs.algebraicConstraints.foldl addE ∅
  cs.busInteractions.foldl (fun m bi => bi.payload.foldl addE (addE m bi.multiplicity)) m

/-- Variables occurring as a *raw* payload slot of a stateless interaction. Substituting a
    compound expression into such a slot destroys fact-derivable range knowledge
    (`interactionBound` in `DomainProp.lean` needs the slot to be literally a variable), so
    pivots on these variables are penalized unless their solution is itself a variable. -/
def protectedVars (cs : ConstraintSystem p) (bs : BusSemantics p) : Std.HashSet Variable :=
  cs.busInteractions.foldl (init := ∅) fun s bi =>
    if bs.isStateful bi.busId then s
    else bi.payload.foldl (fun s e => match e with | .var x => s.insert x | _ => s) s

/-- The duplication cost of a pivot `x := t`, with the protection penalty. -/
def pivotScore (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable)
    (xt : Variable × Expression p) : Nat :=
  let base := (occ.getD xt.1 1 - 1) * (1 + xt.2.varCount)
  if prot.contains xt.1 && !xt.2.isVar then base + 1000000 else base

/-! ## Fast pivot selection (build only the winning candidate)

`pm1PivotsOf`/`unitPivotsOf` build a full solution `Expression` (`toExpr`) for *every* solvable
pivot of a constraint, then `argmin` keeps one and discards the rest — wasteful expression
allocation, which dominates via reference-count churn on large systems. `fastBest` scans
lightweight `(variable, score)` descriptors instead, computing each candidate's exact `pivotScore`
from the linear form's coefficients and term counts *without materialising any solution*, then
builds `toExpr` only for the winner. It is proven equal to the old `argmin` over
`pm1PivotsOf ++ unitPivotsOf` (`fastBest_eq`), so `gaussLoop`'s decisions and output are unchanged.

Each candidate's coefficient and solution size are read from the `coeffIdx` (built once per
constraint), so scoring is O(terms), not O(terms²). -/

/-- `argmin` commutes with a key-preserving map: when `g` carries the key (`kγ (g a) = kα a`), the
    winner of the mapped list is the mapped winner. This lets us score cheap descriptors in place
    of built candidates. -/
theorem argmin_map_key {α γ : Type*} (g : α → γ) (kα : α → Nat) (kγ : γ → Nat)
    (h : ∀ a, kγ (g a) = kα a) : ∀ l : List α, (l.map g).argmin kγ = (l.argmin kα).map g := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.argmin_cons, List.argmin_cons, ih]
      cases t.argmin kα with
      | none => simp
      | some c =>
          simp only [Option.map_some, h]
          by_cases hlt : kα c < kα a <;> simp [hlt]

theorem map_filterMap {α β γ : Type*} (f : α → Option β) (g : β → γ) (l : List α) :
    (l.filterMap f).map g = l.filterMap (fun a => (f a).map g) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.filterMap_cons]
      cases f a with
      | none => simpa using ih
      | some b => simp [ih]

/-! ### `toExpr` size facts (score a candidate without building it) -/

theorem toExpr_foldl_varCount (terms : List (Variable × ZMod p)) :
    ∀ init : Expression p,
      (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).varCount
        = init.varCount + terms.length := by
  induction terms with
  | nil => intro init; simp
  | cons t rest ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp only [Expression.varCount, List.length_cons]
      omega

theorem LinExpr.toExpr_varCount (l : LinExpr p) : l.toExpr.varCount = l.terms.length := by
  rw [LinExpr.toExpr, toExpr_foldl_varCount]
  simp [Expression.varCount]

theorem LinExpr.scale_terms_length (k : ZMod p) (l : LinExpr p) :
    (l.scale k).terms.length = l.terms.length := by
  simp [LinExpr.scale]

theorem toExpr_foldl_isVar (terms : List (Variable × ZMod p)) :
    ∀ init : Expression p, init.isVar = false →
      (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).isVar = false := by
  induction terms with
  | nil => intro init h; simpa using h
  | cons t rest ih => intro init _; exact ih _ rfl

theorem LinExpr.toExpr_isVar (l : LinExpr p) : l.toExpr.isVar = false :=
  toExpr_foldl_isVar l.terms _ rfl

/-! ### Descriptors -/

/-- Score of a pivot on `v` whose solution has `oc` variable occurrences. The `pivotScore`
    protection penalty reduces to `prot.contains v`, since a `toExpr` solution is never a bare
    variable. -/
def gaussScore (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) (v : Variable)
    (oc : Nat) : Nat :=
  let base := (occ.getD v 1 - 1) * (1 + oc)
  if prot.contains v then base + 1000000 else base

theorem gaussScore_eq_pivotScore (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable)
    (v : Variable) (t : Expression p) (oc : Nat) (hiv : t.isVar = false) (hvc : t.varCount = oc) :
    gaussScore occ prot v oc = pivotScore occ prot (v, t) := by
  subst hvc
  simp only [gaussScore, pivotScore, hiv, Bool.not_false, Bool.and_true]

/-- `l.trySolve` in closed form (keeps the `Option (Variable × Expression p)` type, so rewriting
    with it — unlike unfolding into `none` — never leaves the element type ambiguous). -/
theorem LinExpr.trySolve_eq_of_one (l : LinExpr p) (v : Variable) (h : l.coeff v = 1) :
    l.trySolve v = some (v, ((l.others v).scale (-1)).toExpr) := by
  unfold LinExpr.trySolve; rw [if_pos h]

theorem LinExpr.trySolve_eq_of_negOne (l : LinExpr p) (v : Variable) (h1 : l.coeff v ≠ 1)
    (h2 : l.coeff v = -1) : l.trySolve v = some (v, (l.others v).toExpr) := by
  unfold LinExpr.trySolve; rw [if_neg h1, if_pos h2]

theorem LinExpr.trySolve_eq_none (l : LinExpr p) (v : Variable)
    (h : ¬(l.coeff v = 1 ∨ l.coeff v = -1)) : l.trySolve v = none := by
  unfold LinExpr.trySolve; rw [if_neg (fun hh => h (Or.inl hh)), if_neg (fun hh => h (Or.inr hh))]

theorem LinExpr.trySolveUnit_eq_of (l : LinExpr p) (v : Variable)
    (h : l.coeff v * (l.coeff v)⁻¹ = 1) :
    l.trySolveUnit v = some (v, ((l.others v).scale (-(l.coeff v)⁻¹)).toExpr) := by
  unfold LinExpr.trySolveUnit; rw [if_pos h]

theorem LinExpr.trySolveUnit_eq_none (l : LinExpr p) (v : Variable)
    (h : ¬l.coeff v * (l.coeff v)⁻¹ = 1) : l.trySolveUnit v = none := by
  unfold LinExpr.trySolveUnit; rw [if_neg h]

/-! ### Coefficient/occurrence index (linear pivot scoring)

Scoring a constraint's candidates needs, per variable, its total coefficient (`l.coeff v`, to
classify `±1`/unit) and the size of its solution (`(l.others v).terms.length`, the pivot's
`varCount`). Computed directly those are O(terms) each, so scoring is O(terms²) per constraint.
`coeffIdx` folds the term list once into a `Std.HashMap Variable (ZMod p × Nat)` = (coefficient sum,
occurrence count) per variable; then `coeff = idx[v].1` and `others-length = |terms| - idx[v].2` are
O(1). Proven equal to `l.coeff`/`l.others` (`coeffIdx_coeff`/`coeffIdx_others`), so the descriptors
below are unchanged in meaning. Each descriptor binds `idx[v]` once (the `let e`), so a candidate
visit performs a single index lookup on both the success and failure branch. -/

/-- Coefficient sum of the terms whose variable is `v`. `l.coeff v` unfolds to `csum l.terms v`. -/
def csum (terms : List (Variable × ZMod p)) (v : Variable) : ZMod p :=
  ((terms.filter (fun t => t.1 = v)).map Prod.snd).sum

/-- Occurrence count of `v` among the terms. -/
def ccnt (terms : List (Variable × ZMod p)) (v : Variable) : Nat :=
  (terms.filter (fun t => t.1 = v)).length

/-- One index step: add `t`'s coefficient and one occurrence to `t.1`'s entry (0 if absent). -/
def idxStep (m : Std.HashMap Variable (ZMod p × Nat)) (t : Variable × ZMod p) :
    Std.HashMap Variable (ZMod p × Nat) :=
  m.insert t.1 (((m[t.1]?).getD (0, 0)).1 + t.2, ((m[t.1]?).getD (0, 0)).2 + 1)

/-- The coefficient/occurrence index of a term list. -/
def coeffIdx (terms : List (Variable × ZMod p)) : Std.HashMap Variable (ZMod p × Nat) :=
  terms.foldl idxStep ∅

theorem idxStep_fold (terms : List (Variable × ZMod p)) :
    ∀ (m : Std.HashMap Variable (ZMod p × Nat)) (v : Variable),
      ((terms.foldl idxStep m)[v]?).getD (0, 0)
        = (((m[v]?).getD (0, 0)).1 + csum terms v, ((m[v]?).getD (0, 0)).2 + ccnt terms v) := by
  induction terms with
  | nil => intro m v; simp [csum, ccnt]
  | cons t rest ih =>
      intro m v
      rw [List.foldl_cons, ih (idxStep m t) v]
      have hstep : ((idxStep m t)[v]?).getD (0, 0)
          = (((m[v]?).getD (0, 0)).1 + (if t.1 = v then t.2 else 0),
             ((m[v]?).getD (0, 0)).2 + (if t.1 = v then 1 else 0)) := by
        unfold idxStep
        rw [Std.HashMap.getElem?_insert]
        by_cases htv : t.1 = v
        · subst htv; simp
        · rw [if_neg (by simpa using htv), if_neg htv, if_neg htv]
          simp
      rw [hstep]
      have hcsum : csum (t :: rest) v = (if t.1 = v then t.2 else 0) + csum rest v := by
        unfold csum; by_cases htv : t.1 = v <;> simp [htv]
      have hccnt : ccnt (t :: rest) v = ccnt rest v + (if t.1 = v then 1 else 0) := by
        unfold ccnt; by_cases htv : t.1 = v <;> simp [htv]
      rw [hcsum, hccnt]
      refine Prod.ext ?_ ?_ <;> ring

theorem coeffIdx_get (terms : List (Variable × ZMod p)) (v : Variable) :
    ((coeffIdx terms)[v]?).getD (0, 0) = (csum terms v, ccnt terms v) := by
  simp [coeffIdx, idxStep_fold terms ∅ v]

theorem coeffIdx_coeff (l : LinExpr p) (v : Variable) :
    (((coeffIdx l.terms)[v]?).getD (0, 0)).1 = l.coeff v := by
  rw [coeffIdx_get]; rfl

theorem filter_eq_ne_length (terms : List (Variable × ZMod p)) (v : Variable) :
    (terms.filter (fun t => t.1 ≠ v)).length + (terms.filter (fun t => t.1 = v)).length
      = terms.length := by
  induction terms with
  | nil => rfl
  | cons t rest ih => by_cases htv : t.1 = v <;> simp_all <;> omega

theorem coeffIdx_others (l : LinExpr p) (v : Variable) :
    l.terms.length - (((coeffIdx l.terms)[v]?).getD (0, 0)).2 = (l.others v).terms.length := by
  rw [coeffIdx_get]
  simp only [LinExpr.others, ccnt]
  have h := filter_eq_ne_length l.terms v
  omega

/-- `±1`-pivot descriptor: `some (v, score)` exactly when `l.trySolve v` succeeds. The coefficient
    and occurrence count come from the O(1) index (`total` = `|l.terms|`), so scanning all
    candidates is O(terms) rather than O(terms²). -/
def pm1Desc (idx : Std.HashMap Variable (ZMod p × Nat)) (total : Nat)
    (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) (v : Variable) :
    Option (Variable × Nat) :=
  let e := (idx[v]?).getD (0, 0)
  if e.1 = 1 ∨ e.1 = -1 then some (v, gaussScore occ prot v (total - e.2)) else none

theorem pm1Desc_eq (l : LinExpr p) (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable)
    (v : Variable) :
    pm1Desc (coeffIdx l.terms) l.terms.length occ prot v
      = (l.trySolve v).map (fun xt => (xt.1, pivotScore occ prot xt)) := by
  simp only [pm1Desc, coeffIdx_coeff l v, coeffIdx_others l v]
  by_cases h1 : l.coeff v = 1
  · rw [if_pos (Or.inl h1), LinExpr.trySolve_eq_of_one l v h1, Option.map_some,
      gaussScore_eq_pivotScore occ prot v (((l.others v).scale (-1)).toExpr)
        (l.others v).terms.length (LinExpr.toExpr_isVar _)
        (by rw [LinExpr.toExpr_varCount, LinExpr.scale_terms_length])]
  · by_cases h2 : l.coeff v = -1
    · rw [if_pos (Or.inr h2), LinExpr.trySolve_eq_of_negOne l v h1 h2, Option.map_some,
        gaussScore_eq_pivotScore occ prot v ((l.others v).toExpr)
          (l.others v).terms.length (LinExpr.toExpr_isVar _) (LinExpr.toExpr_varCount _)]
    · rw [if_neg (by rintro (h | h); exacts [h1 h, h2 h]),
        LinExpr.trySolve_eq_none l v (by rintro (h | h); exacts [h1 h, h2 h]), Option.map_none]

/-- Unit-pivot descriptor: `some (v, score)` exactly when `l.trySolve v` fails but
    `l.trySolveUnit v` succeeds. Index-driven, O(1), like `pm1Desc`. -/
def unitDesc (idx : Std.HashMap Variable (ZMod p × Nat)) (total : Nat)
    (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) (v : Variable) :
    Option (Variable × Nat) :=
  let e := (idx[v]?).getD (0, 0)
  if ¬(e.1 = 1 ∨ e.1 = -1) ∧ e.1 * e.1⁻¹ = 1 then
    some (v, gaussScore occ prot v (total - e.2))
  else none

theorem unitDesc_eq (l : LinExpr p) (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable)
    (v : Variable) :
    unitDesc (coeffIdx l.terms) l.terms.length occ prot v
      = (match l.trySolve v with | some _ => none | none => l.trySolveUnit v).map
          (fun xt : Variable × Expression p => (xt.1, pivotScore occ prot xt)) := by
  simp only [unitDesc, coeffIdx_coeff l v, coeffIdx_others l v]
  by_cases h1 : l.coeff v = 1
  · rw [if_neg (fun hc => hc.1 (Or.inl h1)), LinExpr.trySolve_eq_of_one l v h1]; rfl
  · by_cases h2 : l.coeff v = -1
    · rw [if_neg (fun hc => hc.1 (Or.inr h2)), LinExpr.trySolve_eq_of_negOne l v h1 h2]; rfl
    · rw [LinExpr.trySolve_eq_none l v (by rintro (h | h); exacts [h1 h, h2 h])]
      by_cases h3 : l.coeff v * (l.coeff v)⁻¹ = 1
      · rw [if_pos ⟨by rintro (h | h); exacts [h1 h, h2 h], h3⟩,
          LinExpr.trySolveUnit_eq_of l v h3,
          gaussScore_eq_pivotScore occ prot v (((l.others v).scale (-(l.coeff v)⁻¹)).toExpr)
            (l.others v).terms.length (LinExpr.toExpr_isVar _)
            (by rw [LinExpr.toExpr_varCount, LinExpr.scale_terms_length])]
        rfl
      · rw [if_neg (fun hc => h3 hc.2), LinExpr.trySolveUnit_eq_none l v h3]; rfl

/-- All pivot descriptors, `±1` first (mirroring `pm1PivotsOf ++ unitPivotsOf`). The coefficient/
    occurrence index is built once (O(terms)); each descriptor is then O(1). -/
def pivotDescs (l : LinExpr p) (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) :
    List (Variable × Nat) :=
  let idx := coeffIdx l.terms
  let total := l.terms.length
  (l.terms.map Prod.fst).filterMap (pm1Desc idx total occ prot)
    ++ (l.terms.map Prod.fst).filterMap (unitDesc idx total occ prot)

theorem pivotDescs_eq (c : Expression p) (l : LinExpr p) (hlin : linearize c = some l)
    (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) :
    pivotDescs l occ prot
      = (pm1PivotsOf c ++ unitPivotsOf c).map (fun xt => (xt.1, pivotScore occ prot xt)) := by
  show (l.terms.map Prod.fst).filterMap (pm1Desc (coeffIdx l.terms) l.terms.length occ prot)
      ++ (l.terms.map Prod.fst).filterMap (unitDesc (coeffIdx l.terms) l.terms.length occ prot)
      = (pm1PivotsOf c ++ unitPivotsOf c).map (fun xt => (xt.1, pivotScore occ prot xt))
  unfold pm1PivotsOf unitPivotsOf
  rw [hlin, List.map_append, map_filterMap, map_filterMap]
  congr 1
  · exact List.filterMap_congr (fun v _ => pm1Desc_eq l occ prot v)
  · exact List.filterMap_congr (fun v _ => unitDesc_eq l occ prot v)

/-- The cheapest solvable pivot of a constraint, building the solution only for the winner. -/
def fastBest (c : Expression p) (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) :
    Option (Variable × Expression p) :=
  match linearize c with
  | none => none
  | some l =>
      match (pivotDescs l occ prot).argmin Prod.snd with
      | none => none
      | some (x, _) =>
          match l.trySolve x with
          | some xt => some xt
          | none => l.trySolveUnit x

theorem LinExpr.trySolve_fst (l : LinExpr p) (v : Variable) (w : Variable × Expression p)
    (h : l.trySolve v = some w) : w.1 = v := by
  unfold LinExpr.trySolve at h
  split_ifs at h
  all_goals simp_all [Prod.ext_iff]

theorem LinExpr.trySolveUnit_fst (l : LinExpr p) (v : Variable) (w : Variable × Expression p)
    (h : l.trySolveUnit v = some w) : w.1 = v := by
  unfold LinExpr.trySolveUnit at h
  split_ifs at h
  all_goals simp_all [Prod.ext_iff]

theorem mem_pm1_trySolve (c : Expression p) (l : LinExpr p) (hlin : linearize c = some l)
    (w : Variable × Expression p) (h : w ∈ pm1PivotsOf c) : l.trySolve w.1 = some w := by
  unfold pm1PivotsOf at h
  rw [hlin] at h
  obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
  rw [LinExpr.trySolve_fst l v w hv]; exact hv

theorem mem_unit_trySolveUnit (c : Expression p) (l : LinExpr p) (hlin : linearize c = some l)
    (w : Variable × Expression p) (h : w ∈ unitPivotsOf c) :
    l.trySolve w.1 = none ∧ l.trySolveUnit w.1 = some w := by
  unfold unitPivotsOf at h
  rw [hlin] at h
  obtain ⟨v, _, hv⟩ := List.mem_filterMap.1 h
  cases hts : l.trySolve v with
  | some r => rw [hts] at hv; simp at hv
  | none =>
      rw [hts] at hv
      rw [LinExpr.trySolveUnit_fst l v w hv]
      exact ⟨hts, hv⟩

theorem fastBest_eq (c : Expression p) (occ : Std.HashMap Variable Nat)
    (prot : Std.HashSet Variable) :
    fastBest c occ prot = (pm1PivotsOf c ++ unitPivotsOf c).argmin (pivotScore occ prot) := by
  unfold fastBest
  split
  · next hlin => simp [pm1PivotsOf, unitPivotsOf, hlin]
  · next l hlin =>
      rw [pivotDescs_eq c l hlin occ prot,
        argmin_map_key (fun xt => (xt.1, pivotScore occ prot xt)) (pivotScore occ prot) Prod.snd
          (fun _ => rfl)]
      cases hA : (pm1PivotsOf c ++ unitPivotsOf c).argmin (pivotScore occ prot) with
      | none => simp
      | some w =>
          simp only [Option.map_some]
          have hmem : w ∈ pm1PivotsOf c ++ unitPivotsOf c :=
            List.argmin_mem (by rw [hA]; exact Option.mem_some_self w)
          rcases List.mem_append.1 hmem with hp | hu
          · rw [mem_pm1_trySolve c l hlin w hp]
          · obtain ⟨hn, hs⟩ := mem_unit_trySolveUnit c l hlin w hu
            rw [hn, hs]

/-! ### Allocation-free best-descriptor scan

`fastBest` above is proved correct through `pivotDescs`, which materialises two descriptor lists
(`±1` then unit) and `argmin`s their append. `bestDesc` computes the same winner with **no
intermediate lists**: two ordered left-folds over `l.terms` (the `±1` class first, the unit class
seeded with the first fold's winner) that keep only the current best `(variable, score)`
descriptor, replacing it solely on a *strictly smaller* score — so `List.argmin`'s first-minimum
tie behaviour is preserved, including repeated occurrences of the same variable, and the two folds
preserve candidate-class precedence. `bestDesc_eq` proves it equals `(pivotDescs l occ prot).argmin
Prod.snd`, and `fastBestFold`/`fastBestFold_eq` lift that to `fastBest`; a `@[csimp]` installs it as
the compiled implementation. The correspondence is short because `List.argmin` is *itself* a left
fold of `List.argAux`, so `argMerge` is definitionally that step (`argmin_eq_foldl`) and the rest is
`List.foldl_append` plus a filterMap/fold fusion (`foldl_argMerge_filterMap`). -/

/-- One `argmin` fold step: keep incumbent `acc` unless the new element `b` scores strictly lower.
    Definitionally `List.argAux (fun b c => f b < f c)`, so `argmin = foldl argMerge none`. -/
def argMerge {α : Type*} (f : α → Nat) (acc : Option α) (b : α) : Option α :=
  match acc with
  | none => some b
  | some c => if f b < f c then some b else some c

theorem argmin_eq_foldl {α : Type*} (f : α → Nat) (l : List α) :
    l.argmin f = l.foldl (argMerge f) none := by
  show l.foldl (List.argAux fun b c => f b < f c) none = l.foldl (argMerge f) none
  congr 1
  funext acc b
  cases acc with
  | none => rfl
  | some c => simp only [argMerge, List.argAux]

/-- One term-scan fold step: classify the term's variable (`cl t.1`) and, if it yields a
    descriptor, merge it into the running best with `argMerge` (strict `<`). Named (rather than an
    inline lambda) so the fusion lemma below matches syntactically. -/
def descFoldStep (cl : Variable → Option (Variable × Nat)) (acc : Option (Variable × Nat))
    (t : Variable × ZMod p) : Option (Variable × Nat) :=
  match cl t.1 with | none => acc | some c => argMerge Prod.snd acc c

/-- Fuse the classifier into the `argMerge` fold: scanning terms with `descFoldStep cl` equals
    folding `argMerge` over the classified variables `(terms.map Prod.fst).filterMap cl` — the exact
    shape of one `pivotDescs` half — so no descriptor list is materialised at runtime. -/
theorem foldl_descFoldStep (cl : Variable → Option (Variable × Nat))
    (terms : List (Variable × ZMod p)) :
    ∀ init : Option (Variable × Nat),
      terms.foldl (descFoldStep cl) init
        = ((terms.map Prod.fst).filterMap cl).foldl (argMerge Prod.snd) init := by
  induction terms with
  | nil => intro init; rfl
  | cons t rest ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons]
      cases hcl : cl t.1 with
      | none =>
          rw [List.filterMap_cons_none hcl,
            show descFoldStep cl init t = init from by simp only [descFoldStep, hcl]]
          exact ih init
      | some c =>
          rw [List.filterMap_cons_some hcl, List.foldl_cons,
            show descFoldStep cl init t = argMerge Prod.snd init c from by
              simp only [descFoldStep, hcl]]
          exact ih (argMerge Prod.snd init c)

/-- The winning pivot descriptor of a linear form via two ordered `argMerge` folds over the terms:
    `±1` candidates (`pm1Desc`) first, then unit candidates (`unitDesc`) seeded with the first
    winner. `coeffIdx`/`total` are computed once and passed in, so no descriptor list is built. -/
def bestDescAux (idx : Std.HashMap Variable (ZMod p × Nat)) (total : Nat)
    (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable)
    (terms : List (Variable × ZMod p)) : Option (Variable × Nat) :=
  terms.foldl (descFoldStep (unitDesc idx total occ prot))
    (terms.foldl (descFoldStep (pm1Desc idx total occ prot)) none)

def bestDesc (l : LinExpr p) (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) :
    Option (Variable × Nat) :=
  bestDescAux (coeffIdx l.terms) l.terms.length occ prot l.terms

theorem bestDesc_eq (l : LinExpr p) (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) :
    bestDesc l occ prot = (pivotDescs l occ prot).argmin Prod.snd := by
  simp only [bestDesc, bestDescAux, pivotDescs, argmin_eq_foldl]
  rw [List.foldl_append,
    foldl_descFoldStep (pm1Desc (coeffIdx l.terms) l.terms.length occ prot) l.terms none,
    foldl_descFoldStep (unitDesc (coeffIdx l.terms) l.terms.length occ prot) l.terms _]

/-- Runtime pivot selection: like `fastBest`, but choosing the winner via `bestDesc`'s
    allocation-free folds rather than `pivotDescs`'s `argmin`. Installed as `fastBest`'s compiled
    form by the `@[csimp]` below, so `gaussLoop`'s proof (which mentions `fastBest`) is untouched. -/
def fastBestFold (c : Expression p) (occ : Std.HashMap Variable Nat)
    (prot : Std.HashSet Variable) : Option (Variable × Expression p) :=
  match linearize c with
  | none => none
  | some l =>
      match bestDesc l occ prot with
      | none => none
      | some (x, _) =>
          match l.trySolve x with
          | some xt => some xt
          | none => l.trySolveUnit x

theorem fastBestFold_eq (c : Expression p) (occ : Std.HashMap Variable Nat)
    (prot : Std.HashSet Variable) : fastBestFold c occ prot = fastBest c occ prot := by
  simp only [fastBestFold, fastBest, bestDesc_eq]

@[csimp] theorem fastBest_eq_fastBestFold : @fastBest = @fastBestFold := by
  funext p c occ prot; exact (fastBestFold_eq c occ prot).symm

/-- Process the pending constraints: reduce each by the current solutions, adopt the cheapest
    solvable pivot (if any), resolve it into the stored solutions, and continue. Structure of
    the per-step proof: the reduced constraint evaluates like the original (which a satisfying
    assignment makes `0`), so the chosen candidate's `pm1PivotsOf`/`unitPivotsOf` soundness
    applies; stored solutions stay entailed under resolution because `env x = t.eval env`
    makes `Function.update` a no-op. -/
def gaussLoop (cs : ConstraintSystem p) (bs : BusSemantics p)
    (occ : Std.HashMap Variable Nat) (prot : Std.HashSet Variable) :
    (pending : List (Expression p)) → (∀ c ∈ pending, c ∈ cs.algebraicConstraints) →
    Solved p cs bs → Solved p cs bs
  | [], _, σ => σ
  | c :: rest, hmem, σ =>
    let hrest := fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc')
    let c' := (c.substF σ.fn).normalize
    match hbest : fastBest c' occ prot with
    | none => gaussLoop cs bs occ prot rest hrest σ
    | some (x, t) =>
        -- `fastBest` picks exactly the old `argmin` pivot (`fastBest_eq`), so every downstream
        -- soundness/vars proof is discharged against the original candidate-list membership.
        have hbest' : (pm1PivotsOf c' ++ unitPivotsOf c').argmin (pivotScore occ prot) = some (x, t) :=
          (fastBest_eq c' occ prot).symm.trans hbest
        have hx : ∀ env, cs.satisfies bs env → env x = t.eval env := by
          intro env hsat
          have hc0 : c.eval env = 0 := hsat.1 c (hmem c (List.mem_cons_self ..))
          have hc' : c'.eval env = 0 := by
            show ((c.substF σ.fn).normalize).eval env = 0
            rw [σ.eval_reduce c env hsat, hc0]
          rcases List.mem_append.1 (List.argmin_mem hbest') with h | h
          · exact pm1PivotsOf_sound c' x t h env hc'
          · exact unitPivotsOf_sound c' x t h env hc'
        -- every variable of the reduced constraint (hence of any pivot solved from it) is a
        -- variable of `cs`: reduction only substitutes stored solutions (all in `cs`) and folds
        have hc'vars : ∀ z ∈ c'.vars, z ∈ cs.vars := by
          intro z hz
          rcases Expression.substF_vars σ.fn c z (Expression.normalize_vars _ z hz) with
            h2 | ⟨y', t', hft', hzt'⟩
          · exact ConstraintSystem.mem_vars_of_constraint (hmem c (List.mem_cons_self ..)) h2
          · exact σ.varsIn y' t' hft' z hzt'
        have htvars : ∀ z ∈ t.vars, z ∈ cs.vars := by
          intro z hz
          rcases List.mem_append.1 (List.argmin_mem hbest') with h | h
          · exact hc'vars z (pm1PivotsOf_vars c' x t h z hz)
          · exact hc'vars z (unitPivotsOf_vars c' x t h z hz)
        -- resolve `x` out of the stored solutions, then store `x := t`. Only the keys in `x`'s
        -- reverse-dependency bucket can mention `x`; re-check `mentions` (buckets may be stale).
        -- gather the stored solutions mentioning `x` from `x`'s reverse-dependency bucket. By
        -- `mem_touchedOf` this is exactly the current solutions mentioning `x` (the full-map scan).
        let touched := σ.touchedOf x
        have htouched : ∀ y s, (y, s) ∈ touched → σ.map[y]? = some s :=
          fun y s hys => ((σ.mem_touchedOf x y s).1 hys).1
        let pairs := touched.map (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)]
        have hpairs : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env := by
          intro env hsat yt hyt
          rcases List.mem_append.1 hyt with h | h
          · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 h
            have hmemys : σ.map[y]? = some s := htouched y s hys
            have hy : env y = s.eval env := σ.sound env hsat y s hmemys
            have hxe : env x = t.eval env := hx env hsat
            show env y = ((s.subst x t).normalize).eval env
            rw [Expression.normalize_eval, Expression.eval_subst, ← hxe,
              Function.update_eq_self, hy]
          · obtain rfl : yt = (x, t) := by simpa using h
            exact hx env hsat
        have hpairsV : ∀ yt ∈ pairs, ∀ z ∈ yt.2.vars, z ∈ cs.vars := by
          intro yt hyt z hz
          rcases List.mem_append.1 hyt with h | h
          · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 h
            have hmemys : σ.map[y]? = some s := htouched y s hys
            rcases Expression.subst_vars s x t z (Expression.normalize_vars _ z hz) with h2 | h2
            · exact σ.varsIn y s hmemys z h2
            · exact htvars z h2
          · obtain rfl : yt = (x, t) := by simpa using h
            exact htvars z hz
        gaussLoop cs bs occ prot rest hrest (σ.insertAll pairs hpairs hpairsV)

/-- The batch linear-elimination pass. Two sweeps over the constraints (so substitutions can
    unlock later pivots within one invocation), then a single full-system substitution. -/
def gaussElimPass : VerifiedPass p := fun cs bs =>
  let occ := occurrenceMap cs
  let prot := protectedVars cs bs
  let pending := cs.algebraicConstraints ++ cs.algebraicConstraints
  let σ := gaussLoop cs bs occ prot pending
    (fun _c hc => (List.mem_append.1 hc).elim id id) Solved.empty
  if σ.map.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs.substF σ.fn, [],
    cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)
      (fun y t hyt => σ.varsIn y t hyt)⟩
