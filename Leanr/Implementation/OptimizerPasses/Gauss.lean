import Leanr.Implementation.OptimizerPasses.SubstMap
import Leanr.Implementation.OptimizerPasses.Subst
import Leanr.Implementation.OptimizerPasses.Affine
import Leanr.Implementation.OptimizerPasses.Normalize

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

/-! ## The proof-carrying solution map -/

/-- A set of solved variables `x := t`, each entailed by every satisfying assignment of `cs`.
    The `Std.HashMap` makes both lookup during reduction and the final `substF` application
    cheap; the bundled proof is exactly the hypothesis `ConstraintSystem.substF_correct`
    consumes. -/
structure Solved (p : ℕ) (cs : ConstraintSystem p) (bs : BusSemantics p) where
  map : Std.HashMap Variable (Expression p)
  sound : ∀ env, cs.satisfies bs env → ∀ y t, map[y]? = some t → env y = t.eval env
  varsIn : ∀ (y : Variable) (t : Expression p), map[y]? = some t → ∀ z ∈ t.vars, z ∈ cs.vars

namespace Solved

variable {cs : ConstraintSystem p} {bs : BusSemantics p}

def empty : Solved p cs bs where
  map := ∅
  sound := by
    intro _ _ y t h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)
  varsIn := by
    intro y t h
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
              exact σ.varsIn y s hys }
      σ'.insertAll rest (fun env hsat yt hyt => H env hsat yt (List.mem_cons_of_mem _ hyt))
        (fun yt hyt => Hv yt (List.mem_cons_of_mem _ hyt))

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

/-! ## The elimination loop -/

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
    match hbest : (pm1PivotsOf c' ++ unitPivotsOf c').argmin (pivotScore occ prot) with
    | none => gaussLoop cs bs occ prot rest hrest σ
    | some (x, t) =>
        have hx : ∀ env, cs.satisfies bs env → env x = t.eval env := by
          intro env hsat
          have hc0 : c.eval env = 0 := hsat.1 c (hmem c (List.mem_cons_self ..))
          have hc' : c'.eval env = 0 := by
            show ((c.substF σ.fn).normalize).eval env = 0
            rw [σ.eval_reduce c env hsat, hc0]
          rcases List.mem_append.1 (List.argmin_mem hbest) with h | h
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
          rcases List.mem_append.1 (List.argmin_mem hbest) with h | h
          · exact hc'vars z (pm1PivotsOf_vars c' x t h z hz)
          · exact hc'vars z (unitPivotsOf_vars c' x t h z hz)
        -- resolve `x` out of the stored solutions, then store `x := t`
        let touched := σ.map.toList.filter (fun ys => ys.2.mentions x)
        let pairs := touched.map (fun ys => (ys.1, (ys.2.subst x t).normalize)) ++ [(x, t)]
        have hpairs : ∀ env, cs.satisfies bs env → ∀ yt ∈ pairs, env yt.1 = yt.2.eval env := by
          intro env hsat yt hyt
          rcases List.mem_append.1 hyt with h | h
          · obtain ⟨⟨y, s⟩, hys, rfl⟩ := List.mem_map.1 h
            have hmemys : σ.map[y]? = some s :=
              Std.HashMap.mem_toList_iff_getElem?_eq_some.1 (List.mem_of_mem_filter hys)
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
            have hmemys : σ.map[y]? = some s :=
              Std.HashMap.mem_toList_iff_getElem?_eq_some.1 (List.mem_of_mem_filter hys)
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
