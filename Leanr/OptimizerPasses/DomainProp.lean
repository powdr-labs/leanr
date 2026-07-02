import Leanr.OptimizerPasses.Normalize
import Leanr.Utils.Size
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-! # Finite-domain propagation (boolean/one-hot case analysis)

The first pass that uses the *field* structure of `ZMod p` (`p` prime — decided at runtime, so
the optimizer's signature stays modulus-agnostic; for non-prime `p` the pass is the identity).

Many circuit variables are pinned to a *finite domain* by a constraint that is a product of
affine factors in that single variable: `x * (x - 1) = 0` forces `x ∈ {0, 1}` (booleanity),
`c * (255 - c) = 0` forces `c ∈ {0, 255}`, and so on. Over an integral domain a product is zero
only if a factor is, and an affine factor `a·x + b` with `a ≠ 0` has the single root `-b/a` —
this is where primality is needed (for composite moduli neither step holds).

Once domains are known, any constraint *all of whose variables have finite domains* can be
decided by exhaustive enumeration: evaluate it at every assignment in the domain product and
keep the satisfying ones. If all survivors agree that some variable `x` equals `c`, then `x = c`
is entailed by the whole system, and the proven `ConstraintSystem.subst_correct` eliminates `x`.
This is what SAT solvers call unit propagation, done natively on field elements — e.g. it
resolves the interaction of one-hot selector constraints that no affine reasoning can see:
from `x, y, z ∈ {0,1}` and `(1 + x + 2y + 3z) * (x + 2y + 3z) = 0` the only survivor is
`x = y = z = 0`.

The enumeration is capped (`maxEnumSize`) so the pass stays cheap; everything is decidable, and
the checked certificate (`checkForced`) is what the correctness proof consumes — the candidate
search itself carries no proof obligation. General: works for any bus semantics and any circuit
with finitely-pinned variables (boolean flags, one-hot selectors, small enums). -/

variable {p : ℕ}

/-! ## Evaluation depends only on a expression's variables -/

theorem Expression.eval_congr (e : Expression p) (env1 env2 : String → ZMod p)
    (h : ∀ x ∈ e.vars, env1 x = env2 x) : e.eval env1 = e.eval env2 := by
  induction e with
  | const n => rfl
  | var x => exact h x (by simp [Expression.vars])
  | add a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun x hx => h x (by simp [Expression.vars, hx])),
          ihb (fun x hx => h x (by simp [Expression.vars, hx]))]
  | mul a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun x hx => h x (by simp [Expression.vars, hx])),
          ihb (fun x hx => h x (by simp [Expression.vars, hx]))]

/-! ## Deriving a finite domain for a variable from one constraint -/

/-- Root list for the equation `c + Σ terms = 0`: `[]` for a nonzero constant (never zero),
    the unique root for a single term `a·x` with `a ≠ 0`, `none` otherwise ("cannot bound `x`").
    The root is computed with the ring's `Inv` and then *re-checked* (`a * r + c = 0`), so
    soundness never depends on inversion behaving well. -/
def rootsOfTerms (x : String) (c : ZMod p) : List (String × ZMod p) → Option (List (ZMod p))
  | [] => if c = 0 then none else some []
  | [(y, a)] =>
      let r := -(a⁻¹ * c)
      if y = x ∧ a ≠ 0 ∧ a * r + c = 0 then some [r] else none
  | _ :: _ :: _ => none

theorem rootsOfTerms_sound [Fact p.Prime] (x : String) (c : ZMod p)
    (ts : List (String × ZMod p)) (roots : List (ZMod p))
    (h : rootsOfTerms x c ts = some roots) (env : String → ZMod p)
    (hsum : c + (ts.map (fun t => t.2 * env t.1)).sum = 0) : env x ∈ roots := by
  rcases ts with _ | ⟨⟨y, a⟩, _ | ⟨t2, rest⟩⟩
  · -- no terms: a constant; `hsum` contradicts the nonzero guard
    simp only [rootsOfTerms] at h
    split_ifs at h with hc
    -- (the `c = 0` branch is closed by `split_ifs` itself: `h` is `none = some _`)
    exact absurd (by simpa using hsum) hc
  · -- a single term `a * y`: the unique (re-checked) root
    simp only [rootsOfTerms] at h
    split_ifs at h with hcond
    obtain ⟨rfl, ha, hr⟩ := hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
    have hxy : a * env y + c = 0 := by linear_combination hsum
    have hcancel : a * env y = a * (-(a⁻¹ * c)) := by
      rw [eq_neg_of_add_eq_zero_left hxy, ← eq_neg_of_add_eq_zero_left hr]
    simpa using mul_left_cancel₀ ha hcancel
  · exact absurd h (by simp [rootsOfTerms])

/-- Roots of an expression that is affine in (at most) the single variable `x`. -/
def affineRootsIn (x : String) (e : Expression p) : Option (List (ZMod p)) :=
  (linearize e).bind (fun l => rootsOfTerms x l.norm.const l.norm.terms)

theorem affineRootsIn_sound [Fact p.Prime] (x : String) (e : Expression p)
    (roots : List (ZMod p)) (h : affineRootsIn x e = some roots)
    (env : String → ZMod p) (he : e.eval env = 0) : env x ∈ roots := by
  simp only [affineRootsIn, Option.bind_eq_some_iff] at h
  obtain ⟨l, hlin, hroot⟩ := h
  have heval : l.norm.const + (l.norm.terms.map (fun t => t.2 * env t.1)).sum = 0 := by
    have h1 : l.norm.eval env = 0 := by
      rw [LinExpr.norm_eval, ← linearize_eval e l hlin]; exact he
    simpa [LinExpr.eval] using h1
  exact rootsOfTerms_sound x l.norm.const l.norm.terms roots hroot env heval

/-- Roots of a constraint viewed as a product of affine factors in the single variable `x`:
    if the constraint is zero, one factor is zero (integral domain), so `x` is one of the
    collected roots. `none` when a factor cannot be bounded. -/
def rootsIn (x : String) : Expression p → Option (List (ZMod p))
  | .const n => affineRootsIn x (.const n)
  | .var y => affineRootsIn x (.var y)
  | .add a b => affineRootsIn x (.add a b)
  | .mul a b =>
    match affineRootsIn x (.mul a b) with
    | some r => some r
    | none =>
      match rootsIn x a, rootsIn x b with
      | some ra, some rb => some (ra ++ rb)
      | _, _ => none

theorem rootsIn_sound [Fact p.Prime] (x : String) (e : Expression p) (roots : List (ZMod p))
    (h : rootsIn x e = some roots) (env : String → ZMod p) (he : e.eval env = 0) :
    env x ∈ roots := by
  induction e generalizing roots with
  | const n => exact affineRootsIn_sound x _ roots h env he
  | var y => exact affineRootsIn_sound x _ roots h env he
  | add a b _ _ => exact affineRootsIn_sound x _ roots h env he
  | mul a b iha ihb =>
    rw [rootsIn] at h
    split at h
    · rename_i r haff
      simp only [Option.some.injEq] at h
      subst h
      exact affineRootsIn_sound x _ _ haff env he
    · rename_i haff
      split at h
      · rename_i ra rb hra hrb
        simp only [Option.some.injEq] at h
        subst h
        have he' : a.eval env * b.eval env = 0 := he
        rcases mul_eq_zero.mp he' with hz | hz
        · exact List.mem_append.2 (Or.inl (iha ra hra hz))
        · exact List.mem_append.2 (Or.inr (ihb rb hrb hz))
      all_goals exact absurd h (by simp)

/-- The finite domain of `x` derived from the first constraint that bounds it. -/
def findDomain (all : List (Expression p)) (x : String) : Option (List (ZMod p)) :=
  match all with
  | [] => none
  | c :: rest =>
    match rootsIn x c with
    | some d => some d
    | none => findDomain rest x

theorem findDomain_sound [Fact p.Prime] (all : List (Expression p)) (x : String)
    (d : List (ZMod p)) (h : findDomain all x = some d) (env : String → ZMod p)
    (hall : ∀ c ∈ all, c.eval env = 0) : env x ∈ d := by
  induction all with
  | nil => exact absurd h (by simp [findDomain])
  | cons c rest ih =>
    rw [findDomain] at h
    cases hr : rootsIn x c with
    | some d' =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        exact h ▸ rootsIn_sound x c d' hr env (hall c (List.mem_cons_self ..))
    | none =>
        rw [hr] at h
        exact ih h (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))

/-- Domains for a list of variables, all-or-nothing. -/
def buildDoms (all : List (Expression p)) : List String → Option (List (String × List (ZMod p)))
  | [] => some []
  | x :: xs =>
    match findDomain all x, buildDoms all xs with
    | some d, some rest => some ((x, d) :: rest)
    | _, _ => none

theorem buildDoms_fst (all : List (Expression p)) (xs : List String)
    (doms : List (String × List (ZMod p))) (h : buildDoms all xs = some doms) :
    doms.map Prod.fst = xs := by
  induction xs generalizing doms with
  | nil => simp only [buildDoms, Option.some.injEq] at h; subst h; rfl
  | cons x rest ih =>
    rw [buildDoms] at h
    cases hd : findDomain all x with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : buildDoms all rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some doms' =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [ih doms' hr]

theorem buildDoms_sound [Fact p.Prime] (all : List (Expression p)) (xs : List String)
    (doms : List (String × List (ZMod p))) (h : buildDoms all xs = some doms)
    (env : String → ZMod p) (hall : ∀ c ∈ all, c.eval env = 0) :
    ∀ yd ∈ doms, env yd.1 ∈ yd.2 := by
  induction xs generalizing doms with
  | nil => simp only [buildDoms, Option.some.injEq] at h; subst h; simp
  | cons x rest ih =>
    rw [buildDoms] at h
    cases hd : findDomain all x with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : buildDoms all rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some doms' =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        intro yd hyd
        rcases List.mem_cons.1 hyd with rfl | hyd
        · exact findDomain_sound all x d hd env hall
        · exact ih doms' hr yd hyd

/-! ## Exhaustive enumeration over domain products -/

/-- All assignments in the cartesian product of the domains. -/
def assignments : List (String × List (ZMod p)) → List (List (String × ZMod p))
  | [] => [[]]
  | (x, d) :: rest => (assignments rest).flatMap (fun a => d.map (fun v => (x, v) :: a))

/-- Read an assignment as an environment (`0` for unassigned variables). -/
def envOf : List (String × ZMod p) → String → ZMod p
  | [], _ => 0
  | (x, v) :: rest, y => if y = x then v else envOf rest y

/-- The pointwise-in-domain restriction of `f` is one of the enumerated assignments. -/
theorem mem_assignments (doms : List (String × List (ZMod p))) (f : String → ZMod p)
    (h : ∀ yd ∈ doms, f yd.1 ∈ yd.2) :
    doms.map (fun yd => (yd.1, f yd.1)) ∈ assignments doms := by
  induction doms with
  | nil => simp [assignments]
  | cons yd rest ih =>
    obtain ⟨x, d⟩ := yd
    simp only [List.map_cons, assignments, List.mem_flatMap]
    refine ⟨rest.map (fun yd => (yd.1, f yd.1)),
            ih (fun yd hyd => h yd (List.mem_cons_of_mem _ hyd)), ?_⟩
    exact List.mem_map.2 ⟨f x, h (x, d) (List.mem_cons_self ..), rfl⟩

/-- On its own variables, the restriction environment agrees with `f`. -/
theorem envOf_map (doms : List (String × List (ZMod p))) (f : String → ZMod p) (y : String)
    (hy : y ∈ doms.map Prod.fst) :
    envOf (doms.map (fun yd => (yd.1, f yd.1))) y = f y := by
  induction doms with
  | nil => simp at hy
  | cons yd rest ih =>
    simp only [List.map_cons, envOf]
    by_cases hyx : y = yd.1
    · rw [if_pos hyx, hyx]
    · rw [if_neg hyx]
      refine ih ?_
      simp only [List.map_cons] at hy
      rcases List.mem_cons.1 hy with h | h
      · exact absurd h hyx
      · exact h

/-- The checked certificate: every enumerated assignment either falsifies the constraint or
    assigns `c` to `x`. -/
def checkForced (doms : List (String × List (ZMod p))) (e : Expression p) (x : String)
    (c : ZMod p) : Bool :=
  (assignments doms).all
    (fun a => !(decide (e.eval (envOf a) = 0)) || decide (envOf a x = c))

/-- Candidate search (proof-free; `checkForced` re-verifies): the value of each variable in the
    first surviving assignment, if all survivors agree on it. -/
def pickForced (doms : List (String × List (ZMod p))) (e : Expression p) :
    Option (String × ZMod p) :=
  match (assignments doms).filter (fun a => decide (e.eval (envOf a) = 0)) with
  | [] => (doms.map Prod.fst).head?.map (fun x => (x, 0))
  | a₀ :: survivors =>
    (doms.map Prod.fst).findSome? (fun x =>
      if survivors.all (fun a => decide (envOf a x = envOf a₀ x)) then some (x, envOf a₀ x)
      else none)

/-- Cap on the number of enumerated assignments, to keep the pass cheap. -/
def maxEnumSize : Nat := 4096

/-- Try to derive a forced value from one constraint: bound all its variables by finite domains
    (found anywhere in `all`), enumerate, and return a *checked* forced `(x, c)`. -/
def tryConstraint (all : List (Expression p)) (e : Expression p) : Option (String × ZMod p) :=
  match buildDoms all e.vars.dedup with
  | none => none
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ maxEnumSize then
      match pickForced doms e with
      | some (x, c) =>
          if decide (x ∈ doms.map Prod.fst) && checkForced doms e x c then some (x, c)
          else none
      | none => none
    else none

theorem tryConstraint_sound [Fact p.Prime] (all : List (Expression p)) (e : Expression p)
    (x : String) (c : ZMod p) (h : tryConstraint all e = some (x, c)) (he : e ∈ all)
    (env : String → ZMod p) (hall : ∀ c' ∈ all, c'.eval env = 0) : env x = c := by
  unfold tryConstraint at h
  split at h
  · exact absurd h (by simp)
  · rename_i doms hbd
    split_ifs at h with hsize
    · split at h
      · rename_i x' c' hpf
        split_ifs at h with hcheck
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [Bool.and_eq_true] at hcheck
          obtain ⟨hxmem, hforced⟩ := hcheck
          have hx := of_decide_eq_true hxmem
          -- the restriction of `env` to the domains is an enumerated assignment
          have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
            mem_assignments doms env (buildDoms_sound all _ doms hbd env hall)
          -- the constraint evaluates the same under the restriction
          have hcover : ∀ y ∈ e.vars, y ∈ doms.map Prod.fst := by
            rw [buildDoms_fst all _ doms hbd]
            intro y hy
            exact List.mem_dedup.2 hy
          have heval : e.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = e.eval env :=
            Expression.eval_congr e _ _ (fun y hy => envOf_map doms env y (hcover y hy))
          -- consume the certificate at the restriction
          have hcert := List.all_eq_true.mp hforced _ hmem
          have he0 : e.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = 0 := by
            rw [heval]; exact hall e he
          rcases (Bool.or_eq_true _ _).mp hcert with hbad | hgood
          · rw [Bool.not_eq_true'] at hbad
            exact absurd he0 (of_decide_eq_false hbad)
          · have hxc := of_decide_eq_true hgood
            rw [envOf_map doms env _ hx] at hxc
            exact hxc
      · exact absurd h (by simp)

/-- Scan the constraints for the first checked forced value. -/
def findForced (all : List (Expression p)) : List (Expression p) → Option (String × ZMod p)
  | [] => none
  | e :: rest =>
    match tryConstraint all e with
    | some r => some r
    | none => findForced all rest

theorem findForced_sound [Fact p.Prime] (all sub : List (Expression p)) (x : String)
    (c : ZMod p) (h : findForced all sub = some (x, c)) (hsub : ∀ e ∈ sub, e ∈ all)
    (env : String → ZMod p) (hall : ∀ c' ∈ all, c'.eval env = 0) : env x = c := by
  induction sub with
  | nil => exact absurd h (by simp [findForced])
  | cons e rest ih =>
    rw [findForced] at h
    cases htc : tryConstraint all e with
    | some r =>
        rw [htc] at h
        simp only [Option.some.injEq] at h
        subst h
        exact tryConstraint_sound all e x c htc (hsub e (List.mem_cons_self ..)) env hall
    | none =>
        rw [htc] at h
        exact ih h (fun e' he' => hsub e' (List.mem_cons_of_mem _ he'))

/-! ## The pass -/

/-- The finite-domain propagation pass: substitute one variable whose value is forced by
    domain enumeration. Requires `p` prime (decided at runtime; identity otherwise) — the only
    field-dependent step is "product zero ⇒ some affine factor zero ⇒ unique root". -/
def domainPropPass : VerifiedPass p := fun cs bs =>
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    match hf : findForced cs.algebraicConstraints cs.algebraicConstraints with
    | some (x, c) =>
        ⟨cs.subst x (.const c),
         cs.subst_correct x (.const c) bs (fun env hsat =>
           findForced_sound cs.algebraicConstraints cs.algebraicConstraints x c hf
             (fun _ he => he) env (fun c' hc' => hsat.1 c' hc'))⟩
    | none => ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
  else ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
