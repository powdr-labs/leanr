import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.Gauss

set_option autoImplicit false

/-! # Batch finite-domain propagation

`domainPropPass` substitutes one forced variable per invocation, and each invocation
re-derives every variable's domain by scanning all constraints and interactions — quadratic
on parsed machines. This pass does the same reasoning in one sweep:

1. Build a **domain table** once (`DomainTable`, a proof-carrying `Std.HashMap`): domains from
   product-of-affine-factor constraints (`rootsIn`) and from bus obligations with proven slot
   bounds (`interactionDomain`), keeping the smallest domain per variable.
2. For every constraint and every bus obligation, scan the box of the table's domains once
   (same caps as `DomainProp.lean`) with `scanInit`/`scanWith` — a fold that keeps the list of
   candidates every surviving point so far agrees on and **aborts as soon as it is empty** —
   and *collect* every forced `(x, c)`; the completed scan is itself the checked certificate
   (`scanInit_some`).
3. Substitute all of them in a single traversal (the `Solved`/`substF` machinery from
   `Gauss.lean`/`SubstMap.lean`; constant solutions need no resolution).

All certificates are checked against the *same* input system, so the collected entailments
hold simultaneously and one batch substitution is sound. Prime `p` only (decided at runtime,
like `domainPropPass`); identity otherwise. -/

variable {p : ℕ}

/-! ## The proof-carrying domain table -/

/-- Finite domains for variables, each entailed by every satisfying assignment of `cs`. -/
structure DomainTable (p : ℕ) (cs : ConstraintSystem p) (bs : BusSemantics p) where
  map : Std.HashMap Variable (List (ZMod p))
  sound : ∀ env, cs.satisfies bs env → ∀ x d, map[x]? = some d → env x ∈ d

namespace DomainTable

variable {cs : ConstraintSystem p} {bs : BusSemantics p}

def empty : DomainTable p cs bs where
  map := ∅
  sound := by
    intro _ _ x d h
    rw [Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)

/-- Insert an entailed domain, keeping the smaller of two candidate domains for a variable. -/
def insertEntry (T : DomainTable p cs bs) (x : Variable) (d : List (ZMod p))
    (h : ∀ env, cs.satisfies bs env → env x ∈ d) : DomainTable p cs bs :=
  let keep : Bool := match T.map[x]? with
    | some d0 => decide (d.length < d0.length)
    | none => true
  if keep then
    { map := T.map.insert x d,
      sound := by
        intro env hsat y e hye
        rw [Std.HashMap.getElem?_insert] at hye
        by_cases hxy : (x == y) = true
        · rw [if_pos hxy] at hye
          have hxy' : x = y := by simpa using hxy
          have hde : d = e := by simpa using hye
          subst hxy'; subst hde
          exact h env hsat
        · rw [if_neg hxy] at hye
          exact T.sound env hsat y e hye }
  else T

/-- The table's domains for a variable list, all-or-nothing (mirrors `buildDoms`). -/
def doms (T : DomainTable p cs bs) : List Variable → Option (List (Variable × List (ZMod p)))
  | [] => some []
  | x :: xs =>
    match T.map[x]?, T.doms xs with
    | some d, some rest => some ((x, d) :: rest)
    | _, _ => none

theorem doms_fst (T : DomainTable p cs bs) (xs : List Variable)
    (ds : List (Variable × List (ZMod p))) (h : T.doms xs = some ds) : ds.map Prod.fst = xs := by
  induction xs generalizing ds with
  | nil => simp only [doms, Option.some.injEq] at h; subst h; rfl
  | cons x rest ih =>
    rw [doms] at h
    cases hd : T.map[x]? with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : T.doms rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some ds' =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [ih ds' hr]

theorem doms_sound (T : DomainTable p cs bs) (xs : List Variable)
    (ds : List (Variable × List (ZMod p))) (h : T.doms xs = some ds) (env : Variable → ZMod p)
    (hsat : cs.satisfies bs env) : ∀ yd ∈ ds, env yd.1 ∈ yd.2 := by
  induction xs generalizing ds with
  | nil => simp only [doms, Option.some.injEq] at h; subst h; simp
  | cons x rest ih =>
    rw [doms] at h
    cases hd : T.map[x]? with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some d =>
      cases hr : T.doms rest with
      | none => rw [hd, hr] at h; exact absurd h (by simp)
      | some ds' =>
        rw [hd, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        intro yd hyd
        rcases List.mem_cons.1 hyd with rfl | hyd
        · exact T.sound env hsat x d hd
        · exact ih ds' hr yd hyd

end DomainTable

/-! ## Building the table -/

/-- Constraint-sourced domains: for each constraint that is a product of affine factors in a
    single variable (up to 3 distinct variables tried), record the root domains. -/
def addConstraintDoms [Fact p.Prime] {cs : ConstraintSystem p} {bs : BusSemantics p} :
    (pending : List (Expression p)) → (∀ c ∈ pending, c ∈ cs.algebraicConstraints) →
    DomainTable p cs bs → DomainTable p cs bs
  | [], _, T => T
  | c :: rest, hmem, T =>
    let hc := hmem c (List.mem_cons_self ..)
    let hrest := fun c' h => hmem c' (List.mem_cons_of_mem _ h)
    let rec addVars (xs : List Variable) (T : DomainTable p cs bs) : DomainTable p cs bs :=
      match xs with
      | [] => T
      | x :: xs =>
        match hr : rootsIn x c with
        | some d =>
            addVars xs (T.insertEntry x d
              (fun env hsat => rootsIn_sound x c d hr env (hsat.1 c hc)))
        | none => addVars xs T
    let vs := c.vars.dedup
    addConstraintDoms rest hrest (if vs.length ≤ 3 then addVars vs T else T)

/-- The raw-variable payload entries of an interaction. -/
def payloadRawVars (bi : BusInteraction (Expression p)) : List Variable :=
  bi.payload.filterMap (fun e => match e with | .var x => some x | _ => none)

/-- Bus-sourced domains: proven slot bounds on raw variable slots of interactions with
    constant nonzero multiplicity (mirrors `interactionDomain`). -/
def addBusDoms [NeZero p] {cs : ConstraintSystem p} {bs : BusSemantics p}
    (facts : BusFacts p bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) →
    DomainTable p cs bs → DomainTable p cs bs
  | [], _, T => T
  | bi :: rest, hmem, T =>
    let hbi := hmem bi (List.mem_cons_self ..)
    let hrest := fun bi' h => hmem bi' (List.mem_cons_of_mem _ h)
    let rec addVars (xs : List Variable) (T : DomainTable p cs bs) : DomainTable p cs bs :=
      match xs with
      | [] => T
      | x :: xs =>
        match hr : interactionDomain bs facts bi x with
        | some d =>
            addVars xs (T.insertEntry x d
              (fun env hsat => interactionDomain_sound bs facts bi x d hr env
                (hsat.2 bi hbi)))
        | none => addVars xs T
    addBusDoms facts rest hrest (addVars (payloadRawVars bi).dedup T)

/-! ## Joint enumeration against the table

A single constraint often does not force anything even though the *conjunction* of the
constraints over the same small variable set does (a one-hot selector: booleanity constraints
plus the sum and weighted-sum residues force every flag, but no single one of them has a
unique solution). For a target's variable set `xs`, we therefore enumerate the domain box
once and filter by **all** constraints and bus obligations whose variables lie inside `xs`,
then collect *every* variable on which the survivors agree. -/

/-! ### A faster environment lookup for enumeration

The enumeration evaluates covered constraints/interactions at *every* box point, and each
evaluation looks up every variable leaf via `envOf`, whose `if y = x` uses the derived
`DecidableEq Variable`. That instance compares the `name` **String** first (it is the first
field), so a lookup pays a full String comparison at essentially every entry it scans — the
dominant cost of the whole pass. `envOfFast` performs the identical lookup but tests the cheap
`powdrId?` discriminator first (`&&` short-circuits), skipping the String comparison for the
overwhelmingly common mismatched entries. It is extensionally equal to `envOf` (`envOfFast_eq`),
so every soundness lemma reduces to the `envOf` versions by rewriting with that one equation. -/

/-- `(y.powdrId? == x.powdrId? && y.name == x.name) = true` decides `y = x` (both fields agree),
    but checks the cheap `powdrId?` first. -/
theorem varFastEq_iff (y x : Variable) :
    ((y.powdrId? == x.powdrId? && y.name == x.name) = true) ↔ y = x := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨hp, hn⟩; cases y; cases x; simp_all
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- Enumeration-time variable lookup: extensionally `envOf`, but compares `powdrId?` before the
    `name` String so mismatched entries are rejected without a String comparison. -/
def envOfFast : List (Variable × ZMod p) → Variable → ZMod p
  | [], _ => 0
  | (x, v) :: rest, y =>
      if (y.powdrId? == x.powdrId? && y.name == x.name) = true then v else envOfFast rest y

theorem envOfFast_eq (a : List (Variable × ZMod p)) : envOfFast a = envOf a := by
  funext y
  induction a with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [envOfFast, envOf]
    by_cases hyx : y = x
    · rw [if_pos ((varFastEq_iff y x).mpr hyx), if_pos hyx]
    · rw [if_neg (fun h => hyx ((varFastEq_iff y x).mp h)), if_neg hyx]; exact ih

/-- Does the assignment satisfy all covered constraints and survive all covered obligations?
    Uses `envOfFast` (`= envOf`, see `envOfFast_eq`) for the per-point evaluation; the covered
    obligation check is `interactionSurvives` inlined against `envOfFast` (with the interaction
    evaluated once — the `let` is definitionally transparent to the proofs). -/
def survivesAllM (bs : BusSemantics p) (es : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (a : List (Variable × ZMod p)) : Bool :=
  es.all (fun e => decide (e.eval (envOfFast a) = 0)) &&
    bis.all (fun bi =>
      let v := bi.eval (envOfFast a)
      decide (v.multiplicity = 0) || !bs.violatesConstraint v)

/-- The constraints of the system whose variables all lie in `xs`. Uses the allocation-free
    `Expression.varsIn` (equivalent to `c.vars.all (· ∈ xs)`) so the per-target covered-item scan
    does not rebuild every constraint's variable list. -/
def coveredCs (cs : ConstraintSystem p) (xs : List Variable) : List (Expression p) :=
  cs.algebraicConstraints.filter (fun c => c.varsIn xs)

/-- The interactions of the system whose variables all lie in `xs` (allocation-free, as `coveredCs`),
    restricted to **stateless** buses. A stateful bus (memory / execution bridge) carries state, and
    its `violatesConstraint` never rejects a value assignment (it is checked via the memory
    discipline / `breaksInvariant`, not `violatesConstraint`), so its obligation
    (`multiplicity = 0 ∨ ¬violatesConstraint …`) survives *every* assignment. Such interactions
    therefore never eliminate a box point — dropping them from the enumeration is sound (the survivor
    filter only weakens) and, since they never filtered anything, leaves the survivor set (hence
    every forced value) unchanged, while avoiding their (large, e.g. memory) payload evaluations at
    every box point. -/
def coveredBis (bs : BusSemantics p) (cs : ConstraintSystem p) (xs : List Variable) :
    List (BusInteraction (Expression p)) :=
  cs.busInteractions.filter (fun bi => bi.varsIn xs && !bs.isStateful bi.busId)

/-- Work cap for one joint enumeration: box size × number of covered targets. -/
def maxEnumWork : Nat := 524288

/-- Is this constraint *redundant* for enumeration — identically zero on the box of its own
    variables' domains (from `T`)? Such a constraint is then zero on every larger box that contains
    those variables, so it never eliminates a survivor and can be dropped from every joint
    enumeration without changing any survivor set (only the wasted per-point evaluation is removed).
    The booleanity / range constraints that *defined* the domains are exactly of this form, and in
    practice they are the overwhelming majority of the covered constraints. `false` (keep it) when
    the sub-box is unbounded or too large to check cheaply. -/
def constraintRedundant {cs : ConstraintSystem p} {bs : BusSemantics p} (T : DomainTable p cs bs)
    (c : Expression p) : Bool :=
  match T.doms c.vars.dedup with
  | none => false
  | some d =>
    (d.map (fun yd => yd.2.length)).prod ≤ maxEnumSize &&
      (assignments d).all (fun a => decide (c.eval (envOfFast a) = 0))

/-- The single-pass box scan, after the first survivor: walk the remaining points, intersecting
    the list of `(x, c)` candidates on which every survivor seen so far agrees. The moment no
    candidate remains the scan **aborts** without visiting the remaining points — a target that
    forces nothing (the overwhelmingly common case) is abandoned after the first few disagreeing
    survivors instead of paying the full `box × items` evaluation cost. Claiming nothing needs no
    certificate, so the abort carries no proof obligation; for the candidates that do survive to
    the end, the scan itself is the checked certificate (`scanWith_agrees`). -/
def scanWith (bs : BusSemantics p) (es : List (Expression p))
    (bis : List (BusInteraction (Expression p))) :
    List (List (Variable × ZMod p)) → List (Variable × ZMod p) → List (Variable × ZMod p)
  | [], cands => cands
  | pt :: rest, cands =>
    if survivesAllM bs es bis pt = true then
      match cands.filter (fun xc => decide (envOfFast pt xc.1 = xc.2)) with
      | [] => []
      | c :: cands' => scanWith bs es bis rest (c :: cands')
    else scanWith bs es bis rest cands

/-- The box scan up to the first survivor, whose values over `keys` initialize the candidate
    list for `scanWith`. `none` means no point survived at all. -/
def scanInit (bs : BusSemantics p) (es : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (keys : List Variable) :
    List (List (Variable × ZMod p)) → Option (List (Variable × ZMod p))
  | [] => none
  | pt :: rest =>
    if survivesAllM bs es bis pt = true then
      some (scanWith bs es bis rest (keys.map (fun x => (x, envOfFast pt x))))
    else scanInit bs es bis keys rest

/-- The intersection certificate: every candidate returned by `scanWith` was among the input
    candidates and agrees with every surviving point of the scanned list. -/
theorem scanWith_agrees {bs : BusSemantics p} (es : List (Expression p))
    (bis : List (BusInteraction (Expression p)))
    (pts : List (List (Variable × ZMod p))) (cands : List (Variable × ZMod p)) :
    ∀ xc ∈ scanWith bs es bis pts cands, xc ∈ cands ∧
      ∀ pt ∈ pts, survivesAllM bs es bis pt = true → envOfFast pt xc.1 = xc.2 := by
  induction pts generalizing cands with
  | nil =>
    intro xc hxc
    exact ⟨hxc, by simp⟩
  | cons pt rest ih =>
    intro xc hxc
    rw [scanWith] at hxc
    by_cases hs : survivesAllM bs es bis pt = true
    · rw [if_pos hs] at hxc
      cases hfil : cands.filter (fun xc => decide (envOfFast pt xc.1 = xc.2)) with
      | nil => rw [hfil] at hxc; exact absurd hxc (by simp)
      | cons c cands' =>
        rw [hfil] at hxc
        obtain ⟨hmem, hagree⟩ := ih _ xc hxc
        rw [← hfil] at hmem
        have hf := List.mem_filter.1 hmem
        refine ⟨hf.1, ?_⟩
        intro pt' hpt' hs'
        rcases List.mem_cons.1 hpt' with rfl | hpt'
        · exact of_decide_eq_true hf.2
        · exact hagree pt' hpt' hs'
    · rw [if_neg hs] at hxc
      obtain ⟨hmem, hagree⟩ := ih _ xc hxc
      refine ⟨hmem, ?_⟩
      intro pt' hpt' hs'
      rcases List.mem_cons.1 hpt' with rfl | hpt'
      · exact absurd hs' hs
      · exact hagree pt' hpt' hs'

/-- The scan's certificate: every returned candidate `(x, c)` has `x ∈ keys` and agrees with
    every surviving point of the scanned list. -/
theorem scanInit_some {bs : BusSemantics p} (es : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (keys : List Variable)
    (pts : List (List (Variable × ZMod p))) (res : List (Variable × ZMod p))
    (h : scanInit bs es bis keys pts = some res) :
    ∀ xc ∈ res, xc.1 ∈ keys ∧
      ∀ pt ∈ pts, survivesAllM bs es bis pt = true → envOfFast pt xc.1 = xc.2 := by
  induction pts with
  | nil => exact absurd h (by simp [scanInit])
  | cons pt rest ih =>
    rw [scanInit] at h
    by_cases hs : survivesAllM bs es bis pt = true
    · rw [if_pos hs] at h
      simp only [Option.some.injEq] at h
      subst h
      intro xc hxc
      obtain ⟨hmem, hagree⟩ := scanWith_agrees es bis rest _ xc hxc
      obtain ⟨x, hxkeys, hxeq⟩ := List.mem_map.1 hmem
      constructor
      · rw [← hxeq]
        exact hxkeys
      · intro pt' hpt' hs'
        rcases List.mem_cons.1 hpt' with rfl | hpt'
        · rw [← hxeq]
        · exact hagree pt' hpt' hs'
    · rw [if_neg hs] at h
      intro xc hxc
      obtain ⟨hk, hagree⟩ := ih h xc hxc
      refine ⟨hk, ?_⟩
      intro pt' hpt' hs'
      rcases List.mem_cons.1 hpt' with rfl | hpt'
      · exact absurd hs' hs
      · exact hagree pt' hpt' hs'

/-- If the scan returns `none`, no enumerated point survived. -/
theorem scanInit_none {bs : BusSemantics p} (es : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (keys : List Variable)
    (pts : List (List (Variable × ZMod p)))
    (h : scanInit bs es bis keys pts = none) :
    ∀ pt ∈ pts, survivesAllM bs es bis pt = false := by
  induction pts with
  | nil => simp
  | cons pt rest ih =>
    rw [scanInit] at h
    by_cases hs : survivesAllM bs es bis pt = true
    · rw [if_pos hs] at h
      exact absurd h (by simp)
    · rw [if_neg hs] at h
      intro pt' hpt'
      rcases List.mem_cons.1 hpt' with rfl | hpt'
      · exact Bool.eq_false_iff.mpr hs
      · exact ih h pt' hpt'

/-- The restriction of a satisfying assignment to the target's domains survives every covered
    item: `es`/`bis` are only required to be members of the system covered by `xs` (via
    `hes`/`hbis`) — they may be any *sub-selection* of the covered items (e.g. after dropping
    redundant constraints or stateful obligations). -/
theorem restriction_survives {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (hdoms : T.doms xs = some doms)
    (es : List (Expression p)) (bis : List (BusInteraction (Expression p)))
    (hes : ∀ e ∈ es, e ∈ cs.algebraicConstraints ∧ e.varsIn xs = true)
    (hbis : ∀ bi ∈ bis, bi ∈ cs.busInteractions ∧ bi.varsIn xs = true)
    (env : Variable → ZMod p) (hsat : cs.satisfies bs env) :
    survivesAllM bs es bis (doms.map (fun yd => (yd.1, env yd.1))) = true := by
  have hkeys : doms.map Prod.fst = xs := T.doms_fst xs doms hdoms
  set a₀ := doms.map (fun yd => (yd.1, env yd.1)) with ha₀
  unfold survivesAllM
  simp only [envOfFast_eq]
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro e hemem
    obtain ⟨hein, hall⟩ := hes e hemem
    have hevars : ∀ v ∈ e.vars, v ∈ doms.map Prod.fst := by
      rw [hkeys]
      exact Expression.varsIn_sound xs e hall
    have : e.eval (envOf a₀) = e.eval env :=
      Expression.eval_congr e _ _ (fun y hy => envOf_map doms env y (hevars y hy))
    rw [decide_eq_true_iff, this]
    exact hsat.1 e hein
  · rw [List.all_eq_true]
    intro bi hbimem
    obtain ⟨hbiin, hbiall⟩ := hbis bi hbimem
    have hbivars : ∀ v ∈ bi.vars, v ∈ doms.map Prod.fst := by
      rw [hkeys]
      exact BusInteraction.varsIn_sound xs bi hbiall
    have heval : bi.eval (envOf a₀) = bi.eval env :=
      BusInteraction.eval_congr bi _ _ (fun y hy => envOf_map doms env y (hbivars y hy))
    rw [heval]
    by_cases hm : (bi.eval env).multiplicity = 0
    · simp [hm]
    · simp [hm, hsat.2 bi hbiin hm]

/-- Soundness of the scan-based certificate: a candidate returned by the full scan is entailed —
    the restriction of any satisfying `env` is an enumerated point that survives
    (`restriction_survives`), so the candidate agrees with it (`scanInit_some`). -/
theorem scanForced_sound {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (hdoms : T.doms xs = some doms)
    (es : List (Expression p)) (bis : List (BusInteraction (Expression p)))
    (hes : ∀ e ∈ es, e ∈ cs.algebraicConstraints ∧ e.varsIn xs = true)
    (hbis : ∀ bi ∈ bis, bi ∈ cs.busInteractions ∧ bi.varsIn xs = true)
    (res : List (Variable × ZMod p))
    (hscan : scanInit bs es bis (doms.map Prod.fst) (assignments doms) = some res)
    (xc : Variable × ZMod p) (hxc : xc ∈ res)
    (env : Variable → ZMod p) (hsat : cs.satisfies bs env) : env xc.1 = xc.2 := by
  have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
    mem_assignments doms env (T.doms_sound xs doms hdoms env hsat)
  have hsurv := restriction_survives T xs doms hdoms es bis hes hbis env hsat
  obtain ⟨hkey, hagree⟩ := scanInit_some es bis (doms.map Prod.fst)
    (assignments doms) res hscan xc hxc
  have hxc' := hagree _ hmem hsurv
  rw [envOfFast_eq, envOf_map doms env _ hkey] at hxc'
  exact hxc'

/-- When the scan finds no survivor at all, no satisfying assignment exists (its restriction
    would be a surviving enumerated point), so anything is entailed. -/
theorem scanNone_unsat {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (hdoms : T.doms xs = some doms)
    (es : List (Expression p)) (bis : List (BusInteraction (Expression p)))
    (hes : ∀ e ∈ es, e ∈ cs.algebraicConstraints ∧ e.varsIn xs = true)
    (hbis : ∀ bi ∈ bis, bi ∈ cs.busInteractions ∧ bi.varsIn xs = true)
    (hscan : scanInit bs es bis (doms.map Prod.fst) (assignments doms) = none)
    (env : Variable → ZMod p) (hsat : cs.satisfies bs env) : False := by
  have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
    mem_assignments doms env (T.doms_sound xs doms hdoms env hsat)
  have hsurv := restriction_survives T xs doms hdoms es bis hes hbis env hsat
  have hdead := scanInit_none es bis (doms.map Prod.fst) (assignments doms) hscan _ hmem
  rw [hsurv] at hdead
  exact absurd hdead (by simp)

/-- All checked forced constants over the variable set `xs` (the vars of one target
    constraint or interaction): scan the domain box once against everything the set
    covers (`scanInit`/`scanWith`), aborting early when nothing can be forced. Skips
    *uninformative* targets — no covered constraint and no covered interaction with a compound
    payload slot (a box constrained only by the raw range checks that produced the domains can
    never force anything).

    The covered constraints are drawn from `activeCs` (the system's constraints with the
    *redundant* ones — those identically zero on their own domain box — already removed): a
    redundant constraint can never eliminate a survivor, so restricting to `activeCs` changes no
    survivor set while removing almost all of the per-box-point constraint evaluations. Covered
    obligations likewise omit stateful buses (`coveredBis`). Both are just sub-selections of the
    covered items, which `scanForced_sound` accepts (`hactive`/membership). -/
def forcedOver {cs : ConstraintSystem p} {bs : BusSemantics p} (T : DomainTable p cs bs)
    (activeCs : List (Expression p)) (hactiveCs : ∀ c ∈ activeCs, c ∈ cs.algebraicConstraints)
    (xs : List Variable) : List ((x : Variable) × { c : ZMod p //
      ∀ env, cs.satisfies bs env → env x = c }) :=
  match hdoms : T.doms xs with
  | none => []
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ maxEnumSize then
      -- `esFull` (all covered constraints) drives the informativeness gate and the work cap, so
      -- exactly the same targets/boxes are enumerated as before the redundancy optimization. The
      -- survivor filter is evaluated only against the non-redundant subset `es`: dropping the
      -- redundant constraints — each identically zero on the box — leaves every survivor set (hence
      -- every forced value) unchanged while removing the wasted per-box-point evaluations. (The
      -- analogous drop for *obligations* is not worthwhile: an interaction's sub-box is large and
      -- its payload evaluation costly, and it is covered by few targets, so verifying its
      -- redundancy costs about what it would save.)
      let esFull := coveredCs cs xs
      let bis := coveredBis bs cs xs
      let es := activeCs.filter (fun c => c.varsIn xs)
      let informative := !esFull.isEmpty ||
        bis.any (fun bi => bi.payload.any (fun e => !(e.isVar || e.constValue?.isSome)))
      if informative && boxSize * (esFull.length + bis.length) ≤ maxEnumWork then
        have hes : ∀ e ∈ es, e ∈ cs.algebraicConstraints ∧ e.varsIn xs = true :=
          fun e he => ⟨hactiveCs e (List.mem_filter.1 he).1, (List.mem_filter.1 he).2⟩
        have hbis : ∀ bi ∈ bis, bi ∈ cs.busInteractions ∧ bi.varsIn xs = true := by
          intro bi hbi
          have hm := List.mem_filter.1 hbi
          have h2 := hm.2
          rw [Bool.and_eq_true] at h2
          exact ⟨hm.1, h2.1⟩
        match hscan : scanInit bs es bis (doms.map Prod.fst) (assignments doms) with
        | none =>
          -- no surviving point: the box is empty of solutions, everything is vacuously forced
          (doms.map Prod.fst).map (fun x => ⟨x, 0, fun env hsat =>
            (scanNone_unsat T xs doms hdoms es bis hes hbis hscan env hsat).elim⟩)
        | some res =>
          res.attach.map (fun xc => ⟨xc.1.1, xc.1.2, fun env hsat =>
            scanForced_sound T xs doms hdoms es bis hes hbis res hscan xc.1 xc.2 env hsat⟩)
      else []
    else []

/-! ## Collecting all forced values -/

/-- Canonical key of a variable set, for target deduplication. -/
def varSetKey (xs : List Variable) : String :=
  String.intercalate "\x00" ((xs.mergeSort (fun a b => compare a b != .gt)).map (fun x => x.name))

/-- Collect forced constants from joint enumerations of the given targets' variable sets,
    skipping variable sets already enumerated. `activeCs` (the non-redundant constraints) and its
    membership witness are threaded to `forcedOver`. -/
def collectForced {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (activeCs : List (Expression p))
    (hactiveCs : ∀ c ∈ activeCs, c ∈ cs.algebraicConstraints) :
    List (List Variable) → Std.HashSet String → Solved p cs bs → Solved p cs bs
  | [], _, σ => σ
  | xs :: rest, seen, σ =>
    let key := varSetKey xs
    if seen.contains key then collectForced T activeCs hactiveCs rest seen σ
    else
      let found := forcedOver T activeCs hactiveCs xs
      collectForced T activeCs hactiveCs rest (seen.insert key)
        (σ.insertAll (found.map (fun f => (f.1, .const f.2.val)))
          (by
            intro env hsat yt hyt
            obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hyt
            exact f.2.property env hsat)
          (by
            intro yt hyt z hz
            obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hyt
            simp [Expression.vars] at hz))

/-! ## The pass -/

/-- The batch finite-domain propagation pass: build the domain table once, collect every
    checked forced constant from constraints and bus obligations, substitute them all in one
    traversal. Prime `p` only (runtime-decided); identity otherwise. -/
def domainBatchPass : VerifiedPassW p := fun cs bs facts =>
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    let T : DomainTable p cs bs :=
      addBusDoms facts cs.busInteractions (fun _ h => h)
        (addConstraintDoms cs.algebraicConstraints (fun _ h => h) DomainTable.empty)
    let targets := cs.algebraicConstraints.map (fun e => e.vars.dedup) ++
      cs.busInteractions.map (fun bi => bi.vars.dedup)
    let activeCs := cs.algebraicConstraints.filter (fun c => !constraintRedundant T c)
    let σ := collectForced T activeCs (fun _ h => (List.mem_filter.1 h).1) targets ∅ Solved.empty
    if σ.map.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs.substF σ.fn, [],
      cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)
        (fun y t hyt => σ.varsIn y t hyt)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
