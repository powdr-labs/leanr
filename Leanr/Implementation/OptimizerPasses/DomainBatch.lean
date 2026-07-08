import Leanr.Implementation.OptimizerPasses.DomainProp
import Leanr.Implementation.OptimizerPasses.Gauss

set_option autoImplicit false

/-! # Batch finite-domain propagation

`domainPropPass` substitutes one forced variable per invocation, and each invocation
re-derives every variable's domain by scanning all constraints and interactions — quadratic
on parsed machines. This pass does the same reasoning in one sweep:

1. Build a **domain table** once (`DomainTable`, a proof-carrying `Std.HashMap`): domains from
   product-of-affine-factor constraints (`rootsIn`) and from bus obligations with proven slot
   bounds (`interactionDomain`), keeping the smallest domain per variable.
2. For every constraint and every bus obligation, enumerate over the table's domains (same
   caps and checked certificates as `DomainProp.lean` — `checkForced`/`checkForcedBi` are
   reused verbatim) and *collect* every forced `(x, c)`.
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

/-- Does the assignment satisfy all covered constraints and survive all covered obligations? -/
def survivesAllM (bs : BusSemantics p) (es : List (Expression p))
    (bis : List (BusInteraction (Expression p))) (a : List (Variable × ZMod p)) : Bool :=
  es.all (fun e => decide (e.eval (envOf a) = 0)) &&
    bis.all (fun bi => interactionSurvives bs bi a)

/-- The constraints of the system whose variables all lie in `xs`. Uses the allocation-free
    `Expression.varsIn` (equivalent to `c.vars.all (· ∈ xs)`) so the per-target covered-item scan
    does not rebuild every constraint's variable list. -/
def coveredCs (cs : ConstraintSystem p) (xs : List Variable) : List (Expression p) :=
  cs.algebraicConstraints.filter (fun c => c.varsIn xs)

/-- The interactions of the system whose variables all lie in `xs` (allocation-free, as `coveredCs`). -/
def coveredBis (cs : ConstraintSystem p) (xs : List Variable) :
    List (BusInteraction (Expression p)) :=
  cs.busInteractions.filter (fun bi => bi.varsIn xs)

/-- Work cap for one joint enumeration: box size × number of covered targets. -/
def maxEnumWork : Nat := 524288

/-- Candidate forced values read off a **precomputed** survivor list (the enumerated assignments
    that satisfy every covered constraint/obligation): the variables on which all survivors agree,
    with the agreed value; when there are no survivors, every domain variable is (vacuously) forced
    to `0`. Taking the survivor list as input (rather than recomputing it) is what lets `forcedOver`
    enumerate + filter the box **once** per target rather than once per candidate variable. -/
def forcedFromSurvivors (doms : List (Variable × List (ZMod p)))
    (survivors : List (List (Variable × ZMod p))) : List (Variable × ZMod p) :=
  match survivors with
  | [] => (doms.map Prod.fst).map (fun x => (x, 0))
  | a₀ :: rest =>
    (doms.map Prod.fst).filterMap (fun x =>
      if rest.all (fun a => decide (envOf a x = envOf a₀ x)) then some (x, envOf a₀ x) else none)

/-- Soundness of the survivor-based certificate: if every surviving assignment (an enumerated
    assignment that passes all covered constraints/obligations) assigns `c` to `x`, then `x = c` is
    entailed. The restriction of a satisfying `env` to the domains is an enumerated assignment that
    survives, so it is one of the `survivors`; the certificate ranges only over the (precomputed)
    survivors, so `forcedOver` does not re-enumerate per candidate. -/
theorem forcedFromSurvivors_sound {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (xs : List Variable) (doms : List (Variable × List (ZMod p)))
    (hdoms : T.doms xs = some doms)
    (es : List (Expression p)) (bis : List (BusInteraction (Expression p)))
    (hes : es = coveredCs cs xs) (hbis : bis = coveredBis cs xs)
    (x : Variable) (c : ZMod p) (hx : x ∈ doms.map Prod.fst)
    (hforced : ((assignments doms).filter (survivesAllM bs es bis)).all
        (fun a => decide (envOf a x = c)) = true)
    (env : Variable → ZMod p) (hsat : cs.satisfies bs env) : env x = c := by
  subst hes; subst hbis
  have hkeys : doms.map Prod.fst = xs := T.doms_fst xs doms hdoms
  have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
    mem_assignments doms env (T.doms_sound xs doms hdoms env hsat)
  set a₀ := doms.map (fun yd => (yd.1, env yd.1)) with ha₀
  have hsurv : survivesAllM bs (coveredCs cs xs) (coveredBis cs xs) a₀ = true := by
    unfold survivesAllM
    rw [Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro e hemem
      rw [coveredCs, List.mem_filter] at hemem
      obtain ⟨hein, hall⟩ := hemem
      have hevars : ∀ v ∈ e.vars, v ∈ doms.map Prod.fst := by
        rw [hkeys]
        exact Expression.varsIn_sound xs e hall
      have : e.eval (envOf a₀) = e.eval env :=
        Expression.eval_congr e _ _ (fun y hy => envOf_map doms env y (hevars y hy))
      rw [decide_eq_true_iff, this]
      exact hsat.1 e hein
    · rw [List.all_eq_true]
      intro bi hbimem
      rw [coveredBis, List.mem_filter] at hbimem
      obtain ⟨hbiin, hbiall⟩ := hbimem
      have hbivars : ∀ v ∈ bi.vars, v ∈ doms.map Prod.fst := by
        rw [hkeys]
        exact BusInteraction.varsIn_sound xs bi hbiall
      have heval : bi.eval (envOf a₀) = bi.eval env :=
        BusInteraction.eval_congr bi _ _ (fun y hy => envOf_map doms env y (hbivars y hy))
      unfold interactionSurvives
      rw [heval]
      by_cases hm : (bi.eval env).multiplicity = 0
      · simp [hm]
      · simp [hm, hsat.2 bi hbiin hm]
  have ha0mem : a₀ ∈ (assignments doms).filter
      (survivesAllM bs (coveredCs cs xs) (coveredBis cs xs)) := List.mem_filter.2 ⟨hmem, hsurv⟩
  have hxc := of_decide_eq_true (List.all_eq_true.mp hforced a₀ ha0mem)
  rw [envOf_map doms env _ hx] at hxc
  exact hxc

/-- All checked forced constants over the variable set `xs` (the vars of one target
    constraint or interaction): enumerate the domain box once against everything the set
    covers, and re-check each agreed variable. Skips *uninformative* targets — no covered
    constraint and no covered interaction with a compound payload slot (a box constrained
    only by the raw range checks that produced the domains can never force anything). -/
def forcedOver {cs : ConstraintSystem p} {bs : BusSemantics p} (T : DomainTable p cs bs)
    (xs : List Variable) : List ((x : Variable) × { c : ZMod p //
      ∀ env, cs.satisfies bs env → env x = c }) :=
  match hdoms : T.doms xs with
  | none => []
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ maxEnumSize then
      let es := coveredCs cs xs
      let bis := coveredBis cs xs
      let informative := !es.isEmpty ||
        bis.any (fun bi => bi.payload.any (fun e => !(e.isVar || e.constValue?.isSome)))
      if informative && boxSize * (es.length + bis.length) ≤ maxEnumWork then
        -- Enumerate the box and filter to survivors **once**, then read off each candidate and
        -- re-check it against that survivor list — rather than re-enumerating the whole box once
        -- per candidate variable.
        let survivors := (assignments doms).filter (survivesAllM bs es bis)
        (forcedFromSurvivors doms survivors).filterMap (fun xc =>
          if hx : xc.1 ∈ doms.map Prod.fst then
            if hchk : survivors.all (fun a => decide (envOf a xc.1 = xc.2)) = true then
              some ⟨xc.1, xc.2, fun env hsat =>
                forcedFromSurvivors_sound T xs doms hdoms es bis rfl rfl xc.1 xc.2 hx hchk env hsat⟩
            else none
          else none)
      else []
    else []

/-! ## Collecting all forced values -/

/-- Canonical key of a variable set, for target deduplication. -/
def varSetKey (xs : List Variable) : String :=
  String.intercalate "\x00" ((xs.mergeSort (fun a b => compare a b != .gt)).map (fun x => x.name))

/-- Collect forced constants from joint enumerations of the given targets' variable sets,
    skipping variable sets already enumerated. -/
def collectForced {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) :
    List (List Variable) → Std.HashSet String → Solved p cs bs → Solved p cs bs
  | [], _, σ => σ
  | xs :: rest, seen, σ =>
    let key := varSetKey xs
    if seen.contains key then collectForced T rest seen σ
    else
      let found := forcedOver T xs
      collectForced T rest (seen.insert key)
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
    let σ := collectForced T targets ∅ Solved.empty
    if σ.map.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
    else ⟨cs.substF σ.fn, [],
      cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)
        (fun y t hyt => σ.varsIn y t hyt)⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩
