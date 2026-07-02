import Leanr.OptimizerPasses.DomainProp
import Leanr.OptimizerPasses.Gauss

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
  map : Std.HashMap String (List (ZMod p))
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
def insertEntry (T : DomainTable p cs bs) (x : String) (d : List (ZMod p))
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
def doms (T : DomainTable p cs bs) : List String → Option (List (String × List (ZMod p)))
  | [] => some []
  | x :: xs =>
    match T.map[x]?, T.doms xs with
    | some d, some rest => some ((x, d) :: rest)
    | _, _ => none

theorem doms_fst (T : DomainTable p cs bs) (xs : List String)
    (ds : List (String × List (ZMod p))) (h : T.doms xs = some ds) : ds.map Prod.fst = xs := by
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

theorem doms_sound (T : DomainTable p cs bs) (xs : List String)
    (ds : List (String × List (ZMod p))) (h : T.doms xs = some ds) (env : String → ZMod p)
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
    let rec addVars (xs : List String) (T : DomainTable p cs bs) : DomainTable p cs bs :=
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
def payloadRawVars (bi : BusInteraction (Expression p)) : List String :=
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
    let rec addVars (xs : List String) (T : DomainTable p cs bs) : DomainTable p cs bs :=
      match xs with
      | [] => T
      | x :: xs =>
        match hr : interactionDomain bs facts bi x with
        | some d =>
            addVars xs (T.insertEntry x d
              (fun env hsat => interactionDomain_sound bs facts bi x d hr env
                (hsat.2.1 bi hbi)))
        | none => addVars xs T
    addBusDoms facts rest hrest (addVars (payloadRawVars bi).dedup T)

/-! ## Enumeration against the table -/

/-- `tryConstraint` against the table: derive a checked forced `(x, c)` from one constraint. -/
def tryConstraintT {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (e : Expression p) : Option (String × ZMod p) :=
  match T.doms e.vars.dedup with
  | none => none
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ maxEnumSize then
      match pickForced doms e with
      | some (x, c) =>
          if decide (x ∈ doms.map Prod.fst) && checkForced doms e x c then some (x, c)
          else none
      | none => none
    else none

theorem tryConstraintT_sound {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (e : Expression p) (x : String) (c : ZMod p)
    (h : tryConstraintT T e = some (x, c)) (he : e ∈ cs.algebraicConstraints)
    (env : String → ZMod p) (hsat : cs.satisfies bs env) : env x = c := by
  unfold tryConstraintT at h
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
          have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
            mem_assignments doms env (T.doms_sound _ doms hbd env hsat)
          have hcover : ∀ y ∈ e.vars, y ∈ doms.map Prod.fst := by
            rw [T.doms_fst _ doms hbd]
            intro y hy
            exact List.mem_dedup.2 hy
          have heval : e.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = e.eval env :=
            Expression.eval_congr e _ _ (fun y hy => envOf_map doms env y (hcover y hy))
          have hcert := List.all_eq_true.mp hforced _ hmem
          have he0 : e.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = 0 := by
            rw [heval]; exact hsat.1 e he
          rcases (Bool.or_eq_true _ _).mp hcert with hbad | hgood
          · rw [Bool.not_eq_true'] at hbad
            exact absurd he0 (of_decide_eq_false hbad)
          · have hxc := of_decide_eq_true hgood
            rw [envOf_map doms env _ hx] at hxc
            exact hxc
      · exact absurd h (by simp)

/-- `tryInteraction` against the table: a checked forced `(x, c)` from one bus obligation. -/
def tryInteractionT {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (bi : BusInteraction (Expression p)) :
    Option (String × ZMod p) :=
  match T.doms bi.vars.dedup with
  | none => none
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ maxEnumSize then
      match pickForcedBi bs doms bi with
      | some (x, c) =>
          if decide (x ∈ doms.map Prod.fst) && checkForcedBi bs doms bi x c then some (x, c)
          else none
      | none => none
    else none

theorem tryInteractionT_sound {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) (bi : BusInteraction (Expression p)) (x : String) (c : ZMod p)
    (h : tryInteractionT T bi = some (x, c)) (hbi : bi ∈ cs.busInteractions)
    (env : String → ZMod p) (hsat : cs.satisfies bs env) : env x = c := by
  unfold tryInteractionT at h
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
          have hmem : doms.map (fun yd => (yd.1, env yd.1)) ∈ assignments doms :=
            mem_assignments doms env (T.doms_sound _ doms hbd env hsat)
          have hcover : ∀ y ∈ bi.vars, y ∈ doms.map Prod.fst := by
            rw [T.doms_fst _ doms hbd]
            intro y hy
            exact List.mem_dedup.2 hy
          have heval : bi.eval (envOf (doms.map (fun yd => (yd.1, env yd.1)))) = bi.eval env :=
            BusInteraction.eval_congr bi _ _ (fun y hy => envOf_map doms env y (hcover y hy))
          have hsurv : interactionSurvives bs bi (doms.map (fun yd => (yd.1, env yd.1)))
              = true := by
            unfold interactionSurvives
            rw [heval]
            by_cases hm : (bi.eval env).multiplicity = 0
            · simp [hm]
            · simp [hm, hsat.2.1 bi hbi hm]
          have hcert := List.all_eq_true.mp hforced _ hmem
          rcases (Bool.or_eq_true _ _).mp hcert with hbad | hgood
          · rw [Bool.not_eq_true'] at hbad
            rw [hsurv] at hbad
            exact absurd hbad (by simp)
          · have hxc := of_decide_eq_true hgood
            rw [envOf_map doms env _ hx] at hxc
            exact hxc
      · exact absurd h (by simp)

/-! ## Collecting all forced values -/

/-- Collect forced constants from all constraints into a `Solved` map. -/
def collectForcedC {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) :
    (pending : List (Expression p)) → (∀ c ∈ pending, c ∈ cs.algebraicConstraints) →
    Solved p cs bs → Solved p cs bs
  | [], _, σ => σ
  | e :: rest, hmem, σ =>
    let hrest := fun c' h => hmem c' (List.mem_cons_of_mem _ h)
    match htry : tryConstraintT T e with
    | some (x, v) =>
        collectForcedC T rest hrest (σ.insertAll [(x, .const v)]
          (by
            intro env hsat yt hyt
            obtain rfl : yt = (x, Expression.const v) := by simpa using hyt
            exact tryConstraintT_sound T e x v htry (hmem e (List.mem_cons_self ..)) env hsat))
    | none => collectForcedC T rest hrest σ

/-- Collect forced constants from all bus obligations into a `Solved` map. -/
def collectForcedI {cs : ConstraintSystem p} {bs : BusSemantics p}
    (T : DomainTable p cs bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) →
    Solved p cs bs → Solved p cs bs
  | [], _, σ => σ
  | bi :: rest, hmem, σ =>
    let hrest := fun bi' h => hmem bi' (List.mem_cons_of_mem _ h)
    match htry : tryInteractionT T bi with
    | some (x, v) =>
        collectForcedI T rest hrest (σ.insertAll [(x, .const v)]
          (by
            intro env hsat yt hyt
            obtain rfl : yt = (x, Expression.const v) := by simpa using hyt
            exact tryInteractionT_sound T bi x v htry (hmem bi (List.mem_cons_self ..))
              env hsat))
    | none => collectForcedI T rest hrest σ

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
    let σ := collectForcedI T cs.busInteractions (fun _ h => h)
      (collectForcedC T cs.algebraicConstraints (fun _ h => h) Solved.empty)
    if σ.map.isEmpty then ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
    else ⟨cs.substF σ.fn,
      cs.substF_correct σ.fn bs (fun env hsat y t hyt => σ.sound env hsat y t hyt)⟩
  else ⟨cs, cs.equivalentTo_refl bs, _root_.id⟩
