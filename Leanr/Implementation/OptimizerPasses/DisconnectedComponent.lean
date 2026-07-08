import Leanr.Implementation.OptimizerPasses.Basic
import Leanr.Implementation.OptimizerPasses.Rewrite
import Leanr.Implementation.OptimizerPasses.DomainProp
import Leanr.Utils.Size

set_option autoImplicit false

/-! # Disconnected-component removal

A *disconnected component* is a set of algebraic constraints and (stateless) bus interactions whose
variables never touch any **stateful** bus interaction — a self-contained subcircuit that produces
no observable side effect. Dropping it changes nothing observable *provided the subcircuit is
satisfiable*: soundness has to reconstruct a full satisfying assignment of the input from one of the
output, and that needs a witness for the dropped variables.

This pass finds such a component (by connectivity from the stateful buses), tries a concrete witness
(all variables `0`), and drops the component **only if** that witness provably satisfies every
dropped constraint (`c.eval w = 0`) and makes every dropped interaction non-violating
(`violatesConstraint (bi.eval w) = false`, checked against the given semantics at run time — the
same trick `guardDegree` uses, so it needs no extra audited knowledge). If the witness fails, the
pass is the identity.

Correctness is `dropComponent_correct`, which is fully VM-agnostic: it takes the partition
(`keepCon`/`keepBi`), a witness `w`, and the (checkable) facts that the removed part is satisfied by
`w`, is stateless, and shares no variable with the kept part. Soundness extends an output
assignment by `w` on the removed variables (they occur nowhere else); completeness and side-effect
preservation follow because the removed interactions are stateless. Field-free. -/

variable {p : ℕ}

/-! ## Side effects are unchanged when dropping stateless interactions

The evaluated stateful interactions of the filtered system (under `e1`) equal those of the original
(under `e2`), given that every dropped interaction is stateless and every *stateful* interaction
evaluates the same under `e1` and `e2`. -/
theorem sideEffects_drop_eq (bs : BusSemantics p) (keepBi : BusInteraction (Expression p) → Bool)
    (e1 e2 : String → ZMod p) (L : List (BusInteraction (Expression p)))
    (hst : ∀ bi ∈ L, keepBi bi = false → bs.isStateful bi.busId = false)
    (heq : ∀ bi ∈ L, bs.isStateful bi.busId = true → bi.eval e2 = bi.eval e1) :
    ((L.filter keepBi).filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := bi.eval e1; ((m.busId, m.payload), m.multiplicity))
      = (L.filter (fun bi => bs.isStateful bi.busId)).map
        (fun bi => let m := bi.eval e2; ((m.busId, m.payload), m.multiplicity)) := by
  induction L with
  | nil => rfl
  | cons bi rest ih =>
    have ihr := ih (fun b hb => hst b (List.mem_cons_of_mem _ hb))
                   (fun b hb => heq b (List.mem_cons_of_mem _ hb))
    by_cases hstate : bs.isStateful bi.busId = true
    · have hkeep : keepBi bi = true := by
        by_contra hk
        have hkf : keepBi bi = false := by simpa using hk
        rw [hst bi (List.mem_cons_self ..) hkf] at hstate
        exact absurd hstate (by simp)
      rw [List.filter_cons_of_pos hkeep,
          List.filter_cons_of_pos (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate,
          List.filter_cons_of_pos (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) hstate]
      simp only [List.map_cons]
      rw [heq bi (List.mem_cons_self ..) hstate, ihr]
    · have hns : bs.isStateful bi.busId = false := by simpa using hstate
      rw [List.filter_cons_of_neg (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) (by simp [hns])]
      by_cases hkeep : keepBi bi = true
      · rw [List.filter_cons_of_pos hkeep,
            List.filter_cons_of_neg (p := fun b : BusInteraction (Expression p) => bs.isStateful b.busId) (by simp [hns])]
        exact ihr
      · rw [List.filter_cons_of_neg hkeep]
        exact ihr

/-! ## The general correctness lemma -/

/-- Dropping a disconnected, witness-satisfiable component preserves correctness.

`keepCon`/`keepBi` mark the *kept* constraints/interactions; the rest are removed. The hypotheses
say: every removed item's variables are all "removed" variables (`remV`), the witness `w` satisfies
every removed constraint and makes every removed interaction non-violating, every removed
interaction is stateless, and every kept item uses only kept variables. -/
theorem dropComponent_correct (cs : ConstraintSystem p) (bs : BusSemantics p)
    (w : String → ZMod p) (remV : String → Bool)
    (keepCon : Expression p → Bool) (keepBi : BusInteraction (Expression p) → Bool)
    (hCrem : ∀ c ∈ cs.algebraicConstraints, keepCon c = false → ∀ x ∈ c.vars, remV x = true)
    (hCsat : ∀ c ∈ cs.algebraicConstraints, keepCon c = false → c.eval w = 0)
    (hCkeep : ∀ c ∈ cs.algebraicConstraints, keepCon c = true → ∀ x ∈ c.vars, remV x = false)
    (hBrem : ∀ bi ∈ cs.busInteractions, keepBi bi = false → ∀ x ∈ bi.vars, remV x = true)
    (hBsat : ∀ bi ∈ cs.busInteractions, keepBi bi = false →
        bs.violatesConstraint (bi.eval w) = false)
    (hBstateless : ∀ bi ∈ cs.busInteractions, keepBi bi = false → bs.isStateful bi.busId = false)
    (hBkeep : ∀ bi ∈ cs.busInteractions, keepBi bi = true → ∀ x ∈ bi.vars, remV x = false) :
    PassCorrect cs { algebraicConstraints := cs.algebraicConstraints.filter keepCon,
                     busInteractions := cs.busInteractions.filter keepBi } bs := by
  -- the merge: keep `env` on kept variables, use the witness on removed ones
  set m : (String → ZMod p) → (String → ZMod p) :=
    fun env x => if remV x = true then w x else env x with hm
  -- evaluation of a "removed" expression / interaction under the merge is the witness value
  have hmwC : ∀ env (e : Expression p), (∀ x ∈ e.vars, remV x = true) →
      e.eval (m env) = e.eval w := by
    intro env e he
    exact Expression.eval_congr e _ _ (fun x hx => by simp [hm, he x hx])
  have hmeC : ∀ env (e : Expression p), (∀ x ∈ e.vars, remV x = false) →
      e.eval (m env) = e.eval env := by
    intro env e he
    exact Expression.eval_congr e _ _ (fun x hx => by simp [hm, he x hx])
  have hmwB : ∀ env (bi : BusInteraction (Expression p)), (∀ x ∈ bi.vars, remV x = true) →
      bi.eval (m env) = bi.eval w := by
    intro env bi hbi
    exact BusInteraction.eval_congr bi _ _ (fun x hx => by simp [hm, hbi x hx])
  have hmeB : ∀ env (bi : BusInteraction (Expression p)), (∀ x ∈ bi.vars, remV x = false) →
      bi.eval (m env) = bi.eval env := by
    intro env bi hbi
    exact BusInteraction.eval_congr bi _ _ (fun x hx => by simp [hm, hbi x hx])
  -- a stateful interaction is always kept
  have hstKeep : ∀ bi ∈ cs.busInteractions, bs.isStateful bi.busId = true → keepBi bi = true := by
    intro bi hbi hstate
    by_contra hk
    rw [hBstateless bi hbi (by simpa using hk)] at hstate
    exact absurd hstate (by simp)
  -- extending a satisfying assignment of the output by the witness satisfies the input
  have keySat : ∀ env,
      (∀ c ∈ cs.algebraicConstraints.filter keepCon, c.eval env = 0) →
      (∀ bi ∈ cs.busInteractions.filter keepBi,
        (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) →
      cs.satisfies bs (m env) := by
    intro env hsc hsb
    refine ⟨fun c hc => ?_, fun bi hbi hne => ?_⟩
    · by_cases hk : keepCon c = true
      · rw [hmeC env c (hCkeep c hc hk)]
        exact hsc c (List.mem_filter.2 ⟨hc, hk⟩)
      · rw [hmwC env c (hCrem c hc (by simpa using hk))]
        exact hCsat c hc (by simpa using hk)
    · by_cases hk : keepBi bi = true
      · rw [hmeB env bi (hBkeep bi hbi hk)] at hne ⊢
        exact hsb bi (List.mem_filter.2 ⟨hbi, hk⟩) hne
      · rw [hmwB env bi (hBrem bi hbi (by simpa using hk))]
        exact hBsat bi hbi (by simpa using hk)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- soundness: out.implies cs
    intro env hsat
    refine ⟨m env, keySat env hsat.1 hsat.2, ?_⟩
    -- side effects: out under env = cs under (m env)
    have hse : ({ algebraicConstraints := cs.algebraicConstraints.filter keepCon,
                  busInteractions := cs.busInteractions.filter keepBi } :
                  ConstraintSystem p).sideEffects bs env = cs.sideEffects bs (m env) :=
      sideEffects_drop_eq bs keepBi env (m env) cs.busInteractions
        (fun bi hbi hkf => hBstateless bi hbi hkf)
        (fun bi hbi hstate => hmeB env bi (hBkeep bi hbi (hstKeep bi hbi hstate)))
    rw [hse]; exact BusState.equiv_refl _
  · -- completeness: cs.impliesAdmissible out
    intro env hadm hsat _hdc
    refine ⟨env, ⟨fun c hc => hsat.1 c (List.mem_filter.1 hc).1,
                  fun bi hbi => hsat.2 bi (List.mem_filter.1 hbi).1⟩, ?_, ?_,
                  ConstraintSystem.derivedConsistent_of_nil env rfl⟩
    · -- admissibility carries over (dropped interactions are stateless)
      exact (cs.admissible_filterBus bs keepBi env
        (fun bi hbi hkf => Or.inr (hBstateless bi hbi hkf))).2 hadm
    · -- side effects: cs under env = out under env
      have hse : ({ algebraicConstraints := cs.algebraicConstraints.filter keepCon,
                    busInteractions := cs.busInteractions.filter keepBi } :
                    ConstraintSystem p).sideEffects bs env = cs.sideEffects bs env :=
        sideEffects_drop_eq bs keepBi env env cs.busInteractions
          (fun bi hbi hkf => hBstateless bi hbi hkf) (fun _ _ _ => rfl)
      rw [hse]; exact BusState.equiv_refl _
  · -- invariant preservation
    intro hinv env hsat bi hbi
    have hbimem : bi ∈ cs.busInteractions := (List.mem_filter.1 hbi).1
    have hbikeep : keepBi bi = true := (List.mem_filter.1 hbi).2
    have hsatm : cs.satisfies bs (m env) := keySat env hsat.1 hsat.2
    have heval : bi.eval (m env) = bi.eval env := hmeB env bi (hBkeep bi hbimem hbikeep)
    have key := hinv (m env) hsatm bi hbimem
    simp only [heval] at key
    exact key

/-! ## Finding a component: connectivity from the stateful buses -/

/-- Variables reachable from a stateful-bus variable via co-occurrence in a constraint or bus
    interaction (`groups` = the variable lists; `v2g` = variable → group indices). This only *finds*
    a candidate component — correctness never depends on it, since the pass re-checks the partition
    the result induces. -/
partial def bfsClosure (groups : Array (List String)) (v2g : Std.HashMap String (List Nat))
    (visited : Std.HashSet String) (procGroups : Std.HashSet Nat) (stack : List String) :
    Std.HashSet String :=
  match stack with
  | [] => visited
  | x :: rest =>
    if visited.contains x then bfsClosure groups v2g visited procGroups rest
    else
      let gids := (v2g.getD x []).filter (fun g => !procGroups.contains g)
      let procGroups := gids.foldl (fun s g => s.insert g) procGroups
      let newVars := gids.foldl (fun acc g => groups.getD g [] ++ acc) rest
      bfsClosure groups v2g (visited.insert x) procGroups newVars

/-- The co-occurrence graph of the system: for each item (constraint, then interaction) its list of
    variables (`groups`), and a map from each variable to the indices of the items it occurs in
    (`v2g`). Both `bfsClosure` seeds run over this graph. -/
def buildGraph (cs : ConstraintSystem p) :
    Array (List String) × Std.HashMap String (List Nat) :=
  let groups : Array (List String) :=
    (cs.algebraicConstraints.map Expression.vars ++
      cs.busInteractions.map BusInteraction.vars).toArray
  let v2g : Std.HashMap String (List Nat) :=
    (List.range groups.size).foldl
      (fun mp i => (groups.getD i []).foldl (fun mp x => mp.insert x (i :: mp.getD x [])) mp) ∅
  (groups, v2g)

/-- Keep a constraint unless *all* of its variables are removable (and it has at least one). -/
def keepConWith (remV : String → Bool) (c : Expression p) : Bool :=
  c.vars.isEmpty || !(c.vars.all remV)

/-- Keep an interaction if it is stateful or has a non-removable variable (or no variables). -/
def keepBiWith (bs : BusSemantics p) (remV : String → Bool)
    (bi : BusInteraction (Expression p)) : Bool :=
  bs.isStateful bi.busId || bi.vars.isEmpty || !(bi.vars.all remV)

/-! ## The pass -/

/-- Remove every disconnected component that the all-zero witness certifies satisfiable.

    A variable is *removable* when it is (a) not connected to any stateful bus interaction and (b)
    not in the co-occurrence closure of any disconnected item the witness fails to satisfy — so a
    component is dropped only if **all** of its constraints evaluate to `0` and **all** of its
    (stateless) interactions are non-violating under the witness. This is per-component: an
    uncertifiable component is kept without blocking the others. The final partition is re-checked
    (`hchk`) so correctness never depends on the connectivity search; if a check fails the pass is
    the identity. -/
def disconnectedComponentPass : VerifiedPass p := fun cs bs =>
  let (groups, v2g) := buildGraph cs
  -- variables connected to a stateful bus interaction
  let conn := bfsClosure groups v2g ∅ ∅
    (cs.busInteractions.foldl (fun acc bi =>
      if bs.isStateful bi.busId then bi.vars ++ acc else acc) [])
  let disc : String → Bool := fun x => !conn.contains x
  -- variables of a disconnected item the all-zero witness fails on: keep its whole component
  let badSeeds : List String :=
    cs.algebraicConstraints.foldl (fun acc c =>
        if !c.vars.isEmpty && c.vars.all disc && !decide (c.eval (fun _ => 0) = 0)
        then c.vars ++ acc else acc)
      (cs.busInteractions.foldl (fun acc bi =>
        if !bs.isStateful bi.busId && !bi.vars.isEmpty && bi.vars.all disc
            && bs.violatesConstraint (bi.eval (fun _ => 0))
        then bi.vars ++ acc else acc) [])
  let bad := bfsClosure groups v2g ∅ ∅ badSeeds
  let remV : String → Bool := fun x => !conn.contains x && !bad.contains x
  if hchk : (
      (cs.algebraicConstraints.any (fun c => !keepConWith remV c) ||
        cs.busInteractions.any (fun bi => !keepBiWith bs remV bi)) &&
      cs.algebraicConstraints.all (fun c => keepConWith remV c || decide (c.eval (fun _ => 0) = 0)) &&
      cs.busInteractions.all (fun bi =>
        keepBiWith bs remV bi || !bs.violatesConstraint (bi.eval (fun _ => 0))) &&
      cs.algebraicConstraints.all (fun c =>
        !keepConWith remV c || c.vars.all (fun x => !remV x)) &&
      cs.busInteractions.all (fun bi =>
        !keepBiWith bs remV bi || bi.vars.all (fun x => !remV x))
    ) = true then
    ⟨{ algebraicConstraints := cs.algebraicConstraints.filter (keepConWith remV),
       busInteractions := cs.busInteractions.filter (keepBiWith bs remV) },
     by
       simp only [Bool.and_eq_true, and_assoc] at hchk
       obtain ⟨_hne, hcz, hbz, hck, hbk⟩ := hchk
       refine dropComponent_correct cs bs (fun _ => 0) remV
         (keepConWith remV) (keepBiWith bs remV) ?_ ?_ ?_ ?_ ?_ ?_ ?_
       · -- hCrem: a removed constraint has all-removable variables
         intro c _ hkf x hx
         simp only [keepConWith, Bool.or_eq_false_iff] at hkf
         exact (List.all_eq_true.1 (by simpa using hkf.2)) x hx
       · -- hCsat: the witness zeroes every removed constraint
         intro c hc hkf
         have h1 := (List.all_eq_true.1 hcz) c hc
         rw [hkf, Bool.false_or] at h1
         exact of_decide_eq_true h1
       · -- hCkeep: a kept constraint uses only connected variables
         intro c hc hkt x hx
         have h1 := (List.all_eq_true.1 hck) c hc
         rw [hkt] at h1
         simp only [Bool.not_true, Bool.false_or] at h1
         simpa using (List.all_eq_true.1 h1) x hx
       · -- hBrem
         intro bi _ hkf x hx
         simp only [keepBiWith, Bool.or_eq_false_iff] at hkf
         exact (List.all_eq_true.1 (by simpa using hkf.2)) x hx
       · -- hBsat: the witness makes every removed interaction non-violating
         intro bi hbi hkf
         have h1 := (List.all_eq_true.1 hbz) bi hbi
         rw [hkf, Bool.false_or] at h1
         simpa using h1
       · -- hBstateless: removed interactions are stateless
         intro bi _ hkf
         simp only [keepBiWith, Bool.or_eq_false_iff] at hkf
         exact hkf.1.1
       · -- hBkeep: a kept interaction uses only connected variables
         intro bi hbi hkt x hx
         have h1 := (List.all_eq_true.1 hbk) bi hbi
         rw [hkt] at h1
         simp only [Bool.not_true, Bool.false_or] at h1
         simpa using (List.all_eq_true.1 h1) x hx⟩
  else
    ⟨cs, cs.refines_refl bs, id⟩
