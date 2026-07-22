import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Disconnected-component removal

A *disconnected component* is a set of algebraic constraints and stateless bus interactions whose
variables never touch a stateful bus interaction. The pass finds one by connectivity from the
stateful buses, tries the all-zero witness, and drops the component only if the witness certifies
it at run time (the same re-check `guardDegree` uses). Correctness is in
`DisconnectedComponentProof.lean`; the connectivity closure is a well-founded recursion (no fuel)
whose decreasing lexicographic measure `(unprocessed-groups-in-range, stack.length)` is proved by
`denseBfsMeasureDecreasing`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The co-occurrence graph -/

/-- The co-occurrence graph: `groups` gives each item (constraint, then interaction) its list of
    `VarId`s; `v2g` maps each `VarId` to the indices of the items it occurs in. -/
def denseBuildGraph (d : DenseConstraintSystem p) :
    Array (List VarId) × Std.HashMap VarId (List Nat) :=
  let groups : Array (List VarId) :=
    (d.algebraicConstraints.map DenseExpr.vars ++
      d.busInteractions.map denseBIVars).toArray
  let v2g : Std.HashMap VarId (List Nat) :=
    (List.range groups.size).foldl
      (fun mp i => (groups.getD i []).foldl (fun mp x => mp.insert x (i :: mp.getD x [])) mp) ∅
  (groups, v2g)

/-! ## The terminating closure -/

/-- Membership in a left-fold of `insert`s over a `Std.HashSet Nat`: an index is present iff it was
    already present or it is one of the folded elements. -/
private theorem denseProcMem (l : List Nat) (s : Std.HashSet Nat) (i : Nat) :
    i ∈ l.foldl (fun s g => s.insert g) s ↔ i ∈ s ∨ i ∈ l := by
  induction l generalizing s with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih (s.insert a), Std.HashSet.mem_insert, List.mem_cons]
    simp only [beq_iff_eq]
    constructor
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h

/-- Folding a list of out-of-range group indices leaves the stack unchanged: each `groups.getD g []`
    is the default empty list. -/
private theorem denseFoldOutOfRange (groups : Array (List VarId)) :
    ∀ (l : List Nat), (∀ g ∈ l, groups.size ≤ g) → ∀ (acc : List VarId),
      l.foldl (fun acc g => groups.getD g [] ++ acc) acc = acc := by
  intro l
  induction l with
  | nil => intro _ acc; rfl
  | cons a t ih =>
    intro hl acc
    rw [List.foldl_cons]
    have ha : groups.getD a ([] : List VarId) = [] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (hl a (List.mem_cons_self ..)),
        Option.getD_none]
    rw [ha, List.nil_append]
    exact ih (fun g hg => hl g (List.mem_cons_of_mem _ hg)) acc

/-- The lexicographic measure `(unprocessed-groups-in-range, stack.length)` strictly decreases on a
    productive closure step: a triggered in-range group index is newly processed (first component
    drops), else every push is empty and the stack shrinks. -/
private theorem denseBfsMeasureDecreasing (groups : Array (List VarId))
    (procGroups : Std.HashSet Nat) (gids : List Nat) (rest : List VarId)
    (hg : ∀ g ∈ gids, procGroups.contains g = false) :
    (toLex (((Finset.range groups.size).filter
                (fun g => (gids.foldl (fun s g => s.insert g) procGroups).contains g = false)).card,
              (gids.foldl (fun acc g => groups.getD g [] ++ acc) rest).length) : Nat ×ₗ Nat)
      < toLex (((Finset.range groups.size).filter (fun g => procGroups.contains g = false)).card,
               rest.length + 1) := by
  set P' := gids.foldl (fun s g => s.insert g) procGroups with hP'
  have hmem : ∀ g, g ∈ P' ↔ g ∈ procGroups ∨ g ∈ gids := fun g => denseProcMem gids procGroups g
  have himpl : ∀ a, P'.contains a = false → procGroups.contains a = false := by
    intro a ha
    rw [Std.HashSet.contains_eq_false_iff_not_mem] at ha ⊢
    exact fun hm => ha ((hmem a).2 (Or.inl hm))
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hcase : ∃ g ∈ gids, g < groups.size
  · left
    obtain ⟨g0, hg0, hg0lt⟩ := hcase
    show ((Finset.range groups.size).filter (fun g => P'.contains g = false)).card
       < ((Finset.range groups.size).filter (fun g => procGroups.contains g = false)).card
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ (fun a _ => himpl a))]
    refine ⟨g0, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hg0lt, hg g0 hg0⟩
    · rw [Finset.mem_filter]
      rintro ⟨-, hc⟩
      rw [Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc ((hmem g0).2 (Or.inr hg0))
  · right
    have hcase' : ∀ g ∈ gids, groups.size ≤ g := by
      intro g hgin; by_contra hlt; exact hcase ⟨g, hgin, by omega⟩
    refine ⟨?_, ?_⟩
    · show ((Finset.range groups.size).filter (fun g => P'.contains g = false)).card
         = ((Finset.range groups.size).filter (fun g => procGroups.contains g = false)).card
      refine congrArg Finset.card (Finset.filter_congr fun g hg' => ?_)
      rw [Finset.mem_range] at hg'
      have hgni : g ∉ gids := fun hgin => absurd (hcase' g hgin) (by omega)
      constructor
      · exact fun h => himpl g h
      · intro h
        rw [Std.HashSet.contains_eq_false_iff_not_mem] at h ⊢
        exact fun hm => h (((hmem g).1 hm).resolve_right hgni)
    · show (gids.foldl (fun acc g => groups.getD g [] ++ acc) rest).length < rest.length + 1
      rw [denseFoldOutOfRange groups gids hcase' rest]; omega

/-- Variables reachable from a seed via co-occurrence in a constraint or interaction. Correctness
    never depends on this result — the pass re-checks the partition it induces. -/
def denseBfsClosure (groups : Array (List VarId)) (v2g : Std.HashMap VarId (List Nat))
    (visited : Std.HashSet VarId) (procGroups : Std.HashSet Nat) (stack : List VarId) :
    Std.HashSet VarId :=
  match stack with
  | [] => visited
  | x :: rest =>
    if visited.contains x then denseBfsClosure groups v2g visited procGroups rest
    else
      let gids := (v2g.getD x []).filter (fun g => !procGroups.contains g)
      let procGroups' := gids.foldl (fun s g => s.insert g) procGroups
      let newVars := gids.foldl (fun acc g => groups.getD g [] ++ acc) rest
      denseBfsClosure groups v2g (visited.insert x) procGroups' newVars
  termination_by toLex (((Finset.range groups.size).filter
      (fun g => procGroups.contains g = false)).card, stack.length)
  decreasing_by
    · exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, by simp⟩)
    · simp only [List.length_cons]
      exact denseBfsMeasureDecreasing groups procGroups
        ((v2g.getD x []).filter (fun g => !procGroups.contains g)) rest
        (fun g hg => by simpa using (List.mem_filter.1 hg).2)

/-! ## Keep predicates -/

/-- Keep a constraint unless *all* of its variables are removable (and it has at least one). -/
def denseKeepConWith (remV : VarId → Bool) (c : DenseExpr p) : Bool :=
  c.vars.isEmpty || !(c.vars.all remV)

/-- Keep an interaction if it is stateful or has a non-removable variable (or no variables). -/
def denseKeepBiWith (bs : BusSemantics p) (remV : VarId → Bool)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  bs.isStateful bi.busId || (denseBIVars bi).isEmpty || !((denseBIVars bi).all remV)

/-! ## Computing the removable set

`denseConnBad` returns the two reachable sets as data (a pair), not a `VarId → Bool` predicate: a
function-valued def is eta-expanded to maximal arity, which would rebuild the graph and rerun both
closures on every `remV x` application (arity-expansion trap). The `remV` predicate is built once at
the use site in `denseDisconnectedF`. -/

/-- The two reachable sets: `conn` (variables connected to a stateful bus interaction) and `bad`
    (the co-occurrence closure of any disconnected item the all-zero witness fails on). Treated
    opaquely by the correctness proof. -/
def denseConnBad (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    Std.HashSet VarId × Std.HashSet VarId :=
  let (groups, v2g) := denseBuildGraph d
  -- variables connected to a stateful bus interaction
  let connSeed : List VarId :=
    d.busInteractions.foldl (fun acc bi =>
      if bs.isStateful bi.busId then denseBIVars bi ++ acc else acc) []
  let conn := denseBfsClosure groups v2g ∅ ∅ connSeed
  let disc : VarId → Bool := fun x => !conn.contains x
  -- variables of a disconnected item the all-zero witness fails on: keep its whole component
  let badSeeds : List VarId :=
    d.algebraicConstraints.foldl (fun acc c =>
        if !c.vars.isEmpty && c.vars.all disc && !decide (c.eval (fun _ => 0) = 0)
        then c.vars ++ acc else acc)
      (d.busInteractions.foldl (fun acc bi =>
        if !bs.isStateful bi.busId && !(denseBIVars bi).isEmpty && (denseBIVars bi).all disc
            && bs.violatesConstraint (denseBIEval bi (fun _ => 0))
        then denseBIVars bi ++ acc else acc) [])
  let bad := denseBfsClosure groups v2g ∅ ∅ badSeeds
  (conn, bad)

/-! ## The guarded drop -/

/-- The run-time re-check: the induced partition is a genuine drop, the all-zero witness satisfies
    every removed constraint and non-violates every removed interaction, and every kept item uses
    only non-removable variables. Stated for an arbitrary `remV`. -/
def denseDropCheck (bs : BusSemantics p) (d : DenseConstraintSystem p) (remV : VarId → Bool) : Bool :=
  (d.algebraicConstraints.any (fun c => !denseKeepConWith remV c) ||
    d.busInteractions.any (fun bi => !denseKeepBiWith bs remV bi)) &&
  d.algebraicConstraints.all (fun c => denseKeepConWith remV c || decide (c.eval (fun _ => 0) = 0)) &&
  d.busInteractions.all (fun bi =>
    denseKeepBiWith bs remV bi || !bs.violatesConstraint (denseBIEval bi (fun _ => 0))) &&
  d.algebraicConstraints.all (fun c =>
    !denseKeepConWith remV c || c.vars.all (fun x => !remV x)) &&
  d.busInteractions.all (fun bi =>
    !denseKeepBiWith bs remV bi || (denseBIVars bi).all (fun x => !remV x))

/-- Drop the removable component if the re-check passes; otherwise the identity. Stated for an
    arbitrary `remV` so the correctness proof is generic in the connectivity search. -/
def denseDropGuarded (bs : BusSemantics p) (d : DenseConstraintSystem p) (remV : VarId → Bool) :
    DenseConstraintSystem p :=
  if denseDropCheck bs d remV then
    { algebraicConstraints := d.algebraicConstraints.filter (denseKeepConWith remV),
      busInteractions := d.busInteractions.filter (denseKeepBiWith bs remV) }
  else d

/-- Finds a set of constraints and stateless interactions whose variables never reach a stateful
    bus, and — if the all-zero witness satisfies them (re-checked at run time by `denseDropCheck`) —
    drops the whole component. -/
def denseDisconnectedF (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  let cb := denseConnBad bs d
  denseDropGuarded bs d (fun x => !cb.1.contains x && !cb.2.contains x)

end ApcOptimizer.Dense
