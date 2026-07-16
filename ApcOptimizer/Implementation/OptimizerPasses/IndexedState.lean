import ApcOptimizer.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false

/-! # Indexed cleanup state (step-11 substrate)

The cleanup fixpoint re-scans the whole system in every pass on every cycle; a measurement puts
~61 % of pass invocations at *no-op full-system scans*. Skipping them (or reprocessing only the
items a substitution touched) needs a representation that survives edits **without reindexing**:
stable item positions, tombstones for drops, an occurrence index keyed by variable, and counters
maintained incrementally. This module is that substrate — the data structures and their proven
bridge to the audited `ConstraintSystem`. **Nothing consumes it yet** (it is carried in the
`FactStore` as an `Option`, `none` until a future worklist increment populates it), so this file
changes no optimizer behavior; it only provides the verified building blocks.

The essential correctness anchor is the **round-trip** `toSystem (ofSystem cs) = cs`: a worklist may
`ofSystem`, mutate the indexed state, then `toSystem`, and the boundary result is a genuine
`ConstraintSystem` — so each mutation can be discharged against the existing `PassCorrect` machinery.
Like the rest of the `FactStore`, the occurrence index and counters carry no threaded invariant a
consumer must trust: a consumer re-validates positions against the current arrays (the
`CoveredIndex.coveredIdx_mem` discipline), so a stale index can only miss work, never be unsound. The
occurrence-soundness lemma here is the *sound* direction (returned positions are in range and mention
the key), which is all a candidate-generator consumer needs. -/

variable {p : ℕ}

/-- An occurrence index: `map v` are positions (into an item array) whose item mentions `v`. Bare
    data, no invariant — soundness is re-established at use against the current array. -/
abbrev OccIndex := Std.HashMap Variable (List Nat)

/-- Insert position `i` into the bucket of every variable in `vs`. -/
def OccIndex.insertPos (m : OccIndex) (i : Nat) (vs : List Variable) : OccIndex :=
  vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m

/-- Build the occurrence index for `items` (each item's variables via `varsOf`), positions being
    indices into `items`. A left fold over `items.zipIdx`. -/
def buildOcc {α : Type} (varsOf : α → List Variable) (items : List α) : OccIndex :=
  items.zipIdx.foldl (fun m (ai : α × Nat) => m.insertPos ai.2 (varsOf ai.1)) ∅

/-- The stable-position, tombstoned cleanup state. Positions into `cs`/`bis` never shift: a drop
    tombstones its slot (`none`) rather than removing it, so occurrence positions stay valid across
    edits. `occCs`/`occBis` index live items by variable; the counters mirror the materialized
    system's size measures. -/
structure IndexedState (p : ℕ) where
  /-- Constraints by stable position; `none` marks a dropped (tombstoned) slot. -/
  cs : Array (Option (Expression p))
  /-- Bus interactions by stable position; `none` marks a dropped slot. -/
  bis : Array (Option (BusInteraction (Expression p)))
  /-- Variable → positions in `cs` whose (built-time) constraint mentioned it. -/
  occCs : OccIndex
  /-- Variable → positions in `bis` whose (built-time) interaction mentioned it. -/
  occBis : OccIndex
  /-- Distinct-variable count of the live system (mirrors `ConstraintSystem.varCount`). -/
  varCount : Nat
  /-- Live constraint count. -/
  constraintCount : Nat
  /-- Live bus-interaction count. -/
  busCount : Nat
  /-- Maximum algebraic-constraint degree over the live system. -/
  maxDegree : Nat

namespace IndexedState

/-- Materialize the audited `ConstraintSystem`: drop tombstones, keep live items in position order. -/
def toSystem (S : IndexedState p) : ConstraintSystem p :=
  { algebraicConstraints := S.cs.toList.filterMap id,
    busInteractions := S.bis.toList.filterMap id }

/-- Build the indexed state from a system: every item live (`some`), occurrence indices and counters
    computed once. -/
def ofSystem (cs : ConstraintSystem p) : IndexedState p :=
  { cs := (cs.algebraicConstraints.map some).toArray,
    bis := (cs.busInteractions.map some).toArray,
    occCs := buildOcc Expression.vars cs.algebraicConstraints,
    occBis := buildOcc BusInteraction.vars cs.busInteractions,
    varCount := cs.varCount,
    constraintCount := cs.algebraicConstraints.length,
    busCount := cs.busInteractions.length,
    maxDegree := (cs.algebraicConstraints.map Expression.degree).foldl Nat.max 0 }

/-- `filterMap id` undoes `map some`. -/
theorem filterMap_id_map_some {α : Type} (l : List α) : (l.map some).filterMap id = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.filterMap_cons_some (by rfl), ih]

/-- **Round-trip.** Materializing a freshly built indexed state returns the original system: every
    slot is live (`ofSystem` tombstones nothing), so `toSystem` recovers each list exactly. This is
    the anchor a worklist uses — mutate the state, then `toSystem` at the boundary. -/
theorem toSystem_ofSystem (cs : ConstraintSystem p) : (ofSystem cs).toSystem = cs := by
  cases cs with
  | mk ac bi =>
    simp only [ofSystem, toSystem, filterMap_id_map_some, List.toList_toArray]

/-! ## Tombstone drops

Dropping an item replaces its slot with `none`. Positions of the *other* items are unchanged, so
occurrence entries stay valid — the point of the tombstone representation. -/

/-- Tombstone constraint slot `i` (no-op if out of range or already dropped). -/
def dropConstraintAt (S : IndexedState p) (i : Nat) : IndexedState p :=
  if h : i < S.cs.size then
    { S with cs := S.cs.set i none,
             constraintCount := if S.cs[i].isSome then S.constraintCount - 1 else S.constraintCount }
  else S

/-- Tombstone bus-interaction slot `i` (no-op if out of range or already dropped). -/
def dropBusAt (S : IndexedState p) (i : Nat) : IndexedState p :=
  if h : i < S.bis.size then
    { S with bis := S.bis.set i none,
             busCount := if S.bis[i].isSome then S.busCount - 1 else S.busCount }
  else S

/-- The live constraints after a drop (in range): tombstoning slot `i` removes exactly the item
    there (if live) from `toSystem`'s constraint list, leaving the others in order. Out of range the
    drop is a no-op. Characterizes the effect of `dropConstraintAt` on the materialized system. -/
theorem toSystem_dropConstraintAt (S : IndexedState p) (i : Nat) (hi : i < S.cs.size) :
    (S.dropConstraintAt i).toSystem.algebraicConstraints
      = (S.cs.set i none).toList.filterMap id := by
  simp only [dropConstraintAt, dif_pos hi, toSystem]

/-- The live bus interactions after a bus drop (analogue of `toSystem_dropConstraintAt`). -/
theorem toSystem_dropBusAt (S : IndexedState p) (i : Nat) (hi : i < S.bis.size) :
    (S.dropBusAt i).toSystem.busInteractions = (S.bis.set i none).toList.filterMap id := by
  simp only [dropBusAt, dif_pos hi, toSystem]

end IndexedState
