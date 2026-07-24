import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses

set_option autoImplicit false

/-! # Dense consecutive-match bus unification (runtime transform for `busUnify`)

Impl-only (no soundness lemma). `denseBusUnifyF` matches the `denseF` shape
`DenseVerifiedPassW.of` (`Bridge.lean`) wraps directly. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Address/equality helpers -/

/-- `e₂ - e₁` as a dense expression. -/
def denseEqExpr (e2 e1 : DenseExpr p) : DenseExpr p := .add e2 (.mul (.const (-1)) e1)

def denseMultConst (bi : BusInteraction (DenseExpr p)) : Option (ZMod p) :=
  bi.multiplicity.constValue?

def denseSetNewMult (ops : DenseZModOps p) (shape : MemoryBusShape) : ZMod p :=
  match shape.direction with
  | .receiveThenSend => ops.one
  | .sendThenReceive => ops.negOne

def denseGetPreviousMult (ops : DenseZModOps p) (shape : MemoryBusShape) : ZMod p :=
  match shape.direction with
  | .receiveThenSend => ops.negOne
  | .sendThenReceive => ops.one

theorem denseSetNewMult_eq (ops : DenseZModOps p) (shape : MemoryBusShape) :
    denseSetNewMult ops shape = shape.setNewMult := by
  cases shape with
  | mk addressFields direction => cases direction <;> simp [denseSetNewMult,
      MemoryBusShape.setNewMult, ops.one_eq, ops.negOne_eq]

theorem denseGetPreviousMult_eq (ops : DenseZModOps p) (shape : MemoryBusShape) :
    denseGetPreviousMult ops shape = -shape.setNewMult := by
  cases shape with
  | mk addressFields direction => cases direction <;> simp [denseGetPreviousMult,
      MemoryBusShape.setNewMult, ops.one_eq, ops.negOne_eq]

/-- Do the two sends carry equal constant address entries? -/
def denseAddrConstsEq (shape : MemoryBusShape) (S S' : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.all (fun slot =>
    match S.payload[slot]?, S'.payload[slot]? with
    | some e, some e' =>
      decide (e = e') ||
      (match e.constValue?, e'.constValue? with
       | some c, some c' => c = c'
       | _, _ => false)
    | _, _ => false)

/-- The entailed conclusions: slot-wise equality of the receive's and the send's payloads,
    excluding the (constant, already-equal) address slots. -/
def denseMemEqConstraints (shape : MemoryBusShape) (S Rt : BusInteraction (DenseExpr p)) :
    List (DenseExpr p) :=
  ((List.range S.payload.length).filter (fun i => decide (i ∉ shape.addressFields))).map
    (fun i => denseEqExpr ((Rt.payload[i]?).getD (.const 0)) ((S.payload[i]?).getD (.const 0)))

/-! ## Address inequality -/

/-- Some address slot carries provably-different constants: the two interactions provably have
    different addresses. -/
def denseAddrConstsNeq (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' =>
      (match e.constValue?, e'.constValue? with
       | some c, some c' => decide (c ≠ c')
       | _, _ => false)
    | _, _ => false)

/-! ## The checked pair -/

/-- A checked consecutive send→receive pair on bus `busId`: `S` a constant send, `R` a constant
    receive, same constant address, and every `mid` message provably inactive or of a different
    address. -/
def denseCheckPair (shape : MemoryBusShape) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (S : BusInteraction (DenseExpr p))
    (mid : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p)) : Bool :=
  decide (denseMultConst S = some shape.setNewMult) &&
    decide (denseMultConst R = some (-shape.setNewMult)) &&
  denseAddrConstsEq shape S R &&
  mid.all (fun m => denseAddrConstsNeq shape S m || denseAddrAffineNeq shape S m
    || denseAddrTwoRootNeq shape T S m || denseAddrNonzeroNeq shape nw S m
    || decide (denseMultConst m = some 0))

/-! ## The pass -/

/-- One `(pre, S, mid, R, post)` split candidate. -/
abbrev DenseSplitCand (p : ℕ) :=
  List (BusInteraction (DenseExpr p)) × BusInteraction (DenseExpr p)
    × List (BusInteraction (DenseExpr p)) × BusInteraction (DenseExpr p)
    × List (BusInteraction (DenseExpr p))

/-! ## The consumer sweep

`denseSweepGo` is one left-to-right pass over a bus's interactions maintaining open send windows
(`constOpen`, keyed by canonical address; `symOpen`, tested against every message) and closing,
excluding, or dropping them as later messages consume, exclude, or block them. -/

/-- One message tested against one open window. -/
inductive DenseStepRes
  | consumer
  | excluded
  | blocker

/-- Classify message `m` against an open send window `S` (consumer / excluded / blocker). The
    certificate tables are `Thunk`s, forced only if a pair reaches the two-root / nonzero-witness
    arms, and call the same certificates `denseCheckPair`'s `mid` arms re-verify. -/
def denseStepTest (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p))
    (S m : BusInteraction (DenseExpr p)) : DenseStepRes :=
  if decide (denseMultConst m = some (denseGetPreviousMult ops shape)) &&
      denseAddrConstsEq shape S m then .consumer
  else if denseAddrConstsNeq shape S m || denseAddrAffineNeq shape S m
      || denseAddrTwoRootNeq shape T.get S m || denseAddrNonzeroNeq shape nw.get S m
      || decide (denseMultConst m = some ops.zero) then .excluded
  else .blocker

/-- A canonical address key. -/
structure DenseAddrKey (p : ℕ) where
  exprs : List (DenseExpr p)
deriving DecidableEq

instance : Hashable (DenseAddrKey p) :=
  ⟨fun k => k.exprs.foldl (fun h e => mixHash h e.bHash) 7⟩

/-- The canonical key of an interaction's address slots, `none` if a slot is missing (such a message
    never `denseAddrConstsEq`-matches anything, so it can neither open a window nor consume one). -/
def denseAddrKey? (shape : MemoryBusShape) (bi : BusInteraction (DenseExpr p)) :
    Option (DenseAddrKey p) :=
  (shape.addressFields.foldr (fun slot acc =>
    match acc, bi.payload[slot]? with
    | some ks, some e =>
      match e.constValue? with
      | some c => some (.const c :: ks)
      | none => some (e :: ks)
    | _, _ => none) (some [])).map DenseAddrKey.mk

def DenseAddrKey.allConst (k : DenseAddrKey p) : Bool :=
  k.exprs.all fun e => match e with
    | .const _ => true
    | _ => false

/-- An open send window: the send `S`, its split context, and its position `i`. -/
structure DenseOpenRec (p : ℕ) where
  revPre : List (BusInteraction (DenseExpr p))
  S : BusInteraction (DenseExpr p)
  restAfter : List (BusInteraction (DenseExpr p))
  i : Nat

/-- Assemble the split candidate for a consumed window, tagged with its send position; `mid` is
    recovered positionally from the send's stored suffix (`take (j−i−1)`). -/
def denseEmitCand (w : DenseOpenRec p) (j : Nat) (R : BusInteraction (DenseExpr p))
    (post : List (BusInteraction (DenseExpr p))) : Option (Nat × DenseSplitCand p) :=
  if w.i < j then
    some (w.i, (w.revPre.reverse, w.S, w.restAfter.take (j - w.i - 1), R, post))
  else none

/-- The sweep: one pass over the interaction list. `acc` collects `(sendPosition, candidate)` pairs,
    order restored by the caller's sort. -/
def denseSweepGo (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p)) :
    (revSeen rest : List (BusInteraction (DenseExpr p))) → (j : Nat) →
    (constOpen : Std.HashMap (DenseAddrKey p) (DenseOpenRec p)) →
    (symOpen : List (DenseOpenRec p)) →
    (acc : List (Nat × DenseSplitCand p)) →
    List (Nat × DenseSplitCand p)
  | _, [], _, _, _, acc => acc
  | revSeen, m :: rest', j, constOpen, symOpen, acc =>
    let mKey? := denseAddrKey? shape m
    let mAllConst := match mKey? with
      | some k => k.allConst
      | none => false
    -- (1) constant-keyed windows: an all-constant message meets only the window at its own key; a
    --     symbolic-address message is tested against every one.
    let (constOpen, acc) :=
      if mAllConst then
        match mKey? with
        | some k =>
          match constOpen[k]? with
          | some w =>
            match denseStepTest ops shape T nw w.S m with
            | .consumer =>
              (constOpen.erase k,
               match denseEmitCand w j m rest' with
               | some c => c :: acc
               | none => acc)
            | .excluded => (constOpen, acc)
            | .blocker => (constOpen.erase k, acc)
          | none => (constOpen, acc)
        | none => (constOpen, acc)
      else
        let (drops, acc) := constOpen.toList.foldl (init := (([] : List (DenseAddrKey p)), acc))
          fun (ds, a) kw =>
            match denseStepTest ops shape T nw kw.2.S m with
            | .consumer =>
              (kw.1 :: ds,
               match denseEmitCand kw.2 j m rest' with
               | some c => c :: a
               | none => a)
            | .excluded => (ds, a)
            | .blocker => (kw.1 :: ds, a)
        (drops.foldl (·.erase ·) constOpen, acc)
    -- (2) symbolic-keyed windows are tested literally against every message.
    let (symOpen, acc) :=
      if symOpen.isEmpty then (symOpen, acc) else
      symOpen.foldr (init := (([] : List (DenseOpenRec p)), acc)) fun w (so, a) =>
        match denseStepTest ops shape T nw w.S m with
        | .consumer =>
          (so,
           match denseEmitCand w j m rest' with
           | some c => c :: a
           | none => a)
        | .excluded => (w :: so, a)
        | .blocker => (so, a)
    -- (3) a send opens its window; a same-key window that survived (1) as excluded moves to the
    --     literally-tested `symOpen` list.
    let (constOpen, symOpen) :=
      if decide (denseMultConst m = some (denseSetNewMult ops shape)) then
        match mKey? with
        | some k =>
          let w : DenseOpenRec p := ⟨revSeen, m, rest', j⟩
          if k.allConst then
            match constOpen[k]? with
            | some old => (constOpen.insert k w, old :: symOpen)
            | none => (constOpen.insert k w, symOpen)
          else (constOpen, w :: symOpen)
        | none => (constOpen, symOpen)
      else (constOpen, symOpen)
    denseSweepGo ops shape T nw (m :: revSeen) rest' (j + 1) constOpen symOpen acc

/-- All consumer candidates of one bus, in send-position order. -/
def denseCandidateSplitsSweep (shape : MemoryBusShape) (T : Thunk (DenseTwoRootMap p))
    (nw : Thunk (DenseNonzeroWits p)) (L : List (BusInteraction (DenseExpr p))) :
    List (DenseSplitCand p) :=
  let ops : DenseZModOps p := denseZModOps
  ((denseSweepGo ops shape T nw [] L 0 ∅ [] []).mergeSort
    (fun a b => decide (a.1 ≤ b.1))).map (·.2)

/-- Collect the entailed equalities for one bus: for each candidate, `denseCheckPair` and, when it
    holds, emit the slot-wise equalities. -/
def denseCollectForBus (shape : MemoryBusShape) (T : Thunk (DenseTwoRootMap p))
    (nw : Thunk (DenseNonzeroWits p)) :
    List (DenseSplitCand p) → List (DenseExpr p)
  | [] => []
  | (_pre, S, mid, R, _post) :: rest =>
    let acc := denseCollectForBus shape T nw rest
    if denseCheckPair shape T.get nw.get S mid R = true then
      denseMemEqConstraints shape S R ++ acc
    else acc

/-- Collect over every declared bus; `facts.memShape busId` decides whether — and with what `shape`
    — a bus's candidates are enumerated. -/
def denseCollectAllBuses (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : Thunk (DenseTwoRootMap p)) (nw : Thunk (DenseNonzeroWits p)) :
    List Nat → List (DenseExpr p)
  | [] => []
  | busId :: rest =>
    let acc := denseCollectAllBuses d bs facts T nw rest
    match facts.memShape busId with
    | some shape =>
      let eqs := denseCollectForBus shape T nw
        (denseCandidateSplitsSweep shape T nw (d.busInteractions.filter (fun bi => bi.busId = busId)))
      eqs ++ acc
    | none => acc

/-- For a memory bus, a `set` (send) at address `a` immediately followed by a matching `get`
    (receive) at the same address must carry the same payload, so this adds the entailed slot
    equalities `getᵢ = setᵢ` for every provably-matched consecutive send→receive pair on each
    declared memory / execution-bridge bus (skipping equations already present or zero). -/
def denseBusUnifyF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    -- Thunked: built only when a window test reaches the two-root / nonzero-witness arms.
    let T : Thunk (DenseTwoRootMap p) :=
      Thunk.mk fun _ => DenseTwoRootMap.build d.algebraicConstraints
    let nw : Thunk (DenseNonzeroWits p) :=
      Thunk.mk fun _ => DenseNonzeroWits.build d.algebraicConstraints
    let eqs := denseCollectAllBuses d bs facts T nw
      -- `hashedDedup` = `List.dedup` (`hashedDedup_eq`), one bucket per id instead of the
      -- quadratic full-list membership walk (the interaction list is system-sized).
      (HashedDedup.hashedDedup (hash ·) (d.busInteractions.map (fun bi => bi.busId)))
    if eqs.isEmpty then d
    else
      -- No-new-variable side condition holds by construction (`denseMemEqConstraints_vars`); the
      -- already-present test buckets constraints by `DenseExpr.bHash` before comparing.
      let dHashes : Std.HashMap UInt64 (List (DenseExpr p)) :=
        d.algebraicConstraints.foldl (fun m c =>
          let h := c.bHash
          m.insert h (c :: m.getD h [])) ∅
      let containsC : DenseExpr p → Bool := fun c =>
        (dHashes.getD c.bHash []).any (fun c' => c' == c)
      let new := eqs.filter
        (fun c => !c.normalize.fold.isConstZero && !containsC c)
      if new.isEmpty then d
      else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
