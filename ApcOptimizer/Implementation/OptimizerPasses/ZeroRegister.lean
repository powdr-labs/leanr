import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.TautoBus

set_option autoImplicit false

/-! # Pinning fixed-zero register reads (RISC-V `x0`, powdr's `seqz`/`beqz` enabler)

An OpenVM `beqz`/`bnez` (branch on `a == 0`) reads the second operand from register `x0`, which
RISC-V hardwires to `0`. Locally the chip cannot see this: `x0` is read and written back on the
memory bus with a *free* value `b`, at two different timestamps, so `b` is observable and the
last-write-wins discipline (both accesses dangle within the block) cannot pin it. The
`BusFacts.zeroCell` fact — backed by the `zeroRegisterReads` clause of OpenVM's `admissible`
(`ApcOptimizer/OpenVmSemantics.lean`) — supplies exactly this real-trace knowledge.

This pass consumes it: for every *active* memory message whose address is a declared fixed-zero
cell (constant address `(1, 0)`, constant nonzero multiplicity), it **adds the constraints**
`data_i = 0` for the message's data limbs. Soundness is free (the added constraints only shrink the
accepted set; the buses are untouched, so the side effects are unchanged); completeness discharges
them from the `zeroCell` fact (`addConstraints_correct`, as in `busUnifyPass`). The existing
substitution / constant-fold passes then propagate `b → 0`, eliminating the operand limbs — the
first, larger half of powdr's `seqz` reduction. With `BusFacts.trivial` (no `zeroCell`) the pass is
a no-op. -/

variable {p : ℕ}

/-- The data-slot expressions of one interaction that a `zeroCell` fact forces to zero, or `[]` if
    the interaction is not an active fixed-zero cell: its multiplicity must be a constant `≠ 0` (so
    the message is unconditionally active), and every address slot must be syntactically the
    required constant. -/
def cellZeroExprs (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : List (Expression p) :=
  match facts.zeroCell bi.busId with
  | none => []
  | some (addrReq, dataSlots) =>
    match bi.multiplicity.constValue? with
    | none => []
    | some c =>
      if decide (c ≠ 0) &&
          addrReq.all (fun ar => decide (bi.payload[ar.1]? = some (.const ar.2))) then
        dataSlots.map (fun slot => (bi.payload[slot]?).getD (.const 0))
      else []

/-- Every expression `cellZeroExprs` returns evaluates to `0` on an admissible assignment: the
    interaction is an active fixed-zero cell, so `zeroCell_sound` forces each of its data limbs to
    `0`. Needs only admissibility (not satisfaction) — the value is fixed by the real-trace fact. -/
theorem cellZeroExprs_eval_zero (cs : ConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (Expression p)) (hbi : bi ∈ cs.busInteractions)
    (env : Variable → ZMod p) (hadm : cs.admissible bs env) (c : Expression p)
    (hc : c ∈ cellZeroExprs bs facts bi) : c.eval env = 0 := by
  unfold cellZeroExprs at hc
  split at hc
  · exact absurd hc (by simp)
  · rename_i addrReq dataSlots hzc
    split at hc
    · exact absurd hc (by simp)
    · rename_i cval hconst
      split at hc
      · rename_i hcond
        rw [Bool.and_eq_true] at hcond
        obtain ⟨hcne, haddrall⟩ := hcond
        have hcne' : cval ≠ 0 := of_decide_eq_true hcne
        rw [List.mem_map] at hc
        obtain ⟨slot, hslot, rfl⟩ := hc
        -- The evaluated message and the facts placing it in the active∧stateful list.
        have hmem : bi.eval env ∈ cs.busInteractions.map (fun b => b.eval env) :=
          List.mem_map.2 ⟨bi, hbi, rfl⟩
        have hadm' : bs.admissible ((cs.busInteractions.map (fun b => b.eval env)).filter
            (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
        have hbusId : (bi.eval env).busId = bi.busId := rfl
        have hmult : (bi.eval env).multiplicity = cval :=
          bi.multiplicity.constValue?_sound cval hconst env
        have hmne : (bi.eval env).multiplicity ≠ 0 := by rw [hmult]; exact hcne'
        have haddr : ∀ ar ∈ addrReq, (bi.eval env).payload[ar.1]? = some ar.2 := by
          intro ar har
          have hpay : bi.payload[ar.1]? = some (.const ar.2) :=
            of_decide_eq_true (List.all_eq_true.1 haddrall ar har)
          show (bi.payload.map (fun e => e.eval env))[ar.1]? = some ar.2
          rw [List.getElem?_map, hpay]; rfl
        -- Split on whether the data slot is present in the payload.
        cases hpsl : bi.payload[slot]? with
        | none => simp [Expression.eval]
        | some e =>
          rw [Option.getD_some]
          have hget : (bi.eval env).payload[slot]? = some (e.eval env) := by
            show (bi.payload.map (fun e => e.eval env))[slot]? = some (e.eval env)
            rw [List.getElem?_map, hpsl]; rfl
          exact facts.zeroCell_sound (cs.busInteractions.map (fun b => b.eval env)) hadm'
            bi.busId addrReq dataSlots hzc (bi.eval env) hmem hbusId hmne haddr slot hslot
            (e.eval env) hget
      · exact absurd hc (by simp)

/-- Collect every interaction's fixed-zero data-limb expressions, with the proof that each
    evaluates to `0` on an admissible assignment. -/
def collectZeroCells (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) →
    { out : List (Expression p) //
        ∀ env, cs.admissible bs env → ∀ c ∈ out, c.eval env = 0 }
  | [], _ => ⟨[], fun _ _ _ h => absurd h (by simp)⟩
  | bi :: rest, hmem =>
    let ⟨acc, hacc⟩ := collectZeroCells cs bs facts rest
      (fun b hb => hmem b (List.mem_cons_of_mem _ hb))
    ⟨cellZeroExprs bs facts bi ++ acc, by
      intro env hadm c hc
      rcases List.mem_append.1 hc with h | h
      · exact cellZeroExprs_eval_zero cs bs facts bi (hmem bi (List.mem_cons_self ..)) env hadm c h
      · exact hacc env hadm c h⟩

/-- The fixed-zero-register pass. Adds `data_i = 0` for every active fixed-zero-cell memory message
    (RISC-V `x0`), justified by the `zeroCell` real-trace fact. Skips equalities that are already
    trivially zero or already present, and keeps only equalities over existing columns (so it
    introduces no variable — the data limbs are existing payload columns). -/
def zeroRegisterPass : VerifiedPassW p := fun cs bs facts =>
  let ⟨exprs, hexprs⟩ := collectZeroCells cs bs facts cs.busInteractions (fun _ h => h)
  let csVars := cs.vars
  let new := exprs.filter
    (fun c => !c.normalize.fold.isConstZero && !cs.algebraicConstraints.contains c
      && c.vars.all (fun z => decide (z ∈ csVars)))
  if new.isEmpty then ⟨cs, [], PassCorrect.refl cs bs⟩
  else
    ⟨{ cs with algebraicConstraints := cs.algebraicConstraints ++ new }, [],
     cs.addConstraints_correct bs new
       (fun env hadm _hsat c hc => hexprs env hadm c (List.mem_of_mem_filter hc))
       (fun c hc z hz => by
         have hp := (List.mem_filter.1 hc).2
         simp only [Bool.and_eq_true, List.all_eq_true] at hp
         exact of_decide_eq_true (hp.2 z hz))⟩
