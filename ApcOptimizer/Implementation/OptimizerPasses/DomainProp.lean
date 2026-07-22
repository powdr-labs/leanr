import ApcOptimizer.Implementation.OptimizerPasses.Basic
import ApcOptimizer.Utils.Size
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-! # Shared finite-domain lemmas and bounds: the `eval_congr` family (evaluation depends only on
the variables read) and the enumeration/probe helpers. -/

variable {p : ℕ}

/-! ## Evaluation depends only on an expression's variables -/

theorem Expression.eval_congr (e : Expression p) (env1 env2 : Variable → ZMod p)
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

theorem BusInteraction.eval_congr (bi : BusInteraction (Expression p))
    (env1 env2 : Variable → ZMod p) (h : ∀ x ∈ bi.vars, env1 x = env2 x) :
    bi.eval env1 = bi.eval env2 := by
  have hmult : bi.multiplicity.eval env1 = bi.multiplicity.eval env2 :=
    bi.multiplicity.eval_congr env1 env2
      (fun x hx => h x (by simp [BusInteraction.vars, hx]))
  have hpay : bi.payload.map (fun e => e.eval env1) = bi.payload.map (fun e => e.eval env2) := by
    apply List.map_congr_left
    intro e he
    exact e.eval_congr env1 env2
      (fun x hx => h x (by
        simp only [BusInteraction.vars, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨e, he, hx⟩))
  simp only [BusInteraction.eval, hmult, hpay]

/-- A computation method reads only its variables; consumed by the master-theorem completeness
    proof (`Implementation/Optimizer.lean`). -/
theorem ComputationMethod.eval_congr (cm : ComputationMethod p) (e1 e2 : Variable → ZMod p) :
    (∀ v ∈ cm.vars, e1 v = e2 v) → cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => intro _; rfl
  | quotientOrZero num den =>
      intro h
      have hn : num.eval e1 = num.eval e2 :=
        Expression.eval_congr num _ _ (fun v hv => h v (List.mem_append_left _ hv))
      have hd : den.eval e1 = den.eval e2 :=
        Expression.eval_congr den _ _ (fun v hv => h v (List.mem_append_right _ hv))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      intro h
      have hc : cond.eval e1 = cond.eval e2 :=
        Expression.eval_congr cond _ _ (fun v hv =>
          h v (List.mem_append_left _ (List.mem_append_left _ hv)))
      have ht := iht (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv)))
      have he := ihe (fun v hv => h v (List.mem_append_right _ hv))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, ht, he]

/-! ## Enumeration and probe bounds -/

/-- Cap on fact-derived domain sizes (a `2^17` range bound is real but not enumerable).
    `2^16` is included so that base-`2^16` digit decompositions (e.g. `to_pc_limbs`) can be
    pinned by probing the rewritten range lookup once the other digit is affine-eliminated. -/
def maxDomainBound : Nat := 65536

/-- Cap on the number of enumerated assignments, to keep the pass cheap. -/
def maxEnumSize : Nat := 65536

/-- A value below `bound` lies in the cast image of `List.range bound`. -/
theorem mem_range_cast [NeZero p] (v : ZMod p) (bound : Nat) (h : v.val < bound) :
    v ∈ (List.range bound).map (Nat.cast : Nat → ZMod p) :=
  List.mem_map.2 ⟨v.val, List.mem_range.2 h, ZMod.natCast_rightInverse v⟩

/-- One plus the largest `v < n` passing `test` (`0` if none) — the least strict upper bound on
    the survivors of a probe. -/
def probeMax (test : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if test n then n + 1 else probeMax test n

theorem probeMax_lt (test : Nat → Bool) :
    ∀ (n v : Nat), v < n → test v = true → v < probeMax test n
  | 0, v, hv, _ => absurd hv (by omega)
  | n + 1, v, hv, htest => by
    rw [probeMax]
    split
    · omega
    · rename_i hn
      have hvn : v ≠ n := fun h => by rw [h] at htest; rw [htest] at hn; exact hn rfl
      exact probeMax_lt test n v (by omega) htest

/-- `some bnd` exactly when it strictly improves on the base bound. -/
def capBound (bnd B₀ : Nat) : Option Nat := if bnd < B₀ then some bnd else none
