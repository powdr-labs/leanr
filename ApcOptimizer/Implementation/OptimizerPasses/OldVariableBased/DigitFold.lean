import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Subst
import ApcOptimizer.Implementation.OptimizerPasses.OldVariableBased.Affine
import ApcOptimizer.Implementation.OptimizerPasses.MemoryUnify
import ApcOptimizer.Implementation.OptimizerPasses.BytePack
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold

set_option autoImplicit false

/-! # Bounded-payload digit fold (constant limb decomposition via byte checks)

Optimized blocks keep families of witness limbs that are in fact *compile-time constants*: a
byte check (bitwise pair check, or any bus fact asserting a payload value is a byte) is applied
to an affine expression

    `E = K ± (g·v₀ + 256g·v₁ + 65536g·v₂ + …)`    (a scaled base-256 "ladder"),

whose variables `vᵢ` each carry their own range check `vᵢ < Bᵢ ≤ 256`. Writing `S` for the
ladder's ℕ-value, the byte check pins `(K ± S mod p)` to a byte `b < 256`, so over ℕ

    `S = tval(b) + m·p`   for some byte `b` and wrap count `m ≤ maxM/p`.

Enumerating the whole `(b, m)` grid and decoding each admissible `M` as a bounded base-256
ladder yields the *complete* set of digit vectors any satisfying assignment can take. When that
set is a **singleton** `[d⃗]`, every `vᵢ` is forced to the constant `dᵢ` — the pass substitutes
`v₀ := d₀` (one variable per invocation; the cleanup fixpoint re-solves the shrunken ladder and
converges), and the now-entailed range checks are dropped by the existing cleanup passes.

The wrap analysis is essential: `p ≡ 1 (mod 256)` for BabyBear, so each wrap count `m` admits a
digit-vector candidate — narrow range checks on the high limbs (e.g. the 6-bit top PC limb) are
what kill the phantoms. The enumeration is exact and generic (no OpenVM specifics): it fires
precisely when byte-check + range facts force uniqueness.

Correctness: the ℕ-side `solutions_complete` theorem shows any satisfying assignment's digit
vector appears in the enumerated set; with the singleton check this forces `env v₀ = d₀`, and
`ConstraintSystem.subst_correct` turns that into a `PassCorrect`. -/

namespace DigitFold

variable {p : ℕ}

/-! ## Ladder recognition on linear forms

The `Nat`/`ZMod`-only ladder layer (`ladderVal` / `unpack?` / `solutions` / `coeffNat` / `signum` /
`tval` and the completeness theorems) lives in `OptimizerPasses/DigitFold.lean` (re-homed there so
the dense tree needs no import of this file); it is imported back above and reused unqualified. -/

/-- Check that the (sorted) terms carry the exact coefficient ladder `n, 256n, 65536n, …`. -/
def isLadder (pos : Bool) : ℕ → List (Variable × ZMod p) → Bool
  | _, [] => true
  | n, (_, c) :: rest => coeffNat pos c == n && isLadder pos (256 * n) rest

/-- A ladder's ZMod sum is the cast of its ℕ positional value (up to the sign). -/
theorem isLadder_sum [NeZero p] (pos : Bool) :
    ∀ (g : ℕ) (l : List (Variable × ZMod p)), isLadder pos g l = true →
    ∀ (env : Variable → ZMod p),
    (l.map (fun t => t.2 * env t.1)).sum =
      signum pos * ((g * ladderVal (l.map (fun t => (env t.1).val)) : ℕ) : ZMod p) := by
  intro g l
  induction l generalizing g with
  | nil => intro _ env; simp [ladderVal]
  | cons t rest ih =>
    intro h env
    obtain ⟨v, c⟩ := t
    simp only [isLadder, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, hrest⟩ := h
    have hsum := ih (256 * g) hrest env
    simp only [List.map_cons, List.sum_cons, hsum, ladderVal]
    have henv : env v = (((env v).val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse (env v)).symm
    cases pos with
    | true =>
      have hcv : c = ((g : ℕ) : ZMod p) := by
        rw [← hc]
        exact (ZMod.natCast_rightInverse c).symm
      rw [hcv, signum_true]
      conv_lhs => rw [henv]
      push_cast
      ring
    | false =>
      have hcv : -c = ((g : ℕ) : ZMod p) := by
        rw [← hc]
        exact (ZMod.natCast_rightInverse (-c)).symm
      have hcv' : c = -((g : ℕ) : ZMod p) := by rw [← hcv]; ring
      rw [hcv', signum_false]
      conv_lhs => rw [henv]
      push_cast
      ring

/-- The env-side forcing theorem: if the solution grid for a byte-checked ladder is the singleton
    `[ds]`, any satisfying assignment's digit vector is exactly `ds`. -/
theorem env_forced [NeZero p] (hp : 256 < p) (pos : Bool) (g : ℕ) (hg : 0 < g) (K : ZMod p)
    (l : List (Variable × ZMod p)) (hlad : isLadder pos g l = true)
    (Bs : List ℕ) (hB : ∀ B ∈ Bs, B ≤ 256)
    (env : Variable → ZMod p)
    (hbound : List.Forall₂ (fun (t : Variable × ZMod p) B => (env t.1).val < B) l Bs)
    (hbyte : ((K + (l.map (fun t => t.2 * env t.1)).sum).val) < 256)
    (ds : List ℕ)
    (hsol : solutions p (tval pos K) g Bs (g * ladderVal (Bs.map (· - 1))) = [ds]) :
    l.map (fun t => (env t.1).val) = ds := by
  have hp0 : 0 < p := by omega
  have hxB : List.Forall₂ (· < ·) (l.map (fun t => (env t.1).val)) Bs := by
    rw [List.forall₂_map_left_iff]
    exact hbound
  have hsum := isLadder_sum pos g l hlad env
  have hEvcast : (((K + (l.map (fun t => t.2 * env t.1)).sum).val : ℕ) : ZMod p)
      = K + (l.map (fun t => t.2 * env t.1)).sum :=
    ZMod.natCast_rightInverse _
  have hmod : (g * ladderVal (l.map (fun t => (env t.1).val))) % p
      = tval pos K ((K + (l.map (fun t => t.2 * env t.1)).sum).val) := by
    have hvalS : (((g * ladderVal (l.map (fun t => (env t.1).val)) : ℕ)) : ZMod p).val
        = g * ladderVal (l.map (fun t => (env t.1).val)) % p := by
      rw [ZMod.val_natCast]
    rw [← hvalS]
    unfold tval
    congr 1
    rw [hEvcast]
    cases pos with
    | true =>
      rw [hsum, signum_true, one_mul]
      simp
    | false =>
      rw [hsum, signum_false]
      simp only [Bool.false_eq_true, if_false]
      ring
  have hle : g * ladderVal (l.map (fun t => (env t.1).val))
      ≤ g * ladderVal (Bs.map (· - 1)) :=
    Nat.mul_le_mul_left g (ladderVal_le_box _ Bs hxB)
  exact solutions_forced p (tval pos K) g Bs _ hp0 hg ds hsol _ hxB hB
    ((K + (l.map (fun t => t.2 * env t.1)).sum).val) hbyte hmod hle

/-! ## The driver: recognize byte-checked ladders and fire a substitution -/


/-- Recognize a packed byte pair check (decoded op `= pairOp`, result `0`) at multiplicity `1` on a
    `byteXorSpec` bus with byte bound `256`: acceptance asserts both operands are bytes. -/
def pairByteOps? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) : Option (Expression p × Expression p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | some (op, o1, o2, r) =>
      if spec.bound = 256 ∧ op = Expression.const spec.pairOp ∧ r = Expression.const 0
          ∧ bi.multiplicity = Expression.const 1
      then some (o1, o2) else none
    | none => none

/-- Acceptance of a recognized pair check bounds both operands below 256. -/
theorem pairByteOps?_bytes (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (Expression p)) (x y : Expression p)
    (h : pairByteOps? bs facts bi = some (x, y))
    (h1 : (1 : ZMod p) ≠ 0) (env : Variable → ZMod p)
    (hacc : (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false) :
    (x.eval env).val < 256 ∧ (y.eval env).val < 256 := by
  unfold pairByteOps? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    split at h
    · rename_i op o1 o2 r hdec
      split_ifs at h with hcond
      obtain ⟨hbound, hop, _, hm⟩ := hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmv : (bi.eval env).multiplicity = 1 := by
        show bi.multiplicity.eval env = 1; rw [hm]; rfl
      have hviol : bs.violatesConstraint (bi.eval env) = false := hacc (by rw [hmv]; simpa using h1)
      have hopEv : op.eval env = spec.pairOp := by rw [hop]; rfl
      obtain ⟨hb1, hb2, _⟩ :=
        ((byteXorSpec_decode_iff bs facts spec bi hspec op o1 o2 r hdec env).2 hopEv).mp hviol
      rw [hbound] at hb1 hb2
      exact ⟨hb1, hb2⟩
    · exact absurd h (by simp)

/-- Sort a linear form's terms by the sign-interpreted coefficient and check the ladder shape;
    returns the leading ℕ-coefficient and the sorted terms. -/
def tryLadder (pos : Bool) (terms : List (Variable × ZMod p)) :
    Option (ℕ × List (Variable × ZMod p)) :=
  match terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2) with
  | [] => none
  | t :: rest =>
    if 0 < coeffNat pos t.2 ∧ isLadder pos (coeffNat pos t.2) (t :: rest) = true
    then some (coeffNat pos t.2, t :: rest) else none

theorem tryLadder_spec (pos : Bool) (terms : List (Variable × ZMod p))
    (g : ℕ) (sorted : List (Variable × ZMod p))
    (h : tryLadder pos terms = some (g, sorted)) :
    terms.Perm sorted ∧ 0 < g ∧ isLadder pos g sorted = true := by
  unfold tryLadder at h
  split at h
  · exact absurd h (by simp)
  · rename_i t rest hms
    split_ifs at h with hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hperm : (terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2)).Perm terms :=
      List.mergeSort_perm terms _
    rw [hms] at hperm
    exact ⟨hperm.symm, hcond.1, hcond.2⟩

/-- Look up a fact-derived bound `≤ 256` for every ladder variable, in order. -/
def lookupBounds (bounds : Std.HashMap Variable Nat) :
    List (Variable × ZMod p) → Option (List ℕ)
  | [] => some []
  | (v, _) :: rest =>
    match bounds[v]? with
    | some B => if B ≤ 256 then (lookupBounds bounds rest).map (B :: ·) else none
    | none => none

theorem lookupBounds_spec (bounds : Std.HashMap Variable Nat) :
    ∀ (l : List (Variable × ZMod p)) (Bs : List ℕ), lookupBounds bounds l = some Bs →
    (∀ B ∈ Bs, B ≤ 256) ∧
      List.Forall₂ (fun (t : Variable × ZMod p) B => bounds[t.1]? = some B) l Bs := by
  intro l
  induction l with
  | nil =>
    intro Bs h
    simp only [lookupBounds, Option.some.injEq] at h
    subst h
    exact ⟨by simp, List.Forall₂.nil⟩
  | cons t rest ih =>
    intro Bs h
    obtain ⟨v, c⟩ := t
    simp only [lookupBounds] at h
    split at h
    · rename_i B hB
      split_ifs at h with hle
      obtain ⟨Bs', hBs', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h256, hall⟩ := ih Bs' hBs'
      refine ⟨?_, List.Forall₂.cons hB hall⟩
      intro B' hB'
      rcases List.mem_cons.1 hB' with rfl | hB'
      · exact hle
      · exact h256 B' hB'
    · exact absurd h (by simp)

/-- Attempt one sign interpretation on a linearized operand: ladder-match, collect bounds,
    enumerate the grid; on a singleton return the lowest-coefficient variable and its digit. -/
def attemptLadder (pos : Bool) (bounds : Std.HashMap Variable Nat) (l : LinExpr p) :
    Option (Variable × ℕ) :=
  match tryLadder pos l.terms with
  | none => none
  | some gs =>
    match lookupBounds bounds gs.2 with
    | none => none
    | some Bs =>
      match solutions p (tval pos l.const) gs.1 Bs (gs.1 * ladderVal (Bs.map (· - 1))) with
      | [ds] =>
        match gs.2, ds with
        | t :: _, d :: _ => some (t.1, d)
        | _, _ => none
      | _ => none

theorem attemptLadder_sound [NeZero p] (hp : 256 < p)
    {cs : ConstraintSystem p} {bs : BusSemantics p} (bm : BoundsMap p cs bs)
    (pos : Bool) (l : LinExpr p) (v : Variable) (d : ℕ)
    (h : attemptLadder pos bm.map l = some (v, d))
    (env : Variable → ZMod p)
    (hbus : ∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false)
    (hbyte : (l.eval env).val < 256) :
    env v = (d : ZMod p) := by
  unfold attemptLadder at h
  split at h
  · exact absurd h (by simp)
  · rename_i gs hladder
    split at h
    · exact absurd h (by simp)
    · rename_i Bs hbounds
      split at h
      · rename_i hsol'
        split at h
        · rename_i t htail d' dtail hsorted
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hperm, hg, hlad⟩ := tryLadder_spec pos l.terms gs.1 gs.2 hladder
          obtain ⟨h256, hbmap⟩ := lookupBounds_spec bm.map gs.2 Bs hbounds
          -- env-level bounds from the BoundsMap
          have hbound : List.Forall₂ (fun (t : Variable × ZMod p) B => (env t.1).val < B)
              gs.2 Bs :=
            hbmap.imp (fun {t} {B} hlk => bm.sound env hbus t.1 B hlk)
          -- the linear form's value over sorted terms
          have hsumeq : (l.terms.map (fun t => t.2 * env t.1)).sum
              = (gs.2.map (fun t => t.2 * env t.1)).sum :=
            (hperm.map (fun t => t.2 * env t.1)).sum_eq
          have hbyte' : ((l.const + (gs.2.map (fun t => t.2 * env t.1)).sum).val) < 256 := by
            have hev : l.eval env = l.const + (gs.2.map (fun t => t.2 * env t.1)).sum := by
              rw [LinExpr.eval, hsumeq]
            rwa [hev] at hbyte
          have hforced := env_forced hp pos gs.1 hg l.const gs.2 hlad Bs h256 env hbound
            hbyte' (d' :: dtail) hsol'
          -- extract the head digit
          rw [hsorted] at hforced
          simp only [List.map_cons, List.cons.injEq] at hforced
          have hv : (env t.1).val = d' := hforced.1
          rw [← hv]
          exact (ZMod.natCast_rightInverse (env t.1)).symm
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- Solve one byte-checked operand: linearize, then try both sign interpretations. -/
def solveOperand (bounds : Std.HashMap Variable Nat) (E : Expression p) :
    Option (Variable × ℕ) :=
  match linearize E with
  | none => none
  | some l =>
    -- the idiom needs at least two ladder digits; length-1 "ladders" are every plain
    -- byte-checked variable, and enumerating their grids is pure overhead
    if l.terms.length < 2 then none
    else
      match attemptLadder true bounds l with
      | some r => some r
      | none => attemptLadder false bounds l

theorem solveOperand_sound [NeZero p] (hp : 256 < p)
    {cs : ConstraintSystem p} {bs : BusSemantics p} (bm : BoundsMap p cs bs)
    (E : Expression p) (v : Variable) (d : ℕ)
    (h : solveOperand bm.map E = some (v, d))
    (env : Variable → ZMod p)
    (hbus : ∀ bi ∈ cs.busInteractions, (bi.eval env).multiplicity ≠ 0 →
      bs.violatesConstraint (bi.eval env) = false)
    (hbyte : (E.eval env).val < 256) :
    env v = (d : ZMod p) := by
  unfold solveOperand at h
  split at h
  · exact absurd h (by simp)
  · rename_i l hlin
    have hEl : E.eval env = l.eval env := linearize_eval E l hlin env
    rw [hEl] at hbyte
    split_ifs at h
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      subst h
      exact attemptLadder_sound hp bm true l v d hr env hbus hbyte
    · exact attemptLadder_sound hp bm false l v d h env hbus hbyte

/-- A forced substitution: a variable, its constant value, and the entailment proof. -/
structure Fold (p : ℕ) (cs : ConstraintSystem p) (bs : BusSemantics p) where
  v : Variable
  d : ℕ
  sound : ∀ env, cs.satisfies bs env → env v = (d : ZMod p)

/-- Scan the interactions for a byte-checked ladder operand with a forced digit. -/
def findFold [NeZero p] (hp : 256 < p) {cs : ConstraintSystem p} {bs : BusSemantics p}
    (facts : BusFacts p bs) (bm : BoundsMap p cs bs) :
    (pending : List (BusInteraction (Expression p))) →
    (∀ bi ∈ pending, bi ∈ cs.busInteractions) → Option (Fold p cs bs)
  | [], _ => none
  | bi :: rest, hmem =>
    let hbi := hmem bi (List.mem_cons_self ..)
    let hrest := fun bi' h => hmem bi' (List.mem_cons_of_mem _ h)
    have h1 : (1 : ZMod p) ≠ 0 := by
      haveI : Fact (1 < p) := ⟨by omega⟩
      exact one_ne_zero
    match hop : pairByteOps? bs facts bi with
    | none => findFold hp facts bm rest hrest
    | some (x, y) =>
      match hx : solveOperand bm.map x with
      | some (v, d) =>
        some ⟨v, d, fun env hsat =>
          solveOperand_sound hp bm x v d hx env hsat.2
            (pairByteOps?_bytes bs facts bi x y hop h1 env (hsat.2 bi hbi)).1⟩
      | none =>
        match hy : solveOperand bm.map y with
        | some (v, d) =>
          some ⟨v, d, fun env hsat =>
            solveOperand_sound hp bm y v d hy env hsat.2
              (pairByteOps?_bytes bs facts bi x y hop h1 env (hsat.2 bi hbi)).2⟩
        | none => findFold hp facts bm rest hrest

/-- The pass: substitute one forced digit per invocation (the cleanup fixpoint re-solves the
    shrunken ladder on the next iteration and converges). -/
def digitFoldPass : VerifiedPassW p := fun cs bs facts =>
  if hp : 256 < p then
    haveI : NeZero p := ⟨by omega⟩
    let bm : BoundsMap p cs bs := BoundsMap.build facts
    match findFold hp facts bm cs.busInteractions (fun _ h => h) with
    | some f =>
      ⟨cs.subst f.v (Expression.const (f.d : ZMod p)), [],
        cs.subst_correct f.v (Expression.const (f.d : ZMod p)) bs
          (fun env hsat => f.sound env hsat)
          (fun y hy => absurd hy (by simp [Expression.vars]))⟩
    | none => ⟨cs, [], PassCorrect.refl cs bs⟩
  else ⟨cs, [], PassCorrect.refl cs bs⟩

end DigitFold
