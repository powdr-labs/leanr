import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Value-level semantic core of the seqz-collapse gadget

The `ZMod p`-value-level lemmas and range-check bus facts underlying the `seqzCollapse` pass,
re-homed here from the reference `SeqzCollapse` pass so the dense proof
(`SeqzCollapseProof.lean`) consumes them from a neutral home. They quantify over `ZMod p` values and bus specs only, so they
are wholly representation-independent; kept under the original `SeqzCollapse` namespace so every
consumer's fully-qualified name is unchanged. `sum_zero_all_zero` is reused unqualified from
`HintCollapse.lean` (itself re-homed there). -/

namespace SeqzCollapse

variable {p : ℕ}

/-! ## Value-level semantic core

Two facts about the gadget's constraint *values* (`ZMod p` equalities), stated with the constraints
already simplified from their serialised trees. `seqz_forward` is used for completeness (derive the
is-zero constraints); `seqz_reconstruct` is used for soundness (rebuild the marker witnesses). Both
need the byte bounds on the four limbs and the monic constant `2K = -1`. -/

/-- For a byte-valued `y` with `1 ≤ y.val`, the negation `-y` has value `≥ 256` in a field with
    `512 ≤ p` — so `-y` cannot be a byte. The engine of every range-check contradiction below. -/
theorem neg_byte_val_big [NeZero p] (hp : 512 ≤ p) (y : ZMod p)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 256) : 256 ≤ (-y).val := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, ZMod.val_zero] at hy1; omega
  haveI : NeZero y := ⟨hy0⟩
  rw [ZMod.val_neg_of_ne_zero y]
  omega

/-- `m·(m−1) = 0` in a field forces `m ∈ {0, 1}`. -/
theorem zbool [Fact p.Prime] {m : ZMod p} (h : m * (m - 1) = 0) : m = 0 ∨ m = 1 := by
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

/-- A small positive natural is nonzero in `ZMod p` when `p` is large. -/
theorem small_natCast_ne_zero [NeZero p] (hp : 1024 ≤ p) {k : ℕ} (hk1 : 0 < k) (hk2 : k < 1024) :
    ((k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd hk1 hdvd
  omega

/-- `(1 : ZMod p).val = 1` when `p` is large. -/
theorem val_one_eq [NeZero p] (hp : 1024 ≤ p) : (1 : ZMod p).val = 1 := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  exact ZMod.val_one p

/-- Adding `1` to a byte value adds `1` to its `.val`. -/
theorem val_add_one [NeZero p] (hp : 1024 ≤ p) {a : ZMod p} (ha : a.val < 256) :
    (a + 1).val = a.val + 1 := by
  rw [ZMod.val_add, val_one_eq hp]
  exact Nat.mod_eq_of_lt (by omega)

/-- `-1 + x` stays a byte when `x` is a nonzero byte (matches the template's `-1 + dv` form). -/
theorem byte_sub_one_val [NeZero p] (hp : 1024 ≤ p) {x : ZMod p} (hx : x ≠ 0) (hxb : x.val < 256) :
    (-1 + x).val < 256 := by
  have hxv : x.val ≠ 0 := by rw [ne_eq, ZMod.val_eq_zero]; exact hx
  have hle : (1 : ZMod p).val ≤ x.val := by rw [val_one_eq hp]; omega
  rw [show (-1 : ZMod p) + x = x - 1 by ring, ZMod.val_sub hle, val_one_eq hp]; omega

/-- `x − 2` stays a byte when `x` is a byte with `x.val ≥ 2`. -/
theorem byte_sub_two_val [NeZero p] (hp : 1024 ≤ p) {x : ZMod p} (hx : 2 ≤ x.val) (hxb : x.val < 256) :
    (x - 2).val < 256 := by
  have hv2 : (2 : ZMod p).val = 2 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ZMod.val_cast_of_lt (by omega)]
  have hle : (2 : ZMod p).val ≤ x.val := by rw [hv2]; omega
  rw [ZMod.val_sub hle, hv2]; omega

/-- Four Boolean values summing (in the field) to `1` have exactly one equal to `1`. -/
theorem oneHot [Fact p.Prime] (hp : 1024 ≤ p) {m0 m1 m2 m3 : ZMod p}
    (h3 : m3 = 0 ∨ m3 = 1) (h2 : m2 = 0 ∨ m2 = 1) (h1 : m1 = 0 ∨ m1 = 1) (h0 : m0 = 0 ∨ m0 = 1)
    (hsum : m3 + m2 + m1 + m0 = 1) :
    (m3 = 1 ∧ m2 = 0 ∧ m1 = 0 ∧ m0 = 0) ∨ (m3 = 0 ∧ m2 = 1 ∧ m1 = 0 ∧ m0 = 0) ∨
    (m3 = 0 ∧ m2 = 0 ∧ m1 = 1 ∧ m0 = 0) ∨ (m3 = 0 ∧ m2 = 0 ∧ m1 = 0 ∧ m0 = 1) := by
  haveI : NeZero p := ⟨by omega⟩
  have h1ne : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have := small_natCast_ne_zero hp (k := 2) (by norm_num) (by norm_num); simpa using this
  have h3ne : (3 : ZMod p) ≠ 0 := by
    have := small_natCast_ne_zero hp (k := 3) (by norm_num) (by norm_num); simpa using this
  rcases h3 with h3 | h3 <;> rcases h2 with h2 | h2 <;> rcases h1 with h1 | h1 <;>
    rcases h0 with h0 | h0 <;> subst_vars <;>
    first
      | (left; exact ⟨rfl, rfl, rfl, rfl⟩)
      | (right; left; exact ⟨rfl, rfl, rfl, rfl⟩)
      | (right; right; left; exact ⟨rfl, rfl, rfl, rfl⟩)
      | (right; right; right; exact ⟨rfl, rfl, rfl, rfl⟩)
      | (exfalso; apply h1ne; linear_combination hsum)
      | (exfalso; apply h1ne; linear_combination -hsum)
      | (exfalso; apply h2ne; linear_combination hsum)
      | (exfalso; apply h3ne; linear_combination hsum)

/-- **Forward** (completeness engine): the gadget forces `cmp = [S == 0]`, i.e. `R·S = 0` and
    `S = 0 → R = 1`. -/
theorem seqz_forward [Fact p.Prime] (hp : 1024 ≤ p)
    (K R a0 a1 a2 a3 m0 m1 m2 m3 dv : ZMod p)
    (hK : 2 * K + 1 = 0)
    (hb0 : a0.val < 256) (hb1 : a1.val < 256) (hb2 : a2.val < 256) (hb3 : a3.val < 256)
    (hE1 : m3 * (m3 - 1) = 0) (hE4 : m2 * (m2 - 1) = 0)
    (hE7 : m1 * (m1 - 1) = 0) (hE10 : m0 * (m0 - 1) = 0)
    (hE13 : (m3 + m2 + m1 + m0) * (m3 + m2 + m1 + m0 - 1) = 0)
    (hE14 : (m3 + m2 + m1 + m0 - 1) * R = 0)
    (hp3 : (m3 - 1) * (a3 * (K + R)) = 0)
    (hp2 : (m3 + m2 - 1) * (a2 * (K + R)) = 0)
    (hp1 : (m3 + m2 + m1 - 1) * (a1 * (K + R)) = 0)
    (hp0 : (m3 + m2 + m1 + m0 - 1) * ((a0 - 1) * (K + R)) = 0)
    (hd3 : m3 * (dv + a3 * (2 * R - 1)) = 0)
    (hd2 : m2 * (dv + a2 * (2 * R - 1)) = 0)
    (hd1 : m1 * (dv + a1 * (2 * R - 1)) = 0)
    (hd0 : m0 * (dv + (a0 - 1) * (2 * R - 1)) = 0)
    (hRbool : R = 0 ∨ R = 1)
    (hbus : (m3 + m2 + m1 + m0) ≠ 0 → (-1 + dv).val < 256) :
    R * (a0 + a1 + a2 + a3) = 0 ∧ ((a0 + a1 + a2 + a3) = 0 → R = 1) := by
  haveI hnz : NeZero p := ⟨by omega⟩
  have hv1 : (1 : ZMod p).val = 1 := val_one_eq hp
  have hbm3 := zbool hE1
  have hbm2 := zbool hE4
  have hbm1 := zbool hE7
  have hbm0 := zbool hE10
  -- `R = 1` forces the value to be zero.
  have F1 : R = 1 → a0 + a1 + a2 + a3 = 0 := by
    intro hR; subst hR
    have hsum1 : m3 + m2 + m1 + m0 = 1 := by
      have h : m3 + m2 + m1 + m0 - 1 = 0 := by linear_combination hE14
      linear_combination h
    have hsumne : m3 + m2 + m1 + m0 ≠ 0 := by rw [hsum1]; exact one_ne_zero
    have hKR1 : K + 1 ≠ 0 := by
      intro hk
      exact one_ne_zero (by linear_combination (2 : ZMod p) * hk - hK)
    rcases oneHot hp hbm3 hbm2 hbm1 hbm0 hsum1 with
        ⟨e3, e2, e1, e0⟩ | ⟨e3, e2, e1, e0⟩ | ⟨e3, e2, e1, e0⟩ | ⟨e3, e2, e1, e0⟩ <;> subst_vars
    · exfalso
      have hdv : dv = -a3 := by linear_combination hd3
      have hbyte := hbus hsumne
      rw [show (-1 : ZMod p) + dv = -(a3 + 1) by rw [hdv]; ring] at hbyte
      have hv := val_add_one hp hb3
      have := neg_byte_val_big (by omega) (a3 + 1) (by omega) (by omega)
      omega
    · exfalso
      have hdv : dv = -a2 := by linear_combination hd2
      have hbyte := hbus hsumne
      rw [show (-1 : ZMod p) + dv = -(a2 + 1) by rw [hdv]; ring] at hbyte
      have hv := val_add_one hp hb2
      have := neg_byte_val_big (by omega) (a2 + 1) (by omega) (by omega)
      omega
    · exfalso
      have hdv : dv = -a1 := by linear_combination hd1
      have hbyte := hbus hsumne
      rw [show (-1 : ZMod p) + dv = -(a1 + 1) by rw [hdv]; ring] at hbyte
      have hv := val_add_one hp hb1
      have := neg_byte_val_big (by omega) (a1 + 1) (by omega) (by omega)
      omega
    · have hdv : dv = 1 - a0 := by linear_combination hd0
      by_cases ha0 : a0 = 0
      · subst ha0
        have ha3 : a3 = 0 := by
          have : a3 * (K + 1) = 0 := by linear_combination -hp3
          exact (mul_eq_zero.1 this).resolve_right hKR1
        have ha2 : a2 = 0 := by
          have : a2 * (K + 1) = 0 := by linear_combination -hp2
          exact (mul_eq_zero.1 this).resolve_right hKR1
        have ha1 : a1 = 0 := by
          have : a1 * (K + 1) = 0 := by linear_combination -hp1
          exact (mul_eq_zero.1 this).resolve_right hKR1
        subst ha1; subst ha2; subst ha3; ring
      · exfalso
        have hbyte := hbus hsumne
        rw [show (-1 : ZMod p) + dv = -a0 by rw [hdv]; ring] at hbyte
        have ha0v : 1 ≤ a0.val := by
          rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact ha0
        have := neg_byte_val_big (by omega) a0 ha0v (by omega)
        omega
  -- The value being zero forces `R = 1`.
  have F2 : a0 + a1 + a2 + a3 = 0 → R = 1 := by
    intro hS
    have hall : ∀ x ∈ [a0, a1, a2, a3], x = 0 := by
      apply sum_zero_all_zero (by omega : 0 < p) [a0, a1, a2, a3]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
      · simp only [List.sum_cons, List.sum_nil]; linear_combination hS
    have ha0 : a0 = 0 := hall a0 (by simp)
    have ha1 : a1 = 0 := hall a1 (by simp)
    have ha2 : a2 = 0 := hall a2 (by simp)
    have ha3 : a3 = 0 := hall a3 (by simp)
    rcases hRbool with hR | hR
    · exfalso; subst hR; subst ha0; subst ha1; subst ha2; subst ha3
      have hKne : K ≠ 0 := fun hk => one_ne_zero (by linear_combination hK - (2 : ZMod p) * hk)
      have hsum1 : m3 + m2 + m1 + m0 = 1 := by
        have hp0' : (m3 + m2 + m1 + m0 - 1) * (-K) = 0 := by linear_combination hp0
        rcases mul_eq_zero.1 hp0' with h' | h'
        · linear_combination h'
        · exact absurd (by linear_combination -h' : K = 0) hKne
      have hsumne : m3 + m2 + m1 + m0 ≠ 0 := by rw [hsum1]; exact one_ne_zero
      rcases oneHot hp hbm3 hbm2 hbm1 hbm0 hsum1 with
          ⟨e3, e2, e1, e0⟩ | ⟨e3, e2, e1, e0⟩ | ⟨e3, e2, e1, e0⟩ | ⟨e3, e2, e1, e0⟩ <;> subst_vars
      · have hdv : dv = 0 := by linear_combination hd3
        have hbyte := hbus hsumne
        rw [show (-1 : ZMod p) + dv = -(1 : ZMod p) by rw [hdv]; ring] at hbyte
        have := neg_byte_val_big (by omega) (1 : ZMod p) (by omega) (by omega)
        omega
      · have hdv : dv = 0 := by linear_combination hd2
        have hbyte := hbus hsumne
        rw [show (-1 : ZMod p) + dv = -(1 : ZMod p) by rw [hdv]; ring] at hbyte
        have := neg_byte_val_big (by omega) (1 : ZMod p) (by omega) (by omega)
        omega
      · have hdv : dv = 0 := by linear_combination hd1
        have hbyte := hbus hsumne
        rw [show (-1 : ZMod p) + dv = -(1 : ZMod p) by rw [hdv]; ring] at hbyte
        have := neg_byte_val_big (by omega) (1 : ZMod p) (by omega) (by omega)
        omega
      · have hdv : dv = -1 := by linear_combination hd0
        have hbyte := hbus hsumne
        rw [show (-1 : ZMod p) + dv = -((1 : ZMod p) + 1) by rw [hdv]; ring] at hbyte
        have hv := val_add_one hp (a := (1 : ZMod p)) (by omega)
        have := neg_byte_val_big (by omega) ((1 : ZMod p) + 1) (by omega) (by omega)
        omega
    · exact hR
  refine ⟨?_, F2⟩
  rcases hRbool with hR | hR
  · rw [hR]; ring
  · rw [hR, F1 hR]; ring

/-- **Reconstruction** (soundness engine): whenever `cmp = [S == 0]` and the limbs are bytes, the
    marker/`diff_val` witnesses can be rebuilt so the whole gadget (all 14 constraints and the
    range-check bus obligation `Σmₖ ≠ 0 → (dv − 1) byte`) holds. -/
theorem seqz_reconstruct [Fact p.Prime] (hp : 1024 ≤ p)
    (K R a0 a1 a2 a3 : ZMod p)
    (_hK : 2 * K + 1 = 0)
    (hb0 : a0.val < 256) (hb1 : a1.val < 256) (hb2 : a2.val < 256) (hb3 : a3.val < 256)
    (hRbool : R = 0 ∨ R = 1)
    (hRS : R * (a0 + a1 + a2 + a3) = 0)
    (hSR : (a0 + a1 + a2 + a3) = 0 → R = 1) :
    ∃ m0 m1 m2 m3 dv : ZMod p,
      m3 * (m3 - 1) = 0 ∧ m2 * (m2 - 1) = 0 ∧ m1 * (m1 - 1) = 0 ∧ m0 * (m0 - 1) = 0 ∧
      (m3 + m2 + m1 + m0) * (m3 + m2 + m1 + m0 - 1) = 0 ∧
      (m3 + m2 + m1 + m0 - 1) * R = 0 ∧
      (m3 - 1) * (a3 * (K + R)) = 0 ∧
      (m3 + m2 - 1) * (a2 * (K + R)) = 0 ∧
      (m3 + m2 + m1 - 1) * (a1 * (K + R)) = 0 ∧
      (m3 + m2 + m1 + m0 - 1) * ((a0 - 1) * (K + R)) = 0 ∧
      m3 * (dv + a3 * (2 * R - 1)) = 0 ∧
      m2 * (dv + a2 * (2 * R - 1)) = 0 ∧
      m1 * (dv + a1 * (2 * R - 1)) = 0 ∧
      m0 * (dv + (a0 - 1) * (2 * R - 1)) = 0 ∧
      ((m3 + m2 + m1 + m0) ≠ 0 → (-1 + dv).val < 256) := by
  haveI hnz : NeZero p := ⟨by omega⟩
  have hv1 : (1 : ZMod p).val = 1 := val_one_eq hp
  rcases hRbool with hR | hR
  · -- `R = 0`: the value is nonzero; mark the highest differing limb.
    subst hR
    have hSne : a0 + a1 + a2 + a3 ≠ 0 := fun h => absurd (hSR h) zero_ne_one
    by_cases h3 : a3 = 0
    · subst h3
      by_cases h2 : a2 = 0
      · subst h2
        by_cases h1 : a1 = 0
        · subst h1
          have ha0ne : a0 ≠ 0 := fun h => hSne (by rw [h]; ring)
          by_cases h0 : a0 = 1
          · subst h0
            refine ⟨0, 0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?last⟩
            case last => intro h; exact absurd (by ring) h
            all_goals ring
          · have ha0v2 : 2 ≤ a0.val := by
              have hne0 : a0.val ≠ 0 := by rw [ne_eq, ZMod.val_eq_zero]; exact ha0ne
              have hne1 : a0.val ≠ 1 := fun h => h0 (ZMod.val_injective p (by rw [h, hv1]))
              omega
            refine ⟨1, 0, 0, 0, a0 - 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?last⟩
            case last =>
              intro _
              convert byte_sub_two_val hp ha0v2 hb0 using 2
              ring
            all_goals ring
        · refine ⟨0, 1, 0, 0, a1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?last⟩
          case last => intro _; convert byte_sub_one_val hp h1 hb1 using 2
          all_goals ring
      · refine ⟨0, 0, 1, 0, a2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?last⟩
        case last => intro _; convert byte_sub_one_val hp h2 hb2 using 2
        all_goals ring
    · refine ⟨0, 0, 0, 1, a3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?last⟩
      case last => intro _; convert byte_sub_one_val hp h3 hb3 using 2
      all_goals ring
  · -- `R = 1`: the value is zero; mark limb 0.
    subst hR
    have hS0 : a0 + a1 + a2 + a3 = 0 := by linear_combination hRS
    have hall : ∀ x ∈ [a0, a1, a2, a3], x = 0 := by
      apply sum_zero_all_zero (by omega : 0 < p) [a0, a1, a2, a3]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
      · simp only [List.sum_cons, List.sum_nil]; linear_combination hS0
    have ha0 : a0 = 0 := hall a0 (by simp)
    have ha1 : a1 = 0 := hall a1 (by simp)
    have ha2 : a2 = 0 := hall a2 (by simp)
    have ha3 : a3 = 0 := hall a3 (by simp)
    subst ha0; subst ha1; subst ha2; subst ha3
    refine ⟨1, 0, 0, 0, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?last⟩
    case last => intro _; simp
    all_goals ring

/-- The range-check bus obligation for the pair-check payload `spec.encode pairOp x 0 0`: on a
    `byteXorSpec` bus with byte bound `256`, the message is accepted whenever `x` is a byte (the
    other operand `0` and the result `0` are bytes / zero for free). -/
theorem bus_accepts_byte_zero {bs : BusSemantics p} (facts : BusFacts p bs) (busId : Nat)
    (spec : ByteXorSpec p) (hspec : facts.byteXorSpec busId = some spec) (hbound : spec.bound = 256)
    (x mult : ZMod p) (hx : x.val < 256) :
    bs.violatesConstraint
      { busId := busId, multiplicity := mult, payload := spec.encode spec.pairOp x 0 0 } = false := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  have hdec : spec.decode (spec.encode spec.pairOp x 0 0) = some (spec.pairOp, x, 0, 0) :=
    spec.decode_encode _ _ _ _
  rw [(hsound _ spec.pairOp x 0 0 mult hdec).2 rfl]
  refine ⟨by rw [hbound]; exact hx, by rw [hbound, ZMod.val_zero]; omega, rfl⟩

/-- Reverse direction: an accepted pair-check message pins `x` to the byte range. -/
theorem bus_byte_of_accepts {bs : BusSemantics p} (facts : BusFacts p bs) (busId : Nat)
    (spec : ByteXorSpec p) (hspec : facts.byteXorSpec busId = some spec) (hbound : spec.bound = 256)
    (x mult : ZMod p)
    (h : bs.violatesConstraint
      { busId := busId, multiplicity := mult, payload := spec.encode spec.pairOp x 0 0 } = false) :
    x.val < 256 := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  have hdec : spec.decode (spec.encode spec.pairOp x 0 0) = some (spec.pairOp, x, 0, 0) :=
    spec.decode_encode _ _ _ _
  rw [(hsound _ spec.pairOp x 0 0 mult hdec).2 rfl] at h
  rw [← hbound]; exact h.1

end SeqzCollapse
