import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # Collapsing the `sltu x, 1` (seqz) comparison gadget to a two-line is-zero gadget

powdr specialises OpenVM's `LessThanCoreChip` when the second comparand is the constant `1`
(`sltu rd, x, 1`, i.e. `rd = (x < 1) = (x == 0)`). OpenVM's generic gadget keeps, per instance,
four `diff_marker` booleans and a `diff_val`, tied together by a 14-constraint cluster plus a
range-check bus interaction; powdr replaces all of it with the is-zero gadget

    cmp·S = 0 ∧ inv·S + cmp − 1 = 0            (S = x₀ + x₁ + x₂ + x₃)

keeping a single derived witness `inv = QuotientOrZero(1 − cmp, S)`. Because the limbs `xᵢ` are
byte-range-checked, `S = 0 ⇔ x == 0`, so both gadgets compute exactly `cmp = [x == 0]`.

This pass performs that collapse. It is *not* an instance of `HintCollapse.collapse_correct` — the
cluster is 14 constraints (not one bilinear reciprocal-witness constraint) and one of its private
witnesses (`diff_val`) lives inside a bus interaction, so neither `collapse_correct` (bus-free
witnesses) nor `reencode_correct` (keeps every bus) applies. The transformation is proven directly:
soundness reconstructs the markers/`diff_val` from `(cmp, x)` by a per-limb case analysis; the range
check pins the reconstruction to the byte range; completeness derives `cmp = [S == 0]` from the
gadget and supplies `inv` by `QuotientOrZero`.

The gadget's constants are field-independent: `-1`, `2`, `1`, and the monic-scale constant
`c` with `2·c = -1` (i.e. `c = -2⁻¹`, rendered `(p-1)/2`). The pass matches those constants
structurally, so it is not tied to BabyBear. It runs in the coda (after `monicScale`), where the
cluster has stabilised into the recognised form. With `BusFacts.trivial` it is the identity (no
byte bounds, `bytePairBus` false). -/

namespace SeqzCollapse

variable {p : ℕ}

/-! ## Expression templates for the recognised gadget

Everything is built from the private witnesses `m0..m3`, `dv`, the shared result `R`, the shared
byte limbs `a0..a3`, and the monic constant `K` (`2K = -1`). The trees match the optimiser's
post-`monicScale` serialisation exactly (subtraction is `-1 * ·`, so every `x - 1` is `-1 + x`). -/

/-- `-1` as a constant expression. -/
def eM1 : Expression p := .const (-1)
/-- `0` as a constant expression. -/
def e0 : Expression p := .const 0
/-- `1` as a constant expression. -/
def e1 : Expression p := .const 1
/-- `2` as a constant expression. -/
def e2 : Expression p := .const 2

/-- The partial marker sums `sₖ = -1 + mₖ + … + m₃` (`s3` is `-1 + m3`), nested left. -/
def sExpr (m3 m2 m1 m0 : Variable) : Nat → Expression p
  | 0 => .add (.add (.add (.add eM1 (.var m3)) (.var m2)) (.var m1)) (.var m0)
  | 1 => .add (.add (.add eM1 (.var m3)) (.var m2)) (.var m1)
  | 2 => .add (.add eM1 (.var m3)) (.var m2)
  | _ => .add eM1 (.var m3)

/-- The marker sum `Σ mₖ = ((m3 + m2) + m1) + m0` (no `-1`), the bus multiplicity. -/
def markerSum (m3 m2 m1 m0 : Variable) : Expression p :=
  .add (.add (.add (.var m3) (.var m2)) (.var m1)) (.var m0)

/-- `K + R`, the "sign" factor of the prefix constraints. -/
def krExpr (K : ZMod p) (R : Variable) : Expression p := .add (.const K) (.var R)

/-- `-1 + 2·R`, the `2·cmp − 1` sign selector of the diff constraints. -/
def twoRExpr (R : Variable) : Expression p := .add eM1 (.mul e2 (.var R))

/-- Diff-definition inner term for limbs 1..3: `dv + (-1)·((-1·aᵢ)·(2R−1))`. -/
def diffInner (dv ai R : Variable) : Expression p :=
  .add (.var dv) (.mul eM1 (.mul (.mul eM1 (.var ai)) (twoRExpr R)))

/-- Diff-definition inner term for limb 0: `dv + (-1)·((1 + (-1·a0))·(2R−1))`. -/
def diffInner0 (dv a0 R : Variable) : Expression p :=
  .add (.var dv) (.mul eM1 (.mul (.add e1 (.mul eM1 (.var a0))) (twoRExpr R)))

/-- The 14 algebraic constraints of the gadget, in machine order (limb 3 → 0, then the two
    marker-sum constraints). Built from the recognised roles. -/
def clusterConstraints (m3 m2 m1 m0 dv R a3 a2 a1 a0 : Variable) (K : ZMod p) :
    List (Expression p) :=
  [ -- limb 3
    .mul (.var m3) (.add eM1 (.var m3)),
    .mul (sExpr m3 m2 m1 m0 3) (.mul (.var a3) (krExpr K R)),
    .mul (.var m3) (diffInner dv a3 R),
    -- limb 2
    .mul (.var m2) (.add eM1 (.var m2)),
    .mul (sExpr m3 m2 m1 m0 2) (.mul (.var a2) (krExpr K R)),
    .mul (.var m2) (diffInner dv a2 R),
    -- limb 1
    .mul (.var m1) (.add eM1 (.var m1)),
    .mul (sExpr m3 m2 m1 m0 1) (.mul (.var a1) (krExpr K R)),
    .mul (.var m1) (diffInner dv a1 R),
    -- limb 0 (comparand digit is 1, so the operand is `a0 - 1`)
    .mul (.var m0) (.add eM1 (.var m0)),
    .mul (sExpr m3 m2 m1 m0 0) (.mul (.add eM1 (.var a0)) (krExpr K R)),
    .mul (.var m0) (diffInner0 dv a0 R),
    -- marker-sum booleanity and the "no marker ⇒ cmp = 0" constraint
    .mul (markerSum m3 m2 m1 m0) (sExpr m3 m2 m1 m0 0),
    .mul (sExpr m3 m2 m1 m0 0) (.var R) ]

/-- The gadget's range-check bus interaction: `mult = Σ mₖ`, `args = [dv − 1, 0, 0, 0]`. -/
def clusterBus (busId : Nat) (m3 m2 m1 m0 dv : Variable) : BusInteraction (Expression p) :=
  { busId := busId, multiplicity := markerSum m3 m2 m1 m0,
    payload := [.add eM1 (.var dv), e0, e0, e0] }

/-- The result's booleanity constraint `R·(R − 1)` (kept, not part of the cluster). -/
def boolConstraint (R : Variable) : Expression p := .mul (.var R) (.add eM1 (.var R))

/-- `S = a0 + a1 + a2 + a3`, the limb sum. -/
def sumExpr4 (a0 a1 a2 a3 : Variable) : Expression p :=
  .add (.add (.add (.var a0) (.var a1)) (.var a2)) (.var a3)

/-- The two is-zero constraints replacing the cluster: `R·S` and `inv·S + (R − 1)`. -/
def newConstraints (R a0 a1 a2 a3 inv : Variable) : List (Expression p) :=
  [ .mul (.var R) (sumExpr4 a0 a1 a2 a3),
    .add (.mul (.var inv) (sumExpr4 a0 a1 a2 a3)) (.add (.var R) eM1) ]

/-- The derivation for `inv`: `QuotientOrZero(1 − R, S)`. -/
def invMethod (R a0 a1 a2 a3 : Variable) : ComputationMethod p :=
  .quotientOrZero (.add e1 (.mul eM1 (.var R))) (sumExpr4 a0 a1 a2 a3)

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
            refine ⟨0, 0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            all_goals try ring
            intro h; exact absurd (by ring) h
          · have ha0v2 : 2 ≤ a0.val := by
              have hne0 : a0.val ≠ 0 := by rw [ne_eq, ZMod.val_eq_zero]; exact ha0ne
              have hne1 : a0.val ≠ 1 := fun h => h0 (ZMod.val_injective p (by rw [h, hv1]))
              omega
            refine ⟨1, 0, 0, 0, a0 - 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            all_goals try ring
            intro _; convert byte_sub_two_val hp ha0v2 hb0 using 2 <;> ring
        · refine ⟨0, 1, 0, 0, a1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals try ring
          intro _; convert byte_sub_one_val hp h1 hb1 using 2
      · refine ⟨0, 0, 1, 0, a2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals try ring
        intro _; convert byte_sub_one_val hp h2 hb2 using 2
    · refine ⟨0, 0, 0, 1, a3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try ring
      intro _; convert byte_sub_one_val hp h3 hb3 using 2
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
    refine ⟨1, 0, 0, 0, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try ring
    intro _; simp

/-! ## Bridging the constraint templates and their value forms -/

/-- The 14 gadget constraints all hold at `g` iff the 14 value equations do. Bridges the
    template `Expression.eval` forms to the clean forms `seqz_forward`/`seqz_reconstruct` use. -/
theorem clusterEval_iff (m3 m2 m1 m0 dv R a3 a2 a1 a0 : Variable) (K : ZMod p)
    (g : Variable → ZMod p) :
    (∀ c ∈ clusterConstraints m3 m2 m1 m0 dv R a3 a2 a1 a0 K, c.eval g = 0) ↔
      (g m3 * (g m3 - 1) = 0 ∧
        (g m3 - 1) * (g a3 * (K + g R)) = 0 ∧
        g m3 * (g dv + g a3 * (2 * g R - 1)) = 0 ∧
        g m2 * (g m2 - 1) = 0 ∧
        (g m3 + g m2 - 1) * (g a2 * (K + g R)) = 0 ∧
        g m2 * (g dv + g a2 * (2 * g R - 1)) = 0 ∧
        g m1 * (g m1 - 1) = 0 ∧
        (g m3 + g m2 + g m1 - 1) * (g a1 * (K + g R)) = 0 ∧
        g m1 * (g dv + g a1 * (2 * g R - 1)) = 0 ∧
        g m0 * (g m0 - 1) = 0 ∧
        (g m3 + g m2 + g m1 + g m0 - 1) * ((g a0 - 1) * (K + g R)) = 0 ∧
        g m0 * (g dv + (g a0 - 1) * (2 * g R - 1)) = 0 ∧
        (g m3 + g m2 + g m1 + g m0) * (g m3 + g m2 + g m1 + g m0 - 1) = 0 ∧
        (g m3 + g m2 + g m1 + g m0 - 1) * g R = 0) := by
  simp only [clusterConstraints, List.forall_mem_cons, List.forall_mem_nil, and_true,
    Expression.eval, eM1, e0, e1, e2, sExpr, markerSum, krExpr, twoRExpr, diffInner, diffInner0]
  constructor
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, -⟩
    exact ⟨by linear_combination c1, by linear_combination c2, by linear_combination c3,
      by linear_combination c4, by linear_combination c5, by linear_combination c6,
      by linear_combination c7, by linear_combination c8, by linear_combination c9,
      by linear_combination c10, by linear_combination c11, by linear_combination c12,
      by linear_combination c13, by linear_combination c14⟩
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩
    exact ⟨by linear_combination c1, by linear_combination c2, by linear_combination c3,
      by linear_combination c4, by linear_combination c5, by linear_combination c6,
      by linear_combination c7, by linear_combination c8, by linear_combination c9,
      by linear_combination c10, by linear_combination c11, by linear_combination c12,
      by linear_combination c13, by linear_combination c14, by simp⟩

/-- Reassign the five private witnesses to given values, leaving everything else at `env`. -/
def setFive (m3 m2 m1 m0 dv : Variable) (v3 v2 v1 v0 vd : ZMod p) (env : Variable → ZMod p) :
    Variable → ZMod p :=
  fun x => if x = m3 then v3 else if x = m2 then v2 else if x = m1 then v1
    else if x = m0 then v0 else if x = dv then vd else env x

/-- Off the five witnesses, `setFive` agrees with `env`. -/
theorem setFive_free {m3 m2 m1 m0 dv : Variable} {v3 v2 v1 v0 vd : ZMod p}
    {env : Variable → ZMod p} {x : Variable}
    (h3 : x ≠ m3) (h2 : x ≠ m2) (h1 : x ≠ m1) (h0 : x ≠ m0) (hd : x ≠ dv) :
    setFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env x = env x := by
  simp only [setFive, if_neg h3, if_neg h2, if_neg h1, if_neg h0, if_neg hd]

/-- `setFive` at `m3` (the first key) is `v3`. -/
theorem setFive_at3 {m3 m2 m1 m0 dv : Variable} {v3 v2 v1 v0 vd : ZMod p}
    {env : Variable → ZMod p} :
    setFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m3 = v3 := by
  simp only [setFive, if_true]

/-- `setFive` at `m2`. -/
theorem setFive_at2 {m3 m2 m1 m0 dv : Variable} {v3 v2 v1 v0 vd : ZMod p}
    {env : Variable → ZMod p} (h32 : m2 ≠ m3) :
    setFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m2 = v2 := by
  simp only [setFive, if_neg h32, if_true]

/-- `setFive` at `m1`. -/
theorem setFive_at1 {m3 m2 m1 m0 dv : Variable} {v3 v2 v1 v0 vd : ZMod p}
    {env : Variable → ZMod p} (h31 : m1 ≠ m3) (h21 : m1 ≠ m2) :
    setFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m1 = v1 := by
  simp only [setFive, if_neg h31, if_neg h21, if_true]

/-- `setFive` at `m0`. -/
theorem setFive_at0 {m3 m2 m1 m0 dv : Variable} {v3 v2 v1 v0 vd : ZMod p}
    {env : Variable → ZMod p} (h30 : m0 ≠ m3) (h20 : m0 ≠ m2) (h10 : m0 ≠ m1) :
    setFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env m0 = v0 := by
  simp only [setFive, if_neg h30, if_neg h20, if_neg h10, if_true]

/-- `setFive` at `dv` (the last key). -/
theorem setFive_atd {m3 m2 m1 m0 dv : Variable} {v3 v2 v1 v0 vd : ZMod p}
    {env : Variable → ZMod p} (h3d : dv ≠ m3) (h2d : dv ≠ m2) (h1d : dv ≠ m1) (h0d : dv ≠ m0) :
    setFive m3 m2 m1 m0 dv v3 v2 v1 v0 vd env dv = vd := by
  simp only [setFive, if_neg h3d, if_neg h2d, if_neg h1d, if_neg h0d, if_true]

/-! ## Role extraction (recogniser) -/

/-- Match the bus multiplicity `((m3 + m2) + m1) + m0`. -/
def matchMarkerSum : Expression p → Option (Variable × Variable × Variable × Variable)
  | .add (.add (.add (.var m3) (.var m2)) (.var m1)) (.var m0) => some (m3, m2, m1, m0)
  | _ => none

/-- Match `-1 + x` (a variable), returning `x`. -/
def matchNegVar : Expression p → Option Variable
  | .add (.const c) (.var x) => if c = (-1 : ZMod p) then some x else none
  | _ => none

/-- Match constraint E11 `s0 · ((-1 + a0)·(K + R))`, returning `(a0, K, R)`. -/
def matchE11 (s0 : Expression p) : Expression p → Option (Variable × ZMod p × Variable)
  | .mul lhs (.mul (.add (.const c) (.var a0)) (.add (.const k) (.var r))) =>
      if lhs = s0 ∧ c = (-1 : ZMod p) then some (a0, k, r) else none
  | _ => none

/-- Match a prefix constraint `prefixE · (aᵢ · KR)`, returning `aᵢ`. -/
def matchPrefixVar (prefixE kr : Expression p) : Expression p → Option Variable
  | .mul lhs (.mul (.var ai) rhs) => if lhs = prefixE ∧ rhs = kr then some ai else none
  | _ => none

/-- All the recognised roles of a gadget instance. -/
structure Roles where
  m3 : Variable
  m2 : Variable
  m1 : Variable
  m0 : Variable
  dv : Variable
  R : Variable
  a3 : Variable
  a2 : Variable
  a1 : Variable
  a0 : Variable
  K : ZMod p
  busId : Nat

/-- The private witnesses of a gadget instance (dropped by the collapse). -/
def Roles.witnesses (r : Roles (p := p)) : List Variable := [r.m3, r.m2, r.m1, r.m0, r.dv]

/-- The fresh `inv` variable name for a gadget instance. -/
def Roles.inv (r : Roles (p := p)) : Variable := ⟨"seqzinv#" ++ r.dv.name, none⟩

/-- Does variable `w` occur only inside the recognised cluster (the 14 constraints + the bus)?
    Decided with `Expression.mentions`. -/
def pureInCluster (cs : ConstraintSystem p) (cluster : List (Expression p))
    (bus : BusInteraction (Expression p)) (w : Variable) : Bool :=
  (cs.algebraicConstraints.all (fun c => cluster.contains c || !(c.mentions w))) &&
  (cs.busInteractions.all (fun bi => decide (bi = bus) ||
    (!(bi.multiplicity.mentions w) && bi.payload.all (fun e => !(e.mentions w)))))

/-- Extract the gadget roles from a candidate range-check bus interaction and the constraint list.
    Returns `none` unless every template constraint is present in exact form. -/
def extractRoles (cs : ConstraintSystem p) (bi : BusInteraction (Expression p)) :
    Option (Roles (p := p)) := do
  guard (bi.payload.length = 4)
  let dvArg ← bi.payload[0]?
  let dv ← matchNegVar dvArg
  guard (bi.payload[1]? = some e0 ∧ bi.payload[2]? = some e0 ∧ bi.payload[3]? = some e0)
  let (m3, m2, m1, m0) ← matchMarkerSum bi.multiplicity
  let s0 : Expression p := sExpr m3 m2 m1 m0 0
  let (a0, K, R) ← cs.algebraicConstraints.findSome? (matchE11 s0)
  let kr : Expression p := krExpr K R
  let a3 ← cs.algebraicConstraints.findSome? (matchPrefixVar (sExpr m3 m2 m1 m0 3) kr)
  let a2 ← cs.algebraicConstraints.findSome? (matchPrefixVar (sExpr m3 m2 m1 m0 2) kr)
  let a1 ← cs.algebraicConstraints.findSome? (matchPrefixVar (sExpr m3 m2 m1 m0 1) kr)
  pure { m3, m2, m1, m0, dv, R, a3, a2, a1, a0, K, busId := bi.busId }

/-- The collapsed output system: drop the cluster constraints and range bus, add the is-zero
    constraints. -/
def collapsedSystem (cs : ConstraintSystem p) (r : Roles (p := p)) : ConstraintSystem p :=
  let cluster := clusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K
  let bus := clusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv
  { algebraicConstraints :=
      cs.algebraicConstraints.filter (fun c => !cluster.contains c)
        ++ newConstraints r.R r.a0 r.a1 r.a2 r.a3 r.inv,
    busInteractions := cs.busInteractions.filter (fun bi => decide (bi ≠ bus)) }

/-- All checks that must pass for the collapse to be sound: field size and primality, constants,
    template presence, result booleanity (kept), purity/distinctness of the witnesses, byte bounds
    on the limbs (via the *output* bounds map, whose buses are a subset of the input's), and `inv`
    freshness. The bounds map is built for `collapsedSystem cs r` so its guarantees transfer to any
    assignment satisfying the (smaller) output bus set. -/
def rolesValid (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (r : Roles (p := p)) (Bm : BoundsMap p (collapsedSystem cs r) bs) : Bool :=
  let cluster := clusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K
  let bus := clusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv
  decide (Nat.Prime p) && decide (1024 ≤ p) && decide (2 * r.K + 1 = 0) &&
  facts.bytePairBus r.busId && facts.byteCheck r.busId &&
  cs.busInteractions.contains bus &&
  cluster.all (fun c => cs.algebraicConstraints.contains c) &&
  cs.algebraicConstraints.contains (boolConstraint r.R) &&
  (!cluster.contains (boolConstraint r.R)) &&
  r.witnesses.all (fun w => pureInCluster cs cluster bus w) &&
  [r.a0, r.a1, r.a2, r.a3].all (fun a =>
    match Bm.map[a]? with | some b => decide (b ≤ 256) | none => false) &&
  decide ([r.R, r.a0, r.a1, r.a2, r.a3, r.m3, r.m2, r.m1, r.m0, r.dv].Nodup) &&
  decide (r.inv ∉ cs.vars) &&
  [r.R, r.a0, r.a1, r.a2, r.a3].all (fun v => v.powdrId?.isSome)

/-- The range-check bus obligation for the payload `[x, 0, 0, 0]`: on a bus that is both a byte-pair
    bus and a byte-check bus, the message is accepted whenever `x` is a byte (chaining the pair↔singles
    law with the single↔byte law; the `0` slot is a byte for free). -/
theorem bus_accepts_byte_zero {bs : BusSemantics p} (facts : BusFacts p bs) [NeZero p] (busId : Nat)
    (hbpb : facts.bytePairBus busId = true) (hbc : facts.byteCheck busId = true)
    (x mult : ZMod p) (hx : x.val < 256) :
    bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, 0, 0, 0] } = false := by
  obtain ⟨_, _, hpair⟩ := facts.bytePairBus_sound busId hbpb
  obtain ⟨_, _, hsingle⟩ := facts.byteCheck_sound busId hbc
  rw [hpair x 0 mult]
  refine ⟨(hsingle x mult).2 hx, (hsingle 0 mult).2 ?_⟩
  rw [ZMod.val_zero]; omega

/-- Reverse direction: an accepted `[x, 0, 0, 0]` message pins `x` to the byte range. -/
theorem bus_byte_of_accepts {bs : BusSemantics p} (facts : BusFacts p bs) [NeZero p] (busId : Nat)
    (hbpb : facts.bytePairBus busId = true) (hbc : facts.byteCheck busId = true)
    (x mult : ZMod p)
    (h : bs.violatesConstraint { busId := busId, multiplicity := mult, payload := [x, 0, 0, 0] }
        = false) :
    x.val < 256 := by
  obtain ⟨_, _, hpair⟩ := facts.bytePairBus_sound busId hbpb
  obtain ⟨_, _, hsingle⟩ := facts.byteCheck_sound busId hbc
  rw [hpair x 0 mult] at h
  exact (hsingle x mult).1 h.1

/-- **The collapse is a verified pass.** Replacing the recognised gadget cluster (14 constraints +
    range-check bus + five private witnesses) by the two-line is-zero gadget (with one fresh derived
    `inv`) is `PassCorrect`: soundness reconstructs the markers via `seqz_reconstruct`; completeness
    derives the is-zero constraints via `seqz_forward` and computes `inv` by `QuotientOrZero`. -/
theorem seqzCollapse_correct (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (r : Roles (p := p)) (Bm : BoundsMap p (collapsedSystem cs r) bs)
    (hvalid : rolesValid cs bs facts r Bm = true) :
    PassCorrect cs (collapsedSystem cs r) [(r.inv, invMethod r.R r.a0 r.a1 r.a2 r.a3)] bs := by
  classical
  -- Unpack the validity flags (before abstracting, so the bounds map keeps a single identity).
  simp only [rolesValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hvalid
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hprime, h1024⟩, hK⟩, hbpb⟩, hbc⟩, hbusEmemB⟩, hclMem⟩, hboolMem⟩, hboolNC⟩,
    hpure⟩, hbounds⟩, hnodup⟩, hinvfresh⟩, hpow5⟩ := hvalid
  have hpowR : r.R.powdrId?.isSome = true := hpow5 r.R (by simp)
  have hpowa : ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List Variable), a.powdrId?.isSome = true :=
    fun a ha => hpow5 a (List.mem_cons_of_mem r.R ha)
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : NeZero p := ⟨by omega⟩
  -- Byte bounds on the limbs, phrased `Bm`-free (any assignment satisfying the output buses),
  -- so the (soon-abstracted) bounds map is not referenced again.
  have habyteAll : ∀ (e : Variable → ZMod p),
      (∀ bi ∈ (collapsedSystem cs r).busInteractions,
        (bi.eval e).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval e) = false) →
      ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List Variable), (e a).val < 256 := by
    intro e he a ha
    have hb := hbounds a ha
    split at hb
    · rename_i ba heq
      exact lt_of_lt_of_le (Bm.sound e he a ba heq) (by simpa using hb)
    · simp at hb
  set cl := clusterConstraints r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K with hcldef
  set busE := clusterBus r.busId r.m3 r.m2 r.m1 r.m0 r.dv with hbusEdef
  set out := collapsedSystem cs r with houtdef
  set inv := r.inv with hinvdef
  set method : ComputationMethod p := invMethod r.R r.a0 r.a1 r.a2 r.a3 with hmethoddef
  have hinvid : inv.powdrId? = none := rfl
  -- `busE` is stateless (byte-pair bus).
  have hbusStateless : bs.isStateful r.busId = false := (facts.bytePairBus_sound r.busId hbpb).1
  -- `busE` is an input bus interaction (the range check that pins `dv` to a byte).
  have hbusEmem : busE ∈ cs.busInteractions := by simpa using hbusEmemB
  -- Distinctness: `R, a0..a3` are disjoint from the five witnesses.
  have hdisj : ∀ x ∈ ([r.R, r.a0, r.a1, r.a2, r.a3] : List Variable), x ∉ r.witnesses := by
    have hnd : ([r.R, r.a0, r.a1, r.a2, r.a3] ++ r.witnesses).Nodup := hnodup
    have hpw := (List.nodup_append.mp hnd).2.2
    exact fun x hx hxw => hpw x hx x hxw rfl
  have hRw : ∀ w ∈ r.witnesses, r.R ≠ w := fun w hw h => hdisj r.R (by simp) (h ▸ hw)
  have ha0w : ∀ w ∈ r.witnesses, r.a0 ≠ w := fun w hw h => hdisj r.a0 (by simp) (h ▸ hw)
  have ha1w : ∀ w ∈ r.witnesses, r.a1 ≠ w := fun w hw h => hdisj r.a1 (by simp) (h ▸ hw)
  have ha2w : ∀ w ∈ r.witnesses, r.a2 ≠ w := fun w hw h => hdisj r.a2 (by simp) (h ▸ hw)
  have ha3w : ∀ w ∈ r.witnesses, r.a3 ≠ w := fun w hw h => hdisj r.a3 (by simp) (h ▸ hw)
  have hwmem : ∀ w ∈ ([r.m3, r.m2, r.m1, r.m0, r.dv] : List Variable), w ∈ r.witnesses := by
    intro w hw; simpa [Roles.witnesses] using hw
  -- `boolConstraint R` is a kept constraint of `out`.
  have hboolOut : boolConstraint r.R ∈ out.algebraicConstraints := by
    rw [houtdef, collapsedSystem]
    refine List.mem_append_left _ (List.mem_filter.2 ⟨by simpa using hboolMem, ?_⟩)
    simpa using hboolNC
  -- `nc` are kept constraints of `out`.
  have hncOut : ∀ c ∈ newConstraints r.R r.a0 r.a1 r.a2 r.a3 r.inv, c ∈ out.algebraicConstraints := by
    intro c hc; rw [houtdef, collapsedSystem]; exact List.mem_append_right _ hc
  -- Cluster constraints are `cs`-constraints (from validity).
  have hclMem' : ∀ c ∈ cl, c ∈ cs.algebraicConstraints := fun c hc => by
    have := hclMem c hc; simpa using this
  -- Purity: witnesses do not occur outside the cluster / range bus.
  have hpureC : ∀ w ∈ r.witnesses, ∀ c ∈ cs.algebraicConstraints, c ∉ cl → w ∉ c.vars := by
    intro w hw c hc hccl
    have hp := hpure w hw
    simp only [pureInCluster, Bool.and_eq_true, List.all_eq_true] at hp
    have hcc := hp.1 c hc
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcc
    rcases hcc with h | h
    · exact absurd (by simpa using h) hccl
    · exact mentions_false_not_mem_vars w c h
  have hpureB : ∀ w ∈ r.witnesses, ∀ bi ∈ cs.busInteractions, bi ≠ busE →
      w ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, w ∉ e.vars := by
    intro w hw bi hbi hbne
    have hp := hpure w hw
    simp only [pureInCluster, Bool.and_eq_true, List.all_eq_true] at hp
    have hbb := hp.2 bi hbi
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true] at hbb
    rcases hbb with h | ⟨hm, hpay⟩
    · exact absurd h hbne
    · exact ⟨mentions_false_not_mem_vars w bi.multiplicity hm,
        fun e he => mentions_false_not_mem_vars w e (hpay e he)⟩
  -- Witness membership and internal distinctness (for `setFive` lookups).
  have wm3 : r.m3 ∈ r.witnesses := hwmem r.m3 (by simp)
  have wm2 : r.m2 ∈ r.witnesses := hwmem r.m2 (by simp)
  have wm1 : r.m1 ∈ r.witnesses := hwmem r.m1 (by simp)
  have wm0 : r.m0 ∈ r.witnesses := hwmem r.m0 (by simp)
  have wdv : r.dv ∈ r.witnesses := hwmem r.dv (by simp)
  have hwnd : r.witnesses.Nodup :=
    (List.nodup_append.mp (show ([r.R, r.a0, r.a1, r.a2, r.a3] ++ r.witnesses).Nodup from hnodup)).2.1
  simp only [Roles.witnesses, List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
    List.not_mem_nil, List.nodup_nil, and_true, or_false] at hwnd
  obtain ⟨⟨d32, d31, d30, d3d⟩, ⟨d21, d20, d2d⟩, ⟨d10, d1d⟩, d0d, -⟩ := hwnd
  -- `R, a0..a3` are `cs`-variables (anchors for `inv`-freshness framing).
  have hRcs : r.R ∈ cs.vars :=
    ConstraintSystem.mem_vars_of_constraint (by simpa using hboolMem)
      (by simp [boolConstraint, Expression.vars, eM1])
  have ha3cs : r.a3 ∈ cs.vars :=
    ConstraintSystem.mem_vars_of_constraint
      (c := .mul (sExpr r.m3 r.m2 r.m1 r.m0 3) (.mul (.var r.a3) (krExpr r.K r.R)))
      (hclMem' _ (by rw [hcldef]; simp [clusterConstraints]))
      (by simp [Expression.vars, sExpr, krExpr, eM1])
  have ha2cs : r.a2 ∈ cs.vars :=
    ConstraintSystem.mem_vars_of_constraint
      (c := .mul (sExpr r.m3 r.m2 r.m1 r.m0 2) (.mul (.var r.a2) (krExpr r.K r.R)))
      (hclMem' _ (by rw [hcldef]; simp [clusterConstraints]))
      (by simp [Expression.vars, sExpr, krExpr, eM1])
  have ha1cs : r.a1 ∈ cs.vars :=
    ConstraintSystem.mem_vars_of_constraint
      (c := .mul (sExpr r.m3 r.m2 r.m1 r.m0 1) (.mul (.var r.a1) (krExpr r.K r.R)))
      (hclMem' _ (by rw [hcldef]; simp [clusterConstraints]))
      (by simp [Expression.vars, sExpr, krExpr, eM1])
  have ha0cs : r.a0 ∈ cs.vars :=
    ConstraintSystem.mem_vars_of_constraint
      (c := .mul (sExpr r.m3 r.m2 r.m1 r.m0 0) (.mul (.add eM1 (.var r.a0)) (krExpr r.K r.R)))
      (hclMem' _ (by rw [hcldef]; simp [clusterConstraints]))
      (by simp [Expression.vars, sExpr, krExpr, eM1])
  have hacs_mem : ∀ a ∈ ([r.a0, r.a1, r.a2, r.a3] : List Variable), a ∈ cs.vars := by
    intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ha0cs
    · exact ha1cs
    · exact ha2cs
    · exact ha3cs
  -- A stateful bus of `cs` is never the (stateless) range bus `busE`.
  have hstatefulNe : ∀ (bi : BusInteraction (Expression p)),
      bs.isStateful bi.busId = true → bi ≠ busE := by
    intro bi hst h
    rw [h, show busE.busId = r.busId from rfl, hbusStateless] at hst
    exact absurd hst (by decide)
  -- Evaluating the range bus at any assignment.
  have hbusEvalAt : ∀ (e : Variable → ZMod p), busE.eval e =
      { busId := r.busId, multiplicity := e r.m3 + e r.m2 + e r.m1 + e r.m0,
        payload := [-1 + e r.dv, 0, 0, 0] } := by
    intro e
    simp only [hbusEdef, clusterBus, BusInteraction.eval, markerSum, eM1, e0, Expression.eval,
      List.map_cons, List.map_nil]
  -- Dropping stateless bus interactions leaves the stateful-filtered bus list unchanged.
  have hStateEqL : ∀ (keep : BusInteraction (Expression p) → Bool)
      (L : List (BusInteraction (Expression p))),
      (∀ bi ∈ L, keep bi = false → bs.isStateful bi.busId = false) →
      (L.filter keep).filter (fun bi => bs.isStateful bi.busId)
        = L.filter (fun bi => bs.isStateful bi.busId) := by
    intro keep L hL
    induction L with
    | nil => rfl
    | cons bi rest ih =>
      have hrest := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
      by_cases hk : keep bi = true
      · rw [List.filter_cons_of_pos hk]
        by_cases hst : bs.isStateful bi.busId = true
        · rw [List.filter_cons_of_pos (by simpa using hst),
              List.filter_cons_of_pos (by simpa using hst), hrest]
        · rw [List.filter_cons_of_neg (by simpa using hst),
              List.filter_cons_of_neg (by simpa using hst), hrest]
      · have hst : bs.isStateful bi.busId = false := hL bi (List.mem_cons_self ..) (by simpa using hk)
        rw [List.filter_cons_of_neg hk, List.filter_cons_of_neg (by simp [hst]), hrest]
  -- Hence `out` and `cs` have the same side effects at every assignment.
  have hside : ∀ (e : Variable → ZMod p), out.sideEffects bs e = cs.sideEffects bs e := by
    intro e
    simp only [houtdef, collapsedSystem, ConstraintSystem.sideEffects, ← hbusEdef]
    rw [hStateEqL (fun bi => decide (bi ≠ busE)) cs.busInteractions (fun bi _ hkf => by
      have hbe : bi = busE := by simpa using hkf
      rw [hbe]; exact hbusStateless)]
  -- **Soundness reconstruction.** Any `out`-satisfying assignment lifts to a `cs`-satisfying one
  -- (rebuild the five witnesses), agreeing on every non-range bus and on side effects.
  have hReconstruct : ∀ e, out.satisfies bs e → ∃ g,
      cs.satisfies bs g ∧
      (∀ bi ∈ cs.busInteractions, bi ≠ busE → bi.eval g = bi.eval e) ∧
      cs.sideEffects bs g = cs.sideEffects bs e := by
    intro env hsatOut
    -- byte bounds on the limbs (output buses hold at `env`)
    have hb0 := habyteAll env hsatOut.2 r.a0 (by simp)
    have hb1 := habyteAll env hsatOut.2 r.a1 (by simp)
    have hb2 := habyteAll env hsatOut.2 r.a2 (by simp)
    have hb3 := habyteAll env hsatOut.2 r.a3 (by simp)
    -- `R ∈ {0,1}` and the two is-zero constraints hold at `env`.
    have hRbool : env r.R = 0 ∨ env r.R = 1 := by
      have h := hsatOut.1 (boolConstraint r.R) hboolOut
      simp only [boolConstraint, eM1, Expression.eval] at h
      exact zbool (by linear_combination h)
    have hRS : env r.R * (env r.a0 + env r.a1 + env r.a2 + env r.a3) = 0 := by
      have h := hsatOut.1 (Expression.mul (.var r.R) (sumExpr4 r.a0 r.a1 r.a2 r.a3))
        (hncOut _ (by simp [newConstraints]))
      simpa only [sumExpr4, Expression.eval] using h
    have hSR : env r.a0 + env r.a1 + env r.a2 + env r.a3 = 0 → env r.R = 1 := by
      intro hS
      have h := hsatOut.1 (Expression.add (.mul (.var r.inv) (sumExpr4 r.a0 r.a1 r.a2 r.a3))
        (.add (.var r.R) eM1)) (hncOut _ (by simp [newConstraints]))
      simp only [sumExpr4, eM1, Expression.eval] at h
      have hz : env r.R + -1 = 0 := by linear_combination h - env r.inv * hS
      linear_combination hz
    -- rebuild the markers / diff value
    obtain ⟨v0, v1, v2, v3, vd, eB3, eB2, eB1, eB0, eBs, eNM, eP3, eP2, eP1, eP0,
        eD3, eD2, eD1, eD0, eBus⟩ :=
      seqz_reconstruct h1024 r.K (env r.R) (env r.a0) (env r.a1) (env r.a2) (env r.a3)
        hK hb0 hb1 hb2 hb3 hRbool hRS hSR
    set g := setFive r.m3 r.m2 r.m1 r.m0 r.dv v3 v2 v1 v0 vd env with hgdef
    have gm3 : g r.m3 = v3 := setFive_at3
    have gm2 : g r.m2 = v2 := setFive_at2 (Ne.symm d32)
    have gm1 : g r.m1 = v1 := setFive_at1 (Ne.symm d31) (Ne.symm d21)
    have gm0 : g r.m0 = v0 := setFive_at0 (Ne.symm d30) (Ne.symm d20) (Ne.symm d10)
    have gdv : g r.dv = vd := setFive_atd (Ne.symm d3d) (Ne.symm d2d) (Ne.symm d1d) (Ne.symm d0d)
    have ga0 : g r.a0 = env r.a0 :=
      setFive_free (ha0w _ wm3) (ha0w _ wm2) (ha0w _ wm1) (ha0w _ wm0) (ha0w _ wdv)
    have ga1 : g r.a1 = env r.a1 :=
      setFive_free (ha1w _ wm3) (ha1w _ wm2) (ha1w _ wm1) (ha1w _ wm0) (ha1w _ wdv)
    have ga2 : g r.a2 = env r.a2 :=
      setFive_free (ha2w _ wm3) (ha2w _ wm2) (ha2w _ wm1) (ha2w _ wm0) (ha2w _ wdv)
    have ga3 : g r.a3 = env r.a3 :=
      setFive_free (ha3w _ wm3) (ha3w _ wm2) (ha3w _ wm1) (ha3w _ wm0) (ha3w _ wdv)
    have gR : g r.R = env r.R :=
      setFive_free (hRw _ wm3) (hRw _ wm2) (hRw _ wm1) (hRw _ wm0) (hRw _ wdv)
    -- frame: expressions free of the five witnesses evaluate the same at `g` and `env`
    have hgframeE : ∀ (e : Expression p), (∀ w ∈ r.witnesses, w ∉ e.vars) →
        e.eval g = e.eval env := by
      intro e he
      apply Expression.eval_congr
      intro x hx
      exact setFive_free (fun h => he r.m3 wm3 (h ▸ hx)) (fun h => he r.m2 wm2 (h ▸ hx))
        (fun h => he r.m1 wm1 (h ▸ hx)) (fun h => he r.m0 wm0 (h ▸ hx))
        (fun h => he r.dv wdv (h ▸ hx))
    have hgframeBus : ∀ bi ∈ cs.busInteractions, bi ≠ busE → bi.eval g = bi.eval env := by
      intro bi hbi hne
      have hmul : bi.multiplicity.eval g = bi.multiplicity.eval env :=
        hgframeE bi.multiplicity (fun w hw => (hpureB w hw bi hbi hne).1)
      have hpay : bi.payload.map (fun e => e.eval g) = bi.payload.map (fun e => e.eval env) :=
        List.map_congr_left (fun e he => hgframeE e (fun w hw => (hpureB w hw bi hbi hne).2 e he))
      simp only [BusInteraction.eval, hmul, hpay]
    -- the range bus, evaluated at `g`, is a byte-pair message accepted by the fact
    have hbusEval : busE.eval g =
        { busId := r.busId, multiplicity := v3 + v2 + v1 + v0, payload := [-1 + vd, 0, 0, 0] } := by
      rw [hbusEvalAt g, gm3, gm2, gm1, gm0, gdv]
    -- all 14 cluster constraints hold at `g`
    have hclG : ∀ c ∈ cl, c.eval g = 0 := by
      rw [hcldef]
      refine (clusterEval_iff r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K g).mpr ?_
      simp only [gm3, gm2, gm1, gm0, gdv, ga0, ga1, ga2, ga3, gR]
      exact ⟨by linear_combination eB3, by linear_combination eP3, by linear_combination eD3,
        by linear_combination eB2, by linear_combination eP2, by linear_combination eD2,
        by linear_combination eB1, by linear_combination eP1, by linear_combination eD1,
        by linear_combination eB0, by linear_combination eP0, by linear_combination eD0,
        by linear_combination eBs, by linear_combination eNM⟩
    -- `g` satisfies `cs`
    have hgcs : cs.satisfies bs g := by
      refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
      · by_cases hccl : c ∈ cl
        · exact hclG c hccl
        · have hcout : c ∈ out.algebraicConstraints := by
            rw [houtdef, collapsedSystem, ← hcldef]
            exact List.mem_append_left _ (List.mem_filter.2 ⟨hc, by simpa using hccl⟩)
          rw [hgframeE c (fun w hw => hpureC w hw c hc hccl)]
          exact hsatOut.1 c hcout
      · by_cases hbe : bi = busE
        · show (bi.eval g).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval g) = false
          rw [hbe, hbusEval]
          intro hmult
          exact bus_accepts_byte_zero facts r.busId hbpb hbc (-1 + vd) (v3 + v2 + v1 + v0)
            (eBus hmult)
        · have hbout : bi ∈ out.busInteractions := by
            rw [houtdef, collapsedSystem, ← hbusEdef]
            exact List.mem_filter.2 ⟨hbi, by simpa using hbe⟩
          show (bi.eval g).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval g) = false
          rw [hgframeBus bi hbi hbe]
          exact hsatOut.2 bi hbout
    -- side effects agree (frame on the stateful buses, none of which is `busE`)
    have hseSound : cs.sideEffects bs g = cs.sideEffects bs env := by
      simp only [ConstraintSystem.sideEffects]
      apply List.map_congr_left
      intro bi hbi
      have hbimem : bi ∈ cs.busInteractions := List.mem_of_mem_filter hbi
      have hst : bs.isStateful bi.busId = true := by simpa using List.of_mem_filter hbi
      rw [hgframeBus bi hbimem (hstatefulNe bi hst)]
    exact ⟨g, hgcs, hgframeBus, hseSound⟩
  -- Every output variable is either the fresh `inv` or an input variable.
  have hout_vars : ∀ v ∈ out.vars, v = inv ∨ v ∈ cs.vars := by
    intro v hv
    rw [ConstraintSystem.mem_vars] at hv
    rcases hv with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hvbi⟩
    · rw [houtdef, collapsedSystem, List.mem_append] at hc
      rcases hc with hcf | hcnc
      · exact Or.inr (ConstraintSystem.mem_vars_of_constraint (List.mem_of_mem_filter hcf) hvc)
      · simp only [newConstraints, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hcnc
        rcases hcnc with rfl | rfl
        · simp only [sumExpr4, Expression.vars, List.mem_append, List.mem_singleton,
            List.mem_cons, List.nil_append, List.not_mem_nil, or_false, or_assoc] at hvc
          rcases hvc with rfl | rfl | rfl | rfl | rfl
          · exact Or.inr hRcs
          · exact Or.inr ha0cs
          · exact Or.inr ha1cs
          · exact Or.inr ha2cs
          · exact Or.inr ha3cs
        · simp only [sumExpr4, eM1, Expression.vars, List.mem_append, List.mem_singleton,
            List.mem_cons, List.nil_append, List.not_mem_nil, or_false, or_assoc] at hvc
          rcases hvc with rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ha0cs
          · exact Or.inr ha1cs
          · exact Or.inr ha2cs
          · exact Or.inr ha3cs
          · exact Or.inr hRcs
    · rw [houtdef, collapsedSystem] at hbi
      exact Or.inr (ConstraintSystem.mem_vars.2 (Or.inr ⟨bi, List.mem_of_mem_filter hbi, hvbi⟩))
  -- Assemble the four `PassCorrect` obligations.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- soundness
    intro env hsatOut
    obtain ⟨g, hgcs, _, hse⟩ := hReconstruct env hsatOut
    refine ⟨g, hgcs, ?_⟩
    have hEq : cs.sideEffects bs g = out.sideEffects bs env := by rw [hse, ← hside env]
    rw [hEq]
    exact BusState.equiv_refl _
  · -- invariant preservation
    intro hcsInv env hsatOut bi hbiOut
    show (bi.eval env).multiplicity ≠ 0 → bs.breaksInvariant (bi.eval env) = false
    obtain ⟨g, hgcs, hgfr, _⟩ := hReconstruct env hsatOut
    have hbicsmem : bi ∈ cs.busInteractions := by
      have := hbiOut; rw [houtdef, collapsedSystem] at this; exact List.mem_of_mem_filter this
    have hbne : bi ≠ busE := by
      have := hbiOut; rw [houtdef, collapsedSystem, ← hbusEdef] at this
      simpa using (List.of_mem_filter this)
    rw [← hgfr bi hbicsmem hbne]
    exact hcsInv g hgcs bi hbicsmem
  · -- no new powdr-ID column
    intro v hvout hvpow
    rcases hout_vars v hvout with rfl | hcsv
    · rw [hinvid] at hvpow; simp at hvpow
    · exact hcsv
  · -- completeness
    intro env hadm hsat
    set envC := Function.update env inv (method.eval env) with hCdef
    have hagreeC : ∀ x ∈ cs.vars, envC x = env x := by
      intro x hx
      refine Function.update_of_ne (fun h => hinvfresh ?_) _ _
      rw [← h]; exact hx
    have hbeC : ∀ bi ∈ cs.busInteractions, bi.eval envC = bi.eval env := by
      intro bi hbi
      unfold BusInteraction.eval
      congr 1
      · exact Expression.eval_congr _ _ _
          (fun x hx => hagreeC x (ConstraintSystem.mem_vars_of_mult hbi hx))
      · exact List.map_congr_left (fun e he => Expression.eval_congr _ _ _
          (fun x hx => hagreeC x (ConstraintSystem.mem_vars_of_payload hbi he hx)))
    -- the 14 cluster value-equations at `env`
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ :=
      (clusterEval_iff r.m3 r.m2 r.m1 r.m0 r.dv r.R r.a3 r.a2 r.a1 r.a0 r.K env).mp
        (by rw [← hcldef]; exact fun c hc => hsat.1 c (hclMem' c hc))
    -- byte bounds (input buses hold at `env`, and the output buses are a subset)
    have hbusOutEnv : ∀ bi ∈ (collapsedSystem cs r).busInteractions,
        (bi.eval env).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval env) = false := by
      intro bi hbi hm
      rw [collapsedSystem] at hbi
      exact hsat.2 bi (List.mem_of_mem_filter hbi) hm
    have hb0 := habyteAll env hbusOutEnv r.a0 (by simp)
    have hb1 := habyteAll env hbusOutEnv r.a1 (by simp)
    have hb2 := habyteAll env hbusOutEnv r.a2 (by simp)
    have hb3 := habyteAll env hbusOutEnv r.a3 (by simp)
    have hRbool : env r.R = 0 ∨ env r.R = 1 := by
      have h := hsat.1 (boolConstraint r.R) (by simpa using hboolMem)
      simp only [boolConstraint, eM1, Expression.eval] at h
      exact zbool (by linear_combination h)
    -- the range bus at `env` pins `dv − 1` to the byte range when a marker is set
    have hbusFwd : (env r.m3 + env r.m2 + env r.m1 + env r.m0) ≠ 0 → (-1 + env r.dv).val < 256 := by
      intro hmult
      have hbe := hsat.2 busE hbusEmem
      rw [hbusEvalAt env] at hbe
      exact bus_byte_of_accepts facts r.busId hbpb hbc (-1 + env r.dv) _ (hbe hmult)
    -- forward: the gadget computes `cmp = [S == 0]`
    obtain ⟨hfRS, hfSR⟩ :=
      seqz_forward h1024 r.K (env r.R) (env r.a0) (env r.a1) (env r.a2) (env r.a3)
        (env r.m0) (env r.m1) (env r.m2) (env r.m3) (env r.dv)
        hK hb0 hb1 hb2 hb3 f1 f4 f7 f10 f13 f14 f2 f5 f8 f11 f3 f6 f9 f12 hRbool hbusFwd
    refine ⟨envC, ⟨fun c hc => ?_, fun bi hbi => ?_⟩, ?_, ?_, ?_, ?_⟩
    · -- out algebraic constraints hold at `envC`
      rw [houtdef, collapsedSystem, List.mem_append] at hc
      rcases hc with hcf | hcnc
      · have hccs : c ∈ cs.algebraicConstraints := List.mem_of_mem_filter hcf
        rw [Expression.eval_congr c envC env
          (fun x hx => hagreeC x (ConstraintSystem.mem_vars_of_constraint hccs hx))]
        exact hsat.1 c hccs
      · simp only [newConstraints, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hcnc
        rcases hcnc with rfl | rfl
        · show Expression.eval (.mul (.var r.R) (sumExpr4 r.a0 r.a1 r.a2 r.a3)) envC = 0
          simp only [sumExpr4, Expression.eval]
          rw [hagreeC r.R hRcs, hagreeC r.a0 ha0cs, hagreeC r.a1 ha1cs, hagreeC r.a2 ha2cs,
            hagreeC r.a3 ha3cs]
          linear_combination hfRS
        · show Expression.eval
            (.add (.mul (.var inv) (sumExpr4 r.a0 r.a1 r.a2 r.a3)) (.add (.var r.R) eM1)) envC = 0
          simp only [sumExpr4, eM1, Expression.eval]
          rw [hagreeC r.a0 ha0cs, hagreeC r.a1 ha1cs, hagreeC r.a2 ha2cs, hagreeC r.a3 ha3cs,
            hagreeC r.R hRcs, hCdef, Function.update_self, hmethoddef, invMethod]
          by_cases hS0 : env r.a0 + env r.a1 + env r.a2 + env r.a3 = 0
          · simp only [ComputationMethod.eval, sumExpr4, e1, eM1, Expression.eval, if_pos hS0]
            rw [hfSR hS0]; ring
          · simp only [ComputationMethod.eval, sumExpr4, e1, eM1, Expression.eval, if_neg hS0]
            rw [mul_right_comm, inv_mul_cancel₀ hS0, one_mul]; ring
    · -- out bus interactions are accepted at `envC`
      have hbics : bi ∈ cs.busInteractions := by
        rw [houtdef, collapsedSystem] at hbi; exact List.mem_of_mem_filter hbi
      show (bi.eval envC).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval envC) = false
      rw [hbeC bi hbics]; exact hsat.2 bi hbics
    · -- admissibility transfers (the dropped range bus is stateless)
      have hadmC : cs.admissible bs envC := by
        unfold ConstraintSystem.admissible
        rw [List.map_congr_left (fun bi hbi => hbeC bi hbi)]; exact hadm
      exact (ConstraintSystem.admissible_filterBus cs bs (fun bi => decide (bi ≠ busE)) envC
        (fun bi _ hkf => Or.inr (by have hbe : bi = busE := by simpa using hkf
                                    rw [hbe]; exact hbusStateless))).2 hadmC
    · -- side effects match
      have hseC : out.sideEffects bs envC = cs.sideEffects bs env := by
        rw [hside envC]
        show (cs.busInteractions.filter _).map _ = (cs.busInteractions.filter _).map _
        exact List.map_congr_left (fun bi hbi => by rw [hbeC bi (List.mem_of_mem_filter hbi)])
      rw [hseC]; exact BusState.equiv_refl _
    · -- powdr-ID columns keep their values
      intro v hvpow
      exact Function.update_of_ne (fun h => by rw [h, hinvid] at hvpow; simp at hvpow) _ _
    · -- reconstruction of the derived `inv`
      intro inputVars hpowIn dsIn hrec v hvout hvnone
      by_cases hveq : v = inv
      · subst hveq
        have hmvars : ∀ x ∈ method.vars, x = r.R ∨ x ∈ ([r.a0, r.a1, r.a2, r.a3] : List Variable) := by
          intro x hx
          rw [hmethoddef, invMethod] at hx
          simp only [ComputationMethod.vars, sumExpr4, e1, eM1, Expression.vars, List.mem_append,
            List.mem_singleton, List.mem_cons, List.nil_append, List.not_mem_nil, or_false,
            or_assoc] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (by simp)
          · exact Or.inr (by simp)
          · exact Or.inr (by simp)
          · exact Or.inr (by simp)
        refine ⟨method, ?_, ?_, ?_, ?_⟩
        · rw [Derivations.methodFor_append]; simp [Derivations.methodFor]
        · intro x hx
          rcases hmvars x hx with rfl | hxa
          · exact hpowR
          · exact hpowa x hxa
        · intro x hx
          rcases hmvars x hx with rfl | hxa
          · exact hpowIn r.R hRcs hpowR
          · exact hpowIn x (hacs_mem x hxa) (hpowa x hxa)
        · rw [hCdef, Function.update_self]
          refine ComputationMethod.eval_congr method envC env (fun x hx => ?_)
          rcases hmvars x hx with rfl | hxa
          · exact hagreeC r.R hRcs
          · exact hagreeC x (hacs_mem x hxa)
      · have hvcs : v ∈ cs.vars := (hout_vars v hvout).resolve_left hveq
        obtain ⟨cm, hmf, hcmpow, hcmin, hcmev⟩ := hrec v hvcs hvnone
        refine ⟨cm, ?_, hcmpow, hcmin, ?_⟩
        · rw [Derivations.methodFor_append]
          simp only [Derivations.methodFor, Option.orElse]
          rw [if_neg (fun h => hveq h.symm)]; simpa using hmf
        · rw [hCdef, Function.update_of_ne hveq, ← hcmev]
          refine ComputationMethod.eval_congr cm envC env (fun x hx => ?_)
          refine Function.update_of_ne (fun h => ?_) _ _
          have hxp : x.powdrId?.isSome = true := hcmpow x hx
          rw [h, hinvid] at hxp; simp at hxp

/-- Scan the bus interactions for the first collapsible gadget. -/
def tryList (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (Expression p)) → Option (PassResult cs bs)
  | [] => none
  | bi :: rest =>
    match extractRoles cs bi with
    | none => tryList cs bs facts rest
    | some r =>
      if h : rolesValid cs bs facts r (BoundsMap.build facts) = true then
        some ⟨collapsedSystem cs r, [(r.inv, invMethod r.R r.a0 r.a1 r.a2 r.a3)],
          seqzCollapse_correct cs bs facts r (BoundsMap.build facts) h⟩
      else tryList cs bs facts rest

/-- The seqz-collapse pass: replace the first recognised `sltu x, 1` LessThan gadget by the is-zero
    gadget, dropping the four `diff_marker`s and `diff_val` and introducing one `QuotientOrZero`
    witness. Identity with `BusFacts.trivial`. -/
def seqzCollapsePass : VerifiedPassW p := fun cs bs facts =>
  (tryList cs bs facts cs.busInteractions).getD ⟨cs, [], PassCorrect.refl cs bs⟩

end SeqzCollapse
