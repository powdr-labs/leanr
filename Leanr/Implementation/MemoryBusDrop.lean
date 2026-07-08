import Leanr.MemoryBus

set_option autoImplicit false

/-! # Dropping matched send/receive pairs preserves `admissibleMemoryBus`

The `MemoryBus`-level machinery behind the pair-cancellation pass (`OptimizerPasses/BusPairCancel`).
When a memory access chain leaves a *send* `S` (multiplicity `1`) and a later *receive* `R`
(multiplicity `-1`) carrying the same payload — the write of one access and the read of the next —
the two contribute `0` to every message's net multiplicity, so both can be dropped. The completeness
half needs the VM's `admissible` predicate to survive that drop; these lemmas discharge that at the
concrete-discipline level (`admissibleMemoryBus`).

Kept out of the audit surface (`MemoryBus.lean`): these are consequences of the discipline, not part
of it. The reverse bridge that lets a *generic* pass rebuild the abstract `bs.admissible` from these
is the `admissible_dropPair` field of `BusFacts`. -/

variable {p : ℕ}

/-- Removing a single interaction `e` from an `admissibleMemoryBus` list preserves the discipline,
    provided `e` is inactive or **no active same-address send precedes it**. The only new
    consecutive pair a removal can expose sits across `e`'s position; a fresh *send→receive* pair
    there would need an active same-address send before `e`, which the side condition forbids. -/
theorem admissibleMemoryBus_dropOne (shape : MemoryBusShape) (hp1 : (1 : ZMod p) ≠ 0)
    (P Q : List (BusInteraction (ZMod p))) (e : BusInteraction (ZMod p))
    (hadm : admissibleMemoryBus shape (P ++ e :: Q))
    (hcond : e.multiplicity = 0 ∨
       ∀ m ∈ P, m.multiplicity ≠ 0 → shape.address m = shape.address e → m.multiplicity ≠ 1) :
    admissibleMemoryBus shape (P ++ Q) := by
  intro pre mid post S R hsplit hS hR haddr hmid
  have hsplit2 : P ++ Q = pre ++ (S :: (mid ++ R :: post)) := by
    rw [hsplit]; simp only [List.append_assoc, List.cons_append]
  rcases List.append_eq_append_iff.mp hsplit2 with ⟨a', hpre, hQ⟩ | ⟨c', hP, hT⟩
  · -- Case A: `pre = P ++ a'`, `Q = a' ++ S :: (mid ++ R :: post)`; `e` lands in the prefix.
    refine hadm (P ++ e :: a') mid post S R ?_ hS hR haddr hmid
    rw [hQ]; simp only [List.append_assoc, List.cons_append]
  · -- Case B: `P = pre ++ c'`, `S :: (mid ++ R :: post) = c' ++ Q`.
    rcases c' with _ | ⟨c0, c''⟩
    · -- `c' = []`: `e` lands just before `S`.
      simp only [List.append_nil] at hP
      simp only [List.nil_append] at hT
      refine hadm (pre ++ [e]) mid post S R ?_ hS hR haddr hmid
      rw [hP, ← hT]; simp only [List.append_assoc, List.cons_append, List.nil_append]
    · -- `c' = c0 :: c''`, so `c0 = S` and `mid ++ R :: post = c'' ++ Q`.
      rw [List.cons_append, List.cons.injEq] at hT
      obtain ⟨rfl, hT2⟩ := hT
      have hSP : S ∈ P := by rw [hP]; exact List.mem_append_right pre (List.mem_cons_self ..)
      have hSne : S.multiplicity ≠ 0 := by rw [hS]; exact hp1
      have hEobl : e.multiplicity ≠ 0 → shape.address e = shape.address S → False := by
        intro hene haddreS
        rcases hcond with h0 | h1
        · exact hene h0
        · exact h1 S hSP hSne haddreS.symm hS
      rcases List.append_eq_append_iff.mp hT2 with ⟨w, hc''w, hRpw⟩ | ⟨w, hmidw, hQw⟩
      · -- `c'' = mid ++ w`, `R :: post = w ++ Q`; `e` lands at/after `R`.
        rcases w with _ | ⟨w0, w'⟩
        · -- `w = []`: `e` lands just before `R`.
          simp only [List.append_nil] at hc''w
          simp only [List.nil_append] at hRpw
          refine hadm pre (mid ++ [e]) post S R ?_ hS hR haddr ?_
          · rw [hP, hc''w, ← hRpw]; simp only [List.append_assoc, List.cons_append, List.nil_append]
          · intro m hm hmne hmaddr
            rw [List.mem_append] at hm
            rcases hm with hmm | hme
            · exact hmid m hmm hmne hmaddr
            · rcases List.mem_cons.mp hme with rfl | hcon
              · exact hEobl hmne hmaddr
              · exact absurd hcon (by simp)
        · -- `w = w0 :: w'`, so `w0 = R` and `post = w' ++ Q`; `e` lands in the suffix.
          rw [List.cons_append, List.cons.injEq] at hRpw
          obtain ⟨rfl, hpost2⟩ := hRpw
          refine hadm pre mid (w' ++ e :: Q) S R ?_ hS hR haddr hmid
          rw [hP, hc''w]; simp only [List.append_assoc, List.cons_append]
      · -- `mid = c'' ++ w`, `Q = w ++ R :: post`; `e` lands inside the middle.
        refine hadm pre (c'' ++ e :: w) post S R ?_ hS hR haddr ?_
        · rw [hP, hQw]; simp only [List.append_assoc, List.cons_append]
        · intro m hm hmne hmaddr
          rw [List.mem_append] at hm
          rcases hm with hmc | hme
          · exact hmid m (by rw [hmidw]; exact List.mem_append_left w hmc) hmne hmaddr
          · rcases List.mem_cons.mp hme with rfl | hmw
            · exact hEobl hmne hmaddr
            · exact hmid m (by rw [hmidw]; exact List.mem_append_right c'' hmw) hmne hmaddr

/-- Dropping a matched consecutive send→receive pair (`S₀` a send, `R₀` a later receive, no active
    same-address message between them) preserves `admissibleMemoryBus`, provided `S₀` is the
    earliest active send to its address (`hearliest`). Proved by removing `S₀` then `R₀`, each a
    `dropOne` whose side condition is met: no active same-address send precedes `S₀` (`hearliest`),
    and none precedes `R₀` either (`hearliest` for the `A` part, `hcons` for the `B` part). -/
theorem admissibleMemoryBus_dropPair (shape : MemoryBusShape) (hp1 : (1 : ZMod p) ≠ 0)
    (A B C : List (BusInteraction (ZMod p))) (S₀ R₀ : BusInteraction (ZMod p))
    (hadm : admissibleMemoryBus shape (A ++ S₀ :: B ++ R₀ :: C))
    (hcons : ∀ m ∈ B, m.multiplicity ≠ 0 → shape.address m = shape.address S₀ → False)
    (hearliest : ∀ m ∈ A, m.multiplicity ≠ 0 → shape.address m = shape.address S₀ →
        m.multiplicity ≠ 1)
    (haddrEq : shape.address S₀ = shape.address R₀) :
    admissibleMemoryBus shape (A ++ B ++ C) := by
  -- Step 1: remove `S₀`. `A ++ S₀ :: B ++ R₀ :: C = A ++ S₀ :: (B ++ R₀ :: C)`.
  have hadm1 : admissibleMemoryBus shape (A ++ S₀ :: (B ++ R₀ :: C)) := by
    have : A ++ S₀ :: B ++ R₀ :: C = A ++ S₀ :: (B ++ R₀ :: C) := by
      simp only [List.append_assoc, List.cons_append]
    rwa [this] at hadm
  have h1 : admissibleMemoryBus shape (A ++ (B ++ R₀ :: C)) :=
    admissibleMemoryBus_dropOne shape hp1 A (B ++ R₀ :: C) S₀ hadm1 (Or.inr hearliest)
  -- Step 2: remove `R₀`. `A ++ (B ++ R₀ :: C) = (A ++ B) ++ R₀ :: C`.
  have h2 : admissibleMemoryBus shape ((A ++ B) ++ R₀ :: C) := by
    have : A ++ (B ++ R₀ :: C) = (A ++ B) ++ R₀ :: C := by
      simp only [List.append_assoc]
    rwa [this] at h1
  have h3 : admissibleMemoryBus shape ((A ++ B) ++ C) := by
    refine admissibleMemoryBus_dropOne shape hp1 (A ++ B) C R₀ h2 (Or.inr ?_)
    intro m hm hmne hmaddr
    rw [List.mem_append] at hm
    have hmaddrS : shape.address m = shape.address S₀ := hmaddr.trans haddrEq.symm
    rcases hm with hmA | hmB
    · exact hearliest m hmA hmne hmaddrS
    · exact absurd (hcons m hmB hmne hmaddrS) not_false
  simpa only [List.append_assoc] using h3
