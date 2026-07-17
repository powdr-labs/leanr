import ApcOptimizer.MemoryBus

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

/-! ## Discipline lemmas kept out of the audit surface (`MemoryBus.lean`) -/

/-- The `setNew` multiplicity is nonzero whenever `1 ≠ 0` (it is `±1`). -/
theorem MemoryBusShape.setNewMult_ne_zero (shape : MemoryBusShape) (hp1 : (1 : ZMod p) ≠ 0) :
    (shape.setNewMult : ZMod p) ≠ 0 := by
  unfold MemoryBusShape.setNewMult
  split
  · exact hp1
  · exact neg_ne_zero.mpr hp1

/-- The consumption form the passes use. Given `admissibleMemoryBus` over the **active** sublist of a
    raw (all-multiplicity) message list `Lraw`, a `setNew` `S` followed by a `getPrevious` `R` to the
    same address in `Lraw`, with no active same-address message between them, have equal payloads.
    The passes exhibit the split of `Lraw` (the raw per-bus interaction list) directly; this lemma
    filters it to the active sublist that `admissibleMemoryBus` ranges over (`S`, `R` survive as they
    are active, given `1 ≠ 0`). -/
theorem admissibleMemoryBus.consecutive (shape : MemoryBusShape)
    (Lraw : List (BusInteraction (ZMod p))) (hp1 : (1 : ZMod p) ≠ 0)
    (h : admissibleMemoryBus shape (Lraw.filter (fun m => decide (m.multiplicity ≠ 0))))
    (pre mid post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p))
    (hsplit : Lraw = pre ++ S :: mid ++ R :: post)
    (hS : S.multiplicity = shape.setNewMult) (hR : R.multiplicity = -shape.setNewMult)
    (haddr : shape.address S = shape.address R)
    (hmid : ∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = shape.address S → False) :
    S.payload = R.payload := by
  have hwm : (shape.setNewMult : ZMod p) ≠ 0 := shape.setNewMult_ne_zero hp1
  have hPS : decide (S.multiplicity ≠ 0) = true := by
    simp only [hS, decide_eq_true_eq]; exact hwm
  have hPR : decide (R.multiplicity ≠ 0) = true := by
    simp only [hR, decide_eq_true_eq]; exact fun hh => hwm (neg_eq_zero.mp hh)
  refine h (pre.filter (fun m => decide (m.multiplicity ≠ 0)))
    (mid.filter (fun m => decide (m.multiplicity ≠ 0)))
    (post.filter (fun m => decide (m.multiplicity ≠ 0))) S R ?_ hS hR haddr ?_
  · subst hsplit
    simp only [List.filter_append, List.filter_cons, hPS, hPR, if_true]
  · intro m hm hmne hmaddr
    exact hmid m (List.mem_of_mem_filter hm) hmne hmaddr

/-! ## List split/filter/map plumbing (used to transport the shield across `filter`/`map`) -/

/-- A split of a filtered list lifts to a split of the original list, filtering each side. -/
theorem filter_split {α : Type*} (q : α → Bool) (x : α) :
    ∀ (l pre' suf' : List α), l.filter q = pre' ++ x :: suf' →
    ∃ pre suf, l = pre ++ x :: suf ∧ pre.filter q = pre' ∧ suf.filter q = suf'
  | [], _, _, h => by simp at h
  | a :: l', pre', suf', h => by
    by_cases hqa : q a = true
    · rw [List.filter_cons, if_pos hqa] at h
      match pre', h with
      | [], h =>
        rw [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, hf⟩ := h
        exact ⟨[], l', by simp, by simp, hf⟩
      | b :: pre'', h =>
        rw [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, hf⟩ := h
        obtain ⟨pre, suf, hl, hpre, hsuf⟩ := filter_split q x l' pre'' suf' hf
        exact ⟨a :: pre, suf, by rw [hl]; rfl, by rw [List.filter_cons, if_pos hqa, hpre], hsuf⟩
    · rw [List.filter_cons, if_neg hqa] at h
      obtain ⟨pre, suf, hl, hpre, hsuf⟩ := filter_split q x l' pre' suf' h
      exact ⟨a :: pre, suf, by rw [hl]; rfl, by rw [List.filter_cons, if_neg hqa, hpre], hsuf⟩

/-- A split of a mapped list lifts to a split of the original list. -/
theorem map_split {α β : Type*} (f : α → β) (x : β) :
    ∀ (l : List α) (pre' suf' : List β), l.map f = pre' ++ x :: suf' →
    ∃ pre a suf, l = pre ++ a :: suf ∧ pre.map f = pre' ∧ f a = x ∧ suf.map f = suf'
  | [], _, _, h => by simp at h
  | a :: l', pre', suf', h => by
    rw [List.map_cons] at h
    match pre', h with
    | [], h =>
      rw [List.nil_append, List.cons.injEq] at h
      obtain ⟨hfa, hsuf⟩ := h
      exact ⟨[], a, l', by simp, by simp, hfa, hsuf⟩
    | b :: pre'', h =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, hf⟩ := h
      obtain ⟨pre, a', suf, hl, hpre, hfa, hsuf⟩ := map_split f x l' pre'' suf' hf
      exact ⟨a :: pre, a', suf, by rw [hl]; rfl, by rw [List.map_cons, hpre], hfa, hsuf⟩

/-- Removing a single interaction `e` from an `admissibleMemoryBus` list preserves the discipline,
    provided `e` is inactive or **every active same-address send in `P` is followed by an active
    same-address receive in `P`** (the *shield* condition; strictly weaker than "no active
    same-address send precedes `e`"). The only new consecutive pair a removal can expose sits
    across `e`'s position; a fresh *send→receive* pair there would need an active same-address send
    in `P` with no active same-address receive between it and the exposed receive — but the shield
    receive sits in that gap and violates the pair's "no active same-address message between"
    obligation, so no such pair survives. -/
theorem admissibleMemoryBus_dropOne (shape : MemoryBusShape) (hp1 : (1 : ZMod p) ≠ 0)
    (P Q : List (BusInteraction (ZMod p))) (e : BusInteraction (ZMod p))
    (hadm : admissibleMemoryBus shape (P ++ e :: Q))
    (hcond : e.multiplicity = 0 ∨
       ∀ (P₁ : List (BusInteraction (ZMod p))) (Sx : BusInteraction (ZMod p))
         (P₂ : List (BusInteraction (ZMod p))),
         P = P₁ ++ Sx :: P₂ → Sx.multiplicity ≠ 0 → shape.address Sx = shape.address e →
         Sx.multiplicity = shape.setNewMult →
         ∃ m ∈ P₂, m.multiplicity ≠ 0 ∧ shape.address m = shape.address e ∧
           m.multiplicity = -shape.setNewMult) :
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
      -- When `e` is active and same-address as `S`, the shield gives an active same-address
      -- receive `Rp` in `c''` (= `P` after `S`, via `hP : P = pre ++ S :: c''`). `Rp` will sit in
      -- the exposed pair's middle, contradicting its clean-middle obligation `hmid`.
      have hEshield : e.multiplicity ≠ 0 → shape.address e = shape.address S →
          ∃ Rp, Rp ∈ c'' ∧ Rp.multiplicity ≠ 0 ∧ shape.address Rp = shape.address S := by
        intro hene haddreS
        rcases hcond with h0 | hsh
        · exact absurd h0 hene
        · obtain ⟨Rp, hRpmem, hRpne, hRpaddr, _⟩ :=
            hsh pre S c'' hP (by rw [hS]; exact shape.setNewMult_ne_zero hp1) haddreS.symm hS
          exact ⟨Rp, hRpmem, hRpne, hRpaddr.trans haddreS⟩
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
              · obtain ⟨Rp, hRpc, hRpne, hRpaddr⟩ := hEshield hmne hmaddr
                exact hmid Rp (hc''w ▸ hRpc) hRpne hRpaddr
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
            · obtain ⟨Rp, hRpc, hRpne, hRpaddr⟩ := hEshield hmne hmaddr
              exact hmid Rp (by rw [hmidw]; exact List.mem_append_left w hRpc) hRpne hRpaddr
            · exact hmid m (by rw [hmidw]; exact List.mem_append_right c'' hmw) hmne hmaddr

/-- Dropping a matched consecutive send→receive pair (`S₀` a send, `R₀` a later receive, no active
    same-address message between them) preserves `admissibleMemoryBus`, provided every active
    same-address send in the before-region `A` is followed by an active same-address receive in
    `A` (the *shield* condition `hshield` — strictly weaker than "`S₀` is the earliest active
    same-address send"). Proved by removing `S₀` then `R₀`, each a `dropOne` whose shield side
    condition is met: `hshield` for `S₀`'s `A`, and for `R₀`'s `A ++ B` a same-address send lands
    in `A` (shielded by `hshield`) or in `B` (excluded by `hcons`). -/
theorem admissibleMemoryBus_dropPair (shape : MemoryBusShape) (hp1 : (1 : ZMod p) ≠ 0)
    (A B C : List (BusInteraction (ZMod p))) (S₀ R₀ : BusInteraction (ZMod p))
    (hadm : admissibleMemoryBus shape (A ++ S₀ :: B ++ R₀ :: C))
    (hcons : ∀ m ∈ B, m.multiplicity ≠ 0 → shape.address m = shape.address S₀ → False)
    (hshield : ∀ (A₁ : List (BusInteraction (ZMod p))) (Sx : BusInteraction (ZMod p))
        (A₂ : List (BusInteraction (ZMod p))),
        A = A₁ ++ Sx :: A₂ → Sx.multiplicity ≠ 0 → shape.address Sx = shape.address S₀ →
        Sx.multiplicity = shape.setNewMult →
        ∃ m ∈ A₂, m.multiplicity ≠ 0 ∧ shape.address m = shape.address S₀ ∧
          m.multiplicity = -shape.setNewMult)
    (haddrEq : shape.address S₀ = shape.address R₀) :
    admissibleMemoryBus shape (A ++ B ++ C) := by
  -- Step 1: remove `S₀`. `A ++ S₀ :: B ++ R₀ :: C = A ++ S₀ :: (B ++ R₀ :: C)`.
  have hadm1 : admissibleMemoryBus shape (A ++ S₀ :: (B ++ R₀ :: C)) := by
    have : A ++ S₀ :: B ++ R₀ :: C = A ++ S₀ :: (B ++ R₀ :: C) := by
      simp only [List.append_assoc, List.cons_append]
    rwa [this] at hadm
  have h1 : admissibleMemoryBus shape (A ++ (B ++ R₀ :: C)) :=
    admissibleMemoryBus_dropOne shape hp1 A (B ++ R₀ :: C) S₀ hadm1 (Or.inr hshield)
  -- Step 2: remove `R₀`. `A ++ (B ++ R₀ :: C) = (A ++ B) ++ R₀ :: C`.
  have h2 : admissibleMemoryBus shape ((A ++ B) ++ R₀ :: C) := by
    have : A ++ (B ++ R₀ :: C) = (A ++ B) ++ R₀ :: C := by
      simp only [List.append_assoc]
    rwa [this] at h1
  have h3 : admissibleMemoryBus shape ((A ++ B) ++ C) := by
    refine admissibleMemoryBus_dropOne shape hp1 (A ++ B) C R₀ h2 (Or.inr ?_)
    -- Shield for `R₀` over `A ++ B`: a same-address send `Sx` lands in `A` (use `hshield`) or in
    -- `B` (impossible by `hcons`).
    intro P₁ Sx P₂ hsplit hSxne hSxaddr hSxmult
    have hSxaddrS : shape.address Sx = shape.address S₀ := hSxaddr.trans haddrEq.symm
    rcases List.append_eq_append_iff.mp hsplit with ⟨t, hP1eq, hBeq⟩ | ⟨t, hAeq, hSxeq⟩
    · -- `P₁ = A ++ t`, `B = t ++ Sx :: P₂`: `Sx ∈ B`.
      exact absurd (hcons Sx (hBeq ▸ List.mem_append_right t (List.mem_cons_self ..))
        hSxne hSxaddrS) not_false
    · -- `A = P₁ ++ t`, `Sx :: P₂ = t ++ B`.
      cases t with
      | nil =>
        -- `Sx :: P₂ = B`: `Sx ∈ B`.
        simp only [List.nil_append] at hSxeq
        exact absurd (hcons Sx (hSxeq ▸ List.mem_cons_self ..) hSxne hSxaddrS) not_false
      | cons t0 t' =>
        -- `Sx = t0`, `P₂ = t' ++ B`, and `A = P₁ ++ Sx :: t'`.
        rw [List.cons_append, List.cons.injEq] at hSxeq
        obtain ⟨rfl, hP₂eq⟩ := hSxeq
        obtain ⟨Rp, hRpmem, hRpne, hRpaddr, hRpmult⟩ :=
          hshield P₁ Sx t' hAeq hSxne hSxaddrS hSxmult
        exact ⟨Rp, by rw [hP₂eq]; exact List.mem_append_left B hRpmem, hRpne,
          hRpaddr.trans haddrEq, hRpmult⟩
  simpa only [List.append_assoc] using h3
