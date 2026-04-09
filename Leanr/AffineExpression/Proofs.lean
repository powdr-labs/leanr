import Leanr.AffineExpression
import Leanr.RangeConstraint.Proofs

variable {p : ℕ} [Fact (Nat.Prime p)]

private theorem List.foldl_add_eq_add_sum {α : Type} (l : List (α × ZMod p))
    (f : α × ZMod p → ZMod p) (init : ZMod p) :
    List.foldl (fun acc b => acc + f b) init l = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih]; ring

theorem AffineExpression.eval_eq_offset_add_sum (e : AffineExpression p) (env : String → ZMod p) :
    e.eval env = e.offset + (e.affine.toList.map (fun (k, v) => v * env k)).sum := by
  unfold AffineExpression.eval; congr 1
  rw [Std.TreeMap.foldl_eq_foldl_toList, List.foldl_add_eq_add_sum]; simp

@[simp]
theorem TreeMap_toList_empty {α β : Type} (cmp : α → α → Ordering) :
    (∅ : Std.TreeMap α β cmp).toList = [] := by
  rfl

@[simp]
theorem TreeMap_empty_insert_toList {α β : Type} (cmp : α → α → Ordering)
    (a : α) (v : β) :
    ((∅ : Std.TreeMap α β cmp).insert a v).toList = [(a, v)] := by
  simp [Std.TreeMap.toList, Std.TreeMap.insert]
  rfl

@[simp]
theorem AffineExpression.eval_of_const (n : ZMod p) :
  (AffineExpression.const n).eval = fun _ => n := by
  unfold AffineExpression.eval AffineExpression.const
  ext x
  simp [Std.TreeMap.foldl_eq_foldl_toList]

@[simp]
theorem AffineExpression.eval_of_var (x : String) :
  (AffineExpression.var (p := p) x).eval = fun env => env x := by
  unfold AffineExpression.eval AffineExpression.var
  simp [Std.TreeMap.foldl_eq_foldl_toList]

private theorem List.map_filter_ne_zero_sum (l : List (String × ZMod p)) (env : String → ZMod p) :
    (l.filter (fun q => decide (q.2 ≠ 0)) |>.map (fun (k, v) => v * env k)).sum =
    (l.map (fun (k, v) => v * env k)).sum := by
  have : (fun q : String × ZMod p => decide (q.2 ≠ 0)) = (fun q => !decide (q.2 = 0)) := by
    ext q; simp [decide_not]
  rw [this]
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases h : hd.2 = 0
    · simp [h, ih]
    · simp [h, ih]

/-! ### Helpers for TreeMap foldl+alter sum (used in eval_of_add) -/

omit [Fact (Nat.Prime p)] in
private theorem toList_nodup (t : Std.TreeMap String (ZMod p)) : t.toList.Nodup :=
  List.Pairwise.imp (fun {a b} hab heq => hab (by
    rw [congr_arg Prod.fst heq]; exact compare_eq_iff_eq.mpr rfl))
    Std.TreeMap.distinct_keys_toList

omit [Fact (Nat.Prime p)] in
private theorem toList_pairwise_keys (t : Std.TreeMap String (ZMod p)) :
    t.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
  List.Pairwise.imp (fun {a b} (h : ¬compare a.1 b.1 = .eq) (heq : a.1 = b.1) =>
    h (heq ▸ compare_eq_iff_eq.mpr rfl))
    Std.TreeMap.distinct_keys_toList

omit [Fact (Nat.Prime p)] in
private theorem toList_perm_of_getElem_eq (t1 t2 : Std.TreeMap String (ZMod p))
    (h : ∀ k : String, (t1 : Std.TreeMap String (ZMod p))[k]? =
                        (t2 : Std.TreeMap String (ZMod p))[k]?) :
    t1.toList.Perm t2.toList := by
  rw [List.perm_ext_iff_of_nodup (toList_nodup t1) (toList_nodup t2)]
  intro ⟨k, v⟩; simp only [Std.TreeMap.mem_toList_iff_getElem?_eq_some, h]

private theorem alter_add_toList_perm (t : Std.TreeMap String (ZMod p)) (k : String) (v : ZMod p) :
    (t.alter k (fun | some v' => some (v' + v) | none => some v)).toList.Perm
    ((k, (t[k]?.getD 0) + v) :: (t.toList.filter (fun x => decide (¬(k == x.1) = true)))) :=
  (toList_perm_of_getElem_eq _ _ (fun k' => by
    rw [Std.TreeMap.getElem?_alter, Std.TreeMap.getElem?_insert]
    split
    · cases hk : (t : Std.TreeMap String (ZMod p))[k]? <;> simp [Option.getD]
    · rfl)).trans Std.TreeMap.toList_insert_perm

omit [Fact (Nat.Prime p)] in
private theorem filter_beq_to_ne (k : String) (l : List (String × ZMod p)) :
    l.filter (fun x => decide (¬(k == x.1) = true)) = l.filter (fun x => decide (x.1 ≠ k)) := by
  congr 1; ext x
  apply decide_eq_decide.mpr
  constructor
  · intro h heq; apply h; subst heq; simp [BEq.beq]
  · intro h hbeq; apply h; exact (beq_iff_eq.mp hbeq).symm

private theorem sum_split_at_key (l : List (String × ZMod p)) (k : String) (val : ZMod p)
    (h_mem : (k, val) ∈ l) (h_distinct : l.Pairwise (fun a b => a.1 ≠ b.1))
    (env : String → ZMod p) :
    (l.map (fun (k, v) => v * env k)).sum =
    val * env k +
    ((l.filter (fun x => decide (x.1 ≠ k))).map (fun (k, v) => v * env k)).sum := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    rw [List.pairwise_cons] at h_distinct
    obtain ⟨h_neq_tl, h_tl_distinct⟩ := h_distinct
    rcases List.mem_cons.mp h_mem with rfl | h_in_tl
    · have h_filter_cons : ((k, val) :: tl).filter (fun x => decide (x.1 ≠ k)) =
          tl.filter (fun x => decide (x.1 ≠ k)) :=
        List.filter_cons_of_neg (by simp)
      have h_filter_tl : tl.filter (fun x => decide (x.1 ≠ k)) = tl := by
        rw [List.filter_eq_self]
        intro x hx; exact decide_eq_true_eq.mpr (h_neq_tl x hx).symm
      simp only [List.map_cons, List.sum_cons, h_filter_cons, h_filter_tl]
    · have h_ne : hd.1 ≠ k :=
        fun heq => by subst heq; exact absurd rfl (h_neq_tl ⟨_, val⟩ h_in_tl)
      have h_filter_cons : (hd :: tl).filter (fun x => decide (x.1 ≠ k)) =
          hd :: tl.filter (fun x => decide (x.1 ≠ k)) :=
        List.filter_cons_of_pos (decide_eq_true_eq.mpr h_ne)
      simp only [List.map_cons, List.sum_cons, h_filter_cons]
      rw [ih h_in_tl h_tl_distinct]; ring

private theorem sum_eq_key_plus_rest (t : Std.TreeMap String (ZMod p)) (k : String)
    (env : String → ZMod p) :
    (t.toList.map (fun (k, v) => v * env k)).sum =
    (t[k]?.getD 0) * env k +
    ((t.toList.filter (fun x => decide (x.1 ≠ k))).map (fun (k, v) => v * env k)).sum := by
  cases hk : (t : Std.TreeMap String (ZMod p))[k]? with
  | none =>
    simp only [Option.getD, zero_mul, zero_add]
    have hfilt : t.toList.filter (fun x => decide (x.1 ≠ k)) = t.toList := by
      rw [List.filter_eq_self]
      intro x hx; simp only [decide_eq_true_eq]
      intro heq; subst heq
      exact absurd (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hx) (by rw [hk]; exact nofun)
    rw [hfilt]
  | some val =>
    simp only [Option.getD]
    exact sum_split_at_key t.toList k val
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hk)
      (toList_pairwise_keys t) env

private theorem alter_add_sum_eq (t : Std.TreeMap String (ZMod p)) (k : String) (v : ZMod p)
    (env : String → ZMod p) :
    ((t.alter k (fun | some v' => some (v' + v) | none => some v)).toList.map
      (fun (k, v) => v * env k)).sum =
    (t.toList.map (fun (k, v) => v * env k)).sum + v * env k := by
  rw [((alter_add_toList_perm t k v).map _).sum_eq, List.map_cons, List.sum_cons,
    filter_beq_to_ne, sum_eq_key_plus_rest t k env]; ring

private theorem foldl_alter_add_sum (t1 : Std.TreeMap String (ZMod p))
    (l2 : List (String × ZMod p)) (env : String → ZMod p) :
    ((l2.foldl (fun acc (entry : String × ZMod p) =>
      acc.alter entry.1 (fun | some v' => some (v' + entry.2) | none => some entry.2)) t1).toList.map
      (fun (k, v) => v * env k)).sum =
    (t1.toList.map (fun (k, v) => v * env k)).sum +
    (l2.map (fun (k, v) => v * env k)).sum := by
  induction l2 generalizing t1 with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, alter_add_sum_eq]; ring

theorem TreeMap_foldl_alter_add_sum (t₁ t₂ : Std.TreeMap String (ZMod p))
    (env : String → ZMod p) :
    ((t₂.foldl (fun acc k v =>
      acc.alter k (fun | some v' => some (v' + v) | none => some v)) t₁).toList.map
      (fun (k, v) => v * env k)).sum =
    (t₁.toList.map (fun (k, v) => v * env k)).sum +
    (t₂.toList.map (fun (k, v) => v * env k)).sum := by
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  exact foldl_alter_add_sum t₁ t₂.toList env

@[simp]
theorem AffineExpression.eval_of_add (x y : AffineExpression p) (env : String → ZMod p) :
  (x + y).eval env = x.eval env + y.eval env := by
  rw [eval_eq_offset_add_sum, eval_eq_offset_add_sum x, eval_eq_offset_add_sum y]
  change (x.offset + y.offset) +
    (((y.affine.foldl (fun acc k v =>
      acc.alter k (fun | some v' => some (v' + v) | none => some v)) x.affine).filter
        (fun _ v => v ≠ 0)).toList.map (fun (k, v) => v * env k)).sum =
    (x.offset + (x.affine.toList.map (fun (k, v) => v * env k)).sum) +
    (y.offset + (y.affine.toList.map (fun (k, v) => v * env k)).sum)
  rw [Std.TreeMap.toList_filter, List.map_filter_ne_zero_sum, TreeMap_foldl_alter_add_sum]
  ring

private theorem TreeMap_map_mul_sum (n : ZMod p) (t : Std.TreeMap String (ZMod p))
    (env : String → ZMod p) :
    ((t.map (fun _ v => n * v)).toList.map (fun (k, v) => v * env k)).sum =
    n * (t.toList.map (fun (k, v) => v * env k)).sum := by
  rw [Std.TreeMap.toList_map, List.map_map]
  have : ((fun x : String × ZMod p => x.2 * env x.1) ∘ fun p_1 : String × ZMod p => (p_1.1, n * p_1.2)) =
      (fun b : String × ZMod p => n * (b.2 * env b.1)) := by ext ⟨k, v⟩; simp; ring
  rw [this, List.sum_map_mul_left]

@[simp]
theorem AffineExpression.eval_of_mul (n : ZMod p) (x : AffineExpression p) (env : String → ZMod p) :
  (n * x).eval env = n * x.eval env := by
  rw [eval_eq_offset_add_sum, eval_eq_offset_add_sum x]
  change (n * x.offset) +
    (((x.affine.map (fun _ v => n * v)).filter (fun _ v => v ≠ 0)).toList.map
      (fun (k, v) => v * env k)).sum =
    n * (x.offset + (x.affine.toList.map (fun (k, v) => v * env k)).sum)
  rw [Std.TreeMap.toList_filter, List.map_filter_ne_zero_sum, TreeMap_map_mul_sum]
  ring

private theorem TreeMap_isEmpty_toList_nil {α β : Type} {cmp : α → α → Ordering}
    (t : Std.TreeMap α β cmp) (h : t.isEmpty = true) : t.toList = [] := by
  rw [Std.TreeMap.isEmpty_eq_size_eq_zero] at h
  exact List.eq_nil_of_length_eq_zero (by rw [Std.TreeMap.length_toList]; exact beq_iff_eq.mp h)

@[simp]
theorem AffineExpression.toConstant?_correct (e : AffineExpression p) (n : ZMod p) :
    e.toConstant? = some n → ∀ env, e.eval env = n := by
  unfold AffineExpression.toConstant?; split
  case isTrue h =>
    intro heq env; have := Option.some.inj heq; subst this
    rw [AffineExpression.eval_eq_offset_add_sum]; simp [TreeMap_isEmpty_toList_nil _ h]
  case isFalse => intro h; simp at h

@[simp]
theorem eval_of_mul? (x y : AffineExpression p) (h : (mul? x y).isSome) :
    ((mul? x y).get h).eval = fun env => (x.eval env) * (y.eval env) := by
  have key : ∀ r, mul? x y = some r → r.eval = fun env => x.eval env * y.eval env := by
    intro r hr
    unfold mul? at hr
    ext env
    match hc1 : x.toConstant?, hc2 : y.toConstant? with
    | some n, _ =>
      simp [hc1] at hr
      subst hr
      simp [hc1]
    | none, some n =>
      simp [hc1, hc2] at hr
      subst hr
      simp [hc2, mul_comm]
    | none, none => simp [hc1, hc2] at hr
  exact key _ (Option.some_get h).symm

--- If an expression can be converted to an affine expression, then their evaluations are the same.
theorem ofExpression_correct' (e : Expression p) (h_isSome : (AffineExpression.ofExpression? e).isSome) :
  ((AffineExpression.ofExpression? e).get h_isSome).eval = e.eval := by
  induction e with
  | const n => simp [AffineExpression.ofExpression?, Expression.eval]
  | var x => simp [AffineExpression.ofExpression?, Expression.eval]
  | add e1 e2 ih1 ih2 =>
    ext env
    simp [AffineExpression.ofExpression?, Expression.eval, ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
    simp [AffineExpression.ofExpression?, Expression.eval, ih1, ih2]

/-! ### Helper lemmas for substituteAll_eval -/

omit [Fact (Nat.Prime p)] in
private theorem insert_sum_eq
    (t : Std.TreeMap String (ZMod p)) (k : String) (v : ZMod p)
    (f : String × ZMod p → ZMod p) (h_not_mem : k ∉ t) :
    ((t.insert k v).toList.map f).sum = f (k, v) + (t.toList.map f).sum := by
  have perm := Std.TreeMap.toList_insert_perm (t := t) (k := k) (v := v)
  rw [(perm.map f).sum_eq]
  simp only [List.map_cons, List.sum_cons]; congr 1
  have : t.toList.filter (fun x => decide (¬(k == x.1) = true)) = t.toList := by
    rw [List.filter_eq_self]; intro x hx; simp only [decide_eq_true_eq]
    intro heq; rw [beq_iff_eq] at heq; subst heq
    exact absurd (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hx)
      (by rw [Std.TreeMap.getElem?_eq_none h_not_mem]; simp)
  simp only [this]

private theorem subst_foldl_correct
    (l : List (String × ZMod p))
    (m : Std.HashMap String (ZMod p))
    (env : String → ZMod p)
    (h_map : ∀ x v, m[x]? = some v → env x = v)
    (init_off : ZMod p)
    (init_aff : Std.TreeMap String (ZMod p))
    (h_distinct : l.Pairwise (fun a b => a.1 ≠ b.1))
    (h_disjoint : ∀ x ∈ l, (x.1 : String) ∉ init_aff) :
    let (off', aff') := l.foldl (fun (acc : ZMod p × Std.TreeMap String (ZMod p)) (entry : String × ZMod p) =>
      let (off, aff) := acc
      let (k, v) := entry
      match m[k]? with
      | some val => (off + v * val, aff)
      | none => (off, aff.insert k v)) (init_off, init_aff)
    off' + (aff'.toList.map (fun (k, v) => v * env k)).sum =
    init_off + (init_aff.toList.map (fun (k, v) => v * env k)).sum +
    (l.map (fun (k, v) => v * env k)).sum := by
  induction l generalizing init_off init_aff with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    obtain ⟨k, v⟩ := hd
    simp only [List.pairwise_cons] at h_distinct
    obtain ⟨h_not_in_tl, h_tl_distinct⟩ := h_distinct
    have h_k_not_in_aff : k ∉ init_aff := h_disjoint (k, v) (List.mem_cons.mpr (Or.inl rfl))
    match h : m[k]? with
    | some val =>
      have h_disjoint' : ∀ x ∈ tl, (x.1 : String) ∉ init_aff :=
        fun x hx => h_disjoint x (List.mem_cons.mpr (Or.inr hx))
      rw [ih (init_off + v * val) init_aff h_tl_distinct h_disjoint']
      have := h_map k val h; rw [this]; ring
    | none =>
      have h_disjoint' : ∀ x ∈ tl, (x.1 : String) ∉ (init_aff.insert k v) := by
        intro x hx
        rw [Std.TreeMap.mem_insert]
        push Not
        constructor
        · intro heq
          rw [compare_eq_iff_eq] at heq
          exact h_not_in_tl x hx heq
        · exact h_disjoint x (List.mem_cons.mpr (Or.inr hx))
      rw [ih init_off (init_aff.insert k v) h_tl_distinct h_disjoint']
      rw [insert_sum_eq init_aff k v _ h_k_not_in_aff]
      ring

/-- substituteAll preserves evaluation when the substitution map agrees with env. -/
theorem AffineExpression.substituteAll_eval (e : AffineExpression p)
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h : ∀ x v, m[x]? = some v → env x = v) :
    (e.substituteAll m).eval env = e.eval env := by
  rw [eval_eq_offset_add_sum, eval_eq_offset_add_sum e]
  unfold substituteAll
  rw [Std.TreeMap.toList_filter, List.map_filter_ne_zero_sum]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  have h_distinct := toList_pairwise_keys e.affine
  have h_disjoint : ∀ x ∈ e.affine.toList, (x.1 : String) ∉ (∅ : Std.TreeMap String (ZMod p)) :=
    fun x _ => Std.TreeMap.not_mem_emptyc
  have := subst_foldl_correct e.affine.toList m env h e.offset ∅ h_distinct h_disjoint
  simp at this
  exact this

/-! ### Range constraint soundness -/

/-- A singleton range constraint allows its value. -/
theorem RangeConstraint.coe_allowsValue (v : ZMod p) :
    (↑v : RangeConstraint p).allowsValue v = true := by
  rw [allowsValue_iff]
  simp only [le_refl, ite_true, and_self, true_and]
  exact Nat.and_self v.val

/-- Helper: foldl over a list combining RCs is sound.
    If `acc_rc` allows `acc_val`, and for each `(k, v)` in `l`, `rc_env k` allows `val_env k`,
    then the result allows `acc_val + Σ v * val_env k`. -/
private theorem rangeConstraint_foldl_sound
    (l : List (String × ZMod p))
    (rc_env : String → RangeConstraint p)
    (val_env : String → ZMod p)
    (h_env : ∀ k, ∀ pair ∈ l, pair.1 = k → (rc_env k).allowsValue (val_env k) = true)
    (acc_rc : RangeConstraint p) (acc_val : ZMod p)
    (h_acc : acc_rc.allowsValue acc_val = true) :
    (l.foldl (fun (acc : RangeConstraint p) (entry : String × ZMod p) =>
      acc + (↑entry.2 : RangeConstraint p) * rc_env entry.1) acc_rc).allowsValue
      (acc_val + (l.map (fun (k, v) => v * val_env k)).sum) = true := by
  induction l generalizing acc_rc acc_val with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have h_hd : (rc_env hd.1).allowsValue (val_env hd.1) = true :=
      h_env hd.1 hd List.mem_cons_self rfl
    have h_coe : (↑hd.2 : RangeConstraint p).allowsValue hd.2 = true :=
      RangeConstraint.coe_allowsValue hd.2
    have h_mul : ((↑hd.2 : RangeConstraint p) * rc_env hd.1).allowsValue (hd.2 * val_env hd.1) = true :=
      RangeConstraint.mul_sound _ _ _ _ h_coe h_hd
    have h_add : (acc_rc + (↑hd.2 : RangeConstraint p) * rc_env hd.1).allowsValue
        (acc_val + hd.2 * val_env hd.1) = true :=
      RangeConstraint.add_sound _ _ _ _ h_acc h_mul
    have h_env' : ∀ k, ∀ pair ∈ tl, pair.1 = k → (rc_env k).allowsValue (val_env k) = true :=
      fun k pair hp hk => h_env k pair (List.mem_cons_of_mem _ hp) hk
    convert ih h_env' _ _ h_add using 1
    ring

/-- The range constraint of an affine expression is sound:
    if every variable's RC allows its actual value, then the expression RC allows
    the expression's actual value. -/
theorem AffineExpression.rangeConstraint_sound
    (ae : AffineExpression p) (rc_env : String → RangeConstraint p)
    (val_env : String → ZMod p)
    (h_env : ∀ v, (rc_env v).allowsValue (val_env v) = true) :
    (ae.rangeConstraint rc_env).allowsValue (ae.eval val_env) = true := by
  rw [eval_eq_offset_add_sum]
  unfold AffineExpression.rangeConstraint
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  exact rangeConstraint_foldl_sound ae.affine.toList rc_env val_env
    (fun k _ _ _ => h_env k) _ _ (RangeConstraint.coe_allowsValue ae.offset)

/-- Helper: foldl over a list that skips one variable is sound.
    The value side uses the same foldl structure with skip. -/
private theorem rest_foldl_sound
    (l : List (String × ZMod p))
    (x : String)
    (rc_env : String → RangeConstraint p)
    (val_env : String → ZMod p)
    (h_env : ∀ k, ∀ pair ∈ l, pair.1 = k → k ≠ x → (rc_env k).allowsValue (val_env k) = true)
    (acc_rc : RangeConstraint p) (acc_val : ZMod p)
    (h_acc : acc_rc.allowsValue acc_val = true) :
    (l.foldl (fun (acc : RangeConstraint p) (entry : String × ZMod p) =>
      if entry.1 == x then acc else acc + (↑entry.2 : RangeConstraint p) * rc_env entry.1) acc_rc).allowsValue
      (l.foldl (fun (acc : ZMod p) (entry : String × ZMod p) =>
        if entry.1 == x then acc else acc + entry.2 * val_env entry.1) acc_val) = true := by
  induction l generalizing acc_rc acc_val with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    by_cases h_eq : hd.1 == x
    · simp only [h_eq, ite_true]
      exact ih (fun k pair hp hk hne => h_env k pair (List.mem_cons_of_mem _ hp) hk hne)
        _ _ h_acc
    · simp only [h_eq, ite_false]
      have h_ne : hd.1 ≠ x := fun heq => h_eq (beq_iff_eq.mpr heq)
      have h_hd : (rc_env hd.1).allowsValue (val_env hd.1) = true :=
        h_env hd.1 hd List.mem_cons_self rfl h_ne
      have h_mul : ((↑hd.2 : RangeConstraint p) * rc_env hd.1).allowsValue (hd.2 * val_env hd.1) = true :=
        RangeConstraint.mul_sound _ _ _ _ (RangeConstraint.coe_allowsValue hd.2) h_hd
      exact ih (fun k pair hp hk hne => h_env k pair (List.mem_cons_of_mem _ hp) hk hne)
        _ _ (RangeConstraint.add_sound _ _ _ _ h_acc h_mul)

/-- The "rest value": evaluation of an affine expression excluding variable x. -/
def AffineExpression.restEval (e : AffineExpression p) (x : String) (val_env : String → ZMod p) : ZMod p :=
  e.affine.foldl (fun (acc : ZMod p) k (v : ZMod p) =>
    if k == x then acc else acc + v * val_env k) e.offset

/-- The rest RC computed in solvedRangeConstraint allows the negated-scaled rest value. -/
theorem AffineExpression.solvedRangeConstraint_sound
    (ae : AffineExpression p) (x : String) (coeff : ZMod p)
    (rc_env : String → RangeConstraint p) (val_env : String → ZMod p)
    (h_env : ∀ v, v ≠ x → (rc_env v).allowsValue (val_env v) = true)
    (h_mem : ae.affine[x]? = some coeff) (h_coeff : coeff ≠ 0) :
    ∃ rc, ae.solvedRangeConstraint x rc_env = some rc ∧
      rc.allowsValue (-(coeff⁻¹) * ae.restEval x val_env) = true := by
  unfold solvedRangeConstraint
  simp only [h_mem, h_coeff, ite_false, bind, Option.bind, pure, Pure.pure]
  refine ⟨_, rfl, ?_⟩
  apply RangeConstraint.multiple_sound
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  unfold restEval
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  exact rest_foldl_sound ae.affine.toList x rc_env val_env
    (fun k _ _ hk hne => h_env k hne) _ _ (RangeConstraint.coe_allowsValue ae.offset)

/-- Helper: the skip-x foldl equals init + Σ_{k≠x} coeff_k * val_env k. -/
private theorem restEval_foldl_eq_sum (l : List (String × ZMod p)) (x : String) (val_env : String → ZMod p)
    (init : ZMod p) :
    l.foldl (fun (acc : ZMod p) (entry : String × ZMod p) =>
      if entry.1 == x then acc else acc + entry.2 * val_env entry.1) init =
    init + ((l.filter (fun e => decide (e.1 ≠ x))).map (fun (k, v) => v * val_env k)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.filter_cons]
    by_cases h_eq : hd.1 == x
    · have : decide (hd.1 ≠ x) = false := by
        simp [decide_eq_false_iff_not]; exact beq_iff_eq.mp h_eq
      simp only [h_eq, ite_true, this, ite_false]
      exact ih init
    · have : decide (hd.1 ≠ x) = true := by
        simp [decide_eq_true_eq]; exact fun h => h_eq (beq_iff_eq.mpr h)
      simp only [h_eq, ite_false, this, ite_true, List.map_cons, List.sum_cons]
      simp only [show (false = true) = False from by simp, ite_false]
      rw [ih (init + hd.2 * val_env hd.1)]; ring

private theorem restEval_eq_sum (ae : AffineExpression p) (x : String) (val_env : String → ZMod p) :
    ae.restEval x val_env = ae.offset +
      ((ae.affine.toList.filter (fun e => decide (e.1 ≠ x))).map (fun (k, v) => v * val_env k)).sum := by
  unfold AffineExpression.restEval
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  exact restEval_foldl_eq_sum _ _ _ _

/-- Splitting eval into x-contribution and rest. -/
theorem AffineExpression.eval_split (ae : AffineExpression p) (x : String) (coeff : ZMod p)
    (val_env : String → ZMod p)
    (h_mem : ae.affine[x]? = some coeff) :
    ae.eval val_env = coeff * val_env x + ae.restEval x val_env := by
  rw [eval_eq_offset_add_sum, restEval_eq_sum]
  rw [sum_eq_key_plus_rest ae.affine x val_env]
  simp only [Option.getD, h_mem]
  ring

/-- Main soundness theorem: if field_rc allows ae.eval and all variable RCs are sound,
    then the deduced RC for variable x allows val_env x.
    This is the core algebraic identity: coeff⁻¹ * (coeff * x + rest) + (-(coeff⁻¹)) * rest = x. -/
theorem AffineExpression.deduce_variable_sound
    (ae : AffineExpression p) (x : String) (coeff : ZMod p)
    (field_rc : RangeConstraint p) (rc_env : String → RangeConstraint p) (val_env : String → ZMod p)
    (h_field : field_rc.allowsValue (ae.eval val_env) = true)
    (h_env : ∀ v, v ≠ x → (rc_env v).allowsValue (val_env v) = true)
    (h_mem : ae.affine[x]? = some coeff) (h_coeff : coeff ≠ 0) :
    (field_rc.multiple coeff⁻¹ +
      (ae.solvedRangeConstraint x rc_env).get
        (by unfold solvedRangeConstraint; simp [h_mem, h_coeff, bind, Option.bind])).allowsValue
      (val_env x) = true := by
  obtain ⟨rc, h_rc_eq, h_rc_allows⟩ := solvedRangeConstraint_sound ae x coeff rc_env val_env h_env h_mem h_coeff
  have h_get : (ae.solvedRangeConstraint x rc_env).get
      (by unfold solvedRangeConstraint; simp [h_mem, h_coeff, bind, Option.bind]) = rc := by
    simp [h_rc_eq]
  rw [h_get]
  have h_scaled : (field_rc.multiple coeff⁻¹).allowsValue (coeff⁻¹ * ae.eval val_env) = true :=
    RangeConstraint.multiple_sound field_rc coeff⁻¹ (ae.eval val_env) h_field
  have h_sum := RangeConstraint.add_sound
    (field_rc.multiple coeff⁻¹) rc
    (coeff⁻¹ * ae.eval val_env) (-(coeff⁻¹) * ae.restEval x val_env)
    h_scaled h_rc_allows
  rw [eval_split ae x coeff val_env h_mem] at h_sum
  have h_inv : coeff * coeff⁻¹ = 1 := mul_inv_cancel₀ h_coeff
  have h_val_eq : val_env x =
      coeff⁻¹ * (coeff * val_env x + ae.restEval x val_env) + -(coeff⁻¹) * ae.restEval x val_env := by
    ring_nf; rw [h_inv]; ring
  show (field_rc.multiple coeff⁻¹ + rc).allowsValue (val_env x) = true
  rw [h_val_eq, show field_rc.multiple coeff⁻¹ + rc = (field_rc.multiple coeff⁻¹).add rc from rfl]
  exact h_sum
