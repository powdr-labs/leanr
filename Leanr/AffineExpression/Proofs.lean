import Leanr.AffineExpression

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

theorem TreeMap_mergeWith_add_sum (t₁ t₂ : Std.TreeMap String (ZMod p)) (env : String → ZMod p) :
    ((t₁.mergeWith (fun _ v1 v2 => v1 + v2) t₂).toList.map (fun (k, v) => v * env k)).sum =
    (t₁.toList.map (fun (k, v) => v * env k)).sum +
    (t₂.toList.map (fun (k, v) => v * env k)).sum := by
  sorry

@[simp]
theorem AffineExpression.eval_of_add (x y : AffineExpression p) (env : String → ZMod p) :
  (x + y).eval env = x.eval env + y.eval env := by
  rw [eval_eq_offset_add_sum, eval_eq_offset_add_sum x, eval_eq_offset_add_sum y]
  change (x.offset + y.offset) +
    (((x.affine.mergeWith (fun _ v1 v2 => v1 + v2) y.affine).filter (fun _ v => v ≠ 0)).toList.map
      (fun (k, v) => v * env k)).sum =
    (x.offset + (x.affine.toList.map (fun (k, v) => v * env k)).sum) +
    (y.offset + (y.affine.toList.map (fun (k, v) => v * env k)).sum)
  rw [Std.TreeMap.toList_filter, List.map_filter_ne_zero_sum, TreeMap_mergeWith_add_sum]
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

/-- substituteAll preserves evaluation when the substitution map agrees with env. -/
theorem AffineExpression.substituteAll_eval (e : AffineExpression p)
    (m : Std.HashMap String (ZMod p)) (env : String → ZMod p)
    (h : ∀ x v, m[x]? = some v → env x = v) :
    (e.substituteAll m).eval env = e.eval env := by
  sorry -- requires TreeMap foldl reasoning
