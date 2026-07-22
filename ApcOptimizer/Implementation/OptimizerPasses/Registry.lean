import ApcOptimizer.Spec
import ApcOptimizer.Implementation.Variable

set_option autoImplicit false

/-! # Dense variable identifiers and the canonical registry

Implementation-only dense variable representation. A `VarId` is a `Nat`-index newtype; a
`VarRegistry` is a bijection between valid `VarId`s and the `Variable` values it has registered
(identity is the pair `(name, powdrId?)`, not just the display string). Nothing here is audited. -/

namespace ApcOptimizer.Dense

/-- A `Nat`-index newtype so the type checker rejects mixing variable IDs with unrelated indexes
    (bus IDs, payload slots, …). -/
structure VarId where
  index : Nat
deriving DecidableEq, Repr, Inhabited, Hashable

/-- A default `Variable` for total array access in `resolve`; never observed on valid IDs. -/
instance : Inhabited Variable := ⟨⟨"", none⟩⟩

/-- The registered `Variable`s indexed by `VarId`, the reverse map, and the two consistency
    invariants. -/
structure VarRegistry where
  /-- Registered variables, indexed by `VarId`. Append-only; removed variables keep their slot. -/
  byId : Array Variable
  toId : Std.HashMap Variable VarId
  /-- Forward consistency: `toId` never points outside `byId`, and it points to the right slot. -/
  fwd : ∀ (v : Variable) (i : VarId), toId[v]? = some i → byId[i.index]? = some v
  /-- Backward consistency: every filled slot of `byId` is registered, pointing back to itself. -/
  bwd : ∀ (i : Nat) (v : Variable), byId[i]? = some v → toId[v]? = some ⟨i⟩

namespace VarRegistry

/-- Resolve a `VarId` to its `Variable`. Total via a default for out-of-range IDs (never hit on a
    valid ID). -/
def resolve (r : VarRegistry) (i : VarId) : Variable := (r.byId[i.index]?).getD default

def idOf? (r : VarRegistry) (v : Variable) : Option VarId := r.toId[v]?

/-- An ID is *valid* in `r` when its index is in range. Every ID in a covered dense value is valid
    (see `Encoding.lean`). -/
def Valid (r : VarRegistry) (i : VarId) : Prop := i.index < r.byId.size

/-! ## Round-trip and injectivity -/

theorem resolve_eq {r : VarRegistry} {i : VarId} (h : i.index < r.byId.size) :
    r.resolve i = r.byId[i.index] := by
  simp [resolve, Array.getElem?_eq_getElem h]

theorem resolve_idOf {r : VarRegistry} {v : Variable} {i : VarId} (h : r.idOf? v = some i) :
    r.resolve i = v := by
  have hf := r.fwd v i h
  simp [resolve, hf]

theorem valid_of_idOf {r : VarRegistry} {v : Variable} {i : VarId} (h : r.idOf? v = some i) :
    r.Valid i := by
  have hf := r.fwd v i h
  rw [Array.getElem?_eq_some_iff] at hf
  exact hf.choose

theorem idOf_resolve {r : VarRegistry} {i : VarId} (h : r.Valid i) :
    r.idOf? (r.resolve i) = some i := by
  have hb : r.byId[i.index]? = some (r.byId[i.index]'h) := Array.getElem?_eq_getElem h
  have := r.bwd i.index (r.byId[i.index]'h) hb
  rw [resolve_eq h, idOf?]
  simpa using this

theorem idOf_inj {r : VarRegistry} {x y : Variable} {i : VarId}
    (hx : r.idOf? x = some i) (hy : r.idOf? y = some i) : x = y := by
  rw [← r.resolve_idOf hx, ← r.resolve_idOf hy]

theorem resolve_inj {r : VarRegistry} {i j : VarId} (hi : r.Valid i) (hj : r.Valid j)
    (h : r.resolve i = r.resolve j) : i = j := by
  have := r.idOf_resolve hi
  rw [h, r.idOf_resolve hj] at this
  exact (Option.some.inj this).symm

/-! ## The empty registry -/

def empty : VarRegistry where
  byId := #[]
  toId := ∅
  fwd := by intro v i h; simp at h
  bwd := by intro i v h; simp at h

/-! ## Append-only registration -/

/-- Register `v`, returning the (possibly extended) registry and `v`'s stable `VarId`. Already
    registered `v` returns its existing ID; otherwise a fresh trailing ID is allocated. -/
def register (r : VarRegistry) (v : Variable) : VarRegistry × VarId :=
  match hlook : r.toId[v]? with
  | some i => (r, i)
  | none =>
    ({ byId := r.byId.push v
       toId := r.toId.insert v ⟨r.byId.size⟩
       fwd := by
         intro w j hj
         rw [Std.HashMap.getElem?_insert] at hj
         split at hj
         · -- v == w : the freshly inserted binding
           rename_i hbeq
           obtain rfl : j = ⟨r.byId.size⟩ := (Option.some.inj hj).symm
           rw [Array.getElem?_push_size]
           rw [eq_of_beq hbeq]
         · -- v != w : falls back to the old map
           have hf := r.fwd w j hj
           have hlt : j.index < r.byId.size := by
             rw [Array.getElem?_eq_some_iff] at hf; exact hf.choose
           rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
           exact hf
       bwd := by
         intro k w hk
         rw [Array.getElem?_push] at hk
         split at hk
         · -- k = size : the freshly pushed slot
           rename_i hks
           obtain rfl : v = w := Option.some.inj hk
           subst hks
           rw [Std.HashMap.getElem?_insert_self]
         · -- k < size : an old slot
           rename_i hks
           have hbwd := r.bwd k w hk
           rw [Std.HashMap.getElem?_insert]
           have hne : (v == w) = false := by
             by_contra hc
             have hvw : v = w := eq_of_beq (by simpa using hc)
             rw [hvw, hbwd] at hlook
             simp at hlook
           rw [if_neg (by simpa using hne)]
           exact hbwd },
     ⟨r.byId.size⟩)

/-! ## Extension -/

/-- `r'` extends `r`: every filled slot of `r` is preserved (same index, same variable) in `r'`. -/
def Extends (r r' : VarRegistry) : Prop :=
  ∀ (i : Nat) (v : Variable), r.byId[i]? = some v → r'.byId[i]? = some v

theorem Extends.refl (r : VarRegistry) : Extends r r := fun _ _ h => h

theorem Extends.valid {r r' : VarRegistry} (h : Extends r r') {i : VarId} (hi : r.Valid i) :
    r'.Valid i := by
  have hb : r.byId[i.index]? = some (r.byId[i.index]'hi) := Array.getElem?_eq_getElem hi
  have hb' := h i.index (r.byId[i.index]'hi) hb
  rw [Array.getElem?_eq_some_iff] at hb'
  exact hb'.choose

theorem Extends.trans {r r' r'' : VarRegistry} (h1 : Extends r r') (h2 : Extends r' r'') :
    Extends r r'' := fun i v h => h2 i v (h1 i v h)

theorem Extends.resolve_eq {r r' : VarRegistry} (h : Extends r r') {i : VarId} (hi : r.Valid i) :
    r'.resolve i = r.resolve i := by
  have hb : r.byId[i.index]? = some (r.byId[i.index]'hi) := Array.getElem?_eq_getElem hi
  have hb' := h i.index (r.byId[i.index]'hi) hb
  simp [resolve, hb, hb']

theorem Extends.idOf_eq {r r' : VarRegistry} (h : Extends r r') {v : Variable} {i : VarId}
    (hv : r.idOf? v = some i) : r'.idOf? v = some i := by
  have hf := r.fwd v i hv
  have hf' := h i.index v hf
  have := r'.bwd i.index v hf'
  rw [idOf?]
  simpa using this

theorem register_extends (r : VarRegistry) (v : Variable) : Extends r (r.register v).1 := by
  unfold register
  split
  · exact Extends.refl r
  · intro i w hiw
    have hlt : i < r.byId.size := by
      rw [Array.getElem?_eq_some_iff] at hiw; exact hiw.choose
    show (r.byId.push v)[i]? = some w
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
    exact hiw

/-! ## Registration results -/

theorem register_resolve (r : VarRegistry) (v : Variable) :
    (r.register v).1.resolve (r.register v).2 = v := by
  unfold register
  split
  · rename_i i hlook
    exact resolve_idOf (r := r) (v := v) (i := i) hlook
  · rename_i hlook
    show ((r.byId.push v)[r.byId.size]?).getD default = v
    rw [Array.getElem?_push_size, Option.getD_some]

theorem register_idOf (r : VarRegistry) (v : Variable) :
    (r.register v).1.idOf? v = some (r.register v).2 := by
  unfold register
  split
  · rename_i i hlook; exact hlook
  · rename_i hlook
    show (r.toId.insert v ⟨r.byId.size⟩)[v]? = some ⟨r.byId.size⟩
    rw [Std.HashMap.getElem?_insert_self]

theorem register_valid (r : VarRegistry) (v : Variable) :
    (r.register v).1.Valid (r.register v).2 :=
  valid_of_idOf (register_idOf r v)

end VarRegistry

end ApcOptimizer.Dense
