import ApcOptimizer.Spec

set_option autoImplicit false

/-! # Implementation support for structured variables

Typeclass laws and helpers for using spec-level `Variable` values in parsers and hash maps; kept
out of `Spec.lean` to minimize the audited surface. -/

instance : Ord Variable := ⟨fun a b =>
  match compare a.name b.name with
  | .eq => compare a.powdrId? b.powdrId?
  | o => o⟩

instance : Hashable Variable := ⟨fun a => mixHash (hash a.name) (hash a.powdrId?)⟩

/-- Parse powdr's legacy `<name>@<id>` variable notation into a structured variable. -/
def Variable.ofPowdrName (raw : String) : Variable :=
  match raw.splitOn "@" with
  | [base, id] =>
      match id.toNat? with
      | some n => { name := base, powdrId? := some n }
      | none => { name := raw }
  | _ => { name := raw }

instance : ReflBEq Variable where
  rfl := by intro a; simp [BEq.beq]

instance : LawfulBEq Variable where
  eq_of_beq := by
    intro a b h
    simpa [BEq.beq] using h

instance : PartialEquivBEq Variable where
  symm := by
    intro a b h
    cases (LawfulBEq.eq_of_beq h)
    simp [BEq.beq]
  trans := by
    intro a b c hab hbc
    cases (LawfulBEq.eq_of_beq hab)
    cases (LawfulBEq.eq_of_beq hbc)
    simp [BEq.beq]

instance : EquivBEq Variable where

instance : LawfulHashable Variable where
  hash_eq := by
    intro a b h
    cases (LawfulBEq.eq_of_beq h)
    rfl
