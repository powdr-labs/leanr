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

/-- `Spec.lean` pins `BEq Variable` to `decide (a = b)`; this is its lawfulness, from which
    `EquivBEq`/`LawfulHashable` (the hash-map key obligations) are inferred. -/
instance : LawfulBEq Variable where
  rfl := by simp [BEq.beq]
  eq_of_beq h := by simpa [BEq.beq] using h
