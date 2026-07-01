import Leanr.Spec
import Leanr.IdentityOptimizer
import Leanr.OpenVM.Semantics

/-!
# OpenVM snapshot test (single ADD-immediate, powdr `single_add_1`)

Ports the constraint system that is the **input** to powdr's `optimize()`
(`autoprecompiles/src/optimizer.rs`) for a single OpenVM ADD-immediate instruction
(`add(rd=8, rs1=8, rs2=1, rs2_as=0)`, the OpenVM analogue of RISC-V `addi`), and asserts
that leanr's `identityOptimizer` returns the same machine.

The machine was dumped from powdr just before `optimize()` (36 columns, 20 bus interactions,
32 constraints — the raw per-instruction AIR before optimization). Bus IDs follow the OpenVM
default bus map (0/1/2/3/6), matching `Leanr.OpenVM.openVmBusSemantics`.

`Expression` (see `Leanr/Spec.lean`) has only `const/var/add/mul`, so `-`/negation are encoded
via multiplication by `-1` through the `Sub`/`Neg` instances below.
-/

set_option autoImplicit false

namespace Leanr.OpenVM.Snapshot

open Leanr.OpenVM

/-- The BabyBear field modulus, `2^31 - 2^27 + 1`. -/
def babyBear : Nat := 2013265921

variable {p : Nat}

-- Arithmetic sugar for writing `Expression` literals.
instance : Add (Expression p) := ⟨Expression.add⟩
instance : Mul (Expression p) := ⟨Expression.mul⟩
instance : Neg (Expression p) := ⟨fun e => Expression.mul (Expression.const (-1)) e⟩
instance : Sub (Expression p) := ⟨fun a b => Expression.add a (Expression.mul (Expression.const (-1)) b)⟩

/-- Variable helper. -/
def V (s : String) : Expression babyBear := .var s
/-- Constant helper (a natural-number literal in the BabyBear field). -/
def C (n : Nat) : Expression babyBear := .const (n : ZMod babyBear)

def addiInput : ConstraintSystem babyBear where
  algebraicConstraints := [
    (V "opcode_add_flag_0" * (V "opcode_add_flag_0" - C 1)),
    (V "opcode_sub_flag_0" * (V "opcode_sub_flag_0" - C 1)),
    (V "opcode_xor_flag_0" * (V "opcode_xor_flag_0" - C 1)),
    (V "opcode_or_flag_0" * (V "opcode_or_flag_0" - C 1)),
    (V "opcode_and_flag_0" * (V "opcode_and_flag_0" - C 1)),
    ((((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") * ((((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") - C 1)),
    (V "opcode_add_flag_0" * ((C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)) * ((C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)) - C 1))),
    (V "opcode_sub_flag_0" * ((C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)) * ((C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)) - C 1))),
    (V "opcode_add_flag_0" * ((C 2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)))) * ((C 2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)))) - C 1))),
    (V "opcode_sub_flag_0" * ((C 2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)))) * ((C 2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)))) - C 1))),
    (V "opcode_add_flag_0" * ((C 2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (C 2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)))))) * ((C 2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (C 2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)))))) - C 1))),
    (V "opcode_sub_flag_0" * ((C 2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (C 2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)))))) * ((C 2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (C 2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)))))) - C 1))),
    (V "opcode_add_flag_0" * ((C 2005401601 * (((V "b__3_0" + V "c__3_0") - V "a__3_0") + (C 2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (C 2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)))))))) * ((C 2005401601 * (((V "b__3_0" + V "c__3_0") - V "a__3_0") + (C 2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (C 2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (C 2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + C 0)))))))) - C 1))),
    (V "opcode_sub_flag_0" * ((C 2005401601 * (((V "a__3_0" + V "c__3_0") - V "b__3_0") + (C 2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (C 2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)))))))) * ((C 2005401601 * (((V "a__3_0" + V "c__3_0") - V "b__3_0") + (C 2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (C 2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (C 2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + C 0)))))))) - C 1))),
    (V "rs2_as_0" * (V "rs2_as_0" - C 1)),
    ((C 1 - V "rs2_as_0") * (V "rs2_0" - ((V "c__0_0" + (V "c__1_0" * C 256)) + (V "c__2_0" * C 65536)))),
    ((C 1 - V "rs2_as_0") * (V "c__2_0" - V "c__3_0")),
    ((C 1 - V "rs2_as_0") * (V "c__2_0" * (C 255 - V "c__2_0"))),
    ((((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") * ((((V "from_state__timestamp_0" + C 0) - V "reads_aux__0__base__prev_timestamp_0") - C 1) - ((C 0 + (V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0" * C 1)) + (V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0" * C 131072)))),
    (V "rs2_as_0" * ((((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") - C 1)),
    (V "rs2_as_0" * ((((V "from_state__timestamp_0" + C 1) - V "reads_aux__1__base__prev_timestamp_0") - C 1) - ((C 0 + (V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0" * C 1)) + (V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0" * C 131072)))),
    ((((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") * ((((V "from_state__timestamp_0" + C 2) - V "writes_aux__base__prev_timestamp_0") - C 1) - ((C 0 + (V "writes_aux__base__timestamp_lt_aux__lower_decomp__0_0" * C 1)) + (V "writes_aux__base__timestamp_lt_aux__lower_decomp__1_0" * C 131072)))),
    ((-(((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")) + C 1),
    (V "from_state__pc_0" - C 0),
    ((C 512 + (((((C 0 + (V "opcode_add_flag_0" * C 0)) + (V "opcode_sub_flag_0" * C 1)) + (V "opcode_xor_flag_0" * C 2)) + (V "opcode_or_flag_0" * C 3)) + (V "opcode_and_flag_0" * C 4))) - C 512),
    (V "rd_ptr_0" - C 8),
    (V "rs1_ptr_0" - C 8),
    (V "rs2_0" - C 1),
    (C 1 - C 1),
    (V "rs2_as_0" - C 0),
    (C 0 - C 0),
    (C 0 - C 0)
  ]
  busInteractions := [
  { busId := 0, multiplicity := (-(((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")),
    payload := [V "from_state__pc_0", V "from_state__timestamp_0"] },
  { busId := 0, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(V "from_state__pc_0" + C 4), (V "from_state__timestamp_0" + C 3)] },
  { busId := 1, multiplicity := (C 2013265920 * (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")),
    payload := [C 1, V "rs1_ptr_0", V "b__0_0", V "b__1_0", V "b__2_0", V "b__3_0", V "reads_aux__0__base__prev_timestamp_0"] },
  { busId := 1, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [C 1, V "rs1_ptr_0", V "b__0_0", V "b__1_0", V "b__2_0", V "b__3_0", (V "from_state__timestamp_0" + C 0)] },
  { busId := 1, multiplicity := (C 2013265920 * V "rs2_as_0"),
    payload := [V "rs2_as_0", V "rs2_0", V "c__0_0", V "c__1_0", V "c__2_0", V "c__3_0", V "reads_aux__1__base__prev_timestamp_0"] },
  { busId := 1, multiplicity := V "rs2_as_0",
    payload := [V "rs2_as_0", V "rs2_0", V "c__0_0", V "c__1_0", V "c__2_0", V "c__3_0", (V "from_state__timestamp_0" + C 1)] },
  { busId := 1, multiplicity := (C 2013265920 * (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")),
    payload := [C 1, V "rd_ptr_0", V "writes_aux__prev_data__0_0", V "writes_aux__prev_data__1_0", V "writes_aux__prev_data__2_0", V "writes_aux__prev_data__3_0", V "writes_aux__base__prev_timestamp_0"] },
  { busId := 1, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [C 1, V "rd_ptr_0", V "a__0_0", V "a__1_0", V "a__2_0", V "a__3_0", (V "from_state__timestamp_0" + C 2)] },
  { busId := 2, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "from_state__pc_0", (C 512 + (((((C 0 + (V "opcode_add_flag_0" * C 0)) + (V "opcode_sub_flag_0" * C 1)) + (V "opcode_xor_flag_0" * C 2)) + (V "opcode_or_flag_0" * C 3)) + (V "opcode_and_flag_0" * C 4))), V "rd_ptr_0", V "rs1_ptr_0", V "rs2_0", C 1, V "rs2_as_0", C 0, C 0] },
  { busId := 3, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", C 17] },
  { busId := 3, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", C 12] },
  { busId := 3, multiplicity := V "rs2_as_0",
    payload := [V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", C 17] },
  { busId := 3, multiplicity := V "rs2_as_0",
    payload := [V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", C 12] },
  { busId := 3, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", C 17] },
  { busId := 3, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", C 12] },
  { busId := 6, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__0_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__0_0")), (((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__0_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__0_0")), (((V "opcode_xor_flag_0" * V "a__0_0") + (V "opcode_or_flag_0" * (((C 2 * V "a__0_0") - V "b__0_0") - V "c__0_0"))) + (V "opcode_and_flag_0" * ((V "b__0_0" + V "c__0_0") - (C 2 * V "a__0_0")))), C 1] },
  { busId := 6, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__1_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__1_0")), (((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__1_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__1_0")), (((V "opcode_xor_flag_0" * V "a__1_0") + (V "opcode_or_flag_0" * (((C 2 * V "a__1_0") - V "b__1_0") - V "c__1_0"))) + (V "opcode_and_flag_0" * ((V "b__1_0" + V "c__1_0") - (C 2 * V "a__1_0")))), C 1] },
  { busId := 6, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__2_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__2_0")), (((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__2_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__2_0")), (((V "opcode_xor_flag_0" * V "a__2_0") + (V "opcode_or_flag_0" * (((C 2 * V "a__2_0") - V "b__2_0") - V "c__2_0"))) + (V "opcode_and_flag_0" * ((V "b__2_0" + V "c__2_0") - (C 2 * V "a__2_0")))), C 1] },
  { busId := 6, multiplicity := (((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__3_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__3_0")), (((C 1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__3_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__3_0")), (((V "opcode_xor_flag_0" * V "a__3_0") + (V "opcode_or_flag_0" * (((C 2 * V "a__3_0") - V "b__3_0") - V "c__3_0"))) + (V "opcode_and_flag_0" * ((V "b__3_0" + V "c__3_0") - (C 2 * V "a__3_0")))), C 1] },
  { busId := 6, multiplicity := ((((((C 0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") - V "rs2_as_0"),
    payload := [V "c__0_0", V "c__1_0", C 0, C 0] }
  ]


/-- Render an `Expression` to a canonical, fully-parenthesized string. -/
def renderExpr : Expression p → String
  | .const n => toString n.val
  | .var x => x
  | .add a b => s!"({renderExpr a} + {renderExpr b})"
  | .mul a b => s!"({renderExpr a} * {renderExpr b})"

/-- Render a single bus interaction. -/
def renderBus (bi : BusInteraction (Expression babyBear)) : String :=
  let args := String.intercalate ", " (bi.payload.map renderExpr)
  s!"bus {bi.busId}: mult={renderExpr bi.multiplicity}, args=[{args}]"

/-- Render a whole constraint system (our own canonical snapshot format). -/
def render (cs : ConstraintSystem babyBear) : String :=
  let buses := String.intercalate "\n" (cs.busInteractions.map renderBus)
  let cons := String.intercalate "\n" (cs.algebraicConstraints.map (fun e => s!"{renderExpr e} = 0"))
  s!"// Bus interactions:\n{buses}\n\n// Algebraic constraints:\n{cons}"


/-- The expected rendering of the ported machine (our canonical snapshot format). -/
def addiInputSnapshot : String :=
"// Bus interactions:
bus 0: mult=(2013265920 * (((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0)), args=[from_state__pc_0, from_state__timestamp_0]
bus 0: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[(from_state__pc_0 + 4), (from_state__timestamp_0 + 3)]
bus 1: mult=(2013265920 * (((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0)), args=[1, rs1_ptr_0, b__0_0, b__1_0, b__2_0, b__3_0, reads_aux__0__base__prev_timestamp_0]
bus 1: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[1, rs1_ptr_0, b__0_0, b__1_0, b__2_0, b__3_0, (from_state__timestamp_0 + 0)]
bus 1: mult=(2013265920 * rs2_as_0), args=[rs2_as_0, rs2_0, c__0_0, c__1_0, c__2_0, c__3_0, reads_aux__1__base__prev_timestamp_0]
bus 1: mult=rs2_as_0, args=[rs2_as_0, rs2_0, c__0_0, c__1_0, c__2_0, c__3_0, (from_state__timestamp_0 + 1)]
bus 1: mult=(2013265920 * (((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0)), args=[1, rd_ptr_0, writes_aux__prev_data__0_0, writes_aux__prev_data__1_0, writes_aux__prev_data__2_0, writes_aux__prev_data__3_0, writes_aux__base__prev_timestamp_0]
bus 1: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[1, rd_ptr_0, a__0_0, a__1_0, a__2_0, a__3_0, (from_state__timestamp_0 + 2)]
bus 2: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[from_state__pc_0, (512 + (((((0 + (opcode_add_flag_0 * 0)) + (opcode_sub_flag_0 * 1)) + (opcode_xor_flag_0 * 2)) + (opcode_or_flag_0 * 3)) + (opcode_and_flag_0 * 4))), rd_ptr_0, rs1_ptr_0, rs2_0, 1, rs2_as_0, 0, 0]
bus 3: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0, 17]
bus 3: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0, 12]
bus 3: mult=rs2_as_0, args=[reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0, 17]
bus 3: mult=rs2_as_0, args=[reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0, 12]
bus 3: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[writes_aux__base__timestamp_lt_aux__lower_decomp__0_0, 17]
bus 3: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[writes_aux__base__timestamp_lt_aux__lower_decomp__1_0, 12]
bus 6: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[(((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__0_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * b__0_0)), (((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__0_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * c__0_0)), (((opcode_xor_flag_0 * a__0_0) + (opcode_or_flag_0 * (((2 * a__0_0) + (2013265920 * b__0_0)) + (2013265920 * c__0_0)))) + (opcode_and_flag_0 * ((b__0_0 + c__0_0) + (2013265920 * (2 * a__0_0))))), 1]
bus 6: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[(((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__1_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * b__1_0)), (((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__1_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * c__1_0)), (((opcode_xor_flag_0 * a__1_0) + (opcode_or_flag_0 * (((2 * a__1_0) + (2013265920 * b__1_0)) + (2013265920 * c__1_0)))) + (opcode_and_flag_0 * ((b__1_0 + c__1_0) + (2013265920 * (2 * a__1_0))))), 1]
bus 6: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[(((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__2_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * b__2_0)), (((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__2_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * c__2_0)), (((opcode_xor_flag_0 * a__2_0) + (opcode_or_flag_0 * (((2 * a__2_0) + (2013265920 * b__2_0)) + (2013265920 * c__2_0)))) + (opcode_and_flag_0 * ((b__2_0 + c__2_0) + (2013265920 * (2 * a__2_0))))), 1]
bus 6: mult=(((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0), args=[(((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__3_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * b__3_0)), (((1 + (2013265920 * ((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0))) * a__3_0) + (((opcode_xor_flag_0 + opcode_or_flag_0) + opcode_and_flag_0) * c__3_0)), (((opcode_xor_flag_0 * a__3_0) + (opcode_or_flag_0 * (((2 * a__3_0) + (2013265920 * b__3_0)) + (2013265920 * c__3_0)))) + (opcode_and_flag_0 * ((b__3_0 + c__3_0) + (2013265920 * (2 * a__3_0))))), 1]
bus 6: mult=((((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0) + (2013265920 * rs2_as_0)), args=[c__0_0, c__1_0, 0, 0]

// Algebraic constraints:
(opcode_add_flag_0 * (opcode_add_flag_0 + (2013265920 * 1))) = 0
(opcode_sub_flag_0 * (opcode_sub_flag_0 + (2013265920 * 1))) = 0
(opcode_xor_flag_0 * (opcode_xor_flag_0 + (2013265920 * 1))) = 0
(opcode_or_flag_0 * (opcode_or_flag_0 + (2013265920 * 1))) = 0
(opcode_and_flag_0 * (opcode_and_flag_0 + (2013265920 * 1))) = 0
((((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0) * ((((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0) + (2013265920 * 1))) = 0
(opcode_add_flag_0 * ((2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)) * ((2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)) + (2013265920 * 1)))) = 0
(opcode_sub_flag_0 * ((2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)) * ((2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)) + (2013265920 * 1)))) = 0
(opcode_add_flag_0 * ((2005401601 * (((b__1_0 + c__1_0) + (2013265920 * a__1_0)) + (2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)))) * ((2005401601 * (((b__1_0 + c__1_0) + (2013265920 * a__1_0)) + (2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)))) + (2013265920 * 1)))) = 0
(opcode_sub_flag_0 * ((2005401601 * (((a__1_0 + c__1_0) + (2013265920 * b__1_0)) + (2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)))) * ((2005401601 * (((a__1_0 + c__1_0) + (2013265920 * b__1_0)) + (2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)))) + (2013265920 * 1)))) = 0
(opcode_add_flag_0 * ((2005401601 * (((b__2_0 + c__2_0) + (2013265920 * a__2_0)) + (2005401601 * (((b__1_0 + c__1_0) + (2013265920 * a__1_0)) + (2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)))))) * ((2005401601 * (((b__2_0 + c__2_0) + (2013265920 * a__2_0)) + (2005401601 * (((b__1_0 + c__1_0) + (2013265920 * a__1_0)) + (2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)))))) + (2013265920 * 1)))) = 0
(opcode_sub_flag_0 * ((2005401601 * (((a__2_0 + c__2_0) + (2013265920 * b__2_0)) + (2005401601 * (((a__1_0 + c__1_0) + (2013265920 * b__1_0)) + (2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)))))) * ((2005401601 * (((a__2_0 + c__2_0) + (2013265920 * b__2_0)) + (2005401601 * (((a__1_0 + c__1_0) + (2013265920 * b__1_0)) + (2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)))))) + (2013265920 * 1)))) = 0
(opcode_add_flag_0 * ((2005401601 * (((b__3_0 + c__3_0) + (2013265920 * a__3_0)) + (2005401601 * (((b__2_0 + c__2_0) + (2013265920 * a__2_0)) + (2005401601 * (((b__1_0 + c__1_0) + (2013265920 * a__1_0)) + (2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)))))))) * ((2005401601 * (((b__3_0 + c__3_0) + (2013265920 * a__3_0)) + (2005401601 * (((b__2_0 + c__2_0) + (2013265920 * a__2_0)) + (2005401601 * (((b__1_0 + c__1_0) + (2013265920 * a__1_0)) + (2005401601 * (((b__0_0 + c__0_0) + (2013265920 * a__0_0)) + 0)))))))) + (2013265920 * 1)))) = 0
(opcode_sub_flag_0 * ((2005401601 * (((a__3_0 + c__3_0) + (2013265920 * b__3_0)) + (2005401601 * (((a__2_0 + c__2_0) + (2013265920 * b__2_0)) + (2005401601 * (((a__1_0 + c__1_0) + (2013265920 * b__1_0)) + (2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)))))))) * ((2005401601 * (((a__3_0 + c__3_0) + (2013265920 * b__3_0)) + (2005401601 * (((a__2_0 + c__2_0) + (2013265920 * b__2_0)) + (2005401601 * (((a__1_0 + c__1_0) + (2013265920 * b__1_0)) + (2005401601 * (((a__0_0 + c__0_0) + (2013265920 * b__0_0)) + 0)))))))) + (2013265920 * 1)))) = 0
(rs2_as_0 * (rs2_as_0 + (2013265920 * 1))) = 0
((1 + (2013265920 * rs2_as_0)) * (rs2_0 + (2013265920 * ((c__0_0 + (c__1_0 * 256)) + (c__2_0 * 65536))))) = 0
((1 + (2013265920 * rs2_as_0)) * (c__2_0 + (2013265920 * c__3_0))) = 0
((1 + (2013265920 * rs2_as_0)) * (c__2_0 * (255 + (2013265920 * c__2_0)))) = 0
((((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0) * ((((from_state__timestamp_0 + 0) + (2013265920 * reads_aux__0__base__prev_timestamp_0)) + (2013265920 * 1)) + (2013265920 * ((0 + (reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0 * 1)) + (reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0 * 131072))))) = 0
(rs2_as_0 * ((((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0) + (2013265920 * 1))) = 0
(rs2_as_0 * ((((from_state__timestamp_0 + 1) + (2013265920 * reads_aux__1__base__prev_timestamp_0)) + (2013265920 * 1)) + (2013265920 * ((0 + (reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0 * 1)) + (reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0 * 131072))))) = 0
((((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0) * ((((from_state__timestamp_0 + 2) + (2013265920 * writes_aux__base__prev_timestamp_0)) + (2013265920 * 1)) + (2013265920 * ((0 + (writes_aux__base__timestamp_lt_aux__lower_decomp__0_0 * 1)) + (writes_aux__base__timestamp_lt_aux__lower_decomp__1_0 * 131072))))) = 0
((2013265920 * (((((0 + opcode_add_flag_0) + opcode_sub_flag_0) + opcode_xor_flag_0) + opcode_or_flag_0) + opcode_and_flag_0)) + 1) = 0
(from_state__pc_0 + (2013265920 * 0)) = 0
((512 + (((((0 + (opcode_add_flag_0 * 0)) + (opcode_sub_flag_0 * 1)) + (opcode_xor_flag_0 * 2)) + (opcode_or_flag_0 * 3)) + (opcode_and_flag_0 * 4))) + (2013265920 * 512)) = 0
(rd_ptr_0 + (2013265920 * 8)) = 0
(rs1_ptr_0 + (2013265920 * 8)) = 0
(rs2_0 + (2013265920 * 1)) = 0
(1 + (2013265920 * 1)) = 0
(rs2_as_0 + (2013265920 * 0)) = 0
(0 + (2013265920 * 0)) = 0
(0 + (2013265920 * 0)) = 0"

/-- The identity optimizer returns the *same* machine (definitional equality). -/
example : identityOptimizer addiInput (openVmBusSemantics babyBear) = addiInput := rfl

-- Snapshot check: rendering the identity optimizer's output reproduces the stored snapshot.
-- (`identityOptimizer` returns its input, so this also guards the ported `addiInput` data.)
#guard render (identityOptimizer addiInput (openVmBusSemantics babyBear)) == addiInputSnapshot

end Leanr.OpenVM.Snapshot
