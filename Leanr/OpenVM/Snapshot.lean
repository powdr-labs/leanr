import Leanr.Spec
import Leanr.Utils.Dsl
import Leanr.Utils.Size
import Leanr.Optimizer
import Leanr.OpenVM.Semantics

/-!
# OpenVM snapshot test (single ADD-immediate, powdr `single_add_1`)

Ports the constraint system that is the **input** to powdr's `optimize()`
(`autoprecompiles/src/optimizer.rs`) for a single OpenVM ADD-immediate instruction
(`add(rd=8, rs1=8, rs2=1, rs2_as=0)`, the OpenVM analogue of RISC-V `addi`), runs `optimizer`
on it, and snapshots the *output*. The snapshot currently equals the input rendering because
`optimizer` is still the identity; regenerate it once the optimizer starts changing the circuit.

The machine was dumped from powdr just before `optimize()` (36 columns, 20 bus interactions,
32 constraints). Bus IDs follow the OpenVM default bus map (0/1/2/3/6), matching
`Leanr.OpenVM.openVmBusSemantics`.

Expressions are written with the `Leanr.Spec.Dsl` sugar (`V`, numeric literals, `+ - *`).
-/

set_option autoImplicit false

namespace Leanr.OpenVM.Snapshot

open Leanr.OpenVM Leanr.Spec.Dsl

/-- The BabyBear field modulus, `2^31 - 2^27 + 1`. -/
def babyBear : Nat := 2013265921

def addiInput : ConstraintSystem babyBear where
  algebraicConstraints := [
    (V "opcode_add_flag_0" * (V "opcode_add_flag_0" - 1)),
    (V "opcode_sub_flag_0" * (V "opcode_sub_flag_0" - 1)),
    (V "opcode_xor_flag_0" * (V "opcode_xor_flag_0" - 1)),
    (V "opcode_or_flag_0" * (V "opcode_or_flag_0" - 1)),
    (V "opcode_and_flag_0" * (V "opcode_and_flag_0" - 1)),
    ((((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") * ((((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") - 1)),
    (V "opcode_add_flag_0" * ((2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)) * ((2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)) - 1))),
    (V "opcode_sub_flag_0" * ((2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)) * ((2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)) - 1))),
    (V "opcode_add_flag_0" * ((2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)))) * ((2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)))) - 1))),
    (V "opcode_sub_flag_0" * ((2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)))) * ((2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)))) - 1))),
    (V "opcode_add_flag_0" * ((2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)))))) * ((2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)))))) - 1))),
    (V "opcode_sub_flag_0" * ((2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)))))) * ((2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)))))) - 1))),
    (V "opcode_add_flag_0" * ((2005401601 * (((V "b__3_0" + V "c__3_0") - V "a__3_0") + (2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)))))))) * ((2005401601 * (((V "b__3_0" + V "c__3_0") - V "a__3_0") + (2005401601 * (((V "b__2_0" + V "c__2_0") - V "a__2_0") + (2005401601 * (((V "b__1_0" + V "c__1_0") - V "a__1_0") + (2005401601 * (((V "b__0_0" + V "c__0_0") - V "a__0_0") + 0)))))))) - 1))),
    (V "opcode_sub_flag_0" * ((2005401601 * (((V "a__3_0" + V "c__3_0") - V "b__3_0") + (2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)))))))) * ((2005401601 * (((V "a__3_0" + V "c__3_0") - V "b__3_0") + (2005401601 * (((V "a__2_0" + V "c__2_0") - V "b__2_0") + (2005401601 * (((V "a__1_0" + V "c__1_0") - V "b__1_0") + (2005401601 * (((V "a__0_0" + V "c__0_0") - V "b__0_0") + 0)))))))) - 1))),
    (V "rs2_as_0" * (V "rs2_as_0" - 1)),
    ((1 - V "rs2_as_0") * (V "rs2_0" - ((V "c__0_0" + (V "c__1_0" * 256)) + (V "c__2_0" * 65536)))),
    ((1 - V "rs2_as_0") * (V "c__2_0" - V "c__3_0")),
    ((1 - V "rs2_as_0") * (V "c__2_0" * (255 - V "c__2_0"))),
    ((((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") * ((((V "from_state__timestamp_0" + 0) - V "reads_aux__0__base__prev_timestamp_0") - 1) - ((0 + (V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0" * 1)) + (V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0" * 131072)))),
    (V "rs2_as_0" * ((((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") - 1)),
    (V "rs2_as_0" * ((((V "from_state__timestamp_0" + 1) - V "reads_aux__1__base__prev_timestamp_0") - 1) - ((0 + (V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0" * 1)) + (V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0" * 131072)))),
    ((((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") * ((((V "from_state__timestamp_0" + 2) - V "writes_aux__base__prev_timestamp_0") - 1) - ((0 + (V "writes_aux__base__timestamp_lt_aux__lower_decomp__0_0" * 1)) + (V "writes_aux__base__timestamp_lt_aux__lower_decomp__1_0" * 131072)))),
    ((-(((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")) + 1),
    (V "from_state__pc_0" - 0),
    ((512 + (((((0 + (V "opcode_add_flag_0" * 0)) + (V "opcode_sub_flag_0" * 1)) + (V "opcode_xor_flag_0" * 2)) + (V "opcode_or_flag_0" * 3)) + (V "opcode_and_flag_0" * 4))) - 512),
    (V "rd_ptr_0" - 8),
    (V "rs1_ptr_0" - 8),
    (V "rs2_0" - 1),
    (1 - 1),
    (V "rs2_as_0" - 0),
    (0 - 0),
    (0 - 0)
  ]
  busInteractions := [
  { busId := 0, multiplicity := (-(((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")),
    payload := [V "from_state__pc_0", V "from_state__timestamp_0"] },
  { busId := 0, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(V "from_state__pc_0" + 4), (V "from_state__timestamp_0" + 3)] },
  { busId := 1, multiplicity := (2013265920 * (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")),
    payload := [1, V "rs1_ptr_0", V "b__0_0", V "b__1_0", V "b__2_0", V "b__3_0", V "reads_aux__0__base__prev_timestamp_0"] },
  { busId := 1, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [1, V "rs1_ptr_0", V "b__0_0", V "b__1_0", V "b__2_0", V "b__3_0", (V "from_state__timestamp_0" + 0)] },
  { busId := 1, multiplicity := (2013265920 * V "rs2_as_0"),
    payload := [V "rs2_as_0", V "rs2_0", V "c__0_0", V "c__1_0", V "c__2_0", V "c__3_0", V "reads_aux__1__base__prev_timestamp_0"] },
  { busId := 1, multiplicity := V "rs2_as_0",
    payload := [V "rs2_as_0", V "rs2_0", V "c__0_0", V "c__1_0", V "c__2_0", V "c__3_0", (V "from_state__timestamp_0" + 1)] },
  { busId := 1, multiplicity := (2013265920 * (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0")),
    payload := [1, V "rd_ptr_0", V "writes_aux__prev_data__0_0", V "writes_aux__prev_data__1_0", V "writes_aux__prev_data__2_0", V "writes_aux__prev_data__3_0", V "writes_aux__base__prev_timestamp_0"] },
  { busId := 1, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [1, V "rd_ptr_0", V "a__0_0", V "a__1_0", V "a__2_0", V "a__3_0", (V "from_state__timestamp_0" + 2)] },
  { busId := 2, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "from_state__pc_0", (512 + (((((0 + (V "opcode_add_flag_0" * 0)) + (V "opcode_sub_flag_0" * 1)) + (V "opcode_xor_flag_0" * 2)) + (V "opcode_or_flag_0" * 3)) + (V "opcode_and_flag_0" * 4))), V "rd_ptr_0", V "rs1_ptr_0", V "rs2_0", 1, V "rs2_as_0", 0, 0] },
  { busId := 3, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", 17] },
  { busId := 3, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", 12] },
  { busId := 3, multiplicity := V "rs2_as_0",
    payload := [V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", 17] },
  { busId := 3, multiplicity := V "rs2_as_0",
    payload := [V "reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", 12] },
  { busId := 3, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", 17] },
  { busId := 3, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [V "writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", 12] },
  { busId := 6, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__0_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__0_0")), (((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__0_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__0_0")), (((V "opcode_xor_flag_0" * V "a__0_0") + (V "opcode_or_flag_0" * (((2 * V "a__0_0") - V "b__0_0") - V "c__0_0"))) + (V "opcode_and_flag_0" * ((V "b__0_0" + V "c__0_0") - (2 * V "a__0_0")))), 1] },
  { busId := 6, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__1_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__1_0")), (((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__1_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__1_0")), (((V "opcode_xor_flag_0" * V "a__1_0") + (V "opcode_or_flag_0" * (((2 * V "a__1_0") - V "b__1_0") - V "c__1_0"))) + (V "opcode_and_flag_0" * ((V "b__1_0" + V "c__1_0") - (2 * V "a__1_0")))), 1] },
  { busId := 6, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__2_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__2_0")), (((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__2_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__2_0")), (((V "opcode_xor_flag_0" * V "a__2_0") + (V "opcode_or_flag_0" * (((2 * V "a__2_0") - V "b__2_0") - V "c__2_0"))) + (V "opcode_and_flag_0" * ((V "b__2_0" + V "c__2_0") - (2 * V "a__2_0")))), 1] },
  { busId := 6, multiplicity := (((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0"),
    payload := [(((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__3_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "b__3_0")), (((1 - ((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0")) * V "a__3_0") + (((V "opcode_xor_flag_0" + V "opcode_or_flag_0") + V "opcode_and_flag_0") * V "c__3_0")), (((V "opcode_xor_flag_0" * V "a__3_0") + (V "opcode_or_flag_0" * (((2 * V "a__3_0") - V "b__3_0") - V "c__3_0"))) + (V "opcode_and_flag_0" * ((V "b__3_0" + V "c__3_0") - (2 * V "a__3_0")))), 1] },
  { busId := 6, multiplicity := ((((((0 + V "opcode_add_flag_0") + V "opcode_sub_flag_0") + V "opcode_xor_flag_0") + V "opcode_or_flag_0") + V "opcode_and_flag_0") - V "rs2_as_0"),
    payload := [V "c__0_0", V "c__1_0", 0, 0] }
  ]

/-- The expected rendering of the ported machine (`Leanr.Spec.Dsl.render` format). -/
def addiInputSnapshot : String :=
"// Bus 0:
mult=2013265920 * (opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0), args=[0, from_state__timestamp_0]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[4, from_state__timestamp_0 + 3]
// Bus 1:
mult=2013265920 * (opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0), args=[1, 8, b__0_0, b__1_0, b__2_0, b__3_0, reads_aux__0__base__prev_timestamp_0]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[1, 8, b__0_0, b__1_0, b__2_0, b__3_0, from_state__timestamp_0]
mult=0, args=[0, 1, c__0_0, c__1_0, c__2_0, c__3_0, reads_aux__1__base__prev_timestamp_0]
mult=0, args=[0, 1, c__0_0, c__1_0, c__2_0, c__3_0, from_state__timestamp_0 + 1]
mult=2013265920 * (opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0), args=[1, 8, writes_aux__prev_data__0_0, writes_aux__prev_data__1_0, writes_aux__prev_data__2_0, writes_aux__prev_data__3_0, writes_aux__base__prev_timestamp_0]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[1, 8, a__0_0, a__1_0, a__2_0, a__3_0, from_state__timestamp_0 + 2]
// Bus 2:
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[0, 512 + (opcode_sub_flag_0 + opcode_xor_flag_0 * 2 + opcode_or_flag_0 * 3 + opcode_and_flag_0 * 4), 8, 8, 1, 1, 0, 0, 0]
// Bus 3:
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0, 17]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0, 12]
mult=0, args=[reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0, 17]
mult=0, args=[reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0, 12]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[writes_aux__base__timestamp_lt_aux__lower_decomp__0_0, 17]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[writes_aux__base__timestamp_lt_aux__lower_decomp__1_0, 12]
// Bus 6:
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[(1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__0_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * b__0_0, (1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__0_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * c__0_0, opcode_xor_flag_0 * a__0_0 + opcode_or_flag_0 * (2 * a__0_0 + 2013265920 * b__0_0 + 2013265920 * c__0_0) + opcode_and_flag_0 * (b__0_0 + c__0_0 + 2013265920 * (2 * a__0_0)), 1]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[(1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__1_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * b__1_0, (1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__1_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * c__1_0, opcode_xor_flag_0 * a__1_0 + opcode_or_flag_0 * (2 * a__1_0 + 2013265920 * b__1_0 + 2013265920 * c__1_0) + opcode_and_flag_0 * (b__1_0 + c__1_0 + 2013265920 * (2 * a__1_0)), 1]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[(1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__2_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * b__2_0, (1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__2_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * c__2_0, opcode_xor_flag_0 * a__2_0 + opcode_or_flag_0 * (2 * a__2_0 + 2013265920 * b__2_0 + 2013265920 * c__2_0) + opcode_and_flag_0 * (b__2_0 + c__2_0 + 2013265920 * (2 * a__2_0)), 1]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[(1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__3_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * b__3_0, (1 + 2013265920 * (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0)) * a__3_0 + (opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * c__3_0, opcode_xor_flag_0 * a__3_0 + opcode_or_flag_0 * (2 * a__3_0 + 2013265920 * b__3_0 + 2013265920 * c__3_0) + opcode_and_flag_0 * (b__3_0 + c__3_0 + 2013265920 * (2 * a__3_0)), 1]
mult=opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0, args=[c__0_0, c__1_0, 0, 0]

// Algebraic constraints:
opcode_add_flag_0 * (opcode_add_flag_0 + 2013265920) = 0
opcode_sub_flag_0 * (opcode_sub_flag_0 + 2013265920) = 0
opcode_xor_flag_0 * (opcode_xor_flag_0 + 2013265920) = 0
opcode_or_flag_0 * (opcode_or_flag_0 + 2013265920) = 0
opcode_and_flag_0 * (opcode_and_flag_0 + 2013265920) = 0
(opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * (opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0 + 2013265920) = 0
opcode_add_flag_0 * (2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0) * (2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0) + 2013265920)) = 0
opcode_sub_flag_0 * (2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0) * (2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0) + 2013265920)) = 0
opcode_add_flag_0 * (2005401601 * (b__1_0 + c__1_0 + 2013265920 * a__1_0 + 2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0)) * (2005401601 * (b__1_0 + c__1_0 + 2013265920 * a__1_0 + 2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0)) + 2013265920)) = 0
opcode_sub_flag_0 * (2005401601 * (a__1_0 + c__1_0 + 2013265920 * b__1_0 + 2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0)) * (2005401601 * (a__1_0 + c__1_0 + 2013265920 * b__1_0 + 2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0)) + 2013265920)) = 0
opcode_add_flag_0 * (2005401601 * (b__2_0 + c__2_0 + 2013265920 * a__2_0 + 2005401601 * (b__1_0 + c__1_0 + 2013265920 * a__1_0 + 2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0))) * (2005401601 * (b__2_0 + c__2_0 + 2013265920 * a__2_0 + 2005401601 * (b__1_0 + c__1_0 + 2013265920 * a__1_0 + 2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0))) + 2013265920)) = 0
opcode_sub_flag_0 * (2005401601 * (a__2_0 + c__2_0 + 2013265920 * b__2_0 + 2005401601 * (a__1_0 + c__1_0 + 2013265920 * b__1_0 + 2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0))) * (2005401601 * (a__2_0 + c__2_0 + 2013265920 * b__2_0 + 2005401601 * (a__1_0 + c__1_0 + 2013265920 * b__1_0 + 2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0))) + 2013265920)) = 0
opcode_add_flag_0 * (2005401601 * (b__3_0 + c__3_0 + 2013265920 * a__3_0 + 2005401601 * (b__2_0 + c__2_0 + 2013265920 * a__2_0 + 2005401601 * (b__1_0 + c__1_0 + 2013265920 * a__1_0 + 2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0)))) * (2005401601 * (b__3_0 + c__3_0 + 2013265920 * a__3_0 + 2005401601 * (b__2_0 + c__2_0 + 2013265920 * a__2_0 + 2005401601 * (b__1_0 + c__1_0 + 2013265920 * a__1_0 + 2005401601 * (b__0_0 + c__0_0 + 2013265920 * a__0_0)))) + 2013265920)) = 0
opcode_sub_flag_0 * (2005401601 * (a__3_0 + c__3_0 + 2013265920 * b__3_0 + 2005401601 * (a__2_0 + c__2_0 + 2013265920 * b__2_0 + 2005401601 * (a__1_0 + c__1_0 + 2013265920 * b__1_0 + 2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0)))) * (2005401601 * (a__3_0 + c__3_0 + 2013265920 * b__3_0 + 2005401601 * (a__2_0 + c__2_0 + 2013265920 * b__2_0 + 2005401601 * (a__1_0 + c__1_0 + 2013265920 * b__1_0 + 2005401601 * (a__0_0 + c__0_0 + 2013265920 * b__0_0)))) + 2013265920)) = 0
1 + 2013265920 * (c__0_0 + c__1_0 * 256 + c__2_0 * 65536) = 0
c__2_0 + 2013265920 * c__3_0 = 0
c__2_0 * (255 + 2013265920 * c__2_0) = 0
(opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * (from_state__timestamp_0 + 2013265920 * reads_aux__0__base__prev_timestamp_0 + 2013265920 + 2013265920 * (reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0 + reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0 * 131072)) = 0
(opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) * (from_state__timestamp_0 + 2 + 2013265920 * writes_aux__base__prev_timestamp_0 + 2013265920 + 2013265920 * (writes_aux__base__timestamp_lt_aux__lower_decomp__0_0 + writes_aux__base__timestamp_lt_aux__lower_decomp__1_0 * 131072)) = 0
2013265920 * (opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0) + 1 = 0
512 + (opcode_sub_flag_0 + opcode_xor_flag_0 * 2 + opcode_or_flag_0 * 3 + opcode_and_flag_0 * 4) + 2013265409 = 0"

/-- The optimizer's output on the ported machine. -/
def addiOptimized : ConstraintSystem babyBear := optimizer addiInput (openVmBusSemantics babyBear)

-- Snapshot check: rendering the optimizer's output reproduces the stored snapshot.
-- To regenerate `addiInputSnapshot`, run: #eval IO.println (render addiOptimized)
#guard matchesSnapshot addiOptimized addiInputSnapshot

-- A correct optimizer must never grow the circuit, i.e. effectiveness ≥ 1.
#guard (1 : ℚ) ≤ effectiveness optimizer addiInput (openVmBusSemantics babyBear)

-- Measured shrink factor of the optimizer on this machine.
#eval s!"effectiveness: {effectiveness optimizer addiInput (openVmBusSemantics babyBear)}"

end Leanr.OpenVM.Snapshot
