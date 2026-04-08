import Leanr.RangeConstraint
import Leanr.BusInteraction
import Lean.Data.Json

namespace OpenVM

def babyBear : Nat := 0x1dffff

/-- Specific bus types used in OpenVM. -/
inductive OpenVMBusType where
  | executionBridge
  | memory
  | pcLookup
  | bitwiseLookup
  | variableRangeChecker
  | tupleRangeChecker (size1 size2 : Nat)
  deriving Repr, BEq

instance : ToString OpenVMBusType where
  toString
    | .executionBridge => "ExecutionBridge"
    | .memory => "Memory"
    | .pcLookup => "PcLookup"
    | .bitwiseLookup => "BitwiseLookup"
    | .variableRangeChecker => "VariableRangeChecker"
    | .tupleRangeChecker s1 s2 => s!"TupleRangeChecker({s1}, {s2})"

/-- Translate a generic `BusType` to an `OpenVMBusType`, if recognized. -/
def OpenVMBusType.ofBusType : BusType → Option OpenVMBusType
  | .executionBridge => some .executionBridge
  | .memory => some .memory
  | .pcLookup => some .pcLookup
  | .other "BitwiseLookup" => some .bitwiseLookup
  | .other "VariableRangeChecker" => some .variableRangeChecker
  | .other s => do
    -- Parse "TupleRangeChecker:[s1, s2]"
    guard (s.startsWith "TupleRangeChecker:")
    let rest := (s.drop "TupleRangeChecker:".length).toString
    let json ← (Lean.Json.parse rest).toOption
    let arr ← json.getArr?.toOption
    let nums ← arr.toList.mapM fun v => v.getNat?.toOption
    match nums with
    | [s1, s2] => some (.tupleRangeChecker s1 s2)
    | _ => none

/-- Check whether an OpenVM bus type is stateful (i.e. order-dependent). -/
def OpenVMBusType.isStateful : OpenVMBusType → Bool
  | .executionBridge => true
  | .memory => true
  | .pcLookup => false
  | .bitwiseLookup => false
  | .variableRangeChecker => false
  | .tupleRangeChecker _ _ => false

/-- An OpenVM-specific bus map: bus IDs mapped to `OpenVMBusType`. -/
def OpenVMBusMap := List (Nat × OpenVMBusType)

/-- Translate a generic `BusMap` to an `OpenVMBusMap`, dropping unrecognized bus types. -/
def OpenVMBusMap.ofBusMap (bm : BusMap) : OpenVMBusMap :=
  bm.filterMap fun (id, ty) => (OpenVMBusType.ofBusType ty).map (id, ·)

instance : ToString OpenVMBusMap where
  toString bm :=
    let entries := bm.map fun (id, ty) => s!"  {id}: {ty}"
    "OpenVMBusMap:\n" ++ String.intercalate "\n" entries

/-- Look up a bus ID in an OpenVMBusMap and return whether it is stateful. -/
def busIsStateful (busMap : OpenVMBusMap) (busId : Nat) : Bool :=
  match busMap.find? (fun (id, _) => id == busId) with
  | some (_, ty) => ty.isStateful
  | none => false

/-- Handle bitwise lookup bus interactions.
    Expects payload (x, y, z, op) where:
    - op == 0: x, y are bytes, z = 0
    - op == 1: x, y are bytes, z = x ^ y -/
def handleBitwiseLookup (payload : Array (RangeConstraint babyBear))
    : Array (RangeConstraint babyBear) :=
  match payload.toList with
  | [x, y, _z, op] =>
    match op.toSingleValue?.map (·.val) with
    | some 0 =>
      -- Range constraint on x & y, z = 0
      #[.byte, .byte, (0 : ZMod babyBear), (0 : ZMod babyBear)]
    | some 1 =>
      -- z = x ^ y
      match x.toSingleValue?, y.toSingleValue? with
      | some xv, some yv =>
        -- Both known: compute XOR concretely
        let z : ZMod babyBear := (Nat.xor xv.val yv.val : Nat)
        #[↑xv, ↑yv, ↑z, (1 : ZMod babyBear)]
      | _, _ =>
        -- Unknown inputs: z can only have bits set in either x or y
        let zConstraint := (RangeConstraint.fromMask (x.mask ||| y.mask)).conjunction .byte
        #[.byte, .byte, zConstraint, (1 : ZMod babyBear)]
    | none =>
      -- Operation unknown: x, y, z are bytes, op is 0 or 1
      #[.byte, .byte, .byte, .fromMask 0x1]
    | _ => payload  -- invalid op
  | _ => payload  -- wrong arity

/-- Maximum number of bits for the variable range checker. -/
def maxBits : Nat := 25

/-- Handle variable range checker bus interactions.
    Expects payload (x, bits), where x is in [0, 2^bits - 1]. -/
def handleVariableRangeChecker (payload : Array (RangeConstraint babyBear))
    : Array (RangeConstraint babyBear) :=
  match payload.toList with
  | [_x, bits] =>
    match bits.toSingleValue? with
    | some bitsVal =>
      if bitsVal.val ≤ maxBits then
        let m := (1 <<< bitsVal.val) - 1
        #[.fromMask m, ↑bitsVal]
      else
        #[.fromMask ((1 <<< maxBits) - 1), .fromRange 0 maxBits]
    | none =>
      #[.fromMask ((1 <<< maxBits) - 1), .fromRange 0 maxBits]
  | _ => payload

/-- Handle tuple range checker bus interactions.
    Expects payload (x, y), where x ∈ [0, size1-1] and y ∈ [0, size2-1]. -/
def handleTupleRangeChecker (size1 size2 : Nat)
    (payload : Array (RangeConstraint babyBear))
    : Array (RangeConstraint babyBear) :=
  match payload.toList with
  | [_x, _y] =>
    #[.fromRange 0 (size1 - 1 : Nat), .fromRange 0 (size2 - 1 : Nat)]
  | _ => payload

def rv32RegisterAS : Nat := 1
def rv32MemoryAS : Nat := 2

/-- Handle memory bus interactions.
    Expects payload (address_space, pointer, data..., timestamp).
    Only tightens constraints for receive interactions (multiplicity == -1). -/
def handleMemory (payload : Array (RangeConstraint babyBear))
    (multiplicity : ZMod babyBear)
    : Array (RangeConstraint babyBear) :=
  -- Only tighten for receives (multiplicity == -1)
  if multiplicity != -1 then payload
  else
    -- payload = [address_space, pointer, data..., timestamp]
    if h : payload.size ≥ 3 then
      let addressSpace := payload[0]
      let pointer := payload[1]
      let timestamp := payload[payload.size - 1]
      let dataSlice := payload.toList.drop 2 |>.dropLast
      match addressSpace.toSingleValue?.map (·.val) with
      | some as_val =>
        if as_val == rv32RegisterAS || as_val == rv32MemoryAS then
          let data :=
            if as_val == rv32RegisterAS && pointer.toSingleValue? == some 0 then
              -- x0 register is always zero
              dataSlice.map fun _ => ((0 : ZMod babyBear) : RangeConstraint babyBear)
            else
              -- Data written to registers/memory is byte-range-checked
              dataSlice.map fun _ => RangeConstraint.byte
          #[addressSpace, pointer] ++ data.toArray ++ #[timestamp]
        else payload
      | none => payload
    else payload

/-- Build an OpenVM bus interaction handler from a BusMap.
    The bus map is first translated to an OpenVMBusMap. -/
def openVMBusInteractionHandler (busMap : BusMap) : BusInteractionHandler babyBear :=
  let ovmMap := OpenVMBusMap.ofBusMap busMap
  {
    isBusStateful := fun busId => busIsStateful ovmMap busId.val,
    handleBusInteraction bi :=
      (do
        let busIdVal ← bi.busId.toSingleValue?
        let multiplicity ← bi.multiplicity.toSingleValue?
        if multiplicity == 0 then return bi
        let busType ← ovmMap.lookup busIdVal.val
        let newPayload := match busType with
          | .executionBridge => bi.payload
          | .pcLookup => bi.payload
          | .memory => handleMemory bi.payload multiplicity
          | .bitwiseLookup => handleBitwiseLookup bi.payload
          | .variableRangeChecker => handleVariableRangeChecker bi.payload
          | .tupleRangeChecker s1 s2 => handleTupleRangeChecker s1 s2 bi.payload
        return { bi with payload := newPayload }
      ).getD bi
  }

end OpenVM
