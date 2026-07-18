import ApcOptimizer.Implementation.JsonParser
import ApcOptimizer.Implementation.JsonSerializer
import ApcOptimizer.Optimizer

/-!
# C FFI entry point

A single `@[export]`ed, total function `apc_optimizer_optimize_json` that the C shim (and, through
it, powdr's `autoprecompiles-lean-ffi` crate) calls. It takes the target VM (`vm`: `0 = OpenVM`,
`1 = SP1`), the degree bound (`degreeIdentities`, `degreeBusInteractions`), and a powdr
`{"machine", "bus_map", "next_free_id"}` JSON export, parses it over the VM's field, runs the
matching verified optimizer with the given degree bound, and serializes the result as
`{"machine": <SymbolicMachine>, "next_free_id": N}`. `next_free_id` is powdr's `ColumnAllocator`
cursor — **required** (a missing one yields `{"error": ...}`), advanced past the fresh ids assigned
to new columns so powdr reseeds its allocator directly.

On any parse error the function returns a `{"error": "..."}` object rather than a machine, so the
Rust side can surface a clear message instead of an opaque deserialization failure. The function
never throws across the FFI boundary.
-/

set_option autoImplicit false

open ApcOptimizer.OpenVM (openVmOptimizer babyBear)
open ApcOptimizer.SP1 (sp1Optimizer koalaBear)

/-- The zkVMs the FFI can dispatch to, matching powdr's VM discriminant. -/
inductive KnownVm where
  | openVm
  | sp1
  deriving Repr, DecidableEq

/-- Decode powdr's VM discriminant (`0 = OpenVM`, `1 = SP1`). -/
def KnownVm.ofUInt8? : UInt8 → Option KnownVm
  | 0 => some .openVm
  | 1 => some .sp1
  | _ => none

/-- A `{"error": <msg>}` JSON object (the only non-machine reply). -/
private def errorJson (msg : String) : String :=
  "{\"error\":" ++ (Lean.Json.str msg).compress ++ "}"

/-- Parse a powdr OpenVM export, run `openVmOptimizer` with degree bound `b`, and serialize. -/
private def runOpenVm (b : DegreeBound) (input : String) : String :=
  match parseJsonSystem (p := babyBear) input with
  | .error err => errorJson err
  | .ok (_, _, none) => errorJson "missing required field `next_free_id`"
  | .ok (cs, busMap, some base) =>
    let (optimized, ds) := openVmOptimizer busMap.toBusMap b cs
    ApcOptimizer.Serialize.serializeResult optimized ds base

/-- Parse a powdr SP1 export, run `sp1Optimizer` with degree bound `b`, and serialize. -/
private def runSp1 (b : DegreeBound) (input : String) : String :=
  match parseJsonSystemSp1 (p := koalaBear) input with
  | .error err => errorJson err
  | .ok (_, _, none) => errorJson "missing required field `next_free_id`"
  | .ok (cs, busMap, some base) =>
    let (optimized, ds) := sp1Optimizer busMap.toBusMap b cs
    ApcOptimizer.Serialize.serializeResult optimized ds base

/-- Parse a powdr export, run the verified optimizer for the requested VM with the given degree
    bound, and serialize the optimized machine plus the advanced `next_free_id`. Returns
    `{"error": ...}` on an unknown VM or a parse failure. -/
@[export apc_optimizer_optimize_json]
def apcOptimizerOptimizeJson (vm : UInt8) (degreeIdentities degreeBusInteractions : UInt64)
    (input : String) : String :=
  let b : DegreeBound := ⟨degreeIdentities.toNat, degreeBusInteractions.toNat⟩
  match KnownVm.ofUInt8? vm with
  | none => errorJson s!"unknown VM discriminant {vm}"
  | some .openVm => runOpenVm b input
  | some .sp1 => runSp1 b input
