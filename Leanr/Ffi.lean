import Leanr.Implementation.JsonParser
import Leanr.Implementation.JsonSerializer
import Leanr.Optimizer

/-!
# C FFI entry point

A single `@[export]`ed, total function `leanr_optimize_json : String → String` that the C shim
(and, through it, powdr's `autoprecompiles-lean-ffi` crate) calls: it parses a powdr
`{"machine", "bus_map"}` JSON export, runs the verified OpenVM optimizer, and serializes the
result back into a powdr `SymbolicMachine` JSON string.

On any parse error the function returns a `{"error": "..."}` object rather than a machine, so the
Rust side can surface a clear message instead of an opaque deserialization failure. The function
never throws across the FFI boundary.
-/

set_option autoImplicit false

open Leanr.OpenVM (openVmOptimizer babyBear)

/-- Escape a string for a JSON string literal (used only for the error path). -/
private def escapeJson (s : String) : String :=
  (Lean.Json.str s).compress

/-- Parse a powdr export, run the OpenVM optimizer, and serialize the optimized machine.
    Returns `{"error": ...}` on failure. -/
@[export leanr_optimize_json]
def leanrOptimizeJson (input : String) : String :=
  match parseJsonSystem (p := babyBear) input with
  | .error err => "{\"error\":" ++ escapeJson err ++ "}"
  | .ok (cs, busMap) =>
    -- `.1` is the optimized circuit; `.2` are the `Derivations` (optimizer-introduced witness
    -- columns paired with how powdr's witgen computes each), serialized under `derived_columns`.
    let (optimized, ds) := openVmOptimizer busMap.toBusMap cs
    Leanr.Serialize.serializeSystem optimized ds
