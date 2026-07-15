import ApcOptimizer.Implementation.JsonParser
import ApcOptimizer.Implementation.JsonSerializer
import ApcOptimizer.Optimizer

/-!
# C FFI entry point

A single `@[export]`ed, total function `apc_optimizer_optimize_json : String → String` that the C shim
(and, through it, powdr's `autoprecompiles-lean-ffi` crate) calls: it parses a powdr
`{"machine", "bus_map", "next_free_id"}` JSON export, runs the verified OpenVM optimizer, and
serializes the result as `{"machine": <SymbolicMachine>, "next_free_id": N}`. `next_free_id` is
powdr's `ColumnAllocator` cursor — **required** in (a missing one yields `{"error": ...}`),
advanced past the fresh ids assigned to new columns out — so powdr reseeds its allocator directly.

On any parse error the function returns a `{"error": "..."}` object rather than a machine, so the
Rust side can surface a clear message instead of an opaque deserialization failure. The function
never throws across the FFI boundary.
-/

set_option autoImplicit false

open ApcOptimizer.OpenVM (openVmOptimizer babyBear)

/-- Escape a string for a JSON string literal (used only for the error path). -/
private def escapeJson (s : String) : String :=
  (Lean.Json.str s).compress

/-- Parse a powdr export, run the OpenVM optimizer, and serialize the optimized machine plus the
    advanced `next_free_id`. Returns `{"error": ...}` on failure. -/
@[export apc_optimizer_optimize_json]
def apcOptimizerOptimizeJson (input : String) : String :=
  match parseJsonSystem (p := babyBear) input with
  | .error err => "{\"error\":" ++ escapeJson err ++ "}"
  -- `next_free_id` is required: fresh column ids are drawn from it, so a missing one is an error.
  | .ok (_, _, none) => "{\"error\":" ++ escapeJson "missing required field `next_free_id`" ++ "}"
  | .ok (cs, busMap, some base) =>
    -- `.1` is the optimized circuit; `.2` the `Derivations` (new witness columns + how powdr's
    -- witgen computes each), serialized under `derived_columns`.
    let (optimized, ds) := openVmOptimizer busMap.toBusMap cs
    ApcOptimizer.Serialize.serializeResult optimized ds base
