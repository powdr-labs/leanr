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

## Witgen safety

The end-to-end path (powdr witgen consumes the optimized circuit) requires that every witness
column can actually be computed. The audited `openVmOptimizer` runs `reencodePass`, which invents
fresh boolean columns whose values powdr's witgen can only fill from a `DerivedVariable` hint —
and the audited spec (`optimizerPreservesDerivedColumns`) forbids the optimizer from emitting such
hints (it must carry derived columns verbatim; see `docs/design/architecture.md`). So this entry
point uses `optimizerWithBusFactsNoReencode` (the same pipeline without `reencodePass`): still a
verified refinement, and it never produces a hint-less witness column. Input `derived_columns` are
carried through verbatim, so any hints powdr already attached survive the round-trip.
-/

set_option autoImplicit false

open Leanr.OpenVM (babyBear openVmFacts BusMap)

/-- OpenVM optimizer without the fresh-column-creating re-encoding pass (see the module doc): a
    witgen-safe drop-in for the FFI path. Still a verified refinement of its input. -/
def openVmOptimizerNoReencode (busMap : BusMap) (iters : Nat := 32) :
    ConstraintSystem babyBear → ConstraintSystem babyBear :=
  optimizerWithBusFactsNoReencode (openVmFacts babyBear busMap) iters

/-- Escape a string for a JSON string literal (used only for the error path). -/
private def escapeJson (s : String) : String :=
  (Lean.Json.str s).compress

/-- Parse a powdr export, run the witgen-safe OpenVM optimizer (32 cleanup cycles, matching the CLI
    default), and serialize the optimized machine. Returns `{"error": ...}` on failure. -/
@[export leanr_optimize_json]
def leanrOptimizeJson (input : String) : String :=
  match parseJsonSystem (p := babyBear) input with
  | .error err => "{\"error\":" ++ escapeJson err ++ "}"
  | .ok (cs, busMap) =>
    let optimized := openVmOptimizerNoReencode busMap.toBusMap 32 cs
    Leanr.Serialize.serializeSystem optimized
