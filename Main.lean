import ApcOptimizer.Implementation.JsonParser
import ApcOptimizer.Optimizer
import ApcOptimizer.Implementation.Optimizer
import ApcOptimizer.Utils.Size
import ApcOptimizer.Utils.Dsl
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Sp1Semantics
import ApcOptimizer.Ffi

/-!
# The apc-optimizer CLI

Benchmark harness for the optimizer on powdr `SymbolicMachine` exports
(`Benchmarks/OpenVM/openvm-eth/*.json.gz`, or any file in the same format — see
`ApcOptimizer/Implementation/JsonParser.lean`):

- `apc-optimizer run [vm] <file.json[.gz]>` — parse, run the apc-optimizer with the file's
  own bus map, report sizes and effectiveness.
- `apc-optimizer powdr [vm] <unopt.json[.gz]> <opt.json[.gz]>` — report powdr's effectiveness from
  its serialized optimizer output (no apc-optimizer run).
- `apc-optimizer compare [vm] <unopt.json[.gz]> <opt.json[.gz]>` — both, side by side.

`vm` is an optional leading `openvm` (default, BabyBear) or `sp1` (KoalaBear) token, selecting the
VM whose bus semantics and fact-aware optimizer to use.

The optimizer takes no iteration count: its cleanup loop (`iterateToFixpoint`) runs to a fixpoint,
provably terminating on the lexicographic size key `(vars, bus, constraints)`.
-/

open ApcOptimizer.OpenVM

/-- Read a benchmark file: `.json.gz` via `gunzip -c` (like the powdr test fixtures),
    `.json` directly. -/
def readInput (fileName : String) : IO String := do
  if fileName.endsWith ".json.gz" then
    let result ← IO.Process.output { cmd := "gunzip", args := #["-c", fileName] }
    if result.exitCode ≠ 0 then
      IO.eprintln s!"Error: gunzip failed: {result.stderr}"
      IO.Process.exit 1
    pure result.stdout
  else if fileName.endsWith ".json" then
    IO.FS.readFile fileName
  else
    IO.eprintln s!"Error: expected a .json or .json.gz file, got {fileName}"
    IO.Process.exit 1

/-- Parse a benchmark file into a constraint system over field `p` plus its bus map, using the
    given VM-specific parser (which already resolves the `BusMapList` to a `busId ↦ type` lookup).
    Rejects systems with bus ids missing from the map: an unmapped bus would be modeled as a
    no-op bus (stateless, never violating), silently licensing unsound optimizations. -/
def parseFileWith {p : ℕ} {τ : Type}
    (parse : String → Except String (ConstraintSystem p × (Nat → Option τ)))
    (fileName : String) : IO (ConstraintSystem p × (Nat → Option τ)) := do
  let contents ← readInput fileName
  match parse contents with
  | .error err =>
    IO.eprintln s!"Error parsing {fileName}: {err}"
    IO.Process.exit 1
  | .ok (system, busMap) =>
    let unmapped :=
      ((system.busInteractions.map (·.busId)).eraseDups).filter
        (fun busId => (busMap busId).isNone)
    unless unmapped.isEmpty do
      IO.eprintln s!"Error: {fileName} uses bus ids {unmapped} that are not in its bus_map"
      IO.Process.exit 1
    pure (system, busMap)

/-- The OpenVM (BabyBear) file parser: resolve the `BusMapList` to a lookup, dropping `next_free_id`
    (the CLI does not need powdr's column cursor). -/
def parseOpenVm (contents : String) :
    Except String (ConstraintSystem babyBear × (Nat → Option OpenVmBusType)) :=
  (parseJsonSystem (p := babyBear) contents).map (fun (s, bm, _) => (s, bm.toBusMap))

/-- The SP1 (KoalaBear) file parser. -/
def parseSp1 (contents : String) :
    Except String (ConstraintSystem ApcOptimizer.SP1.koalaBear ×
      (Nat → Option ApcOptimizer.SP1.Sp1BusType)) :=
  (parseJsonSystemSp1 (p := ApcOptimizer.SP1.koalaBear) contents).map
    (fun (s, bm, _) => (s, bm.toBusMap))

/-- Size measures of a constraint system, as reported by the CLI. -/
structure Stats where
  vars : Nat
  constraints : Nat
  busInteractions : Nat

/-- Same count as `ConstraintSystem.size` (distinct variables), but via a hash set —
    `List.dedup` is quadratic and benchmark machines have ~10⁵ variable occurrences. -/
def distinctVarCount {p : ℕ} (cs : ConstraintSystem p) : Nat :=
  let occurrences := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars
  (occurrences.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).size

/-- The distinct variable names of a constraint system, sorted and rendered for display.
    Variables may carry structured powdr IDs internally, but reports show only `Variable.name`. -/
def distinctVars {p : ℕ} (cs : ConstraintSystem p) : List String :=
  let occurrences := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars
  ((occurrences.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList.map
    (fun x => x.name)).mergeSort (fun a b => decide (a ≤ b))

def statsOf {p : ℕ} (cs : ConstraintSystem p) : Stats :=
  { vars := distinctVarCount cs,
    constraints := cs.algebraicConstraints.length,
    busInteractions := cs.busInteractions.length }

def printStats (label : String) (stats : Stats) : IO Unit :=
  IO.println s!"  {label}: {stats.vars} vars, {stats.constraints} constraints, \
    {stats.busInteractions} bus interactions"

/-- One effectiveness ratio: the factor `before / after` by which a size measure shrank, printed
    as an exact rational and a decimal. Handles `after = 0` explicitly (Lean's `x / 0 = 0` would
    otherwise misread "all removed" as "no reduction"). -/
def printRatio (label : String) (before after : Nat) : IO Unit :=
  if after == 0 then
    IO.println s!"    {label}: {before} → {after}  \
      ({if before == 0 then "1× (unchanged)" else "∞× (all removed)"})"
  else
    let ratio : ℚ := (before : ℚ) / (after : ℚ)
    IO.println s!"    {label}: {before} → {after}  ({ratio} ≈ {before.toFloat / after.toFloat}×)"

/-- Effectiveness of an optimization: the factor by which each size measure shrinks
    (`before / after`), for the three measures in priority order — variables first, then bus
    interactions, then algebraic constraints (the `ApcOptimizer/Utils/Size.lean` metrics). -/
def printEffectiveness (label : String) (before after : Stats) : IO Unit := do
  IO.println s!"{label} effectiveness (before → after):"
  printRatio (label := "variables       ") (before := before.vars) (after := after.vars)
  printRatio (label := "bus interactions") (before := before.busInteractions)
    (after := after.busInteractions)
  printRatio (label := "constraints     ") (before := before.constraints) (after := after.constraints)

/-- A VM's runtime for the CLI: its file parser (resolving the bus map to a `busId ↦ type` lookup),
    its fact-aware optimizer, and its degree bound (reported by `run`). All three are threaded
    through the generic `cmd*Impl` bodies so a single implementation serves both OpenVM and SP1. -/
structure VmBackend (p : ℕ) (τ : Type) where
  parse : String → Except String (ConstraintSystem p × (Nat → Option τ))
  optimize : (Nat → Option τ) → ConstraintSystem p → ConstraintSystem p × Derivations p
  degreeBound : DegreeBound

def cmdRunImpl {p : ℕ} {τ : Type} (be : VmBackend p τ) (fileName : String) : IO Unit := do
  let (cs, busMap) ← parseFileWith be.parse fileName
  IO.println s!"Parsed {cs.algebraicConstraints.length} constraints, \
    {cs.busInteractions.length} bus interactions"
  let before := statsOf cs
  let t0 ← IO.monoMsNow
  -- IO.lazyPure sequences the pure optimizer run between the clock reads (the compiler is
  -- free to float a plain `let` across IO actions, which breaks the measurement).
  let optimized ← IO.lazyPure (fun _ => (be.optimize busMap cs).1)
  let after ← IO.lazyPure (fun _ => statsOf optimized)
  let t1 ← IO.monoMsNow
  printStats (label := "before       ") (stats := before)
  printStats (label := "apc-optimizer") (stats := after)
  printEffectiveness (label := "apc-optimizer") (before := before) (after := after)
  let bound := be.degreeBound
  IO.println s!"  degree bound (identities {bound.identities}, bus {bound.busInteractions}): \
    input {if cs.withinDegreeB bound then "ok" else "EXCEEDED"}, \
    output {if optimized.withinDegreeB bound then "ok" else "EXCEEDED"}"
  IO.println s!"  ({t1 - t0} ms)"

/-- Like `cmdRun`, but also dump the distinct variables remaining after optimization (for
    diagnosing which variable classes the optimizer misses). -/
def cmdVarsImpl {p : ℕ} {τ : Type} (be : VmBackend p τ) (fileName : String) : IO Unit := do
  let (cs, busMap) ← parseFileWith be.parse fileName
  let optimized ← IO.lazyPure (fun _ => (be.optimize busMap cs).1)
  let occurrences := optimized.algebraicConstraints.flatMap Expression.vars ++
    optimized.busInteractions.flatMap BusInteraction.vars
  let distinct := (occurrences.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList
  for v in (distinct.map (fun x => x.name)).mergeSort (fun a b => decide (a ≤ b)) do
    IO.println v

/-- Render the optimized system (for diagnosing residual constraints/interactions). -/
def cmdRenderImpl {p : ℕ} {τ : Type} (be : VmBackend p τ) (fileName : String) : IO Unit := do
  let (cs, busMap) ← parseFileWith be.parse fileName
  let optimized ← IO.lazyPure (fun _ => (be.optimize busMap cs).1)
  IO.println (ApcOptimizer.Spec.Dsl.render optimized)

/-- `opt-export [vm] <in> <out.json>`: run the optimizer and write the optimized machine back out as
    `{"machine", "bus_map"}` JSON — the same shape the parser reads, so the export can be fed to
    `powdr`/`compare` like a `.powdr_opt` file. The `bus_map` is spliced through verbatim from the
    input; the machine comes from the FFI serializer (`serializeSystem`, including
    `derived_columns` for optimizer-introduced witness columns). -/
def cmdOptExportImpl {p : ℕ} {τ : Type} (be : VmBackend p τ)
    (inFile outFile : String) : IO Unit := do
  let (cs, busMap) ← parseFileWith be.parse inFile
  let rawJson ← readInput inFile
  let busMapJson ← do
    match Lean.Json.parse rawJson >>= (·.getObjVal? "bus_map") with
    | .error err =>
      IO.eprintln s!"Error: cannot extract bus_map from {inFile}: {err}"
      IO.Process.exit 1
    | .ok j => pure j
  let (optimized, ds) ← IO.lazyPure (fun _ => be.optimize busMap cs)
  let machineStr ← IO.lazyPure (fun _ => ApcOptimizer.Serialize.serializeSystem optimized ds)
  let machineJson ← do
    match Lean.Json.parse machineStr with
    | .error err =>
      IO.eprintln s!"Error: serializer produced invalid JSON: {err}"
      IO.Process.exit 1
    | .ok j => pure j
  IO.FS.writeFile outFile
    (Lean.Json.mkObj [("machine", machineJson), ("bus_map", busMapJson)]).compress

def cmdPowdrImpl {p : ℕ} {τ : Type} (be : VmBackend p τ)
    (unoptFile optFile : String) : IO Unit := do
  let (csBefore, _) ← parseFileWith be.parse unoptFile
  let (csAfter, _) ← parseFileWith be.parse optFile
  let before := statsOf csBefore
  let after := statsOf csAfter
  printStats (label := "before       ") (stats := before)
  printStats (label := "powdr        ") (stats := after)
  printEffectiveness (label := "powdr") (before := before) (after := after)

def cmdCompareImpl {p : ℕ} {τ : Type} (be : VmBackend p τ)
    (unoptFile optFile : String) : IO Unit := do
  cmdRunImpl be unoptFile
  let (csBefore, _) ← parseFileWith be.parse unoptFile
  let (csAfter, _) ← parseFileWith be.parse optFile
  printStats (label := "powdr        ") (stats := statsOf csAfter)
  printEffectiveness (label := "powdr") (before := statsOf csBefore) (after := statsOf csAfter)

/-- Escape a string for embedding inside a JSON string literal. -/
def jsonEscape (s : String) : String :=
  let s := s.replace "\\" "\\\\"
  let s := s.replace "\"" "\\\""
  let s := s.replace "\n" "\\n"
  let s := s.replace "\r" "\\r"
  s.replace "\t" "\\t"

/-- One circuit as a JSON object: size stats plus the DSL render. -/
def circuitJson {p : ℕ} (cs : ConstraintSystem p) : String :=
  let st := statsOf cs
  let vs := String.intercalate "," ((distinctVars cs).map (fun s => "\"" ++ jsonEscape s ++ "\""))
  "{\"vars\":" ++ toString st.vars ++
    ",\"constraints\":" ++ toString st.constraints ++
    ",\"bus\":" ++ toString st.busInteractions ++
    ",\"vars_list\":[" ++ vs ++ "]" ++
    ",\"render\":\"" ++ jsonEscape (ApcOptimizer.Spec.Dsl.render cs) ++ "\"}"

/-- `report [vm] <unopt> <opt>`: emit one JSON object with the original, powdr-optimized and
    apc-optimizer-optimized circuits (each: vars/constraints/bus + DSL render). Consumed by the
    benchmark HTML report (`Benchmarks/benchmark.py --report`). -/
def cmdReportImpl {p : ℕ} {τ : Type} (be : VmBackend p τ)
    (unoptFile optFile : String) : IO Unit := do
  let (cs, busMap) ← parseFileWith be.parse unoptFile
  let (csPowdr, _) ← parseFileWith be.parse optFile
  let optimized := (be.optimize busMap cs).1
  IO.println ("{\"original\":" ++ circuitJson cs ++
    ",\"powdr\":" ++ circuitJson csPowdr ++
    ",\"apc-optimizer\":" ++ circuitJson optimized ++ "}")

/-- The OpenVM backend: BabyBear field, `openVmOptimizer`, OpenVM's default degree bound. The
    optimizer is eta-expanded so its default `busMap` argument stays open. -/
def openVmBackend : VmBackend babyBear OpenVmBusType where
  parse := parseOpenVm
  optimize := fun bm => openVmOptimizer bm
  degreeBound := defaultDegreeBound

/-- The SP1 backend: KoalaBear field, SP1 bus semantics, `sp1Optimizer`. -/
def sp1Backend : VmBackend ApcOptimizer.SP1.koalaBear ApcOptimizer.SP1.Sp1BusType where
  parse := parseSp1
  optimize := fun bm => ApcOptimizer.SP1.sp1Optimizer bm
  degreeBound := ApcOptimizer.SP1.defaultDegreeBound

/-- Whether a token names the SP1 VM (`sp1`); anything else defaults to OpenVM. -/
def isSp1 (vm : String) : Bool := vm == "sp1"

def cmdRun (vm fileName : String) : IO Unit :=
  if isSp1 vm then cmdRunImpl sp1Backend fileName else cmdRunImpl openVmBackend fileName

def cmdVars (vm fileName : String) : IO Unit :=
  if isSp1 vm then cmdVarsImpl sp1Backend fileName else cmdVarsImpl openVmBackend fileName

def cmdRender (vm fileName : String) : IO Unit :=
  if isSp1 vm then cmdRenderImpl sp1Backend fileName else cmdRenderImpl openVmBackend fileName

def cmdOptExport (vm inFile outFile : String) : IO Unit :=
  if isSp1 vm then cmdOptExportImpl sp1Backend inFile outFile
  else cmdOptExportImpl openVmBackend inFile outFile

def cmdPowdr (vm unoptFile optFile : String) : IO Unit :=
  if isSp1 vm then cmdPowdrImpl sp1Backend unoptFile optFile
  else cmdPowdrImpl openVmBackend unoptFile optFile

def cmdCompare (vm unoptFile optFile : String) : IO Unit :=
  if isSp1 vm then cmdCompareImpl sp1Backend unoptFile optFile
  else cmdCompareImpl openVmBackend unoptFile optFile

def cmdReport (vm unoptFile optFile : String) : IO Unit :=
  if isSp1 vm then cmdReportImpl sp1Backend unoptFile optFile
  else cmdReportImpl openVmBackend unoptFile optFile

/-- Profiling helper: apply one fact-aware pass, forcing full evaluation, and return the new
    system plus the elapsed milliseconds. -/
def applyTimed {p : ℕ} (pass : VerifiedPassW p) (cs : ConstraintSystem p)
    (bs : BusSemantics p) (facts : BusFacts p bs) :
    IO (ConstraintSystem p × Nat) := do
  let t0 ← IO.monoMsNow
  let out ← IO.lazyPure (fun _ => (pass cs bs facts).out)
  -- Force the whole output structure (varCount traverses every expression node).
  let _ ← IO.lazyPure (fun _ =>
    out.varCount + out.algebraicConstraints.length + out.busInteractions.length)
  let t1 ← IO.monoMsNow
  pure (out, t1 - t0)

/-- Run one cleanup cycle's passes in order, accumulating per-pass elapsed time. -/
partial def runCycleTimed {p : ℕ} (passes : List (String × VerifiedPassW p))
    (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (acc : Std.HashMap String Nat) : IO (ConstraintSystem p × Std.HashMap String Nat) := do
  let mut c := cs
  let mut a := acc
  for (name, pass) in passes do
    let (c', dt) ← applyTimed pass c bs facts
    c := c'
    a := a.insert name (a.getD name 0 + dt)
  pure (c, a)

/-- Iterate the cleanup cycle to a fixpoint (mirroring `iterateToFixpoint`), accumulating per-pass
    time and counting iterations. -/
partial def profileLoop {p : ℕ} (passes : List (String × VerifiedPassW p))
    (cs : ConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (acc : Std.HashMap String Nat) (iter : Nat) :
    IO (ConstraintSystem p × Std.HashMap String Nat × Nat) := do
  let (cs', acc') ← runCycleTimed passes cs bs facts acc
  if cs'.sizeKey < cs.sizeKey then
    profileLoop passes cs' bs facts acc' (iter + 1)
  else
    pure (cs, acc', iter)

/-- Step the pipeline's three pass lists with per-pass timing, reporting the cumulative time spent in
    each pass across all fixpoint iterations. `preludePasses` / `cleanupPasses` / `codaPasses` are
    the exact lists `pipeline` folds (`ApcOptimizer/Implementation/Optimizer.lean`); per-pass timing
    is an IO side-effect, so the profiler steps the passes here instead of calling the pure
    `pipeline`, but it reads those same three lists, so it cannot time a pass the optimizer does not
    run, nor drift out of sync. -/
def profileRun {p : ℕ} (b : DegreeBound) (fileName : String) (cs : ConstraintSystem p)
    (bs : BusSemantics p) (facts : BusFacts p bs) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (cs, acc) ← runCycleTimed (preludePasses (p := p) b) cs bs facts ∅
  let (cs, acc, iters) ← profileLoop (cleanupPasses (p := p) b) cs bs facts acc 0
  let (_, acc) ← runCycleTimed (codaPasses (p := p) b) cs bs facts acc
  let t1 ← IO.monoMsNow
  IO.println s!"profile {fileName}: {iters} cleanup iterations, {t1 - t0} ms total"
  let sorted := acc.toList.toArray.qsort (fun a b => a.2 > b.2)
  for (name, ms) in sorted do
    IO.println s!"  {name}: {ms} ms"

/-- `profile [vm] <file>`: per-pass optimizer timing for the selected VM. -/
def cmdProfile (vm fileName : String) : IO Unit := do
  if isSp1 vm then
    let (cs, busMap) ← parseFileWith parseSp1 fileName
    profileRun ApcOptimizer.SP1.defaultDegreeBound fileName cs
      (ApcOptimizer.SP1.sp1BusSemantics ApcOptimizer.SP1.koalaBear busMap)
      (ApcOptimizer.SP1.sp1Facts ApcOptimizer.SP1.koalaBear busMap)
  else
    let (cs, busMap) ← parseFileWith parseOpenVm fileName
    profileRun defaultDegreeBound fileName cs
      (openVmBusSemantics babyBear busMap) (openVmFacts babyBear busMap)

def usage : String :=
  "usage: apc-optimizer run [vm] <file.json[.gz]>\n" ++
  "       apc-optimizer profile [vm] <file.json[.gz]>  (per-pass optimizer timing)\n" ++
  "       apc-optimizer powdr [vm] <unopt.json[.gz]> <opt.json[.gz]>\n" ++
  "       apc-optimizer compare [vm] <unopt.json[.gz]> <opt.json[.gz]>\n" ++
  "       apc-optimizer report  [vm] <unopt.json[.gz]> <opt.json[.gz]>  (JSON: stats + render x3)\n" ++
  "       apc-optimizer opt-export [vm] <in.json[.gz]> <out.json>  (optimize and write the result\n" ++
  "                                as {machine, bus_map} JSON, readable by powdr/compare)\n\n" ++
  "[vm] is an optional `openvm` (default, BabyBear) or `sp1` (KoalaBear) token.\n" ++
  "Files are powdr SymbolicMachine exports (ApcWithBusMap), e.g. Benchmarks/OpenVM/openvm-eth/*.json.gz.\n" ++
  "The optimizer runs its cleanup loop to a fixpoint (provably terminating); there is no\n" ++
  "iteration count to set."

/-- The recognized VM selector tokens. Consumed as an optional leading argument on the commands
    that run the optimizer; anything else is treated as a filename and the VM defaults to OpenVM. -/
def isVmToken (s : String) : Bool := s == "openvm" || s == "sp1"

def main (args : List String) : IO Unit := do
  -- Peel an optional leading VM token off the command's arguments (default: openvm).
  let (vm, rest) := match args with
    | cmd :: tok :: more => if isVmToken tok then (tok, cmd :: more) else ("openvm", args)
    | _ => ("openvm", args)
  match rest with
  | ["run", fileName] => cmdRun vm fileName
  | ["profile", fileName] => cmdProfile vm fileName
  | ["vars", fileName] => cmdVars vm fileName
  | ["render", fileName] => cmdRender vm fileName
  | ["powdr", unoptFile, optFile] => cmdPowdr vm unoptFile optFile
  | ["report", unoptFile, optFile] => cmdReport vm unoptFile optFile
  | ["opt-export", inFile, outFile] => cmdOptExport vm inFile outFile
  | ["compare", unoptFile, optFile] => cmdCompare vm unoptFile optFile
  | _ =>
    IO.eprintln usage
    IO.Process.exit 1
