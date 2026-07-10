import ApcOptimizer.Implementation.JsonParser
import ApcOptimizer.Optimizer
import ApcOptimizer.Implementation.Optimizer
import ApcOptimizer.Utils.Size
import ApcOptimizer.Utils.Dsl
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Ffi

/-!
# The apc-optimizer CLI

Benchmark harness for the optimizer on powdr `SymbolicMachine` exports
(`OpenVmBenchmarks/openvm-eth/*.json.gz`, or any file in the same format — see `ApcOptimizer/Implementation/JsonParser.lean`):

- `apc-optimizer run <file.json[.gz]>` — parse, run the apc-optimizer with the file's
  own bus map, report sizes and effectiveness.
- `apc-optimizer powdr <unopt.json[.gz]> <opt.json[.gz]>` — report powdr's effectiveness from its
  serialized optimizer output (no apc-optimizer run).
- `apc-optimizer compare <unopt.json[.gz]> <opt.json[.gz]>` — both, side by side.

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

/-- Parse a benchmark file into a constraint system over BabyBear plus its bus map.
    Rejects systems with bus ids missing from the map: an unmapped bus would be modeled as a
    no-op bus (stateless, never violating), silently licensing unsound optimizations. -/
def parseFile (fileName : String) : IO (ConstraintSystem babyBear × BusMapList) := do
  let contents ← readInput fileName
  match parseJsonSystem (p := babyBear) contents with
  | .error err =>
    IO.eprintln s!"Error parsing {fileName}: {err}"
    IO.Process.exit 1
  | .ok (system, busMap) =>
    let unmapped :=
      ((system.busInteractions.map (·.busId)).eraseDups).filter
        (fun busId => (busMap.toBusMap busId).isNone)
    unless unmapped.isEmpty do
      IO.eprintln s!"Error: {fileName} uses bus ids {unmapped} that are not in its bus_map"
      IO.Process.exit 1
    pure (system, busMap)

/-- Size measures of a constraint system, as reported by the CLI. -/
structure Stats where
  vars : Nat
  constraints : Nat
  busInteractions : Nat

/-- Same count as `ConstraintSystem.size` (distinct variables), but via a hash set —
    `List.dedup` is quadratic and benchmark machines have ~10⁵ variable occurrences. -/
def distinctVarCount (cs : ConstraintSystem babyBear) : Nat :=
  let occurrences := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars
  (occurrences.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).size

/-- The distinct variable names of a constraint system, sorted and rendered for display.
    Variables may carry structured powdr IDs internally, but reports show only `Variable.name`. -/
def distinctVars (cs : ConstraintSystem babyBear) : List String :=
  let occurrences := cs.algebraicConstraints.flatMap Expression.vars ++
    cs.busInteractions.flatMap BusInteraction.vars
  ((occurrences.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList.map
    (fun x => x.name)).mergeSort (fun a b => decide (a ≤ b))

def statsOf (cs : ConstraintSystem babyBear) : Stats :=
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

def cmdRun (fileName : String) : IO Unit := do
  let (cs, busMap) ← parseFile fileName
  IO.println s!"Parsed {cs.algebraicConstraints.length} constraints, \
    {cs.busInteractions.length} bus interactions, {busMap.length} bus types"
  let before := statsOf cs
  let t0 ← IO.monoMsNow
  -- IO.lazyPure sequences the pure optimizer run between the clock reads (the compiler is
  -- free to float a plain `let` across IO actions, which breaks the measurement).
  let optimized ← IO.lazyPure (fun _ => (openVmOptimizer busMap.toBusMap cs).1)
  let after ← IO.lazyPure (fun _ => statsOf optimized)
  let t1 ← IO.monoMsNow
  printStats (label := "before       ") (stats := before)
  printStats (label := "apc-optimizer") (stats := after)
  printEffectiveness (label := "apc-optimizer") (before := before) (after := after)
  let bound := (openVmBusSemantics babyBear busMap.toBusMap).degreeBound
  IO.println s!"  degree bound (identities {bound.identities}, bus {bound.busInteractions}): \
    input {if cs.withinDegreeB bound then "ok" else "EXCEEDED"}, \
    output {if optimized.withinDegreeB bound then "ok" else "EXCEEDED"}"
  IO.println s!"  ({t1 - t0} ms)"

/-- Like `cmdRun`, but also dump the distinct variables remaining after optimization (for
    diagnosing which variable classes the optimizer misses). -/
def cmdVars (fileName : String) : IO Unit := do
  let (cs, busMap) ← parseFile fileName
  let optimized ← IO.lazyPure (fun _ => (openVmOptimizer busMap.toBusMap cs).1)
  let occurrences := optimized.algebraicConstraints.flatMap Expression.vars ++
    optimized.busInteractions.flatMap BusInteraction.vars
  let distinct := (occurrences.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList
  for v in (distinct.map (fun x => x.name)).mergeSort (fun a b => decide (a ≤ b)) do
    IO.println v

/-- Render the optimized system (for diagnosing residual constraints/interactions). -/
def cmdRender (fileName : String) : IO Unit := do
  let (cs, busMap) ← parseFile fileName
  let optimized ← IO.lazyPure (fun _ => (openVmOptimizer busMap.toBusMap cs).1)
  IO.println (ApcOptimizer.Spec.Dsl.render optimized)

/-- `opt-export <in> <out.json>`: run the optimizer and write the optimized machine back out as
    `{"machine", "bus_map"}` JSON — the same shape `parseFile` reads, so the export can be fed to
    `powdr`/`compare` like a `.powdr_opt` file. The `bus_map` is spliced through verbatim from the
    input; the machine comes from the FFI serializer (`serializeSystem`, including
    `derived_columns` for optimizer-introduced witness columns). -/
def cmdOptExport (inFile outFile : String) : IO Unit := do
  let (cs, busMap) ← parseFile inFile
  let rawJson ← readInput inFile
  let busMapJson ← do
    match Lean.Json.parse rawJson >>= (·.getObjVal? "bus_map") with
    | .error err =>
      IO.eprintln s!"Error: cannot extract bus_map from {inFile}: {err}"
      IO.Process.exit 1
    | .ok j => pure j
  let (optimized, ds) ← IO.lazyPure (fun _ => openVmOptimizer busMap.toBusMap cs)
  let machineStr ← IO.lazyPure (fun _ => ApcOptimizer.Serialize.serializeSystem optimized ds)
  let machineJson ← do
    match Lean.Json.parse machineStr with
    | .error err =>
      IO.eprintln s!"Error: serializer produced invalid JSON: {err}"
      IO.Process.exit 1
    | .ok j => pure j
  IO.FS.writeFile outFile
    (Lean.Json.mkObj [("machine", machineJson), ("bus_map", busMapJson)]).compress

def cmdPowdr (unoptFile : String) (optFile : String) : IO Unit := do
  let (csBefore, _) ← parseFile unoptFile
  let (csAfter, _) ← parseFile optFile
  let before := statsOf csBefore
  let after := statsOf csAfter
  printStats (label := "before       ") (stats := before)
  printStats (label := "powdr        ") (stats := after)
  printEffectiveness (label := "powdr") (before := before) (after := after)

def cmdCompare (unoptFile : String) (optFile : String) : IO Unit := do
  cmdRun (fileName := unoptFile)
  let (csBefore, _) ← parseFile unoptFile
  let (csAfter, _) ← parseFile optFile
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
def circuitJson (cs : ConstraintSystem babyBear) : String :=
  let st := statsOf cs
  let vs := String.intercalate "," ((distinctVars cs).map (fun s => "\"" ++ jsonEscape s ++ "\""))
  "{\"vars\":" ++ toString st.vars ++
    ",\"constraints\":" ++ toString st.constraints ++
    ",\"bus\":" ++ toString st.busInteractions ++
    ",\"vars_list\":[" ++ vs ++ "]" ++
    ",\"render\":\"" ++ jsonEscape (ApcOptimizer.Spec.Dsl.render cs) ++ "\"}"

/-- `report <unopt> <opt>`: emit one JSON object with the original, powdr-optimized and
    apc-optimizer-optimized circuits (each: vars/constraints/bus + DSL render). Consumed by the
    benchmark HTML report (`OpenVmBenchmarks/benchmark.py --report`). -/
def cmdReport (unoptFile optFile : String) : IO Unit := do
  let (cs, busMap) ← parseFile unoptFile
  let (csPowdr, _) ← parseFile optFile
  let optimized := (openVmOptimizer busMap.toBusMap cs).1
  IO.println ("{\"original\":" ++ circuitJson cs ++
    ",\"powdr\":" ++ circuitJson csPowdr ++
    ",\"apc-optimizer\":" ++ circuitJson optimized ++ "}")

open ApcOptimizer.OpenVM in
/-- Profiling helper: apply one fact-aware pass, forcing full evaluation, and return the new
    system plus the elapsed milliseconds. -/
def applyTimed (pass : VerifiedPassW babyBear) (cs : ConstraintSystem babyBear)
    (bs : BusSemantics babyBear) (facts : BusFacts babyBear bs) :
    IO (ConstraintSystem babyBear × Nat) := do
  let t0 ← IO.monoMsNow
  let out ← IO.lazyPure (fun _ => (pass cs bs facts).out)
  -- Force the whole output structure (varCount traverses every expression node).
  let _ ← IO.lazyPure (fun _ =>
    out.varCount + out.algebraicConstraints.length + out.busInteractions.length)
  let t1 ← IO.monoMsNow
  pure (out, t1 - t0)

open ApcOptimizer.OpenVM in
/-- Run one cleanup cycle's passes in order, accumulating per-pass elapsed time. -/
partial def runCycleTimed (passes : List (String × VerifiedPassW babyBear))
    (cs : ConstraintSystem babyBear) (bs : BusSemantics babyBear) (facts : BusFacts babyBear bs)
    (acc : Std.HashMap String Nat) : IO (ConstraintSystem babyBear × Std.HashMap String Nat) := do
  let mut c := cs
  let mut a := acc
  for (name, pass) in passes do
    let (c', dt) ← applyTimed pass c bs facts
    c := c'
    a := a.insert name (a.getD name 0 + dt)
  pure (c, a)

open ApcOptimizer.OpenVM in
/-- Iterate the cleanup cycle to a fixpoint (mirroring `iterateToFixpoint`), accumulating per-pass
    time and counting iterations. -/
partial def profileLoop (passes : List (String × VerifiedPassW babyBear))
    (cs : ConstraintSystem babyBear) (bs : BusSemantics babyBear) (facts : BusFacts babyBear bs)
    (acc : Std.HashMap String Nat) (iter : Nat) :
    IO (ConstraintSystem babyBear × Std.HashMap String Nat × Nat) := do
  let (cs', acc') ← runCycleTimed passes cs bs facts acc
  if cs'.sizeKey < cs.sizeKey then
    profileLoop passes cs' bs facts acc' (iter + 1)
  else
    pure (cs, acc', iter)

open ApcOptimizer.OpenVM in
/-- `profile <file>`: run the OpenVM pipeline with per-pass timing, reporting the cumulative time
    spent in each pass across all fixpoint iterations. -/
def cmdProfile (fileName : String) : IO Unit := do
  let (cs, busMap) ← parseFile fileName
  let bs := openVmBusSemantics babyBear busMap.toBusMap
  let facts := openVmFacts babyBear busMap.toBusMap
  let cleanupPasses : List (String × VerifiedPassW babyBear) :=
    [ ("carryBranch", carryBranchPass.guardDegree),
      ("gauss", gaussElimPass.withFacts.guardDegree),
      ("normalize1", normalizePass.withFacts.guardDegree),
      ("constFold1", constantFoldPass.withFacts.guardDegree),
      ("domainBatch", domainBatchPass.guardDegree),
      ("normalize2", normalizePass.withFacts.guardDegree),
      ("constFold2", constantFoldPass.withFacts.guardDegree),
      ("zeroRegister", zeroRegisterPass.guardDegree),
      ("hintCollapse", hintCollapsePass.guardDegree),
      ("rootPairUnify", rootPairUnifyPass.guardDegree),
      ("flagUnify", flagUnifyPass.guardDegree),
      ("dedup", dedupPass.withFacts.guardDegree),
      ("trivialConstr", trivialConstraintDropPass.withFacts.guardDegree),
      ("zeroMultBus", zeroMultBusDropPass.withFacts.guardDegree),
      ("tautoBus", tautoBusDropPass.withFacts.guardDegree),
      ("domainFold", domainFoldPass.withFacts.guardDegree),
      ("busUnify", busUnifyPass.guardDegree),
      ("busPairCancel", VerifiedPassW.guardDegree (iterateToFixpoint busPairCancelPass)),
      ("bytePack", VerifiedPassW.guardDegree (iterateToFixpoint bytePackPass)),
      ("disconnected", disconnectedComponentPass.withFacts.guardDegree),
      ("reencode", reencodePass.withFacts.guardDegree) ]
  let t0 ← IO.monoMsNow
  -- pipeline prelude: constantFold
  let (cs, acc) ← runCycleTimed [("constFold0", constantFoldPass.withFacts.guardDegree)] cs bs facts ∅
  let (cs, acc, iters) ← profileLoop cleanupPasses cs bs facts acc 0
  -- pipeline coda: monicScale, constantFold
  let (_, acc) ← runCycleTimed
    [("monicScale", monicScalePass.withFacts.guardDegree),
     ("constFoldEnd", constantFoldPass.withFacts.guardDegree)] cs bs facts acc
  let t1 ← IO.monoMsNow
  IO.println s!"profile {fileName}: {iters} cleanup iterations, {t1 - t0} ms total"
  let sorted := acc.toList.toArray.qsort (fun a b => a.2 > b.2)
  for (name, ms) in sorted do
    IO.println s!"  {name}: {ms} ms"

def usage : String :=
  "usage: apc-optimizer run <file.json[.gz]>\n" ++
  "       apc-optimizer profile <file.json[.gz]>  (per-pass optimizer timing)\n" ++
  "       apc-optimizer powdr <unopt.json[.gz]> <opt.json[.gz]>\n" ++
  "       apc-optimizer compare <unopt.json[.gz]> <opt.json[.gz]>\n" ++
  "       apc-optimizer report  <unopt.json[.gz]> <opt.json[.gz]>  (JSON: stats + render x3)\n" ++
  "       apc-optimizer opt-export <in.json[.gz]> <out.json>  (optimize and write the result\n" ++
  "                                as {machine, bus_map} JSON, readable by powdr/compare)\n\n" ++
  "Files are powdr SymbolicMachine exports (ApcWithBusMap), e.g. OpenVmBenchmarks/openvm-eth/*.json.gz.\n" ++
  "The optimizer runs its cleanup loop to a fixpoint (provably terminating); there is no\n" ++
  "iteration count to set."

def main (args : List String) : IO Unit := do
  match args with
  | ["run", fileName] => cmdRun (fileName := fileName)
  | ["profile", fileName] => cmdProfile (fileName := fileName)
  | ["vars", fileName] => cmdVars (fileName := fileName)
  | ["render", fileName] => cmdRender (fileName := fileName)
  | ["powdr", unoptFile, optFile] => cmdPowdr (unoptFile := unoptFile) (optFile := optFile)
  | ["report", unoptFile, optFile] =>
    cmdReport (unoptFile := unoptFile) (optFile := optFile)
  | ["opt-export", inFile, outFile] =>
    cmdOptExport (inFile := inFile) (outFile := outFile)
  | ["compare", unoptFile, optFile] =>
    cmdCompare (unoptFile := unoptFile) (optFile := optFile)
  | _ =>
    IO.eprintln usage
    IO.Process.exit 1
