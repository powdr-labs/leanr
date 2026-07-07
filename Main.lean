import Leanr.Implementation.JsonParser
import Leanr.Optimizer
import Leanr.Utils.Size
import Leanr.Utils.Dsl
import Leanr.OpenVmSemantics

/-!
# The leanr CLI

Benchmark harness for the optimizer on powdr `SymbolicMachine` exports
(`OpenVmBenchmark/data/*.json.gz`, or any file in the same format — see `Leanr/Implementation/JsonParser.lean`):

- `leanr run [--iters N] <file.json[.gz]>` — parse, run the leanr optimizer with the file's
  own bus map, report sizes and effectiveness.
- `leanr powdr <unopt.json[.gz]> <opt.json[.gz]>` — report powdr's effectiveness from its
  serialized optimizer output (no leanr optimizer run).
- `leanr compare [--iters N] <unopt.json[.gz]> <opt.json[.gz]>` — both, side by side.
-/

open Leanr.OpenVM

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
    interactions, then algebraic constraints (the `Leanr/Utils/Size.lean` metrics). -/
def printEffectiveness (label : String) (before after : Stats) : IO Unit := do
  IO.println s!"{label} effectiveness (before → after):"
  printRatio (label := "variables       ") (before := before.vars) (after := after.vars)
  printRatio (label := "bus interactions") (before := before.busInteractions)
    (after := after.busInteractions)
  printRatio (label := "constraints     ") (before := before.constraints) (after := after.constraints)

def cmdRun (fileName : String) (iters : Nat) : IO Unit := do
  let (cs, busMap) ← parseFile fileName
  IO.println s!"Parsed {cs.algebraicConstraints.length} constraints, \
    {cs.busInteractions.length} bus interactions, {busMap.length} bus types"
  let before := statsOf cs
  let t0 ← IO.monoMsNow
  -- IO.lazyPure sequences the pure optimizer run between the clock reads (the compiler is
  -- free to float a plain `let` across IO actions, which breaks the measurement).
  let optimized ← IO.lazyPure (fun _ => openVmOptimizer busMap.toBusMap iters cs)
  let after ← IO.lazyPure (fun _ => statsOf optimized)
  let t1 ← IO.monoMsNow
  printStats (label := "before") (stats := before)
  printStats (label := "leanr ") (stats := after)
  printEffectiveness (label := "leanr") (before := before) (after := after)
  let bound := (openVmBusSemantics babyBear busMap.toBusMap).degreeBound
  IO.println s!"  degree bound (identities {bound.identities}, bus {bound.busInteractions}): \
    input {if cs.withinDegreeB bound then "ok" else "EXCEEDED"}, \
    output {if optimized.withinDegreeB bound then "ok" else "EXCEEDED"}"
  IO.println s!"  ({iters} iters, {t1 - t0} ms)"

/-- Like `cmdRun`, but also dump the distinct variables remaining after optimization (for
    diagnosing which variable classes the optimizer misses). -/
def cmdVars (fileName : String) (iters : Nat) : IO Unit := do
  let (cs, busMap) ← parseFile fileName
  let optimized ← IO.lazyPure (fun _ => openVmOptimizer busMap.toBusMap iters cs)
  let occurrences := optimized.algebraicConstraints.flatMap Expression.vars ++
    optimized.busInteractions.flatMap BusInteraction.vars
  let distinct := (occurrences.foldl (init := (∅ : Std.HashSet Variable)) (·.insert ·)).toList
  for v in (distinct.map (fun x => x.name)).mergeSort (fun a b => decide (a ≤ b)) do
    IO.println v

/-- Render the optimized system (for diagnosing residual constraints/interactions). -/
def cmdRender (fileName : String) (iters : Nat) : IO Unit := do
  let (cs, busMap) ← parseFile fileName
  let optimized ← IO.lazyPure (fun _ => openVmOptimizer busMap.toBusMap iters cs)
  IO.println (Leanr.Spec.Dsl.render optimized)

def cmdPowdr (unoptFile : String) (optFile : String) : IO Unit := do
  let (csBefore, _) ← parseFile unoptFile
  let (csAfter, _) ← parseFile optFile
  let before := statsOf csBefore
  let after := statsOf csAfter
  printStats (label := "before") (stats := before)
  printStats (label := "powdr ") (stats := after)
  printEffectiveness (label := "powdr") (before := before) (after := after)

def cmdCompare (unoptFile : String) (optFile : String) (iters : Nat) : IO Unit := do
  cmdRun (fileName := unoptFile) (iters := iters)
  let (csBefore, _) ← parseFile unoptFile
  let (csAfter, _) ← parseFile optFile
  printStats (label := "powdr ") (stats := statsOf csAfter)
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
    ",\"render\":\"" ++ jsonEscape (Leanr.Spec.Dsl.render cs) ++ "\"}"

/-- `report <unopt> <opt>`: emit one JSON object with the original, powdr-optimized and
    leanr-optimized circuits (each: vars/constraints/bus + DSL render). Consumed by the
    benchmark HTML report (`OpenVmBenchmark/benchmark.py --report`). -/
def cmdReport (unoptFile optFile : String) (iters : Nat) : IO Unit := do
  let (cs, busMap) ← parseFile unoptFile
  let (csPowdr, _) ← parseFile optFile
  let optimized := openVmOptimizer busMap.toBusMap iters cs
  IO.println ("{\"original\":" ++ circuitJson cs ++
    ",\"powdr\":" ++ circuitJson csPowdr ++
    ",\"leanr\":" ++ circuitJson optimized ++ "}")

def usage : String :=
  "usage: leanr run [--iters N] <file.json[.gz]>\n" ++
  "       leanr powdr <unopt.json[.gz]> <opt.json[.gz]>\n" ++
  "       leanr compare [--iters N] <unopt.json[.gz]> <opt.json[.gz]>\n" ++
  "       leanr report  [--iters N] <unopt.json[.gz]> <opt.json[.gz]>  (JSON: stats + render x3)\n\n" ++
  "Files are powdr SymbolicMachine exports (ApcWithBusMap), e.g. OpenVmBenchmark/data/*.json.gz.\n" ++
  "--iters bounds the optimizer's cleanup cycles (default 32)."

/-- Extract a `--iters N` flag (anywhere in the argument list). -/
def splitIters : List String → Except String (Option Nat × List String)
  | [] => .ok (none, [])
  | "--iters" :: [] => .error "--iters expects a number"
  | "--iters" :: n :: rest =>
    match n.toNat? with
    | some k => do
      let (_, others) ← splitIters rest
      .ok (some k, others)
    | none => .error s!"--iters expects a number, got {n}"
  | arg :: rest => do
    let (k, others) ← splitIters rest
    .ok (k, arg :: others)

def main (args : List String) : IO Unit := do
  match splitIters args with
  | .error err =>
    IO.eprintln s!"Error: {err}"
    IO.Process.exit 1
  | .ok (itersOpt, positional) =>
    let iters := itersOpt.getD 32
    match positional with
    | ["run", fileName] => cmdRun (fileName := fileName) (iters := iters)
    | ["vars", fileName] => cmdVars (fileName := fileName) (iters := iters)
    | ["render", fileName] => cmdRender (fileName := fileName) (iters := iters)
    | ["powdr", unoptFile, optFile] => cmdPowdr (unoptFile := unoptFile) (optFile := optFile)
    | ["report", unoptFile, optFile] =>
      cmdReport (unoptFile := unoptFile) (optFile := optFile) (iters := iters)
    | ["compare", unoptFile, optFile] =>
      cmdCompare (unoptFile := unoptFile) (optFile := optFile) (iters := iters)
    | _ =>
      IO.eprintln usage
      IO.Process.exit 1
