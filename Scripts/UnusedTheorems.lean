import ApcOptimizer
import Main

/-! CI helper: flag human-written theorems that no longer contribute to the audited correctness
    theorems in `ApcOptimizer/Optimizer.lean`.

    A theorem is "used" iff it is reachable, through proof terms and types, from the roots seeded in
    `Scripts/unused-theorems.txt` (the correctness statements), together with every `@[csimp]`
    theorem — those are referenced by the compiler, not by any proof term, so a term walk cannot see
    the use. Auto-generated declarations (structure projections, `injEq`, equation lemmas, …) are
    excluded: they carry no source range and are not something a human wrote.

    `Scripts/check-proof-integrity.sh` runs this from the repo root and fails CI if anything is
    flagged. To resolve a flag: delete the dead theorem, or — if it really is used through a channel
    the term walk cannot see (see the `[ignore]` section of the seed) — record it there. -/

open Lean Elab Command

namespace UnusedTheorems

def seedPath : System.FilePath := "Scripts/unused-theorems.txt"

structure Seed where
  roots : Array Name := #[]
  ignore : Std.HashSet Name := {}

-- `String.trim` (String → String) is deprecated in favour of a Slice-returning variant.
set_option linter.deprecated false in
/-- Parse the seed file: `#` comments, blank lines, and `[roots]` / `[ignore]` section headers. -/
def parseSeed (content : String) : Seed := Id.run do
  let mut seed : Seed := {}
  let mut sect := "roots"
  for rawLine in content.splitOn "\n" do
    let line := rawLine.trim
    if line.isEmpty || line.startsWith "#" then continue
    if line == "[roots]" then sect := "roots"; continue
    if line == "[ignore]" then sect := "ignore"; continue
    let n := line.toName
    if sect == "roots" then seed := { seed with roots := seed.roots.push n }
    else seed := { seed with ignore := seed.ignore.insert n }
  return seed

def isProjectModule (m : Name) : Bool :=
  let s := m.toString
  s == "Main" || "ApcOptimizer".isPrefixOf s

def projectModuleIdxs (env : Environment) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  for i in [0:env.header.moduleNames.size] do
    if isProjectModule env.header.moduleNames[i]! then s := s.insert i
  return s

def isProjectConst (env : Environment) (idxs : Std.HashSet Nat) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => idxs.contains i.toNat
  | none => false

/-- The defining term of a constant. `ConstantInfo.value?` omits theorem bodies in this Lean
    version, so read the field directly — the whole point is to walk into proofs. -/
def valueOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def refsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci => ci.type.getUsedConstants ++ ((valueOf ci).map Expr.getUsedConstants).getD #[]

/-- Reachable project constants from `roots`. Restricted to project constants: Mathlib and core
    never reference the project, so the boundary can be cut there without missing anything. -/
def closure (env : Environment) (idxs : Std.HashSet Nat) (roots : Array Name) :
    Std.HashSet Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut stack : Array Name := roots
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    for r in refsOf env n do
      if isProjectConst env idxs r && !visited.contains r then
        stack := stack.push r
  return visited

/-- `@[csimp]` theorems in project modules: compiler-referenced, hence implicit roots. -/
def csimpRoots (env : Environment) (idxs : Std.HashSet Nat) : Array Name :=
  (Lean.Compiler.CSimp.ext.getState env).map.fold
    (fun acc _ v => if isProjectConst env idxs v.thmName then acc.push v.thmName else acc) #[]

/-- Every human-written theorem in a project module: a `thmInfo` that is not internal, not a
    structure projection, and carries a source declaration range. -/
def deadTheorems (env : Environment) (idxs : Std.HashSet Nat) (cl : Std.HashSet Name)
    (ignore : Std.HashSet Name) : CommandElabM (Array (Name × Name × Nat)) := do
  let mut out : Array (Name × Name × Nat) := #[]
  for i in idxs do
    for ci in env.header.moduleData[i]!.constants do
      match ci with
      | .thmInfo _ =>
        let n := ci.name
        if n.isInternalDetail || cl.contains n || ignore.contains n then continue
        if (env.getProjectionFnInfo? n).isSome then continue
        match ← Lean.findDeclarationRanges? n with
        | some dr => out := out.push (env.header.moduleNames[i]!, n, dr.range.pos.line)
        | none => pure ()
      | _ => pure ()
  return out

elab "#checkUnusedTheorems" : command => do
  let env ← getEnv
  let content ← IO.FS.readFile seedPath
  let seed := parseSeed content
  let idxs := projectModuleIdxs env
  let csimp := csimpRoots env idxs
  let cl := closure env idxs (seed.roots ++ csimp)
  let dead := (← deadTheorems env idxs cl seed.ignore).qsort
    (fun a b => if a.1 == b.1 then a.2.2 < b.2.2 else a.1.toString < b.1.toString)
  logInfo m!"checked {cl.size} reachable constants from {seed.roots.size} seeded roots \
    + {csimp.size} @[csimp] theorems; {seed.ignore.size} ignored"
  if dead.isEmpty then
    logInfo "OK: no unused theorems."
  else
    let mut msg := m!"found {dead.size} unused theorem(s) — not reachable from the roots in \
      {seedPath}. Delete them, or add to that file's [ignore] section if genuinely used:"
    for (m, n, line) in dead do
      let file := m.toString.replace "." "/" ++ ".lean"
      msg := msg ++ m!"\n  {file}:{line}  {n}"
    throwError msg

#checkUnusedTheorems

end UnusedTheorems
