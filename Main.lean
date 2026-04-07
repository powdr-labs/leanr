import Leanr
import Leanr.StringParser
import Leanr.JsonParser
import Leanr.Solver

def main (args: List String) : IO Unit := do
  let p := 0x1dffff
  match args with
  | [] =>
    let stdin ← IO.getStdin
    let input ← stdin.readToEnd
    match parseSystem (p := p) input with
    | .error err => IO.eprintln s!"Error: {err}"; IO.Process.exit 1
    | .ok system =>
      let result ← solve system (log := true)
      IO.println s!"{result}"
  | (fileName :: _) =>
    if fileName.endsWith ".json.gz" then
      let result ← IO.Process.output { cmd := "gunzip", args := #["-c", fileName] }
      if result.exitCode ≠ 0 then
        IO.eprintln s!"Error: gunzip failed: {result.stderr}"
        IO.Process.exit 1
      match parseJsonSystem (p := p) result.stdout with
      | .error err => IO.eprintln s!"Error: {err}"; IO.Process.exit 1
      | .ok (system, busMap) =>
        IO.println s!"{busMap}"
        let result ← solve system (log := true)
        IO.println s!"{result}"
    else if fileName.endsWith ".json" then
      let input ← IO.FS.readFile fileName
      match parseJsonSystem (p := p) input with
      | .error err => IO.eprintln s!"Error: {err}"; IO.Process.exit 1
      | .ok (system, busMap) =>
        IO.println s!"{busMap}"
        let result ← solve system (log := true)
        IO.println s!"{result}"
    else
      let input ← IO.FS.readFile fileName
      match parseSystem (p := p) input with
      | .error err => IO.eprintln s!"Error: {err}"; IO.Process.exit 1
      | .ok system =>
        let result ← solve system (log := true)
        IO.println s!"{result}"
