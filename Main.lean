import Leanr
import Leanr.StringParser
import Leanr.Solver

-- Get the file to read from the arguments. If the arguments are empty, read from standard input.
-- call parseSystem to get the system (or an erro) and then run solve on it. print the resulting system
def main (args: List String) : IO Unit := do
  let input ← match args with
    | [] => let stdin ← IO.getStdin; stdin.readToEnd
    | (fileName :: _) => IO.FS.readFile fileName
  let p := 0x1dffff
  match parseSystem (p := p) input with
  | Except.error err => IO.println s!"Error: {err}"
  | Except.ok system =>
    let solved := solve system
    IO.println s!"{solved}"
