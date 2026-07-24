import VersoManual
import Docs

open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no

def main (args : List String) : IO UInt32 :=
  manualMain (%doc Docs) (options := args) (config := config)
