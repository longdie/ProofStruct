import ProofStruct.Extract.Graph
import ProofStruct.Extract.InfoPass
import ProofStruct.Extract.Json
import ProofStruct.Extract.SyntaxPass

namespace ProofStruct

structure CliArgs where
  file? : Option String := none
  theorem? : Option String := none
  output? : Option String := none
  help : Bool := false
deriving Repr

private partial def parseArgsAux : List String → CliArgs → CliArgs
  | [], cfg => cfg
  | "--" :: rest, cfg => parseArgsAux rest cfg
  | "--help" :: rest, cfg => parseArgsAux rest { cfg with help := true }
  | "-h" :: rest, cfg => parseArgsAux rest { cfg with help := true }
  | "--file" :: value :: rest, cfg => parseArgsAux rest { cfg with file? := some value }
  | "--theorem" :: value :: rest, cfg => parseArgsAux rest { cfg with theorem? := some value }
  | "--output" :: value :: rest, cfg => parseArgsAux rest { cfg with output? := some value }
  | _ :: rest, cfg => parseArgsAux rest cfg

private def parseArgs (args : List String) : CliArgs :=
  parseArgsAux args {}

private def usage : String :=
  "Usage:\n" ++
  "  lake exe @ProofStruct/extract_blueprint -- --file <lean-file> --theorem <name> [--output <json-file>]\n\n" ++
  "Example:\n" ++
  "  lake exe @ProofStruct/extract_blueprint -- --file examples/example.lean \\\n" ++
  "    --theorem fermat_little_theorem_1 \\\n" ++
  "    --output output/example/fermat_little_theorem_1/formal.evidence.json\n"

private def writeFileWithParents (path content : String) : IO Unit := do
  match (System.FilePath.mk path).parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  IO.FS.writeFile path content

private def runSemanticExtractor
    (sourceFile theoremName source : String) : IO (Except String String) := do
  match ← extractBlueprintSemanticPrimary sourceFile source theoremName with
  | .error err =>
      pure (.error s!"semantic extractor failed: {err}")
  | .ok bp =>
      pure (.ok (blueprintToJson bp))

private def runExtract (cfg : CliArgs) : IO UInt32 := do
  match cfg.file?, cfg.theorem? with
  | some file, some theoremName =>
      let source ← IO.FS.readFile file
      let json ←
        match ← runSemanticExtractor file theoremName source with
        | Except.ok json => pure json
        | Except.error semanticErr =>
            match extractBlueprintFromSource file source theoremName with
            | Except.ok bp =>
                IO.eprintln s!"warning: semantic-primary extraction skipped; using source_syntax_mvp fallback:\n{semanticErr}"
                pure (blueprintToJson bp)
            | Except.error syntaxErr =>
                IO.eprintln s!"error: semantic-primary extraction failed:\n{semanticErr}\nsource_syntax_mvp fallback also failed:\n{syntaxErr}"
                return 1
      match cfg.output? with
      | some output =>
          writeFileWithParents output json
          IO.println s!"wrote {output}"
      | none =>
          IO.print json
      return 0
  | _, _ =>
      IO.eprintln usage
      return 1

end ProofStruct

def main (args : List String) : IO UInt32 := do
  let cfg := ProofStruct.parseArgs args
  if cfg.help then
    IO.println ProofStruct.usage
    return 0
  else
    ProofStruct.runExtract cfg
