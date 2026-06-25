import ProofStruct.Extract.Graph
import ProofStruct.Extract.InfoPass
import ProofStruct.Extract.Json
import ProofStruct.Extract.Layered
import ProofStruct.Extract.SyntaxPass

namespace ProofStruct

structure LayeredCliArgs where
  file? : Option String := none
  theorem? : Option String := none
  output? : Option String := none
  blueprintOutput? : Option String := none
  help : Bool := false
deriving Repr

private partial def parseArgsAux : List String → LayeredCliArgs → LayeredCliArgs
  | [], cfg => cfg
  | "--" :: rest, cfg => parseArgsAux rest cfg
  | "--help" :: rest, cfg => parseArgsAux rest { cfg with help := true }
  | "-h" :: rest, cfg => parseArgsAux rest { cfg with help := true }
  | "--file" :: value :: rest, cfg => parseArgsAux rest { cfg with file? := some value }
  | "--theorem" :: value :: rest, cfg => parseArgsAux rest { cfg with theorem? := some value }
  | "--output" :: value :: rest, cfg => parseArgsAux rest { cfg with output? := some value }
  | "--blueprint-output" :: value :: rest, cfg => parseArgsAux rest { cfg with blueprintOutput? := some value }
  | _ :: rest, cfg => parseArgsAux rest cfg

private def parseArgs (args : List String) : LayeredCliArgs :=
  parseArgsAux args {}

private def usage : String :=
  "Usage:\n" ++
  "  lake exe @ProofStruct/extract_layered_blueprint -- --file <lean-file> --theorem <name> \\\n" ++
  "    --output <layered-json-file> [--blueprint-output <evidence-json-file>]\n\n" ++
  "Example:\n" ++
  "  lake exe @ProofStruct/extract_layered_blueprint -- --file examples/example.lean \\\n" ++
  "    --theorem fermat_little_theorem_1 \\\n" ++
  "    --output output/example/fermat_little_theorem_1/formal.layered.json \\\n" ++
  "    --blueprint-output output/example/fermat_little_theorem_1/formal.evidence.json\n"

private def writeFileWithParents (path content : String) : IO Unit := do
  match (System.FilePath.mk path).parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  IO.FS.writeFile path content

private def runSemanticLayeredExtractor
    (sourceFile theoremName layeredOutputFile blueprintOutputFile source : String) :
    IO (Except String Unit) := do
  match ← extractBlueprintSemanticPrimary sourceFile source theoremName with
  | .error err =>
      pure (.error s!"semantic layered extractor failed: {err}")
  | .ok bp =>
      writeFileWithParents layeredOutputFile (blueprintToLayeredJson bp)
      if blueprintOutputFile ≠ "" then
        writeFileWithParents blueprintOutputFile (blueprintToJson bp)
      pure (.ok ())

private def writeFallbackOutputs
    (sourceFile theoremName layeredOutputFile blueprintOutputFile source : String) :
    Except String (IO Unit) := do
  let bp ← extractBlueprintFromSource sourceFile source theoremName
  pure do
    writeFileWithParents layeredOutputFile (blueprintToLayeredJson bp)
    if blueprintOutputFile ≠ "" then
      writeFileWithParents blueprintOutputFile (blueprintToJson bp)

private def runExtract (cfg : LayeredCliArgs) : IO UInt32 := do
  match cfg.file?, cfg.theorem?, cfg.output? with
  | some file, some theoremName, some layeredOutputFile =>
      let source ← IO.FS.readFile file
      let blueprintOutputFile := cfg.blueprintOutput?.getD ""
      match ← runSemanticLayeredExtractor file theoremName layeredOutputFile blueprintOutputFile source with
      | Except.ok _ =>
          IO.println s!"wrote {layeredOutputFile}"
          if blueprintOutputFile ≠ "" then
            IO.println s!"wrote {blueprintOutputFile}"
          return 0
      | Except.error semanticErr =>
          match writeFallbackOutputs file theoremName layeredOutputFile blueprintOutputFile source with
          | Except.ok writeOutputs =>
              IO.eprintln s!"warning: semantic-primary layered extraction skipped; using source_syntax_mvp fallback:\n{semanticErr}"
              writeOutputs
              IO.println s!"wrote {layeredOutputFile}"
              if blueprintOutputFile ≠ "" then
                IO.println s!"wrote {blueprintOutputFile}"
              return 0
          | Except.error syntaxErr =>
              IO.eprintln s!"error: semantic-primary layered extraction failed:\n{semanticErr}\nsource_syntax_mvp fallback also failed:\n{syntaxErr}"
              return 1
  | _, _, _ =>
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
