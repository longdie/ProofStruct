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

private def trim (s : String) : String :=
  s.trimAscii.toString

private def pushUniqueLine (items : Array String) (item : String) : Array String :=
  let item := trim item
  if item = "" || items.contains item then items else items.push item

private def sourceImportLines (source : String) : Array String :=
  (source.splitOn "\n").foldl
    (fun acc line =>
      let line := trim line
      if line.startsWith "import " then pushUniqueLine acc line else acc)
    #[]

private def semanticLayeredDriverScript
    (sourceFile theoremName layeredOutputFile blueprintOutputFile source : String) : String :=
  let imports := sourceImportLines source
  let importsText :=
    if imports.isEmpty then "" else String.intercalate "\n" imports.toList ++ "\n"
  importsText ++
  "import ProofStruct.Extract.InfoPass\n" ++
  "import ProofStruct.Extract.Json\n" ++
  "import ProofStruct.Extract.Layered\n" ++
  "import ProofStruct.Extract.SyntaxPass\n\n" ++
  "open ProofStruct\n\n" ++
  "#eval show IO Unit from do\n" ++
  s!"  let sourceFile := {jsonStr sourceFile}\n" ++
  s!"  let theoremName := {jsonStr theoremName}\n" ++
  s!"  let layeredOutputFile := {jsonStr layeredOutputFile}\n" ++
  s!"  let blueprintOutputFile := {jsonStr blueprintOutputFile}\n" ++
  "  let source ← IO.FS.readFile sourceFile\n" ++
  "  let bp ←\n" ++
  "    match ← extractBlueprintSemanticPrimary sourceFile source theoremName with\n" ++
  "    | Except.error err => throw <| IO.userError err\n" ++
  "    | Except.ok bp => pure bp\n" ++
  "  IO.FS.writeFile layeredOutputFile (blueprintToLayeredJson bp)\n" ++
  "  if blueprintOutputFile ≠ \"\" then\n" ++
  "    IO.FS.writeFile blueprintOutputFile (blueprintToJson bp)\n"

private def removeFileIfExists (path : String) : IO Unit := do
  try
    IO.FS.removeFile path
  catch _ =>
    pure ()

private def runSemanticLayeredExtractor
    (sourceFile theoremName layeredOutputFile blueprintOutputFile source : String) :
    IO (Except String Unit) := do
  let tmpDir := "/tmp/proofstruct"
  IO.FS.createDirAll tmpDir
  let stamp ← IO.monoNanosNow
  let safeName := sanitizeId theoremName
  let tmpScript := s!"{tmpDir}/semantic_layered_{safeName}_{stamp}.lean"
  IO.FS.writeFile tmpScript (semanticLayeredDriverScript sourceFile theoremName layeredOutputFile blueprintOutputFile source)
  try
    let out ← IO.Process.output {
      cmd := "lake",
      args := #["env", "lean", tmpScript]
    }
    removeFileIfExists tmpScript
    if out.exitCode == 0 then
      pure (.ok ())
    else
      pure (.error s!"semantic layered extractor failed with exit code {out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")
  catch err =>
    removeFileIfExists tmpScript
    pure (.error s!"semantic layered extractor failed: {err}")

private def writeFallbackOutputs
    (sourceFile theoremName layeredOutputFile blueprintOutputFile source : String) :
    Except String (IO Unit) := do
  let bp ← extractBlueprintFromSource sourceFile source theoremName
  pure do
    IO.FS.writeFile layeredOutputFile (blueprintToLayeredJson bp)
    if blueprintOutputFile ≠ "" then
      IO.FS.writeFile blueprintOutputFile (blueprintToJson bp)

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
