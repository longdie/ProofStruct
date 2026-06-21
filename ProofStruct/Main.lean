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

private def semanticDriverScript
    (sourceFile theoremName outputFile source : String) : String :=
  let imports := sourceImportLines source
  let importsText :=
    if imports.isEmpty then "" else String.intercalate "\n" imports.toList ++ "\n"
  importsText ++
  "import ProofStruct.Extract.InfoPass\n" ++
  "import ProofStruct.Extract.Json\n" ++
  "import ProofStruct.Extract.SyntaxPass\n\n" ++
  "open ProofStruct\n\n" ++
  "#eval show IO Unit from do\n" ++
  s!"  let sourceFile := {jsonStr sourceFile}\n" ++
  s!"  let theoremName := {jsonStr theoremName}\n" ++
  s!"  let outputFile := {jsonStr outputFile}\n" ++
  "  let source ← IO.FS.readFile sourceFile\n" ++
  "  let bp ←\n" ++
  "    match ← extractBlueprintSemanticPrimary sourceFile source theoremName with\n" ++
  "    | Except.error err => throw <| IO.userError err\n" ++
  "    | Except.ok bp => pure bp\n" ++
  "  IO.FS.writeFile outputFile (blueprintToJson bp)\n"

private def removeFileIfExists (path : String) : IO Unit := do
  try
    IO.FS.removeFile path
  catch _ =>
    pure ()

private def runSemanticExtractor
    (sourceFile theoremName source : String) : IO (Except String String) := do
  let tmpDir := "/tmp/proofstruct"
  IO.FS.createDirAll tmpDir
  let stamp ← IO.monoNanosNow
  let safeName := sanitizeId theoremName
  let tmpScript := s!"{tmpDir}/semantic_{safeName}_{stamp}.lean"
  let tmpJson := s!"{tmpDir}/semantic_{safeName}_{stamp}.json"
  IO.FS.writeFile tmpScript (semanticDriverScript sourceFile theoremName tmpJson source)
  try
    let out ← IO.Process.output {
      cmd := "lake",
      args := #["env", "lean", tmpScript]
    }
    if out.exitCode == 0 then
      let json ← IO.FS.readFile tmpJson
      removeFileIfExists tmpScript
      removeFileIfExists tmpJson
      pure (.ok json)
    else
      removeFileIfExists tmpScript
      removeFileIfExists tmpJson
      pure (.error s!"semantic extractor failed with exit code {out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}")
  catch err =>
    removeFileIfExists tmpScript
    removeFileIfExists tmpJson
    pure (.error s!"semantic extractor failed: {err}")

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
          IO.FS.writeFile output json
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
