import ProofStruct.Extract.Graph
import ProofStruct.Extract.InfoPass
import ProofStruct.Extract.Json
import ProofStruct.Extract.Layered
import ProofStruct.Extract.SyntaxPass

namespace ProofStruct

structure FileEntrySpec where
  declName : String := ""
  output : String := ""
  blueprintOutput : String := ""
deriving Repr, Inhabited

structure FileCliArgs where
  file? : Option String := none
  entries : Array FileEntrySpec := #[]
  help : Bool := false
deriving Repr

private def updateLastEntry (cfg : FileCliArgs) (f : FileEntrySpec → FileEntrySpec) :
    FileCliArgs :=
  match cfg.entries.back? with
  | none => cfg
  | some entry => { cfg with entries := cfg.entries.pop.push (f entry) }

private partial def parseArgsAux : List String → FileCliArgs → FileCliArgs
  | [], cfg => cfg
  | "--" :: rest, cfg => parseArgsAux rest cfg
  | "--help" :: rest, cfg => parseArgsAux rest { cfg with help := true }
  | "-h" :: rest, cfg => parseArgsAux rest { cfg with help := true }
  | "--file" :: value :: rest, cfg => parseArgsAux rest { cfg with file? := some value }
  | "--theorem" :: value :: rest, cfg =>
      parseArgsAux rest { cfg with entries := cfg.entries.push { declName := value } }
  | "--output" :: value :: rest, cfg =>
      parseArgsAux rest (updateLastEntry cfg (fun entry => { entry with output := value }))
  | "--blueprint-output" :: value :: rest, cfg =>
      parseArgsAux rest (updateLastEntry cfg (fun entry => { entry with blueprintOutput := value }))
  | _ :: rest, cfg => parseArgsAux rest cfg

private def parseArgs (args : List String) : FileCliArgs :=
  parseArgsAux args {}

private def usage : String :=
  "Usage:\n" ++
  "  lake exe @ProofStruct/extract_file_blueprints -- --file <lean-file> \\\n" ++
  "    --theorem <name> --output <layered-json-file> [--blueprint-output <evidence-json-file>] \\\n" ++
  "    [--theorem <name> --output <layered-json-file> ...]\n\n" ++
  "Example:\n" ++
  "  lake exe @ProofStruct/extract_file_blueprints -- --file examples/example.lean \\\n" ++
  "    --theorem fermat_little_theorem_1 \\\n" ++
  "    --output output/example/fermat_little_theorem_1/formal.layered.json \\\n" ++
  "    --blueprint-output output/example/fermat_little_theorem_1/formal.evidence.json\n"

private def validateEntry (entry : FileEntrySpec) : Except String FileEntrySpec := do
  if entry.declName = "" then
    throw "entry is missing --theorem"
  if entry.output = "" then
    throw s!"entry for theorem '{entry.declName}' is missing --output"
  pure entry

private def validateEntries (entries : Array FileEntrySpec) :
    Except String (Array FileEntrySpec) := do
  if entries.isEmpty then
    throw "no theorem entries were provided"
  let mut out : Array FileEntrySpec := #[]
  for entry in entries do
    out := out.push (← validateEntry entry)
  pure out

private def writeFileWithParents (path content : String) : IO Unit := do
  match (System.FilePath.mk path).parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  IO.FS.writeFile path content

private def writeBlueprintOutputs (entry : FileEntrySpec) (bp : Blueprint) : IO Unit := do
  writeFileWithParents entry.output (blueprintToLayeredJson bp)
  IO.println s!"wrote {entry.output}"
  if entry.blueprintOutput ≠ "" then
    writeFileWithParents entry.blueprintOutput (blueprintToJson bp)
    IO.println s!"wrote {entry.blueprintOutput}"

private def resultFor? (theoremName : String)
    (results : Array (String × Except String Blueprint)) : Option (Except String Blueprint) :=
  match results.find? (fun item => item.fst == theoremName) with
  | some item => some item.snd
  | none => none

private def writeSyntaxFallback
    (sourceFile source : String) (entry : FileEntrySpec) (semanticErr : String) :
    IO Bool := do
  match extractBlueprintFromSource sourceFile source entry.declName with
  | Except.ok bp =>
      IO.eprintln s!"warning: semantic-primary extraction skipped for {entry.declName}; using source_syntax_mvp fallback:\n{semanticErr}"
      writeBlueprintOutputs entry bp
      pure true
  | Except.error syntaxErr =>
      IO.eprintln s!"error: semantic-primary extraction failed for {entry.declName}:\n{semanticErr}\nsource_syntax_mvp fallback also failed:\n{syntaxErr}"
      pure false

private def runWithSemanticResults
    (sourceFile source : String) (entries : Array FileEntrySpec)
    (results : Array (String × Except String Blueprint)) : IO UInt32 := do
  let mut ok := true
  for entry in entries do
    match resultFor? entry.declName results with
    | some (.ok bp) =>
        writeBlueprintOutputs entry bp
    | some (.error semanticErr) =>
        ok := (← writeSyntaxFallback sourceFile source entry semanticErr) && ok
    | none =>
        ok := (← writeSyntaxFallback sourceFile source entry "theorem was not returned by file-level semantic extractor") && ok
  if ok then pure 0 else pure 1

private def runWithSyntaxFallback
    (sourceFile source : String) (entries : Array FileEntrySpec) (semanticErr : String) :
    IO UInt32 := do
  let mut ok := true
  for entry in entries do
    ok := (← writeSyntaxFallback sourceFile source entry semanticErr) && ok
  if ok then pure 0 else pure 1

private def runExtract (cfg : FileCliArgs) : IO UInt32 := do
  match cfg.file?, validateEntries cfg.entries with
  | some file, .ok entries =>
      let source ← IO.FS.readFile file
      let theoremNames := entries.map (·.declName)
      match ← extractBlueprintsSemanticPrimary file source theoremNames with
      | .ok results => runWithSemanticResults file source entries results
      | .error semanticErr => runWithSyntaxFallback file source entries semanticErr
  | none, _ =>
      IO.eprintln usage
      return 1
  | _, .error err =>
      IO.eprintln s!"error: {err}\n\n{usage}"
      return 1

end ProofStruct

def main (args : List String) : IO UInt32 := do
  let cfg := ProofStruct.parseArgs args
  if cfg.help then
    IO.println ProofStruct.usage
    return 0
  else
    ProofStruct.runExtract cfg
