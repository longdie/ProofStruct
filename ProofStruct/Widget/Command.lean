import Lean.Elab.Command
import ProofWidgets.Component.HtmlDisplay
import ProofStruct.Widget.BlueprintLayeredGraph
import ProofStruct.Widget.BlueprintJson
import ProofStruct.Widget.LayeredJson
import ProofStruct.Widget.RenderGraphDisplay
import ProofStruct.Widget.RenderLayeredDisplay

namespace ProofStruct

open Lean Elab Command
open ProofWidgets
open Lean Server

private def currentSourceFile : CommandElabM String := do
  liftCoreM getFileName

private def lastPathPart (path : String) : String :=
  let parts := (path.splitOn "/").toArray
  parts[parts.size - 1]?.getD path

private def dropLeanExtension (fileName : String) : String :=
  if fileName.endsWith ".lean" then
    (fileName.dropEnd 5).copy.trimAscii.toString
  else
    fileName

private def datasetNameFromSourceFile (sourceFile : String) : String :=
  dropLeanExtension (lastPathPart sourceFile)

private partial def findLakeRoot? (dir : System.FilePath) : IO (Option System.FilePath) := do
  if ← (dir / "lakefile.toml").pathExists then
    return some dir
  if ← (dir / "lakefile.lean").pathExists then
    return some dir
  match dir.parent with
  | some parent => findLakeRoot? parent
  | none => pure none

private def projectRootForSource (sourceFile : String) : IO System.FilePath := do
  let cwd ← IO.currentDir
  let sourcePath := System.FilePath.mk sourceFile
  let start := sourcePath.parent.getD cwd
  return (← findLakeRoot? start).getD cwd

private def safeComponent (text : String) : String :=
  let token := text.foldl
    (fun acc c =>
      if c.isAlphanum || c = '_' || c = '.' || c = '-' then
        acc.push c
      else
        acc.push '_')
    ""
  if token.isEmpty then "unnamed" else token

private def isDeclStart (line : String) : Bool :=
  let t := (line.trimAscii).copy
  t.startsWith "theorem " || t.startsWith "lemma " || t.startsWith "example "

private def isProofBlueprintLine (line : String) : Bool :=
  let t := (line.trimAsciiStart).copy
  t.startsWith "#proof_blueprint"

private def declLineMatchesKind (kw theoremName line : String) : Bool :=
  let t := (line.trimAscii).copy
  let pref := s!"{kw} {theoremName}"
  t = pref ||
    t.startsWith (pref ++ " ") ||
    t.startsWith (pref ++ ":") ||
    t.startsWith (pref ++ "(") ||
    t.startsWith (pref ++ "[")

private def declLineMatches (theoremName line : String) : Bool :=
  declLineMatchesKind "theorem" theoremName line ||
    declLineMatchesKind "lemma" theoremName line ||
    declLineMatchesKind "example" theoremName line

private partial def findDeclStart? (theoremName : String) :
    List String → Nat → Option Nat
  | [], _ => none
  | line :: rest, idx =>
      if declLineMatches theoremName line then
        some idx
      else
        findDeclStart? theoremName rest (idx + 1)

private partial def dropN : Nat → List String → List String
  | 0, lines => lines
  | _ + 1, [] => []
  | n + 1, _ :: rest => dropN n rest

private partial def takeDeclBlock : List String → List String
  | [] => []
  | line :: rest =>
      if isDeclStart line || isProofBlueprintLine line then
        []
      else
        line :: takeDeclBlock rest

private def isBlankLine (line : String) : Bool :=
  (line.trimAscii).copy = ""

private def normalizeDeclLines (lines : List String) : String :=
  let lines := lines.map (fun line => (line.trimAsciiEnd).copy)
  let lines := lines.dropWhile isBlankLine
  let lines := lines.reverse.dropWhile isBlankLine |>.reverse
  String.intercalate "\n" lines

private def currentDeclSource? (sourceFile theoremName : String) : IO (Option String) := do
  try
    let source ← IO.FS.readFile (System.FilePath.mk sourceFile)
    let lines := source.splitOn "\n"
    match findDeclStart? theoremName lines 0 with
    | none => pure none
    | some start =>
        match dropN start lines with
        | [] => pure none
        | line :: rest =>
            pure <| some (normalizeDeclLines (line :: takeDeclBlock rest))
  catch _ =>
    pure none

private def jsonStrField? (j : Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .ok value =>
      match value.getStr? with
      | .ok text => some text
      | .error _ => none
  | .error _ => none

private def manifestVersionRoots
    (manifestPath versionRoot : System.FilePath) (normalizedSource : String) :
    IO (Array String) := do
  if !(← manifestPath.pathExists) then
    return #[]
  try
    let text ← IO.FS.readFile manifestPath
    match Json.parse text with
    | .error _ => pure #[]
    | .ok manifest =>
        match manifest.getObjVal? "versions" with
        | .error _ => pure #[]
        | .ok versionsJson =>
            match versionsJson.getArr? with
            | .error _ => pure #[]
            | .ok versions =>
                let mut out : Array String := #[]
                for version in versions do
                  if jsonStrField? version "normalized_source" = some normalizedSource then
                    match jsonStrField? version "hash_dir" with
                    | some hashDir =>
                        out := out.push ((versionRoot / hashDir).toString)
                    | none => pure ()
                pure out
  catch _ =>
    pure #[]

private def currentManifestVersionRoots
    (projectRoot : System.FilePath) (sourceFile theoremName : String) : IO (Array String) := do
  match ← currentDeclSource? sourceFile theoremName with
  | none => pure #[]
  | some normalizedSource =>
      let dataset := datasetNameFromSourceFile sourceFile
      let root := projectRoot.toString
      let theoremToken := safeComponent theoremName
      let datasetRoot := System.FilePath.mk s!"{root}/output/{dataset}/{theoremToken}"
      let exampleRoot := System.FilePath.mk s!"{root}/output/example/{theoremToken}"
      let fromDataset ← manifestVersionRoots (datasetRoot / "manifest.json") datasetRoot normalizedSource
      let fromExample ←
        if dataset = "example" then
          pure #[]
        else
          manifestVersionRoots (exampleRoot / "manifest.json") exampleRoot normalizedSource
      pure (fromDataset ++ fromExample)

private def blueprintJsonCandidates
    (projectRoot : System.FilePath) (sourceFile theoremName : String)
    (versionRoots : Array String) : Array String :=
  let dataset := datasetNameFromSourceFile sourceFile
  let root := projectRoot.toString
  let hashed := versionRoots.map (fun dir => s!"{dir}/formal.evidence.json")
  hashed ++ #[
    s!"{root}/output/{dataset}/blueprints/{dataset}.{theoremName}.json",
    s!"{root}/output/example/blueprints/example.{theoremName}.json"
  ]

private def layeredJsonCandidates
    (projectRoot : System.FilePath) (sourceFile theoremName : String)
    (versionRoots : Array String) : Array String :=
  let dataset := datasetNameFromSourceFile sourceFile
  let root := projectRoot.toString
  let hashed := versionRoots.map (fun dir => s!"{dir}/formal.layered.json")
  hashed ++ #[
    s!"{root}/output/{dataset}/layered/{dataset}.{theoremName}.layered.json",
    s!"{root}/output/example/layered/example.{theoremName}.layered.json"
  ]

private def englishLayeredJsonCandidates
    (_projectRoot : System.FilePath) (_sourceFile _theoremName : String)
    (versionRoots : Array String) : Array String :=
  versionRoots.map (fun dir => s!"{dir}/english.layered.json")

private def firstExistingPath? (paths : Array String) : IO (Option String) := do
  for path in paths do
    if ← (System.FilePath.mk path).pathExists then
      return some path
  pure none

private partial def findProofStructPackageRoot? (dir : System.FilePath) :
    IO (Option System.FilePath) := do
  if ← (dir / "scripts" / "ProofStruct" / "batch_extract.py").pathExists then
    return some dir
  match dir.parent with
  | some parent => findProofStructPackageRoot? parent
  | none => pure none

private def proofStructPackageRootForSource (projectRoot : System.FilePath)
    (sourceFile : String) : IO System.FilePath := do
  let cwd ← IO.currentDir
  let sourcePath := System.FilePath.mk sourceFile
  let candidates := #[
    projectRoot,
    sourcePath.parent.getD cwd,
    cwd
  ]
  for candidate in candidates do
    match ← findProofStructPackageRoot? candidate with
    | some root => return root
    | none => pure ()
  pure projectRoot

private def stripTomlComment (line : String) : String :=
  match line.splitOn "#" with
  | [] => line
  | head :: _ => head

private def unquoteTomlString (value : String) : String :=
  let value := (stripTomlComment value).trimAscii.toString
  if value.startsWith "\"" && value.endsWith "\"" && value.length >= 2 then
    ((value.drop 1).copy.dropEnd 1).copy
  else
    value

private def tomlAssignment? (line : String) : Option (String × String) :=
  match line.splitOn "=" with
  | [] => none
  | [_] => none
  | key :: rest =>
      let key := key.trimAscii.toString
      let value := unquoteTomlString (String.intercalate "=" rest)
      if key = "" then none else some (key, value)

private partial def pythonExecutableInTomlLines : List String → Bool → Option String
  | [], _ => none
  | line :: rest, inPythonSection =>
      let stripped := (stripTomlComment line).trimAscii.toString
      if stripped.startsWith "[" && stripped.endsWith "]" then
        pythonExecutableInTomlLines rest (stripped = "[python]")
      else if inPythonSection then
        match tomlAssignment? line with
        | some ("executable", value) =>
            if value = "" then pythonExecutableInTomlLines rest inPythonSection else some value
        | _ => pythonExecutableInTomlLines rest inPythonSection
      else
        pythonExecutableInTomlLines rest inPythonSection

private def pythonExecutableFromConfig? (path : System.FilePath) : IO (Option String) := do
  if !(← path.pathExists) then
    return none
  try
    let text ← IO.FS.readFile path
    pure (pythonExecutableInTomlLines (text.splitOn "\n") false)
  catch _ =>
    pure none

private def pythonCommand (projectRoot packageRoot : System.FilePath) : IO String := do
  match ← IO.getEnv "PROOFSTRUCT_PYTHON" with
  | some python =>
      let python := python.trimAscii.toString
      if python = "" then pure "python" else pure python
  | none =>
      match ← pythonExecutableFromConfig? (projectRoot / "proofstruct_config.toml") with
      | some python => pure python
      | none =>
          match ← pythonExecutableFromConfig? (packageRoot / "proofstruct_config.toml") with
          | some python => pure python
          | none => pure "python"

private def processOutputText (output : IO.Process.Output) : String :=
  let stdout := output.stdout.trimAscii.toString
  let stderr := output.stderr.trimAscii.toString
  let parts := #[stdout, stderr].filter (fun s => s != "")
  String.intercalate "\n" parts.toList

private def runFormalExtraction
    (projectRoot packageRoot : System.FilePath) (sourceFile theoremName : String) :
    IO (Except String String) := do
  let script := packageRoot / "scripts" / "ProofStruct" / "batch_extract.py"
  if !(← script.pathExists) then
    return .error s!"ProofStruct batch_extract.py not found at {script}"
  let output ← IO.Process.output {
    cmd := ← pythonCommand projectRoot packageRoot
    args := #[
      script.toString,
      "--project-root", projectRoot.toString,
      "--file", sourceFile,
      "--theorem", theoremName,
      "--safe"
    ]
    cwd := projectRoot
  }
  let text := processOutputText output
  if output.exitCode == 0 then
    pure (.ok text)
  else
    pure (.error s!"ProofStruct formal extraction failed with exit code {output.exitCode}.\n{text}")

private def runEnglishExtraction
    (projectRoot packageRoot : System.FilePath) (sourceFile theoremName : String) :
    IO (Except String String) := do
  let script := packageRoot / "scripts" / "ProofStruct" / "batch_extract.py"
  if !(← script.pathExists) then
    return .error s!"ProofStruct batch_extract.py not found at {script}"
  let output ← IO.Process.output {
    cmd := ← pythonCommand projectRoot packageRoot
    args := #[
      script.toString,
      "--project-root", projectRoot.toString,
      "--file", sourceFile,
      "--theorem", theoremName,
      "--safe",
      "--english",
      "--english-only",
      "--english-require-llm"
    ]
    cwd := projectRoot
  }
  let text := processOutputText output
  if output.exitCode == 0 then
    pure (.ok text)
  else
    pure (.error s!"ProofStruct English extraction failed with exit code {output.exitCode}.\n{text}")

private def readBlueprintFromJsonFile (path : String) : IO (Except String Blueprint) := do
  try
    let text ← IO.FS.readFile (System.FilePath.mk path)
    pure (blueprintFromJsonString text)
  catch err =>
    pure (.error s!"failed to read blueprint JSON {path}: {err}")

private def readOptionalLayeredJsonFile (path : String) : IO (Except String Json) := do
  try
    let text ← IO.FS.readFile (System.FilePath.mk path)
    match Json.parse text with
    | .error err =>
        pure (.error s!"failed to parse layered blueprint JSON {path}: {err}")
    | .ok layeredJson =>
        match layeredBlueprintFromJson layeredJson with
        | .error err =>
            pure (.error s!"invalid layered blueprint JSON {path}: {err}")
        | .ok _ =>
            pure (.ok layeredJson)
  catch err =>
    pure (.error s!"failed to read layered blueprint JSON {path}: {err}")

private def readLayeredWidgetPropsFromJsonFile (path : String) (englishPath? : Option String) :
    IO (Except String Json) := do
  match ← readOptionalLayeredJsonFile path with
  | .error err => pure (.error err)
  | .ok layeredJson =>
      match englishPath? with
      | some englishPath =>
          match ← readOptionalLayeredJsonFile englishPath with
          | .error err => pure (.error err)
          | .ok englishJson =>
              pure (.ok <| Json.mkObj [
                ("dataSource", Json.str path),
                ("englishDataSource", Json.str englishPath),
                ("layered", layeredJson),
                ("englishLayered", englishJson)
              ])
      | none =>
          pure (.ok <| Json.mkObj [
            ("dataSource", Json.str path),
            ("layered", layeredJson)
          ])

inductive BlueprintWidgetResult where
  | layered (props : Json)
  | evidenceFallback (html : Html)

private def readBlueprintWidgetFromCache
    (projectRoot : System.FilePath) (sourceFile theoremName : String) :
    CommandElabM BlueprintWidgetResult := do
  let versionRoots ← liftIO <| currentManifestVersionRoots projectRoot sourceFile theoremName
  let layeredCandidates := layeredJsonCandidates projectRoot sourceFile theoremName versionRoots
  match ← liftIO <| firstExistingPath? layeredCandidates with
  | some path =>
      let englishPath? ← liftIO <|
        firstExistingPath? (englishLayeredJsonCandidates projectRoot sourceFile theoremName versionRoots)
      match ← liftIO <| readLayeredWidgetPropsFromJsonFile path englishPath? with
      | .error err => throwError err
      | .ok props => pure <| .layered props
  | none =>
      let blueprintCandidates := blueprintJsonCandidates projectRoot sourceFile theoremName versionRoots
      match ← liftIO <| firstExistingPath? blueprintCandidates with
      | some path =>
          match ← liftIO <| readBlueprintFromJsonFile path with
          | .error err => throwError err
          | .ok bp => pure <| .evidenceFallback (blueprintGraphHtml bp)
      | none =>
          throwError
            s!"layered blueprint JSON not found for theorem '{theoremName}'.\nNo manifest entry matched the current source block, or the matching JSON files were missing.\nTried layered paths:\n{String.intercalate "\n" layeredCandidates.toList}\n\nFallback evidence JSON was also not found. Tried:\n{String.intercalate "\n" blueprintCandidates.toList}\nGenerate it first with the ProofStruct batch_extract.py script."

private def readLayeredBlueprintWidgetFromCache
    (projectRoot : System.FilePath) (sourceFile theoremName : String) :
    CommandElabM BlueprintWidgetResult := do
  let versionRoots ← liftIO <| currentManifestVersionRoots projectRoot sourceFile theoremName
  let layeredCandidates := layeredJsonCandidates projectRoot sourceFile theoremName versionRoots
  match ← liftIO <| firstExistingPath? layeredCandidates with
  | some path =>
      let englishPath? ← liftIO <|
        firstExistingPath? (englishLayeredJsonCandidates projectRoot sourceFile theoremName versionRoots)
      match ← liftIO <| readLayeredWidgetPropsFromJsonFile path englishPath? with
      | .error err => throwError err
      | .ok props => pure <| .layered props
  | none =>
      throwError
        s!"layered blueprint JSON not found for theorem '{theoremName}'.\nNo manifest entry matched the current source block, or the matching JSON files were missing.\nTried layered paths:\n{String.intercalate "\n" layeredCandidates.toList}"

private def currentFormalLayeredPath?
    (projectRoot : System.FilePath) (sourceFile theoremName : String) :
    IO (Option String) := do
  let versionRoots ← currentManifestVersionRoots projectRoot sourceFile theoremName
  let formalCandidates := versionRoots.map (fun dir => s!"{dir}/formal.layered.json")
  firstExistingPath? formalCandidates

private def currentEnglishLayeredPath?
    (projectRoot : System.FilePath) (sourceFile theoremName : String) :
    IO (Option String) := do
  let versionRoots ← currentManifestVersionRoots projectRoot sourceFile theoremName
  let englishCandidates := englishLayeredJsonCandidates projectRoot sourceFile theoremName versionRoots
  firstExistingPath? englishCandidates

private def readEnglishBlueprintWidgetFromCache
    (projectRoot : System.FilePath) (sourceFile theoremName : String) :
    CommandElabM BlueprintWidgetResult := do
  match ← liftIO <| currentFormalLayeredPath? projectRoot sourceFile theoremName with
  | none =>
      throwError s!"formal layered blueprint JSON not found for theorem '{theoremName}'"
  | some formalPath =>
      match ← liftIO <| currentEnglishLayeredPath? projectRoot sourceFile theoremName with
      | none =>
          throwError s!"English layered blueprint JSON not found for theorem '{theoremName}'"
      | some englishPath =>
          match ← liftIO <| readLayeredWidgetPropsFromJsonFile formalPath (some englishPath) with
          | .error err => throwError err
          | .ok props => pure <| .layered props

private def buildBlueprintWidget (theoremName : String) : CommandElabM BlueprintWidgetResult := do
  let sourceFile ← currentSourceFile
  let projectRoot ← liftIO <| projectRootForSource sourceFile
  readBlueprintWidgetFromCache projectRoot sourceFile theoremName

private def buildBlueprintWidgetOrGenerate (theoremName : String) :
    CommandElabM BlueprintWidgetResult := do
  let sourceFile ← currentSourceFile
  let projectRoot ← liftIO <| projectRootForSource sourceFile
  try
    readLayeredBlueprintWidgetFromCache projectRoot sourceFile theoremName
  catch _ =>
    let packageRoot ← liftIO <| proofStructPackageRootForSource projectRoot sourceFile
    match ← liftIO <| runFormalExtraction projectRoot packageRoot sourceFile theoremName with
    | .error err => throwError err
    | .ok _ =>
        readBlueprintWidgetFromCache projectRoot sourceFile theoremName

private def buildEnglishBlueprintWidgetOrGenerate (theoremName : String) :
    CommandElabM BlueprintWidgetResult := do
  let sourceFile ← currentSourceFile
  let projectRoot ← liftIO <| projectRootForSource sourceFile
  let packageRoot ← liftIO <| proofStructPackageRootForSource projectRoot sourceFile
  try
    readEnglishBlueprintWidgetFromCache projectRoot sourceFile theoremName
  catch _ =>
    match ← liftIO <| currentFormalLayeredPath? projectRoot sourceFile theoremName with
    | none =>
        match ← liftIO <| runFormalExtraction projectRoot packageRoot sourceFile theoremName with
        | .error err => throwError err
        | .ok _ => pure ()
    | some _ => pure ()
    match ← liftIO <| runEnglishExtraction projectRoot packageRoot sourceFile theoremName with
    | .error err => throwError err
    | .ok _ =>
        readEnglishBlueprintWidgetFromCache projectRoot sourceFile theoremName

syntax (name := proofBlueprintCmd) "#proof_blueprint " ident : command
syntax (name := proofBlueprintBangCmd) "#proof_blueprint! " ident : command
syntax (name := proofBlueprintEnglishBangCmd) "#proof_blueprint_english! " ident : command

@[command_elab proofBlueprintCmd]
def elabProofBlueprintCmd : CommandElab := fun
  | stx@`(#proof_blueprint $theoremId:ident) => do
      let theoremName := toString theoremId.getId
      match ← buildBlueprintWidget theoremName with
      | .layered props =>
          liftCoreM <| Widget.savePanelWidgetInfo
            (hash BlueprintLayeredGraph.javascript)
            (return props)
            stx
      | .evidenceFallback html =>
          liftCoreM <| Widget.savePanelWidgetInfo
            (hash HtmlDisplayPanel.javascript)
            (return json% { html: $(← rpcEncode html) })
            stx
  | _ => throwUnsupportedSyntax

@[command_elab proofBlueprintBangCmd]
def elabProofBlueprintBangCmd : CommandElab := fun
  | stx@`(#proof_blueprint! $theoremId:ident) => do
      let theoremName := toString theoremId.getId
      match ← buildBlueprintWidgetOrGenerate theoremName with
      | .layered props =>
          liftCoreM <| Widget.savePanelWidgetInfo
            (hash BlueprintLayeredGraph.javascript)
            (return props)
            stx
      | .evidenceFallback html =>
          liftCoreM <| Widget.savePanelWidgetInfo
            (hash HtmlDisplayPanel.javascript)
            (return json% { html: $(← rpcEncode html) })
            stx
  | _ => throwUnsupportedSyntax

@[command_elab proofBlueprintEnglishBangCmd]
def elabProofBlueprintEnglishBangCmd : CommandElab := fun
  | stx@`(#proof_blueprint_english! $theoremId:ident) => do
      let theoremName := toString theoremId.getId
      match ← buildEnglishBlueprintWidgetOrGenerate theoremName with
      | .layered props =>
          liftCoreM <| Widget.savePanelWidgetInfo
            (hash BlueprintLayeredGraph.javascript)
            (return props)
            stx
      | .evidenceFallback html =>
          liftCoreM <| Widget.savePanelWidgetInfo
            (hash HtmlDisplayPanel.javascript)
            (return json% { html: $(← rpcEncode html) })
            stx
  | _ => throwUnsupportedSyntax

end ProofStruct
