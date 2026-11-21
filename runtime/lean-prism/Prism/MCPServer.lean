import Lean.Data.Json
import Prism.Driver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.MCPServer`: Native Lean 4 Stdio MCP Server for Closed-World Nodes & Open-World Sessions

Provides iterative draft authoring (`write_draft`, `patch_draft`, `read_draft`, `list_drafts`),
sub-50ms in-process Lean 4 Prism type/gate checking (`check_agda`, `check_spec`, `check_entry`),
and cleanroom `SessionEnv` Agda probe execution (`run_agda_script`) to Codex CLI while keeping
Codex CLI's `shell_tool=false` and `unified_exec=false`.
-/

namespace Prism.MCP

open Lean (Json ToJson toJson)
open Prism

structure MCPConfig : Type where
  mode      : String := "node"     -- "node" or "session"
  repoDir   : String := "."
  libDir    : String := ""
  irDir     : String := ""
  dumpBin   : Option String := none
  ctxDir    : String := ""         -- `<isolated>/mcp`
  workspace : String := ""         -- session workspace (for `mode == "session"`)
  refFile   : String := ""         -- path to serialized `RefSpec` S-expr (for `mode == "session"`)

private def safeDraftName (s : String) : Bool :=
  !s.isEmpty && s.length <= 128 &&
  s.toList.all (fun c => c.isAlphanum || c == '_' || c == '-' || c == '.') &&
  s != "." && s != ".."

private def draftsDir (cfg : MCPConfig) : String :=
  s!"{cfg.ctxDir}/drafts"

private def draftFilePath (cfg : MCPConfig) (name : String) : String :=
  s!"{draftsDir cfg}/{name}.block"

private def reservedTopPrefixes : List String :=
  ["Ownership", "OwnershipIO", "Code", "Store", "Meta", "Backend", "Test", "Verification", "SessionEnv", "Main", "UI"]

private def checkObjectBoundary (allowEntry : Bool) (modName : String) (imps : List String) : Option String :=
  let mParts := modName.splitOn "."
  let mTop := mParts.headD ""
  let okSelf :=
    if allowEntry && modName == "Main" then true
    else !mParts.isEmpty && !reservedTopPrefixes.contains mTop
  if !okSelf then
    some s!"sandbox: forbidden module name '{modName}'"
  else
    let badImp := imps.find? fun imp =>
      let iParts := imp.splitOn "."
      let iTop := iParts.headD ""
      if allowEntry && (imp == "OwnershipIO.WorldRunner" || imp == "OwnershipIO.FFI") then false
      else iParts.isEmpty || reservedTopPrefixes.contains iTop
    match badImp with
    | some bi => some s!"sandbox: forbidden import '{bi}' in '{modName}'"
    | none    => none

private def hasSubstr (s sub : String) : Bool :=
  !(s.splitOn sub |>.drop 1).isEmpty

private def checkClosedNoPostulatesOrHoles (allowIOGuarded : Bool) (cm : CodeMod) : List String := Id.run do
  let mut errs : List String := []
  let allowedFlags := if allowIOGuarded then ["--safe", "--without-K", "--guardedness"] else ["--safe", "--without-K"]
  let fnNames := cm.decls.filterMap fun | .fun_ _ fn _ => some fn | _ => none
  for d in cm.decls do
    match d with
    | .pragma p =>
        if p.startsWith "OPTIONS" then
          let opts := ((p.drop 7).toString).splitOn " " |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
          for fl in opts do
            if !allowedFlags.contains fl then
              errs := errs ++ [s!"flagEnvelopeViolation: forbidden pragma option '{fl}'"]
        else
          errs := errs ++ [s!"forbidden pragma '{p}'"]
    | .unsupported u =>
        errs := errs ++ [s!"unsupported / FFI construct '{u}' is forbidden"]
    | .sig ms nm _ =>
        if ms.termCheck != .check then
          errs := errs ++ [s!"termination bypass on '{nm}' is forbidden"]
        if nm != "_" && !fnNames.contains nm then
          errs := errs ++ [s!"postulate / unimplemented signature '{nm}' is forbidden in a closed module"]
    | .fun_ ms nm _ =>
        if ms.termCheck != .check then
          errs := errs ++ [s!"termination bypass on '{nm}' is forbidden"]
    | _ => pure ()
  let renderedSexp := renderTopSExpr (encodeCodeMod cm)
  if hasSubstr renderedSexp "(hole)" then
    errs := errs ++ ["unsolved interaction hole '{!!}' / '?' is forbidden"]
  if allowIOGuarded then
    -- Check forbidden OwnershipIO.FFI symbols (e.g. `readProcess`, `readProcessAt`)
    for badSym in ["OwnershipIO.FFI.readProcess", "OwnershipIO.FFI.readProcessAt",
                   "OwnershipIO.FFI.removeAll", "OwnershipIO.FFI.mkdirP",
                   "OwnershipIO.FFI.atomicRename", "OwnershipIO.FFI.withTempDirectory",
                   "OwnershipIO.FFI.linkPath"] do
      if hasSubstr renderedSexp badSym then
        errs := errs ++ [s!"forbidden host FFI primitive '{badSym}' in build-exe (use OwnershipIO.CLIHost instead of shelling out)"]
  errs

private partial def listAgdaFilesBelow (dir : String) : IO (List String) := do
  if !(← System.FilePath.pathExists dir) then
    return []
  let mut acc : List String := []
  let entries ← System.FilePath.readDir dir
  for e in entries do
    let p := e.path.toString
    if (← e.path.isDir) then
      let sub ← listAgdaFilesBelow p
      acc := acc ++ sub
    else if p.endsWith ".agda" then
      acc := acc ++ [p]
  pure acc

private def resolveBlockOrInline (cfg : MCPConfig) (arg : String) : IO (Except String String) := do
  let trimmed := arg.trimAscii.toString
  let blockNameOpt : Option String :=
    if trimmed.startsWith "@" then
      some ((trimmed.drop 1).toString)
    else if safeDraftName trimmed && !(hasSubstr trimmed "\n") && !(trimmed.startsWith "module ") then
      some trimmed
    else
      none
  match blockNameOpt with
  | some nm =>
      if !safeDraftName nm then
        return .error s!"invalid draft block name '{nm}'"
      let p := draftFilePath cfg nm
      if (← System.FilePath.pathExists p) then
        return .ok (← IO.FS.readFile p)
      else
        return .error s!"draft block '{nm}' does not exist; call write_draft first or pass inline Agda source"
  | none =>
      return .ok arg

private def writeModuleToWork (workDir : String) (src : String) : IO (Except String (String × List String × String)) := do
  match tokenizeAgda src with
  | .syntaxErr e => return .error s!"SYNTAX_ERROR: {e}"
  | .bot r       => return .error s!"SYNTAX_ERROR: {r}"
  | .translated toks =>
      let rec scan (rem : List Token) (mName : Option String) (imps : List String) :
          Option String × List String :=
        match rem with
        | [] => (mName, imps.reverse.eraseDups)
        | { kind := .kwModule, .. } :: { kind := .ident nm, .. } :: rest =>
            scan rest (if mName.isNone then some nm else mName) imps
        | { kind := .kwImport, .. } :: { kind := .ident imp, .. } :: rest =>
            scan rest mName (imp :: imps)
        | _ :: rest => scan rest mName imps
      let (mOpt, imps) := scan toks none []
      match mOpt with
      | none => return .error "SYNTAX_ERROR: missing 'module <Name> where' header"
      | some modName =>
          let parts := modName.splitOn "."
          let relDir := match parts.dropLast with | [] => "." | ds => String.intercalate "/" ds
          let relFile := String.intercalate "/" parts ++ ".agda"
          IO.FS.createDirAll s!"{workDir}/{relDir}"
          let fullPath := s!"{workDir}/{relFile}"
          IO.FS.writeFile fullPath src
          return .ok (modName, imps, fullPath)

private def replaceExactOnceOrAll (haystack needle replacement : String) : Option (String × Nat) :=
  if needle.isEmpty then none
  else
    let parts := haystack.splitOn needle
    match parts with
    | [] | [_] => none
    | _ => some (String.intercalate replacement parts, parts.length - 1)

private def jsonStrField (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _            => none

private def jsonBoolField (j : Json) (k : String) (defVal : Bool) : Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => b
  | _             => defVal

private def jsonNatField (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok n => match n.getNat? with | .ok v => some v | .error _ => none
  | _     => none

private def jsonStrArrayField (j : Json) (k : String) : List String :=
  match j.getObjVal? k with
  | .ok (.arr xs) => xs.toList.filterMap fun | .str s => some s | _ => none
  | _             => []

private def mkToolResult (txt : String) (isErr : Bool := false) : Json :=
  Json.mkObj
    [ ("content", Json.arr #[Json.mkObj [("type", Json.str "text"), ("text", Json.str txt)]])
    , ("isError", Json.bool isErr) ]

private def handleWriteDraft (cfg : MCPConfig) (args : Json) : IO Json := do
  match jsonStrField args "name", jsonStrField args "content" with
  | some nm, some content =>
      if !safeDraftName nm then
        return mkToolResult s!"error: invalid draft name '{nm}' (use alphanumeric, '_', '-', '.')" true
      IO.FS.createDirAll (draftsDir cfg)
      IO.FS.writeFile (draftFilePath cfg nm) content
      let lineCount := (content.splitOn "\n").length
      return mkToolResult s!"saved draft @{nm} ({lineCount} lines, {content.utf8ByteSize} bytes). You can reference @{nm} directly in your final envelope without retyping it." false
  | _, _ =>
      return mkToolResult "error: write_draft requires string arguments 'name' and 'content'" true

private def handlePatchDraft (cfg : MCPConfig) (args : Json) : IO Json := do
  match jsonStrField args "name", jsonStrField args "old_text", jsonStrField args "new_text" with
  | some nm, some oldT, some newT =>
      if !safeDraftName nm then
        return mkToolResult s!"error: invalid draft name '{nm}'" true
      let p := draftFilePath cfg nm
      if !(← System.FilePath.pathExists p) then
        return mkToolResult s!"error: draft @{nm} does not exist yet; call write_draft first" true
      let cur ← IO.FS.readFile p
      match replaceExactOnceOrAll cur oldT newT with
      | none =>
          return mkToolResult s!"error: old_text not found in draft @{nm}; call read_draft to inspect exact lines" true
      | some (updated, cnt) =>
          IO.FS.writeFile p updated
          let lineCount := (updated.splitOn "\n").length
          return mkToolResult s!"patched {cnt} occurrence(s) in draft @{nm} (now {lineCount} lines)." false
  | _, _, _ =>
      return mkToolResult "error: patch_draft requires string arguments 'name', 'old_text', and 'new_text'" true

private def handleReadDraft (cfg : MCPConfig) (args : Json) : IO Json := do
  match jsonStrField args "name" with
  | none => return mkToolResult "error: read_draft requires string argument 'name'" true
  | some nm =>
      if !safeDraftName nm then
        return mkToolResult s!"error: invalid draft name '{nm}'" true
      let p := draftFilePath cfg nm
      if !(← System.FilePath.pathExists p) then
        return mkToolResult s!"error: draft @{nm} does not exist" true
      let txt ← IO.FS.readFile p
      let ls := txt.splitOn "\n"
      let sLine := (jsonNatField args "start_line").getD 1
      let eLine := (jsonNatField args "end_line").getD ls.length
      let lo := if sLine == 0 then 0 else sLine - 1
      let hi := Nat.min ls.length eLine
      let mut outLines : List String := []
      for i in [lo:hi] do
        if let some l := ls[i]? then
          outLines := outLines ++ [s!"{i + 1}: {l}"]
      return mkToolResult (String.intercalate "\n" outLines) false

private def handleListDrafts (cfg : MCPConfig) : IO Json := do
  let d := draftsDir cfg
  if !(← System.FilePath.pathExists d) then
    return mkToolResult "no drafts saved yet" false
  let entries ← System.FilePath.readDir d
  let mut items : List String := []
  for e in entries do
    let fn := e.fileName
    if fn.endsWith ".block" then
      let fcs := fn.toList
      let stem := String.ofList (fcs.take (fcs.length - 6))
      let txt ← IO.FS.readFile e.path.toString
      items := items ++ [s!"@{stem} ({(txt.splitOn "\n").length} lines, {txt.utf8ByteSize} bytes)"]
  if items.isEmpty then
    return mkToolResult "no drafts saved yet" false
  else
    return mkToolResult (String.intercalate "\n" items) false

private def runHermeticAgdaFallback (cfg : MCPConfig) (workDir srcDir modName : String) : IO (Bool × String) := do
  let ctxDir := s!"{workDir}/agda_ctx_view"
  IO.FS.createDirAll s!"{ctxDir}/Context/Tools"
  for relF in [
    "Context/Blueprint.agda",
    "Context/PolyTransport.agda",
    "Context/Terminal.agda",
    "Context/Filter.agda",
    "Context/Tools/Clock.agda",
    "Context/Tools/ClockLaws.agda",
    "Context/Tools/TermLaws.agda",
    "Context/Tools/FuzzGen.agda",
    "Context/Tools/FsSandbox.agda",
    "Context/Tools/NetSandbox.agda",
    "Context/Tools/GitSandbox.agda",
    "Context/Tools/WebOperad.agda",
    "Context/World.agda",
    "Context/Tools/FsLaws.agda",
    "Context/Tools/GitLaws.agda",
    "Context/Tools/NetLaws.agda",
    "Context/WorldLaws.agda",
    "Context/Protocol.agda"
  ] do
    let srcP := s!"{cfg.repoDir}/{relF}"
    if (← System.FilePath.pathExists srcP) then
      let txt ← IO.FS.readFile srcP
      IO.FS.writeFile s!"{ctxDir}/{relF}" txt
  IO.FS.writeFile s!"{srcDir}/object.agda-lib" "name: mcp-fallback\ninclude: .\n"
  let agdaCfg := s!"{workDir}/agda_cfg"
  IO.FS.createDirAll agdaCfg
  let relTarget := String.intercalate "/" (modName.splitOn ".") ++ ".agda"
  let (aCode, aOut, aErr) ← runSubproc "agda"
    #["--no-libraries", "-i", ".", "-i", ctxDir, "-i", "/usr/share/agda-stdlib", s!"./{relTarget}"]
    none (some srcDir) #[("AGDA_DIR", some agdaCfg)]
  if aCode == 0 then
    pure (true, s!"OK: '{modName}' passed typecheck (via Agda fallback)")
  else
    pure (false, stripStdlibWarningsLean (aOut ++ aErr))

private def handleCheckAgdaNode (cfg : MCPConfig) (args : Json) : IO Json := do
  match jsonStrField args "main_block" with
  | none => return mkToolResult "error: check_agda requires 'main_block' (draft name like 'main' or inline Agda source)" true
  | some rawMain =>
      match (← resolveBlockOrInline cfg rawMain) with
      | .error e => return mkToolResult e true
      | .ok mainSrc =>
          let depArgs := jsonStrArrayField args "dep_blocks"
          let allowPostulates := jsonBoolField args "allow_postulates" false
          let stamp ← IO.monoMsNow
          let workDir := s!"{cfg.ctxDir}/check_{stamp}"
          let srcDir  := s!"{workDir}/src"
          IO.FS.createDirAll srcDir
          let mut depPaths : List String := []
          -- Include staged immutable ancestor modules if present
          let ancFiles ← listAgdaFilesBelow s!"{cfg.ctxDir}/ancestors"
          for af in ancFiles do
            let txt ← IO.FS.readFile af
            if let .ok (_, _, fp) ← writeModuleToWork srcDir txt then
              depPaths := depPaths ++ [fp]
          for da in depArgs do
            match (← resolveBlockOrInline cfg da) with
            | .error e => return mkToolResult e true
            | .ok dSrc =>
                match (← writeModuleToWork srcDir dSrc) with
                | .error e => return mkToolResult e true
                | .ok (dMod, dImps, dfp) =>
                    if let some bErr := checkObjectBoundary false dMod dImps then
                      return mkToolResult bErr true
                    depPaths := depPaths ++ [dfp]
          match (← writeModuleToWork srcDir mainSrc) with
          | .error e => return mkToolResult e true
          | .ok (mMod, mImps, mainPath) =>
              if let some bErr := checkObjectBoundary false mMod mImps then
                return mkToolResult bErr true
              let dedupDeps := depPaths.filter (· != mainPath) |>.eraseDups
              let parsed ← parseAndSliceBundle dedupDeps mainPath cfg.libDir s!"{workDir}/parse" cfg.dumpBin
              match parsed with
              | .syntaxErr e =>
                  let _ ← runSubproc "rm" #["-rf", workDir] none
                  return mkToolResult s!"SYNTAX_ERROR:\n{e}" true
              | .bot _ =>
                  let (ok, fbMsg) ← runHermeticAgdaFallback cfg workDir srcDir mMod
                  let _ ← runSubproc "rm" #["-rf", workDir] none
                  return mkToolResult fbMsg (!ok)
              | .translated (_, mainSm) =>
                  if !allowPostulates then
                    let closedErrs := checkClosedNoPostulatesOrHoles false mainSm.codeMod
                    if !closedErrs.isEmpty then
                      let _ ← runSubproc "rm" #["-rf", workDir] none
                      return mkToolResult ("CLOSED_IMPL_VIOLATION:\n" ++ String.intercalate "\n" closedErrs) true
                  let (code, msg) ← runPrismCheck cfg.libDir s!"{workDir}/lean" dedupDeps mainPath cfg.dumpBin
                  if code == exitOK then
                    let _ ← runSubproc "rm" #["-rf", workDir] none
                    return mkToolResult s!"OK: '{mMod}' passed Lean 4 Prism kernel typecheck" false
                  else if code == exitBot then
                    let (ok, fbMsg) ← runHermeticAgdaFallback cfg workDir srcDir mMod
                    let _ ← runSubproc "rm" #["-rf", workDir] none
                    return mkToolResult fbMsg (!ok)
                  else
                    let _ ← runSubproc "rm" #["-rf", workDir] none
                    return mkToolResult msg true

private def handleCheckSpecSession (cfg : MCPConfig) (args : Json) : IO Json := do
  match jsonStrField args "spec_block" with
  | none => return mkToolResult "error: check_spec requires 'spec_block'" true
  | some rawSpec =>
      match (← resolveBlockOrInline cfg rawSpec) with
      | .error e => return mkToolResult e true
      | .ok specSrc =>
          let baseTrees := jsonStrArrayField args "base_trees"
          let stamp ← IO.monoMsNow
          let workDir := s!"{cfg.ctxDir}/spec_chk_{stamp}"
          let srcDir  := s!"{workDir}/src"
          IO.FS.createDirAll srcDir
          let mut depPaths : List String := []
          for t in baseTrees do
            let gFiles ← listAgdaFilesBelow s!"{cfg.workspace}/generated/{t}"
            for gf in gFiles do
              let txt ← IO.FS.readFile gf
              if let .ok (_, _, fp) ← writeModuleToWork srcDir txt then
                depPaths := depPaths ++ [fp]
          match (← writeModuleToWork srcDir specSrc) with
          | .error e => return mkToolResult e true
          | .ok (mMod, mImps, mainPath) =>
              if let some bErr := checkObjectBoundary false mMod mImps then
                return mkToolResult bErr true
              let dedupDeps := depPaths.filter (· != mainPath) |>.eraseDups
              let (code, msg) ← runPrismCheck cfg.libDir s!"{workDir}/lean" dedupDeps mainPath cfg.dumpBin
              if code == exitOK then
                let _ ← runSubproc "rm" #["-rf", workDir] none
                return mkToolResult s!"OK: specification '{mMod}' passed Lean 4 Prism typecheck" false
              else if code == exitBot then
                let (ok, fbMsg) ← runHermeticAgdaFallback cfg workDir srcDir mMod
                let _ ← runSubproc "rm" #["-rf", workDir] none
                return mkToolResult fbMsg (!ok)
              else
                let _ ← runSubproc "rm" #["-rf", workDir] none
                return mkToolResult msg true

private def handleCheckEntrySession (cfg : MCPConfig) (args : Json) : IO Json := do
  match jsonStrField args "entry" with
  | none => return mkToolResult "error: check_entry requires 'entry' (e.g. 'Gen.T1.Emph.app')" true
  | some rawEntry =>
      let validSeg (s : String) : Bool :=
        !s.isEmpty && s.toList.all (fun c => !c.isWhitespace && c.toNat >= 32 && c != '.' && c != '/' && c != '\\')
      let parts := rawEntry.splitOn "."
      let modParts := parts.dropLast
      let ident := parts.getLastD ""
      let modName := String.intercalate "." modParts
      if parts.length < 2 || !(modParts.all validSeg) || !validSeg ident || ident == "_" then
        return mkToolResult s!"build-exe: invalid or forbidden entry '{rawEntry}' (expected '<VerifiedModule>.<app>' in Gen.* object namespace)" true
      if let some bErr := checkObjectBoundary false modName [] then
        return mkToolResult s!"build-exe: invalid or forbidden entry '{rawEntry}' ({bErr})" true
      let modeStr := (jsonStrField args "mode").getD "cli"
      let runnerOpt : Option String :=
        match modeStr with
        | "cli"      => some "runCliIO"
        | "reactive" => some "runReactiveIO"
        | _          => none
      match runnerOpt with
      | none => return mkToolResult s!"error: invalid mode '{modeStr}' (expected 'cli' or 'reactive')" true
      | some runner =>
          let depArgs := jsonStrArrayField args "dep_blocks"
          let stamp ← IO.monoMsNow
          let workDir := s!"{cfg.ctxDir}/entry_chk_{stamp}"
          let srcDir  := s!"{workDir}/src"
          IO.FS.createDirAll srcDir
          let mut depPaths : List String := []
          let genTreesDir := s!"{cfg.workspace}/generated"
          let gFiles ← listAgdaFilesBelow genTreesDir
          for gf in gFiles do
            let txt ← IO.FS.readFile gf
            if let .ok (_, _, fp) ← writeModuleToWork srcDir txt then
              depPaths := depPaths ++ [fp]
          for da in depArgs do
            match (← resolveBlockOrInline cfg da) with
            | .error e =>
                let _ ← runSubproc "rm" #["-rf", workDir] none
                return mkToolResult e true
            | .ok dSrc =>
                match (← writeModuleToWork srcDir dSrc) with
                | .error e =>
                    let _ ← runSubproc "rm" #["-rf", workDir] none
                    return mkToolResult e true
                | .ok (dMod, dImps, dfp) =>
                    if let some bErr := checkObjectBoundary false dMod dImps then
                      let _ ← runSubproc "rm" #["-rf", workDir] none
                      return mkToolResult bErr true
                    depPaths := depPaths ++ [dfp]
          let targetFile := s!"{srcDir}/" ++ String.intercalate "/" modParts ++ ".agda"
          if !(← System.FilePath.pathExists targetFile) then
            let _ ← runSubproc "rm" #["-rf", workDir] none
            return mkToolResult s!"error: target module '{modName}' not found in workspace generated/* or dep_blocks" true
          let entrySrc := String.intercalate "\n"
            [ "{-# OPTIONS --guardedness #-}"
            , "module Main where"
            , "open import Agda.Builtin.IO using (IO)"
            , "open import Agda.Builtin.Unit using (⊤)"
            , s!"open import OwnershipIO.WorldRunner using ({runner})"
            , s!"import {modName} as Target"
            , "main : IO ⊤"
            , s!"main = {runner} Target.{ident}"
            , "" ]
          match (← writeModuleToWork srcDir entrySrc) with
          | .error e =>
              let _ ← runSubproc "rm" #["-rf", workDir] none
              return mkToolResult e true
          | .ok (mMod, mImps, mainPath) =>
              if let some bErr := checkObjectBoundary true mMod mImps then
                let _ ← runSubproc "rm" #["-rf", workDir] none
                return mkToolResult bErr true
              let dedupDeps := depPaths.filter (· != mainPath) |>.eraseDups
              let parsed ← parseAndSliceBundle dedupDeps mainPath cfg.libDir s!"{workDir}/parse" cfg.dumpBin
              match parsed with
              | .syntaxErr e =>
                  let _ ← runSubproc "rm" #["-rf", workDir] none
                  return mkToolResult s!"SYNTAX_ERROR:\n{e}" true
              | .bot r =>
                  let _ ← runSubproc "rm" #["-rf", workDir] none
                  return mkToolResult s!"ENTRY_CHECK_ERROR:\n{r}" true
              | .translated (_, mainSm) =>
                  let closedErrs := checkClosedNoPostulatesOrHoles true mainSm.codeMod
                  if !closedErrs.isEmpty then
                    let _ ← runSubproc "rm" #["-rf", workDir] none
                    return mkToolResult ("ENTRY_GATE_VIOLATION:\n" ++ String.intercalate "\n" closedErrs) true
                  let outTmp := s!"{workDir}/candidate.dryrun"
                  let (code, msg) ← runPrismBuildExe cfg.libDir cfg.irDir s!"{workDir}/lean" outTmp dedupDeps mainPath cfg.dumpBin false
                  let _ ← runSubproc "rm" #["-rf", workDir] none
                  if code == exitOK then
                    return mkToolResult s!"OK: entrypoint '{rawEntry}' ({runner}) passed import gates and static native Lean 4 build check" false
                  else
                    return mkToolResult msg true

private def handleRunAgdaScriptSession (cfg : MCPConfig) (args : Json) : IO Json := do
  match jsonStrField args "script_block" with
  | none => return mkToolResult "error: run_agda_script requires 'script_block'" true
  | some rawScript =>
      match (← resolveBlockOrInline cfg rawScript) with
      | .error e => return mkToolResult e true
      | .ok scriptSrc =>
          let mainBin := s!"{cfg.repoDir}/Main"
          if !(← System.FilePath.pathExists mainBin) then
            return mkToolResult s!"error: Main runner binary not found at {mainBin}" true
          let stamp ← IO.monoMsNow
          let scriptFile := s!"{cfg.ctxDir}/probe_{stamp}.agda"
          IO.FS.writeFile scriptFile scriptSrc
          let (code, out, err) ← runSubproc mainBin #["session-probe", cfg.workspace, cfg.refFile, scriptFile] none (some cfg.repoDir)
          let _ ← runSubproc "rm" #["-f", scriptFile] none
          if code == 0 then
            return mkToolResult s!"EXIT 0:\n{out}{err}" false
          else
            return mkToolResult s!"EXIT {code}:\n{out}{err}" true

private def roAnnotations : Json :=
  Json.mkObj
    [ ("readOnlyHint",    Json.bool true)
    , ("destructiveHint", Json.bool false)
    , ("openWorldHint",   Json.bool false) ]

private def mkToolSchema (name desc : String) (props : List (String × Json)) (req : List String) : Json :=
  Json.mkObj
    [ ("name",        Json.str name)
    , ("description", Json.str desc)
    , ("annotations", roAnnotations)
    , ("inputSchema", Json.mkObj
        [ ("type",                 Json.str "object")
        , ("properties",           Json.mkObj props)
        , ("required",             Json.arr (req.map Json.str).toArray)
        , ("additionalProperties", Json.bool false) ]) ]

private def strProp (desc : String) : Json :=
  Json.mkObj [("type", Json.str "string"), ("description", Json.str desc)]

private def natProp (desc : String) : Json :=
  Json.mkObj [("type", Json.str "integer"), ("description", Json.str desc)]

private def boolProp (desc : String) : Json :=
  Json.mkObj [("type", Json.str "boolean"), ("description", Json.str desc)]

private def strArrProp (desc : String) : Json :=
  Json.mkObj [("type", Json.str "array"), ("items", Json.mkObj [("type", Json.str "string")]), ("description", Json.str desc)]

private def toolsForConfig (cfg : MCPConfig) : Array Json :=
  let common : List Json :=
    [ mkToolSchema "write_draft"
        "Create or overwrite a named Agda draft block (e.g. 'main', 'spec', 'entry', 'probe', 'eval'). Reference it as @<name> in your final envelope without retyping the full source."
        [("name", strProp "Block name (alphanumeric, '_', '-', '.')"), ("content", strProp "Complete Agda module text")]
        ["name", "content"]
    , mkToolSchema "patch_draft"
        "Apply an exact local search-and-replace patch inside an existing named draft block @<name> without rewriting the whole file."
        [ ("name", strProp "Existing draft block name")
        , ("old_text", strProp "Exact substring to replace")
        , ("new_text", strProp "Replacement text") ]
        ["name", "old_text", "new_text"]
    , mkToolSchema "read_draft"
        "Read numbered lines of an existing draft block @<name>."
        [ ("name", strProp "Draft block name")
        , ("start_line", natProp "Optional 1-based start line")
        , ("end_line", natProp "Optional 1-based inclusive end line") ]
        ["name"]
    , mkToolSchema "list_drafts"
        "List all currently saved draft blocks in this turn's scratch workspace."
        [] []
    ]
  let specific : List Json :=
    if cfg.mode == "session" then
      [ mkToolSchema "run_agda_script"
          "Compile and execute a closed Agda probe/replay script over SessionEnv (with procExec, pty, fsbox, netbox, gitbox, FuzzGen, 'ref', and 'cand' in the cleanroom sandbox)."
          [("script_block", strProp "Draft block name (e.g. 'probe' or '@probe') or inline Agda module")]
          ["script_block"]
      , mkToolSchema "check_spec"
          "Fast (<50ms) Lean 4 Prism kernel typecheck of a drive-tree specification draft against optional sealed base_trees."
          [ ("spec_block", strProp "Draft block name (e.g. 'spec') or inline Agda spec module")
          , ("base_trees", strArrProp "Optional list of sealed tree names (e.g. ['T0'])") ]
          ["spec_block"]
      , mkToolSchema "check_entry"
          "Fast static native Lean 4 build & import-gate check of a build-exe entrypoint '<TargetMod>.<ident>' (synthesizing the fixed WorldRunner Main.agda glue) against exported generated/* modules and optional unstaged dep_blocks."
          [ ("entry", strProp "Verified entrypoint '<TargetMod>.<ident>' (e.g. 'Gen.T1.Emph.app')")
          , ("mode", strProp "Optional execution mode: 'cli' (default, runCliIO) or 'reactive' (runReactiveIO)")
          , ("dep_blocks", strArrProp "Optional list of draft block names (e.g. ['main']) to stage alongside generated/*") ]
          ["entry"]
      ]
    else
      [ mkToolSchema "check_agda"
          "Fast (<50ms) Lean 4 Prism kernel typecheck and closed-world gate check on a draft block or inline Agda module."
          [ ("main_block", strProp "Draft block name (e.g. 'main') or inline Agda module")
          , ("dep_blocks", strArrProp "Optional list of subspec/dependency draft block names")
          , ("allow_postulates", boolProp "Set true only when checking a child subspec; leave false for closed implementations/refutations") ]
          ["main_block"]
      ]
  (common ++ specific).toArray

private def dispatchToolCall (cfg : MCPConfig) (toolName : String) (args : Json) : IO Json := do
  match toolName with
  | "write_draft"     => handleWriteDraft cfg args
  | "patch_draft"     => handlePatchDraft cfg args
  | "read_draft"      => handleReadDraft cfg args
  | "list_drafts"     => handleListDrafts cfg
  | "check_agda"      => handleCheckAgdaNode cfg args
  | "check_spec"      => handleCheckSpecSession cfg args
  | "check_entry"     => handleCheckEntrySession cfg args
  | "run_agda_script" => handleRunAgdaScriptSession cfg args
  | _                 => pure (mkToolResult s!"unknown tool '{toolName}'" true)

private def handleRPC (cfg : MCPConfig) (msg : Json) : IO (Option Json) := do
  let idOpt : Option Json :=
    match msg.getObjVal? "id" with
    | .ok v => some v
    | .error _ => none
  let method := (jsonStrField msg "method").getD ""
  let params := match msg.getObjVal? "params" with | .ok p => p | .error _ => Json.mkObj []
  match idOpt with
  | none =>
      -- Notification (e.g. `notifications/initialized`)
      pure none
  | some reqId =>
      let mkResp (res : Json) : Json :=
        Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", reqId), ("result", res)]
      let mkErr (code : Int) (errMsg : String) : Json :=
        Json.mkObj
          [ ("jsonrpc", Json.str "2.0")
          , ("id", reqId)
          , ("error", Json.mkObj [("code", toJson code), ("message", Json.str errMsg)]) ]
      match method with
      | "initialize" =>
          let protoVer := (jsonStrField params "protocolVersion").getD "2025-06-18"
          let res := Json.mkObj
            [ ("protocolVersion", Json.str protoVer)
            , ("capabilities", Json.mkObj [("tools", Json.mkObj [])])
            , ("serverInfo", Json.mkObj [("name", Json.str "codetransport-lean-mcp"), ("version", Json.str "4.0.0")]) ]
          pure (some (mkResp res))
      | "ping" =>
          pure (some (mkResp (Json.mkObj [])))
      | "tools/list" =>
          let res := Json.mkObj [("tools", Json.arr (toolsForConfig cfg))]
          pure (some (mkResp res))
      | "tools/call" =>
          match jsonStrField params "name" with
          | none => pure (some (mkErr (-32602) "missing tool name"))
          | some tName =>
              let tArgs := match params.getObjVal? "arguments" with | .ok a => a | .error _ => Json.mkObj []
              let res ← dispatchToolCall cfg tName tArgs
              pure (some (mkResp res))
      | _ =>
          pure (some (mkErr (-32601) s!"method not found: {method}"))

private partial def skipHeadersAndReadBody (stdin : IO.FS.Stream) (contentLen : Nat) : IO (Option String) := do
  let hdrLine ← stdin.getLine
  if hdrLine.isEmpty then
    return none
  let trimmed := hdrLine.trimAscii.toString
  if trimmed.isEmpty then
    let bs ← stdin.read (USize.ofNat contentLen)
    return String.fromUTF8? bs
  else
    skipHeadersAndReadBody stdin contentLen

private partial def mcpLoop (cfg : MCPConfig) (stdin stdout : IO.FS.Stream) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then
    return 0
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    mcpLoop cfg stdin stdout
  else if trimmed.startsWith "Content-Length:" then
    let numStr := ((trimmed.drop 15).toString).trimAscii.toString
    match numStr.toNat? with
    | none => mcpLoop cfg stdin stdout
    | some len =>
        match (← skipHeadersAndReadBody stdin len) with
        | none => return 0
        | some body =>
            if let .ok j := Json.parse body then
              if let some resp ← handleRPC cfg j then
                let outStr := resp.compress
                stdout.putStr s!"Content-Length: {outStr.utf8ByteSize}\r\n\r\n{outStr}"
                stdout.flush
            mcpLoop cfg stdin stdout
  else
    if let .ok j := Json.parse trimmed then
      if let some resp ← handleRPC cfg j then
        stdout.putStr (resp.compress ++ "\n")
        stdout.flush
    mcpLoop cfg stdin stdout

def runMCPServer (cfg : MCPConfig) : IO UInt32 := do
  IO.FS.createDirAll (draftsDir cfg)
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  mcpLoop cfg stdin stdout

end Prism.MCP
