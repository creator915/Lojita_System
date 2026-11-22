import Lean.Data.Json
import Prism.Driver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.MCPServer`: Native Lean 4 Stdio MCP Server for Closed-World Nodes & Open-World Sessions

Provides iterative draft authoring (`write_draft`, `patch_draft`, `read_draft`, `list_drafts`),
Lean 4 Prism type/gate checking (`check_agda`, `check_plan`, `check_spec`, `check_entry`),
and cleanroom `SessionEnv` Agda probe execution (`run_agda_script`) to Codex CLI while keeping
Codex CLI's `shell_tool=false` and `unified_exec=false`.
-/

namespace Prism.MCP

open Lean (Json ToJson toJson)
open Prism

structure NarrowingCertificate where
  kind : String
  witness : String
  cause : String
  detour : String
  deriving Lean.ToJson, Lean.FromJson, BEq, Inhabited

private def NarrowingCertificate.format (c : NarrowingCertificate) : String :=
  s!"[KIND] {c.kind}\n[WITNESS] {c.witness}\n[CAUSE] {c.cause}\n[DETOUR] {c.detour}"

structure MCPConfig : Type where
  -- Created anew for each RPC. The host publishes observations after the pure gates return.
  observations : Option (IO.Ref (Array (String × NarrowingCertificate))) := none
  specCache : Option (IO.Ref (Option (String × List String × CodeMod))) := none
  mode      : String := "node"     -- "node" or "session"
  repoDir   : String := "."
  libDir    : String := ""
  irDir     : String := ""
  dumpBin   : Option String := none
  ctxDir    : String := ""         -- `<isolated>/mcp`
  workspace : String := ""         -- session workspace (for `mode == "session"`)
  refFile   : String := ""         -- path to serialized `RefSpec` S-expr (for `mode == "session"`)
  narrowLog : String := ""         -- optional side-channel JSONL log for narrowing/fallback events

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

private def unsafePath (path : String) : Bool :=
  (path.splitOn ".").any fun part => part == "Unsafe" || part == "TrustMe"

private def unsafeMessage (path : String) : String :=
  s!"sandbox: '{path}' crosses the --safe boundary. TrustMe and *.Unsafe modules are forbidden under --safe. If your parent SPECIFICATION implies an unprovable primitive law such as primStringEquality reflexivity, prove Context.Taboo.SafeTaboo and submit (submission (kind independent) (refute @unprovable))."

-- Match Meta.Boundary.validPart before Agda resolves imports as filenames.
private def validModulePath (path : String) : Bool :=
  (path.splitOn ".").all fun part => !part.isEmpty && part.toList.all fun c =>
    !AgdaMirror.CharClass.space c && c.toNat >= 32 && c != '/' && c != '\\'

#guard validModulePath "Gen.T2.Δ-safe.UnsafeLooking"
#guard !validModulePath "Separate/Components"
#guard !validModulePath "Separate\\Components"
#guard !validModulePath "Empty..Component"
#guard !validModulePath "White Space"
#guard !validModulePath "Control\nCharacter"

private def checkObjectBoundary (allowEntry : Bool) (modName : String) (imps : List String) : Option (String × String) :=
  let mParts := modName.splitOn "."
  let mTop := mParts.headD ""
  let okSelf :=
    if allowEntry && modName == "Main" then true
    else !mParts.isEmpty && !reservedTopPrefixes.contains mTop
  if let some path := (modName :: imps).find? unsafePath then
    some (path, unsafeMessage path)
  else if let some path := (modName :: imps).find? (fun path => !validModulePath path) then
    some (path, s!"sandbox: invalid module path '{path}'")
  else if !okSelf then
    some (modName, s!"sandbox: forbidden module name '{modName}'")
  else
    let badImp := imps.find? fun imp =>
      let iParts := imp.splitOn "."
      let iTop := iParts.headD ""
      if allowEntry && (imp == "OwnershipIO.WorldRunner" || imp == "OwnershipIO.FFI") then false
      else iParts.isEmpty || reservedTopPrefixes.contains iTop
    match badImp with
    | some bi => some (bi, s!"sandbox: forbidden import '{bi}' in '{modName}'")
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
        errs := errs ++ [s!"forbidden host FFI primitive '{badSym}' in build-exe (use OwnershipIO.WorldRunner instead of shelling out)"]
  errs

private def checkSpecEnvelope (cm : CodeMod) : List String := Id.run do
  let mut errs : List String := []
  let allowedFlags := ["--safe", "--without-K"]
  let fnNames := cm.decls.filterMap fun | .fun_ _ fn _ => some fn | _ => none
  for d in cm.decls do
    match d with
    | .pragma p =>
        if p.startsWith "OPTIONS" then
          let opts := ((p.drop 7).toString).splitOn " " |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
          for fl in opts do
            if !allowedFlags.contains fl then
              errs := errs ++ [s!"flagEnvelopeViolation: forbidden pragma option '{fl}' in specification"]
        else
          errs := errs ++ [s!"forbidden pragma '{p}' in specification"]
    | .unsupported u =>
        errs := errs ++ [s!"unsupported / FFI construct '{u}' is forbidden in specification"]
    | .sig ms nm _ =>
        if ms.termCheck != .check then
          errs := errs ++ [s!"termination bypass on '{nm}' is forbidden in specification"]
        if nm == "_" && !fnNames.contains "_" then
          errs := errs ++ ["spec: anonymous '_' declarations must include a definition body (e.g. '_ = refl'); give postulated obligations an explicit name"]
    | .fun_ ms nm _ =>
        if ms.termCheck != .check then
          errs := errs ++ [s!"termination bypass on '{nm}' is forbidden in specification"]
    | _ => pure ()
  let renderedSexp := renderTopSExpr (encodeCodeMod cm)
  if hasSubstr renderedSexp "(hole)" then
    errs := errs ++ ["unsolved interaction hole '{!!}' / '?' is forbidden"]
  errs

private def appendNarrowEvent (cfg : MCPConfig) (kind modName detail : String)
    (cert : Option NarrowingCertificate := none) : IO Unit := do
  if cfg.narrowLog.isEmpty then
    return ()
  try
    let tsMs ← IO.monoMsNow
    let shortDetail := String.ofList (detail.toList.take 600)
    let event := Json.mkObj
      [ ("tsMs",   toJson tsMs)
      , ("source", Json.str "mcp")
      , ("kind",   Json.str kind)
      , ("module", Json.str modName)
      , ("detail", Json.str shortDetail) ]
    let entry := (cert.map (fun c => (event.setObjVal! "certificate" (toJson c)).mergeObj (Json.mkObj [("witness", toJson c.witness), ("cause", toJson c.cause), ("detour", toJson c.detour)])) |>.getD event).compress ++ "\n"
    if let some parent := (System.FilePath.mk cfg.narrowLog).parent then
      IO.FS.createDirAll parent
    let h ← IO.FS.Handle.mk cfg.narrowLog .append
    h.lock
    try
      h.write entry.toUTF8
      h.flush
    finally h.unlock
  catch _ =>
    pure ()

private def observe (cfg : MCPConfig) (modName : String) (cert : NarrowingCertificate) : IO Unit :=
  match cfg.observations with
  | some ref => ref.modify fun seen =>
      if seen.contains (modName, cert) then seen else seen.push (modName, cert)
  | none => pure ()

private def observeSplitFailure (cfg : MCPConfig) (main : String) (deps : List (SourceUnit × CodeMod))
    (reason : String) : IO Unit := do
  let names := main :: deps.map (fun dep => dep.1.modName)
  let moduleName := (names.find? (fun n => reason.startsWith (n ++ ": "))).getD main
  let cause := s!"Prism could not construct a checked SweetMod/ExoMod split. {reason}"
  let remedy := if reason.contains "--without-K" then
    "Keep --without-K. Submit the ordinary plan for authoritative Agda verification, or isolate the Agda-specific code in a child module with a --safe interface."
    else "Isolate the reported construct or import in an Agda-checked child and expose a --safe interface. Recheck the new plan and its module boundaries."
  observe cfg moduleName ⟨"exo_residual_error", moduleName, cause, remedy⟩

private def unsafeCertificate (path cause : String) : NarrowingCertificate :=
  ⟨"unsafe_module", path, cause,
    "Use a permitted --safe import. If the parent assumptions imply a SafeTaboo principle, submit (kind independent) with a proof from Context.Taboo."⟩

private def checkBoundary (cfg : MCPConfig) (allowEntry : Bool) (modName : String)
    (imps : List String) : IO (Option String) := do
  let some (path, err) := checkObjectBoundary allowEntry modName imps | return none
  observe cfg modName (unsafeCertificate path err)
  return some err

-- A primitive occurring in a larger law is an independence hint. A certificate
-- requires the actual open principle, with a single universally bound variable.
private def primitiveTaboo? (law : String) (ty : Expr) : Option NarrowingCertificate := do
  let .pi (.bind _ [bound] domain) (.app (.app (.def_ eq) left) right) := ty | none
  guard (eq.full == ["Agda","Builtin","Equality","_≡_"])
  let endpoint (lhs rhs : Expr) : Option (List String × String × String) := do
    match lhs, rhs with
    | .app (.app (.def_ prim) ⟨_, _, .var a⟩) ⟨_, _, .var b⟩, .con tru =>
        guard (a == bound && b == bound && tru.full == ["Agda","Builtin","Bool","Bool","true"])
        let primitiveDomain := match prim.full with
          | ["Agda","Builtin","String","primStringEquality"] => ["Agda","Builtin","String","String"]
          | ["Agda","Builtin","Char","primCharEquality"] => ["Agda","Builtin","Char","Char"]
          | _ => []
        guard (!primitiveDomain.isEmpty && (match domain with
          | .meta_ => true | .def_ q => q.full == primitiveDomain | _ => false))
        return (prim.full, "Primitive equality on the open variable does not reduce to true in --safe Agda.",
          "Use a constructive comparison such as Context.Tools.FsSandbox.eqStr or Data.Char.Properties._≟_, or derive the corresponding Context.Taboo.SafeTaboo witness from the specification.")
    | .app (.def_ outer) ⟨_, _, .app (.def_ inner) ⟨_, _, .var x⟩⟩, .var y =>
        guard (x == bound && y == bound)
        let toList := ["Agda","Builtin","String","primStringToList"]
        let fromList := ["Agda","Builtin","String","primStringFromList"]
        guard ((outer.full == toList && inner.full == fromList) || (outer.full == fromList && inner.full == toList))
        let str := ["Agda","Builtin","String","String"]
        let validDomain : Bool := match domain with
          | .meta_ => true
          | .def_ q => outer.full == fromList && q.full == str
          | .app (.def_ l) ⟨_, _, .def_ c⟩ =>
            outer.full == toList && l.full == ["Agda","Builtin","List","List"] && c.full == ["Agda","Builtin","Char","Char"]
          | _ => false
        guard validDomain
        return (outer.full, "The primitive String/List conversions compose on literals, but the roundtrip on this open variable does not reduce in --safe Agda.",
          "Keep one representation across the interface or derive the matching Context.Taboo roundtrip constructor from the specification and submit (kind independent).")
    | _, _ => none
  let (symbol, cause, detour) ← endpoint left.thing right.thing <|> endpoint right.thing left.thing
  return ⟨"primitive_taboo", String.intercalate "." symbol, law ++ ": " ++ cause, detour⟩

private partial def primitiveCertificates (scope : List String) (decls : List Decl)
    (failure : Option String := none) : List NarrowingCertificate :=
  let defs := decls.filterMap fun | .fun_ _ name _ => some name | _ => none
  decls.flatMap fun
    | .module_ name _ inner => primitiveCertificates (scope ++ [name]) inner failure
    | .sig _ name ty =>
        let law := String.intercalate "." (scope ++ [name])
        let relevant := match failure with
          | none => !defs.contains name
          | some message => message.startsWith ("LEAN_TYPE_ERROR:\n" ++ law ++ ":")
        if relevant then (primitiveTaboo? law ty).toList else []
    | _ => []

private partial def primitiveHint (decls : List Decl) : Bool :=
  let defs := decls.filterMap fun | .fun_ _ name _ => some name | _ => none
  decls.any fun
    | .module_ _ _ inner => primitiveHint inner
    | .sig _ name ty =>
        let refs := collectExprQNames ty
        !defs.contains name && refs.contains ["Agda","Builtin","Equality","_≡_"] &&
          (refs.contains ["Agda","Builtin","String","primStringEquality"] ||
           refs.contains ["Agda","Builtin","Char","primCharEquality"])
    | _ => false

private def checkUnsafeReferences (cfg : MCPConfig) (cm : CodeMod) : IO (Option String) := do
  let refs := cm.params.flatMap collectBindQNames ++ cm.decls.flatMap collectDeclQNames
  if let some path := refs.find? (fun p => p.contains "TrustMe" || p.contains "Unsafe") then
    let name := String.intercalate "." path
    let err := unsafeMessage name
    observe cfg (fullDot cm.modName) (unsafeCertificate name err)
    return some err
  return none

private def mcpUnitLabel (u : ModUnit) : String :=
  match u.kind with
  | .dataUnit nm _ _ _ _    => nm
  | .recUnit nm _ _ _ _ _   => nm
  | .patSynUnit nm _ _ _    => nm
  | .postulateUnit _ nm _   => nm
  | .funUnit _ nm _ _       => nm
  | .anonUnit idx _ _       => s!"_#{idx}"

private def formatSliceSummary (plan : SlicePlan) : String :=
  let fastCnt := plan.fastUnitIds.length
  let slowNames := plan.units.filter (fun u => plan.slowUnitIds.contains u.uid) |>.map mcpUnitLabel
  if slowNames.isEmpty then
    s!"[Lens: {fastCnt} FastFocus units verified in Lean 4, 0 SlowSlice units]"
  else
    let preview := String.intercalate ", " (slowNames.take 8) ++ (if slowNames.length > 8 then ", ..." else "")
    s!"[Lens: {fastCnt} FastFocus units in Lean 4, {slowNames.length} SlowSlice units in Agda ({preview})]"

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

private def sourceHeader (cfg : MCPConfig) (path src : String) : IO (Except String SourceUnit) := do
  match ← inspectSources cfg.libDir cfg.dumpBin [(path, src)] with
  | .ok [unit] =>
      if unit.modName == "_" then return .error "a named Agda module is required"
      return .ok unit
  | .ok _ => return .error "missing Agda module header"
  | .error e => return .error e

private def writeModuleToWork (cfg : MCPConfig) (workDir : String) (src : String) : IO (Except String (String × List String × String)) := do
  match ← sourceHeader cfg "<draft>" src with
  | .error e => return .error s!"SYNTAX_ERROR: {e}"
  | .ok u =>
      let parts := u.modName.splitOn "."
      if parts.any (fun p => p.isEmpty || p.toList.any (fun c => c == '/' || c == '\\' || c.toNat < 32)) then
        return .error s!"sandbox: invalid module name '{u.modName}'"
      let relDir := String.intercalate "/" parts.dropLast
      IO.FS.createDirAll s!"{workDir}/{relDir}"
      let fullPath := s!"{workDir}/{String.intercalate "/" parts}.agda"
      IO.FS.writeFile fullPath src
      return .ok (u.modName, u.imports, fullPath)

private def runGateEngine (cfg : MCPConfig) (args : Array String) : IO (Except String String) := do
  let exe := s!"{cfg.repoDir}/runtime/lean-prism/.lake/build/bin/harness-engine"
  if !(← System.FilePath.pathExists exe) then
    return .error "harness-engine is missing; rebuild with ./build.sh"
  let (code, out, err) ← runSubproc exe args
  if code == 0 then return .ok out.trimAscii.toString
  return .error s!"harness-engine {args[0]?.getD ""} failed ({code}): {err}{out}"

private def gateJson (cfg : MCPConfig) (args : Array String) : IO Json := do
  match ← runGateEngine cfg args with
  | .error e => throw (IO.userError e)
  | .ok text => IO.ofExcept (Json.parse text)

private def readGateReport (cfg : MCPConfig) (modName : String) (report : Json) : IO (Bool × String) := do
  let ok ← IO.ofExcept (report.getObjValAs? Bool "ok")
  let diagnostics ← IO.ofExcept (report.getObjValAs? (List String) "diagnostics")
  let certs ← IO.ofExcept (report.getObjValAs? (List NarrowingCertificate) "certificates")
  for cert in certs do observe cfg modName cert
  return (ok, String.intercalate "\n" diagnostics)

private def extractSpecFromPromptText (promptTxt : String) : Option String :=
  let parts := promptTxt.splitOn "\nSPECIFICATION\n"
  match parts.drop 1 |>.getLast? with
  | none => none
  | some afterSpec =>
      match (afterSpec.splitOn "\nREFUTATION EXTRA POSTULATES").head? with
      | none => none
      | some specBlk =>
          let trimmed := specBlk.trimAscii.toString
          if !trimmed.isEmpty then some specBlk else none

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

private def writeGateInput (workDir stem : String) (cm : CodeMod) : IO String := do
  IO.FS.createDirAll workDir
  let path := s!"{workDir}/{stem}.sexp"
  IO.FS.writeFile path (renderTopSExpr (encodeCodeMod cm))
  return path

private structure NodeSpec where
  name : String
  src  : String

private def readNodePrompt (cfg : MCPConfig) : IO (Option NodeSpec × List String) := do
  let path := s!"{cfg.ctxDir}/node-prompt.txt"
  if !(← System.FilePath.pathExists path) then return (none, [])
  let prompt := ((← IO.FS.readFile path).splitOn "\nTRANSIENT DIAGNOSTIC\n").headD ""
  let flags := match (prompt.splitOn "\nPARENT FLAGS\n").drop 1 |>.getLast? with
    | none => []
    | some rest => (((rest.splitOn "\nLOCKED SEEDS\n").headD "").splitOn "\n").filter (!·.isEmpty)
  let some src := extractSpecFromPromptText prompt | return (none, flags)
  let .ok hdr ← sourceHeader cfg "<SPECIFICATION>" src | return (none, flags)
  return (some ⟨hdr.modName, src⟩, flags)

-- SPECIFICATION renders the entire newIface, including anonymous test bodies.
-- refuteStubOf recomputes the extra postulates and fresh names from those exact
-- declarations, so adding the displayed REFUTATION EXTRA POSTULATES again
-- would duplicate them.
private def specGateInput (cfg : MCPConfig) (workDir : String)
    (ancPaths : List String) (spec : NodeSpec) : IO (Except String String) := do
  let ancestors ← ancPaths.mapM (fun (path : String) => IO.FS.readFile path)
  if let some ref := cfg.specCache then
    if let some (source, previous, code) ← ref.get then
      if source == spec.src && previous == ancestors then
        return .ok (← writeGateInput workDir "spec" code)
  let specDir := s!"{workDir}/spec_prompt"
  match ← writeModuleToWork cfg specDir spec.src with
  | .error e => return .error e
  | .ok (_, _, path) =>
      match ← dumpSurfaceBundle ancPaths path cfg.libDir s!"{workDir}/spec_parse" cfg.dumpBin with
      | .ok (deps, main) =>
          for (unit, _) in main :: deps do
            if let some e ← checkBoundary cfg false unit.modName unit.imports then return .error e
          if let some ref := cfg.specCache then ref.set (some (spec.src, ancestors, main.2))
          return .ok (← writeGateInput workDir "spec" main.2)
      | .error e => return .error e

-- The checked specification belongs to this MCP session. Verify the exact
-- authored bytes (including the ancestor closure) before reusing its Code.
private def preloadSpec (cfg : MCPConfig) : IO Unit := do
  if cfg.mode != "node" then return
  let (spec?, _) ← readNodePrompt cfg
  if let some spec := spec? then
    let ancestors ← listAgdaFilesBelow s!"{cfg.ctxDir}/ancestors"
    IO.FS.withTempDir fun dir => do
      discard <| specGateInput cfg dir.toString ancestors spec

private def onlyAncestorImports (report : String) (bases : List CodeMod) : Bool :=
  match report.splitOn "\n" with
  | "REFUTE_GATE_ERROR" :: problems@(_ :: _) => problems.all fun line =>
      match parseSExprText line with
      | some (.list [.sym "unauthorizedImport", name]) =>
          (decQ name).any fun q => bases.any fun b => b.modName.full.isPrefixOf q.full
      | _ => false
  | _ => false

private def declaresBottom (cand : CodeMod) : Bool :=
  cand.params.isEmpty && cand.decls.any fun
    | .sig m n (.def_ q) => !m.isPrivate && n != "_" &&
        [["Data", "Empty", "⊥"], ["Agda", "Builtin", "Empty", "⊥"]].contains q.full
    | _ => false

private def checkLiftWitness (cfg : MCPConfig) (workDir spec : String) (flags : List String)
    (bases : List CodeMod) (cand : CodeMod) : IO (Except String (Option String)) := do
  let bundle := SExpr.list (.sym "bundle" :: bases.map encodeCodeMod ++ [encodeCodeMod cand])
  let file := s!"{workDir}/lift-refute.sexp"
  IO.FS.writeFile file (renderTopSExpr bundle)
  match ← runGateEngine cfg (#["check-lift-refute", spec, file] ++ flags.toArray) with
  | .ok report =>
      if (report.splitOn "\n").head? == some "OK:liftObstruction" then return .ok (some "refute-lift")
      return .error report
  | .error e => return .error e

private def verifyDraftGates (cfg : MCPConfig) (workDir role : String) (flags : List String)
    (cand : CodeMod) (refuteSpec ifaceFile : Option String) (ancestors : List CodeMod)
    (explicitLift : Bool) (modelMod : Option CodeMod := none) (isModelBundle : Bool := false) :
    IO (Except String (Option String)) := do
  if explicitLift then
    let some spec := refuteSpec | return .error "REFUTE_GATE_ERROR\nmissing node SPECIFICATION"
    return ← checkLiftWitness cfg workDir spec flags ancestors cand
  let file ← writeGateInput workDir "candidate" cand
  if isModelBundle then
    match ← runGateEngine cfg (#["check-countermodel", file] ++ flags.toArray) with
    | .ok "OK:countermodel-bundle" => return .ok (some "countermodel-bundle")
    | .ok e => return .error e
    | .error e => return .error e
  if let some specName := refuteSpec then
    let gateFile ← match modelMod with
      | some m => do
          let p := s!"{workDir}/refute-bundle.sexp"
          IO.FS.writeFile p (renderTopSExpr (.list (.sym "bundle" :: (ancestors ++ [m, cand]).map encodeCodeMod)))
          pure p
      | none =>
          if ancestors.isEmpty || declaresBottom cand then pure file else do
            let p := s!"{workDir}/refute-bundle.sexp"
            IO.FS.writeFile p (renderTopSExpr (.list (.sym "bundle" :: (ancestors ++ [cand]).map encodeCodeMod)))
            pure p
    let hint := "\nExpose a closed, public proof of Data.Empty.⊥, Context.Taboo.SafeTaboo, or CountermodelCheck.VerifiedClaim."
    match ← runGateEngine cfg (#["check-refute", specName, gateFile] ++ flags.toArray) with
    | .ok "OK:contradiction" => return .ok (some "contradiction")
    | .ok "OK:independent" => return .ok (some "independent")
    | .ok "OK:countermodel" => return .ok (some "countermodel")
    | .ok e =>
        if declaresBottom cand && onlyAncestorImports e ancestors then
          return ← checkLiftWitness cfg workDir specName flags ancestors cand
        return .error (e ++ hint)
    | .error e => return .error (e ++ hint)
  let obj ← gateJson cfg (#["check-object-json", role, file] ++ flags.toArray)
  let (ok, errors) ← readGateReport cfg (fullDot cand.modName) obj
  if !ok then
    return .error errors
  if let some sf := ifaceFile then
    let report ← gateJson cfg #["check-interface-json", sf, file]
    let (ifaceOK, detail) ← readGateReport cfg (fullDot cand.modName) report
    if !ifaceOK then
      return .error ("SPECIFICATION_INTERFACE_MISMATCH (outer `satisfies` gate):\n" ++ detail)
  return .ok none

private def checkStagedDraft (cfg : MCPConfig) (workDir mainPath modName role : String)
    (deps flags : List String) (refuteSpec ifaceFile : Option String)
    (ancestorPaths : List String := []) (explicitLift : Bool := false)
    (modelPath : Option String := none) (isModelBundle : Bool := false) : IO Json := do
  let (depPoints, mainPoint) ← match ← dumpSurfaceBundle deps mainPath cfg.libDir s!"{workDir}/parse" cfg.dumpBin with
    | .ok bundle => pure bundle
    | .error e => return mkToolResult s!"SCOPE_GATE_ERROR:\n{e}" true
  for (unit, _) in mainPoint :: depPoints do
    if let some err ← checkBoundary cfg false unit.modName unit.imports then return mkToolResult err true
  let cm := mainPoint.2
  if let some err ← checkUnsafeReferences cfg cm then return mkToolResult err true
  let closed := role == "closed"
  let envErrs := if closed then checkClosedNoPostulatesOrHoles false cm else checkSpecEnvelope cm
  if !envErrs.isEmpty then
    return mkToolResult ((if closed then "CLOSED_IMPL_VIOLATION" else "SPEC_ENVELOPE_VIOLATION") ++ ":\n" ++ String.intercalate "\n" envErrs) true
  let laws := primitiveCertificates cm.modName.full cm.decls
  for law in laws do observe cfg modName law
  let bases := depPoints.filterMap fun (u, c) => if ancestorPaths.contains u.path then some c else none
  let modelMod := modelPath.bind fun mp => depPoints.findSome? fun (u, c) => if u.path == mp then some c else none
  let verdict ← match ← verifyDraftGates cfg workDir role flags cm refuteSpec ifaceFile bases explicitLift modelMod isModelBundle with
    | .error e => return mkToolResult e true
    | .ok v => pure v
  let hint := if !closed && (primitiveHint cm.decls || !laws.isEmpty) then
    "\n[SAFE_INDEPENDENCE_HINT] Primitive comparison computes on literals. Check whether the assumptions imply open-variable reflexivity. If so, derive Context.Taboo.SafeTaboo or submit (kind countermodel), or use a constructive comparison such as Context.Tools.FsSandbox.eqStr."
    else ""
  let isIndep := verdict == some "independent" || verdict == some "countermodel"
  let unsupported (reason : String) : IO Json := do
    if isIndep then
      let msg := s!"independence requires a scope-checked, kernel-audited witness. Rewrite the proof using FastFocus-supported syntax and run check_agda again:\n{reason}"
      appendNarrowEvent cfg "independence_prism_required" modName msg
      return mkToolResult msg true
    appendNarrowEvent cfg "prism_unsupported" modName reason
    return mkToolResult s!"Prism could not construct a checked slice for '{modName}': {reason}" true
  let (slicedDeps, sm) ← match sliceCodeBundle depPoints mainPoint with
    | .translated inputs => pure inputs
    | .syntaxErr e => return mkToolResult s!"SYNTAX_ERROR:\n{e}" true
    | .bot reason =>
        observeSplitFailure cfg modName depPoints reason
        return ← unsupported reason
  let slice := sm.plan
  let slow := slice.units.filter (fun u => slice.slowUnitIds.contains u.uid) |>.map mcpUnitLabel
  if !slow.isEmpty then appendNarrowEvent cfg "prism_slow_slice" modName (String.intercalate ", " slow)
  let sliceInfo := formatSliceSummary slice
  let (code, msg) ← checkSlicedBundle cfg.libDir s!"{workDir}/lean" slicedDeps sm
    (if isIndep then refuteSpec else none)
  if code == exitOK then
    let label := if role == "spec" then "specification " else ""
    let witness := verdict.map (fun k => s!" [witness: {k}]") |>.getD ""
    return mkToolResult s!"OK: {label}'{modName}' passed Lean 4 Prism kernel typecheck + interface gates {sliceInfo}{witness}{hint}"
  if code == exitBot then
    return ← unsupported msg
  if msg.contains "INDEPENDENCE_AXIOM_ERROR" then
    appendNarrowEvent cfg "independence_axiom" modName msg
  if msg.startsWith "AGDA_SLICE_ERROR (" then
    -- The residual verifier reports the failing module, which may be upstream.
    let name := (((msg.drop "AGDA_SLICE_ERROR (".length).toString.splitOn "):").headD modName)
    let sm? := (sm :: slicedDeps).find? (fun m => m.srcUnit.modName == name)
    let exotics := sm?.map (fun m => m.plan.units.filter (fun u => m.plan.slowUnitIds.contains u.uid) |>.map mcpUnitLabel) |>.getD []
    let target := match exotics with
      | [unit] => name ++ "." ++ unit
      | _ => name
    let rel := (String.intercalate "/" (name.splitOn ".")) ++ ".agda:"
    let cause := match (msg.splitOn rel).drop 1 with
      | [] => String.intercalate "\n" ((msg.splitOn "\n").drop 1)
      | loc :: _ => rel ++ loc
    observe cfg name ⟨"exo_residual_error", target, cause,
      "Check the named ExoMod residual against the shared base. Repair the rejected Agda body or give it an explicit structural recursion."⟩
  else if closed then
    for law in primitiveCertificates cm.modName.full cm.decls (some msg) do observe cfg modName law
  return mkToolResult s!"{msg}\n{sliceInfo}" true

private def checkAgdaNode (cfg : MCPConfig) (args : Json) (workDir : String) : IO Json := do
  let some raw := jsonStrField args "main_block" | return mkToolResult "error: check_agda requires 'main_block'" true
  let mainSrc ← match ← resolveBlockOrInline cfg raw with
    | .error e => return mkToolResult e true
    | .ok src => pure src
  let srcDir := s!"{workDir}/src"
  let allowPost := jsonBoolField args "allow_postulates" false
  let explicitLift := jsonBoolField args "refute_lift" false || jsonStrField args "role" == some "refute-lift"
  let witnessRequested := explicitLift || jsonBoolField args "refute_spec" false
  let (spec, flags) ← readNodePrompt cfg
  if witnessRequested && (allowPost || spec.isNone) then
    return mkToolResult "REFUTE_GATE_ERROR\na witness requires the node SPECIFICATION and allow_postulates=false" true
  let hdr ← match ← sourceHeader cfg "<main>" mainSrc with
    | .error e => return mkToolResult s!"SYNTAX_ERROR: {e}" true
    | .ok u => pure u
  if let some err ← checkBoundary cfg false hdr.modName hdr.imports then return mkToolResult err true
  let usesBridge := !allowPost && hdr.imports.contains "CountermodelCheck"
  let isModelBundle := !allowPost && !usesBridge && hdr.imports.contains "Countermodel" &&
    spec.all (fun s => hdr.modName != s.name && !hdr.imports.contains s.name)
  let refuteSpec := spec.filter fun s => !allowPost && (witnessRequested || usesBridge || (hdr.modName != s.name && hdr.imports.contains s.name))
  if usesBridge && refuteSpec.isNone then
    return mkToolResult "REFUTE_GATE_ERROR\nCountermodelCheck requires node SPECIFICATION and allow_postulates=false" true
  if refuteSpec.any (fun s => s.name == hdr.modName) then
    return mkToolResult "REFUTE_GATE_ERROR\nwitness module shadows SPECIFICATION" true
  let mut deps : List String := []
  for af in ← listAgdaFilesBelow s!"{cfg.ctxDir}/ancestors" do
    match ← writeModuleToWork cfg srcDir (← IO.FS.readFile af) with
    | .error e => return mkToolResult e true
    | .ok (name, _, fp) =>
        if refuteSpec.isSome && name == hdr.modName then
          return mkToolResult s!"REFUTE_GATE_ERROR\nwitness module shadows ancestor {name}" true
        deps := deps ++ [fp]
  let ancestorPaths := deps
  let mut modelPath : Option String := none
  if isModelBundle || usesBridge then
    let cmLibSrc ← match ← runGateEngine cfg #["countermodel-lib"] with
      | .ok s => pure s
      | .error e => return mkToolResult s!"REFUTE_GATE_ERROR: {e}" true
    let cmLibPath ← match ← writeModuleToWork cfg srcDir cmLibSrc with
      | .ok (_, _, p) => pure p
      | .error e => return mkToolResult s!"REFUTE_GATE_ERROR: {e}" true
    deps := deps ++ [cmLibPath]
    if usesBridge then
      let rawModel? := (jsonStrField args "model_block").orElse fun _ =>
        match jsonStrArrayField args "dep_blocks" with
        | [m] => some m
        | _ => none
      let some rawModel := rawModel?
        | return mkToolResult "REFUTE_GATE_ERROR\nCountermodelCheck witness requires 'model_block' (or single @model in 'dep_blocks')" true
      let modelSrc ← match ← resolveBlockOrInline cfg rawModel with
        | .ok s => pure s
        | .error e => return mkToolResult e true
      let mPath ← match ← writeModuleToWork cfg srcDir modelSrc with
        | .ok (mName, mImps, p) =>
            if let some err ← checkBoundary cfg false mName mImps then return mkToolResult err true
            pure p
        | .error e => return mkToolResult e true
      let (_, (_, modelCode)) ← match ← dumpSurfaceBundle [cmLibPath] mPath cfg.libDir s!"{workDir}/model_parse" cfg.dumpBin with
        | .ok b => pure b
        | .error e => return mkToolResult s!"SCOPE_GATE_ERROR (@model):\n{e}" true
      let modelGateFile ← writeGateInput workDir "model" modelCode
      let bridgeSrc ← match ← runGateEngine cfg (#["countermodel-bridge", modelGateFile] ++ flags.toArray) with
        | .ok s => pure s
        | .error e => return mkToolResult e true
      let bPath ← match ← writeModuleToWork cfg srcDir bridgeSrc with
        | .ok (_, _, p) => pure p
        | .error e => return mkToolResult s!"REFUTE_GATE_ERROR: {e}" true
      deps := deps ++ [mPath, bPath]
      modelPath := some mPath
  let mut ifaceFile : Option String := none
  if let some s := spec then
    if refuteSpec.isSome || (!allowPost && hdr.modName == s.name) then
      match ← specGateInput cfg workDir ancestorPaths s with
      | .error e => return mkToolResult s!"SPECIFICATION_GATE_ERROR: {e}" true
      | .ok sf =>
          if refuteSpec.isSome then
            match ← runGateEngine cfg #["refute-stub", sf] with
            | .error e => return mkToolResult e true
            | .ok stub =>
                match ← writeModuleToWork cfg srcDir stub with
                | .ok (name, _, path) =>
                    if name != s.name then return mkToolResult "REFUTE_GATE_ERROR: stub module mismatch" true
                    deps := deps ++ [path]
                | .error e => return mkToolResult s!"REFUTE_GATE_ERROR: {e}" true
          else
            ifaceFile := some sf
  -- A witness is checked against the actual task assumptions even if a caller
  -- supplied an alternative spec or a forged Context module in dep_blocks.
  if refuteSpec.isNone && !isModelBundle then
    for da in jsonStrArrayField args "dep_blocks" do
      match ← resolveBlockOrInline cfg da with
      | .error e => return mkToolResult e true
      | .ok txt =>
          match ← writeModuleToWork cfg srcDir txt with
          | .error e => return mkToolResult e true
          | .ok (name, imps, path) =>
              if let some err ← checkBoundary cfg false name imps then return mkToolResult err true
              deps := deps ++ [path]
  match ← writeModuleToWork cfg srcDir mainSrc with
  | .error e => return mkToolResult e true
  | .ok (name, _, path) =>
      let role := if allowPost then "subspec" else "closed"
      checkStagedDraft cfg workDir path name role ((deps.filter (· != path)).eraseDups)
        flags (refuteSpec.map (·.name)) ifaceFile ancestorPaths explicitLift modelPath isModelBundle

private def handleCheckAgdaNode (cfg : MCPConfig) (args : Json) : IO Json := do
  let workDir := s!"{cfg.ctxDir}/check_{← IO.monoNanosNow}"
  try checkAgdaNode cfg args workDir finally
    if ← System.FilePath.pathExists workDir then IO.FS.removeDirAll workDir

-- Resolve saved blocks using the same fenced-source convention as the node's
-- final submission. The native submission decoder validates the complete envelope.
private def attachPlanDrafts (cfg : MCPConfig) (submission : String) : IO String := do
  if !(← System.FilePath.pathExists (draftsDir cfg)) then return submission
  let mut result := submission
  for entry in ← System.FilePath.readDir (draftsDir cfg) do
    let name := (entry.fileName.dropEnd 6).toString
    if entry.fileName.endsWith ".block" && safeDraftName name &&
        submission.contains ("@" ++ name) && !submission.contains ("```agda " ++ name ++ "\n") then
      result := result ++ "\n```agda " ++ name ++ "\n" ++ (← IO.FS.readFile entry.path) ++ "\n```\n"
  return result

private def planSubmission (cfg : MCPConfig) (args : Json) : IO String := do
  let fields ← IO.ofExcept args.getObj?
  for (key, _) in fields.toList do
    if !["submission", "main", "moves", "subspecs", "lift"].contains key then
      throw (IO.userError s!"unknown check_plan input '{key}'")
  if let .ok value := args.getObjVal? "submission" then
    let wire ← IO.ofExcept value.getStr?
    if ["main", "moves", "subspecs"].any (fun k => (args.getObjVal? k).isOk) then
      throw (IO.userError "provide either submission or main/moves/subspecs")
    return ← attachPlanDrafts cfg wire
  let raw ← IO.ofExcept (args.getObjValAs? String "main")
  let main ← IO.ofExcept (← resolveBlockOrInline cfg raw)
  let ms ← IO.ofExcept (args.getObjValAs? String "moves")
  let some (moves@(.list (.sym "moves" :: _))) := parseSExprText ms
    | throw (IO.userError "moves must be a complete (moves ...) expression")
  let mut subs := []
  if let .ok supplied := args.getObjVal? "subspecs" then
    for (key, value) in (← IO.ofExcept supplied.getObj?).toList do
      let text ← IO.ofExcept value.getStr?
      let src ← IO.ofExcept (← resolveBlockOrInline cfg text)
      subs := subs ++ [.list [.str key, .str src]]
  return renderSExpr (.list [.sym "submission", .list [.sym "kind", .sym "plan"],
    .list [.sym "why", .str "preview"], .list [.sym "main", .str main], moves, .list (.sym "subspecs" :: subs)])

private def namedSources (value : Json) : IO (List (String × String)) := do
  let entries ← IO.ofExcept value.getArr?
  entries.toList.mapM fun item => do
    let .arr #[.str name, .str source] := item | throw (IO.userError "invalid engine source entry")
    return (name, source)

private def stagePreviewSource (cfg : MCPConfig) (dir : String) (src : String)
    (key : Option String := none) : IO (String × String) := do
  let unit ← IO.ofExcept (← sourceHeader cfg "<preview>" src)
  if let some problem ← checkBoundary cfg false unit.modName unit.imports then throw (IO.userError problem)
  if let some expected := key then
    if expected != unit.modName then throw (IO.userError s!"module '{unit.modName}' differs from key '{expected}'")
  let path := System.FilePath.mk dir / ((String.intercalate "/" (unit.modName.splitOn ".")) ++ ".agda")
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path src
  return (unit.modName, path.toString)

private def previewDeps (cfg : MCPConfig) (dir context : String) (subsFile : Option String)
    (skip : List String) : IO (List String) := do
  let response ← gateJson cfg (#["plan-deps", context] ++ subsFile.toList.toArray)
  if !jsonBoolField response "ok" true then throw (IO.userError (String.intercalate "\n" (jsonStrArrayField response "diagnostics")))
  let sources ← namedSources response
  let mut staged := []
  for (key, src) in sources do
    if !skip.contains key then staged := staged ++ [← stagePreviewSource cfg dir src (some key)]
  -- Some node harnesses also seal external source directories outside the Code store.
  for file in ← listAgdaFilesBelow s!"{cfg.ctxDir}/ancestors" do
    let src ← IO.FS.readFile file
    let unit ← IO.ofExcept (← sourceHeader cfg "<ancestor>" src)
    if !skip.contains unit.modName && !(staged.map Prod.fst).contains unit.modName then
      staged := staged ++ [← stagePreviewSource cfg dir src]
  return staged.map Prod.snd

private def previewBundle (cfg : MCPConfig) (dir : String) (deps : List String) (path : String) :
    IO ScopedBundle := do
  let bundle ← IO.ofExcept (← dumpSurfaceBundle deps path cfg.libDir dir cfg.dumpBin)
  for (unit, cm) in bundle.2 :: bundle.1 do
    if let some problem ← checkBoundary cfg false unit.modName unit.imports then throw (IO.userError problem)
    if let some problem ← checkUnsafeReferences cfg cm then throw (IO.userError problem)
  return bundle

-- These are the definitions in the two projected modules. A boundary signature
-- is intentionally absent from the list of bodies verified on that side.
private partial def projectionBodies (scope : List String) (ds : List Decl) : List String :=
  (ds.flatMap fun d => match d with
    | .fun_ _ n _ | .dataDef _ n .. | .recDef _ n .. | .patSyn n .. =>
        [String.intercalate "." (scope ++ [n])]
    | .module_ n _ nested => projectionBodies (scope ++ [n]) nested
    | _ => []).eraseDups

private def pushoutSummary (sm : SlicedModule) : Json :=
  let split := pushoutFor sm
  let names (cm : CodeMod) := projectionBodies cm.modName.full cm.decls
  Json.mkObj [("module", toJson sm.srcUnit.modName), ("SweetMod", toJson (names split.leanSliceSpec)),
    ("ExoMod", toJson (split.agdaResidual?.map (fun r => names r.residualCode) |>.getD [])),
    ("hasResidual", toJson split.agdaResidual?.isSome),
    ("M0", Json.mkObj [("module", toJson (fullDot split.sharedBase.modName)),
      ("units", toJson (names split.sharedBase)), ("declarations", toJson split.sharedBase.decls.length),
      ("leanAssumes", toJson (split.boundaryLeanAssumes.map fullDot)),
      ("agdaAssumes", toJson (split.boundaryAgdaAssumes.map fullDot))])]

private def checkPlanNode (cfg : MCPConfig) (args : Json) (tmp : System.FilePath) : IO Json := do
  let context := s!"{cfg.ctxDir}/plan-context.sexp"
  if !(← System.FilePath.pathExists context) then
    throw (IO.userError "check_plan requires this node's mounted plan-context.sexp")
  let envelope := tmp / "submission"
  IO.FS.writeFile envelope (← planSubmission cfg args)
  let decoded ← gateJson cfg #["decode-plan", envelope.toString]
  if !jsonBoolField decoded "ok" true then
    throw (IO.userError (String.intercalate "\n" (jsonStrArrayField decoded "diagnostics")))
  let main ← IO.ofExcept (decoded.getObjValAs? String "main")
  let some moves := parseSExprText (← IO.ofExcept (decoded.getObjValAs? String "moves"))
    | throw (IO.userError "invalid moves in decoded submission")
  let subs ← namedSources (← IO.ofExcept (decoded.getObjVal? "subspecs"))
  let keys := subs.map Prod.fst
  if keys.length != keys.eraseDups.length then throw (IO.userError "duplicate subspec key")
  let (name, path) ← stagePreviewSource cfg (tmp / "main").toString main
  let mut subCodes := []
  if !subs.isEmpty then
    let basePaths ← previewDeps cfg (tmp / "base").toString context none (subs.map Prod.fst)
    for (key, source) in subs do
      let (_, p) ← stagePreviewSource cfg (tmp / "child").toString source (some key)
      let (_, (_, cm)) ← previewBundle cfg tmp.toString basePaths p
      for law in primitiveCertificates cm.modName.full cm.decls do observe cfg key law
      subCodes := subCodes ++ [.list [.str key, encodeCodeMod cm]]
  let subField : SExpr := .list (.sym "subspecs" :: subCodes)
  let subFile := tmp / "subspecs.sexp"
  if !subs.isEmpty then IO.FS.writeFile subFile (renderSExpr subField)
  let deps ← previewDeps cfg (tmp / "ports").toString context
    (if subs.isEmpty then none else some subFile.toString) [name]
  let bundle ← previewBundle cfg tmp.toString deps path
  let mut lift := []
  if let .ok value := args.getObjVal? "lift" then
    let text ← IO.ofExcept value.getStr?
    let some descriptor := parseSExprText text | throw (IO.userError "invalid lift descriptor")
    lift := [descriptor]
  let request : SExpr := .list [.sym "check-plan", moves, encodeCodeMod bundle.2.2,
    subField, .list (.sym "lift" :: lift)]
  let wire := tmp / "request.sexp"
  IO.FS.writeFile wire (renderSExpr request)
  let report ← gateJson cfg #["check-plan", context, wire.toString]
  let (ok, diag) ← readGateReport cfg name report
  -- Routing is a preview of F_chk. A plan with a structural error can still
  -- report both its frontier and the computable portion of its pushout.
  let reportFields ← IO.ofExcept report.getObj?
  let publicReport := Json.obj (reportFields.erase "candidateCode")
  let routed : PrismOutcome (List SlicedModule × SlicedModule) := do
    let some cm := jsonStrField report "candidateCode" >>= parseSExprText >>= decodeCodeMod
      | .syntaxErr "engine did not return the assembled candidate for routing"
    let imports := ((cm.decls.flatMap allImportsInDecl).map fullDot).eraseDups
    let src : SourceUnit := {bundle.2.1 with modName := fullDot cm.modName, imports, point? := none, content := ""}
    sliceCodeBundle bundle.1 (src, cm)
  let (split, route) ← match routed with
    | .translated (_, sm) => pure (pushoutSummary sm, "")
    | .syntaxErr e => pure (Json.null, e)
    | .bot e => do
        observeSplitFailure cfg name bundle.1 e
        pure (Json.null, e)
  let ok := ok && route.isEmpty
  let structured := (publicReport.setObjVal! "ok" (toJson ok)).setObjVal! "pushoutSplitPlan" split
  let structured := if route.isEmpty then structured else
    structured.setObjVal! "diagnostics" (toJson (jsonStrArrayField structured "diagnostics" ++ [route]))
  let status := if ok then "OK: structural plan gates passed." else "PLAN_GATE_ERROR"
  let text := String.intercalate "\n" ([status, diag, route, "PushoutSplitPlan: " ++ split.compress].filter (!·.isEmpty))
  return (mkToolResult text (!ok)).setObjVal! "structuredContent" structured

private def handleCheckPlan (cfg : MCPConfig) (args : Json) : IO Json :=
  IO.FS.withTempDir (checkPlanNode cfg args)

private def checkSpecSession (cfg : MCPConfig) (args : Json) (workDir : String) : IO Json := do
  let some raw := jsonStrField args "spec_block" | return mkToolResult "error: check_spec requires 'spec_block'" true
  let specSrc ← match ← resolveBlockOrInline cfg raw with
    | .error e => return mkToolResult e true
    | .ok src => pure src
  let srcDir := s!"{workDir}/src"
  let mut deps : List String := []
  for t in jsonStrArrayField args "base_trees" do
    if !safeDraftName t then return mkToolResult s!"invalid base tree name '{t}'" true
    for gf in ← listAgdaFilesBelow s!"{cfg.workspace}/generated/{t}" do
      match ← writeModuleToWork cfg srcDir (← IO.FS.readFile gf) with
      | .error e => return mkToolResult e true
      | .ok (_, _, fp) => deps := deps ++ [fp]
  match ← writeModuleToWork cfg srcDir specSrc with
  | .error e => return mkToolResult e true
  | .ok (name, imps, path) =>
      if let some err ← checkBoundary cfg false name imps then return mkToolResult err true
      checkStagedDraft cfg workDir path name "spec" ((deps.filter (· != path)).eraseDups)
        [] none none

private def handleCheckSpecSession (cfg : MCPConfig) (args : Json) : IO Json := do
  let workDir := s!"{cfg.ctxDir}/spec_chk_{← IO.monoNanosNow}"
  try checkSpecSession cfg args workDir finally
    if ← System.FilePath.pathExists workDir then IO.FS.removeDirAll workDir

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
      if let some bErr ← checkBoundary cfg false modName [] then
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
            if let .ok (_, _, fp) ← writeModuleToWork cfg srcDir txt then
              depPaths := depPaths ++ [fp]
          for da in depArgs do
            match (← resolveBlockOrInline cfg da) with
            | .error e =>
                let _ ← runSubproc "rm" #["-rf", workDir] none
                return mkToolResult e true
            | .ok dSrc =>
                match (← writeModuleToWork cfg srcDir dSrc) with
                | .error e =>
                    let _ ← runSubproc "rm" #["-rf", workDir] none
                    return mkToolResult e true
                | .ok (dMod, dImps, dfp) =>
                    if let some bErr ← checkBoundary cfg false dMod dImps then
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
          match (← writeModuleToWork cfg srcDir entrySrc) with
          | .error e =>
              let _ ← runSubproc "rm" #["-rf", workDir] none
              return mkToolResult e true
          | .ok (mMod, mImps, mainPath) =>
              if let some bErr ← checkBoundary cfg true mMod mImps then
                let _ ← runSubproc "rm" #["-rf", workDir] none
                return mkToolResult bErr true
              let dedupDeps := depPaths.filter (· != mainPath) |>.eraseDups
              let parsed ← parseAndSliceBundle dedupDeps mainPath cfg.libDir s!"{workDir}/parse" cfg.dumpBin true
              match parsed with
              | .syntaxErr e =>
                  let _ ← runSubproc "rm" #["-rf", workDir] none
                  return mkToolResult s!"SYNTAX_ERROR:\n{e}" true
              | .bot r =>
                  let _ ← runSubproc "rm" #["-rf", workDir] none
                  return mkToolResult s!"ENTRY_CHECK_ERROR:\n{r}" true
              | .translated (depMods, mainSm) =>
                  for sm in mainSm :: depMods do
                    if let some err ← checkBoundary cfg (sm.srcUnit.modName == "Main") sm.srcUnit.modName sm.srcUnit.imports then
                      return mkToolResult err true
                  if let some err ← checkUnsafeReferences cfg mainSm.codeMod then return mkToolResult err true
                  let closedErrs := checkClosedNoPostulatesOrHoles true mainSm.codeMod
                  if !closedErrs.isEmpty then
                    let _ ← runSubproc "rm" #["-rf", workDir] none
                    return mkToolResult ("ENTRY_GATE_VIOLATION:\n" ++ String.intercalate "\n" closedErrs) true
                  let outTmp := s!"{workDir}/candidate.dryrun"
                  let (code, msg) ← runPrismBuildExe cfg.libDir cfg.irDir s!"{workDir}/lean" outTmp dedupDeps mainPath cfg.dumpBin false (slices := some parsed)
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
          "Typecheck a drive-tree specification draft against optional sealed base_trees and report primitive equality laws that may require a safe independence witness."
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
          "Typecheck a draft and run the closed-world gates. Import your SPECIFICATION to check a contradiction, independence, or lift-obstruction witness against its authoritative stub."
          [ ("main_block", strProp "Draft block name (e.g. 'main') or inline Agda module")
          , ("dep_blocks", strArrProp "Optional list of subspec/dependency draft block names")
          , ("refute_spec", boolProp "Check a witness against the node SPECIFICATION and its staged ancestors")
          , ("refute_lift", boolProp "Require a closed public proof of ⊥ that references a staged ancestor")
          , ("role", strProp "Set to refute-lift to require the lift-obstruction gate")
          , ("allow_postulates", boolProp "Set true only when checking a child subspec; leave false for closed implementations/refutations") ]
          ["main_block"]
      , mkToolSchema "check_plan"
          "Preview the node's structural plan gates and SweetMod/ExoMod pushout. Supply a plan submission, or main and moves. Use check_agda for typechecking."
          [ ("submission", strProp "The (submission (kind plan) ...) envelope with inline source, fences or @drafts")
          , ("main", strProp "Candidate main Agda source or saved draft")
          , ("moves", strProp "Complete (moves ...) S-expression")
          , ("subspecs", Json.mkObj [("type", Json.str "object"),
              ("additionalProperties", strProp "Agda source or saved draft keyed by module name")])
          , ("lift", strProp "Optional lift S-expression for an additional preview check") ]
          []
      ]
  (common ++ specific).toArray

private def dispatchToolCall (cfg : MCPConfig) (toolName : String) (args : Json) : IO Json := do
  if !(toolsForConfig cfg).any (fun t => jsonStrField t "name" == some toolName) then
    return mkToolResult s!"unknown tool '{toolName}' for {cfg.mode} mode" true
  match toolName with
  | "write_draft"     => handleWriteDraft cfg args
  | "patch_draft"     => handlePatchDraft cfg args
  | "read_draft"      => handleReadDraft cfg args
  | "list_drafts"     => handleListDrafts cfg
  | "check_plan"      => handleCheckPlan cfg args
  | "check_agda"      => handleCheckAgdaNode cfg args
  | "check_spec"      => handleCheckSpecSession cfg args
  | "check_entry"     => handleCheckEntrySession cfg args
  | "run_agda_script" => handleRunAgdaScriptSession cfg args
  | _                 => pure (mkToolResult s!"unknown tool '{toolName}'" true)

private def callWithDiagnostics (cfg : MCPConfig) (tool : String) (args : Json) : IO Json := do
  let observations ← IO.mkRef #[]
  let cfg := { cfg with observations := some observations }
  let result ← try dispatchToolCall cfg tool args catch e => pure (mkToolResult (toString e) true)
  let events ← observations.get
  let certs := events.map Prod.snd
  for (name, cert) in events do
    appendNarrowEvent cfg cert.kind name cert.cause (some cert)
    -- Retain the pre-v6 event names consumed by existing ledger readers.
    if tool == "check_agda" && jsonBoolField args "allow_postulates" false then
      if cert.kind == "subspec_laundering" then
        appendNarrowEvent cfg "subspec_axiom_laundering" name cert.cause (some cert)
      else if cert.kind == "subspec_narrowing" then
        appendNarrowEvent cfg "subspec_depth_cap" name cert.cause (some cert)
  if certs.isEmpty && tool != "check_plan" && tool != "check_agda" then return result
  let content := result.getObjValD "content"
  let txt := ((content.getArrVal? 0) >>= (·.getObjValAs? String "text")).toOption.getD ""
  let structured := (result.getObjVal? "structuredContent").toOption.getD (Json.mkObj [
    ("ok", toJson (!jsonBoolField result "isError" true)), ("diagnostics", toJson [txt])])
  let result := result.setObjVal! "structuredContent" (structured.setObjVal! "certificates" (toJson certs))
  if certs.isEmpty then return result
  let shown := txt ++ "\n" ++ String.intercalate "\n" (certs.toList.map NarrowingCertificate.format)
  return result.setObjVal! "content" (.arr #[Json.mkObj [("type", .str "text"), ("text", .str shown)]])

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
          try KernelDriver.preload cfg.libDir catch _ => pure ()
          try preloadSpec cfg catch _ => pure ()
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
              let res ← callWithDiagnostics cfg tName tArgs
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
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let specCache ← IO.mkRef none
  mcpLoop {cfg with specCache := some specCache} stdin stdout

end Prism.MCP
