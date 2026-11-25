import Lojita.Session.Runner
import Lojita.MCP.CheckWorker

namespace Lojita.MCP
open System Lean Lojita.Session Lojita.Harness Lojita.Store Lojita.Kernel Lojita.Transport

inductive Mode where | node | session
  deriving BEq

structure Config where
  mode : Mode
  repo : FilePath
  ctx : FilePath
  ws : Option FilePath := none
  refFile : Option FilePath := none
  narrowLog : Option FilePath := none

def parseConfig (args : List String) : Except String Config := do
  let mut args := args
  let mut flags : Std.HashMap String String := {}
  while let k :: rest := args do
    let v :: tail := rest | throw s!"missing value for {k}"
    unless ["--mode","--repo","--ctx-dir","--workspace","--ref-file","--narrow-log"].contains k && !flags.contains k do
      throw s!"unknown or duplicate option {k}"
    flags := flags.insert k v
    args := tail
  let some kind := flags["--mode"]? | throw "missing --mode"
  let mode ← match kind with | "node" => pure Mode.node | "session" => pure .session | _ => throw "expected node or session"
  let some repo := flags["--repo"]? | throw "missing --repo"
  let some ctx := flags["--ctx-dir"]? | throw "missing --ctx-dir"
  return ⟨mode,repo,ctx,FilePath.mk <$> flags["--workspace"]?,FilePath.mk <$> flags["--ref-file"]?,
    FilePath.mk <$> flags["--narrow-log"]?⟩

private structure Tool where
  name : String
  description : String
  props : List (String × String)
  required : List String := []

private def tools (mode : Mode) : List Tool :=
  let draft := [("name","string")]
  let checks := [("main_block","string"),("source","string"),("name","string"),("dep_blocks","array"),
    ("allow_axioms","boolean"),("allow_postulates","boolean"),("refute_lift","boolean"),
    ("refute_spec","boolean"),("role","string"),("model_block","string")]
  let check := fun n => Tool.mk n "Check a Lean draft against the resident node context." checks []
  let probe := fun n => Tool.mk n "Run a typed SessionEnv probe in an isolated relay workspace."
    [("script_block","string"),("source","string"),("name","string")] []
  [⟨"read_context","List modules with {} or module=list. Read a listed module by exact name, optionally selecting inclusive 1-based lines.",
     [("module","string"),("start_line","integer"),("end_line","integer")],[]⟩,
   ⟨"write_draft","Save a complete named draft.",draft ++ [("content","string")],["name","content"]⟩,
   ⟨"patch_draft","Replace one exact, unambiguous substring.",draft ++ [("old_text","string"),("new_text","string")],
     ["name","old_text","new_text"]⟩,
   ⟨"read_draft","Read a draft or an inclusive range of lines.",draft ++ [("start_line","integer"),("end_line","integer")],["name"]⟩,
   ⟨"list_drafts","List saved draft names.",[],[]⟩] ++
   match mode with
   | .node => [check "check_lean",check "check_agda",
       ⟨"check_plan","Preview a complete plan against the frozen node, without starting children.",
        [("submission","string")],["submission"]⟩]
   | .session => [
       ⟨"check_spec","Check a specification and the source side of its optional vertical and horizontal obligations.",
         [("spec_block","string"),("source","string"),("name","string"),("base_trees","array"),("lift_src","string"),
          ("transport_src","string"),("replaces","array")],[]⟩,
       ⟨"check_entry","Check a sealed executable entry and its exact mode.",[("entry","string"),("mode","string")],["entry"]⟩,
       probe "run_lean_script",probe "run_agda_script"]

private def Tool.schema (t : Tool) : Json :=
  let props := t.props.map fun (k,ty) => (k,Json.mkObj ([("type",toJson ty)] ++
    (if ty == "array" then [("items",Json.mkObj [("type","string")])] else [])))
  Json.mkObj [("name",toJson t.name),("description",toJson t.description),("inputSchema",Json.mkObj [
    ("type","object"),("properties",Json.mkObj props),("required",toJson t.required)])]

private def value {α : Type} [FromJson α] (args : Json) (key : String) : Option α :=
  (args.getObjValAs? α key).toOption

private def required (args : Json) (key : String) : IO String :=
  match value args key with | some s => pure s | none => fail s!"expected string {key}"

private def resolved (ds : DraftStore) (s : String) : IO String := do
  if s.startsWith "@" then return ← IO.ofExcept (sourceValue ds (.sym s))
  return ds[s]?.getD s

private def source (args : Json) (ds : DraftStore) (key : String) : IO String := do
  let some src := value args key <|> value args "source" <|> value args "name" | fail s!"expected {key} or source"
  resolved ds src

private def toolResult (text : String) (data : Json) (isError := false) : Json :=
  Json.mkObj [("content",Json.arr #[Json.mkObj [("type","text"),("text",toJson text)]]),
    ("structuredContent",data),("isError",toJson isError)]

private def success (text : String) := toolResult text (Json.mkObj [("ok",true)])

private def lineRange (src : String) (args : Json) : IO String := do
  let rows := src.splitOn "\n"
  let bound := fun k fallback => match args.getObjVal? k with
    | .error _ => pure fallback
    | .ok n => IO.ofExcept (fromJson? (α := Nat) n)
  let first ← bound "start_line" 1
  let last ← bound "end_line" rows.length
  unless first > 0 && last ≥ first do fail "invalid line range"
  return String.intercalate "\n" ((rows.drop (first-1)).take (last-first+1))

private def draftTool (cfg : Config) (tool : String) (args : Json) : IO Json := do
  if tool == "list_drafts" then
    let ns := (← loadDrafts cfg.ctx).toList.map Prod.fst |>.mergeSort
    return toolResult (String.intercalate "\n" ns) (Json.mkObj [("drafts",toJson ns)])
  let name ← required args "name"
  unless safeDraftName name do fail "invalid draft name"
  let file := cfg.ctx / "drafts" / (name ++ ".block")
  match tool with
  | "write_draft" => atomicText file (← required args "content"); return success s!"saved @{name}"
  | "patch_draft" =>
    let old ← required args "old_text"
    let newText ← required args "new_text"
    let src ← IO.FS.readFile file
    let [a,b] := src.splitOn old | fail "old_text must match exactly once"
    if old.isEmpty then fail "empty old_text"
    atomicText file (a ++ newText ++ b)
    return success s!"patched @{name}"
  | _ =>
    let src ← IO.FS.readFile file
    let body ← lineRange src args
    return toolResult body (Json.mkObj [("name",toJson name),("content",toJson body)])

private def checkLean (ctx : Option NodeContext) (args : Json) (ds : DraftStore) : IO Json := do
  let m ← IO.ofExcept (parseLeanMod (← source args ds "main_block"))
  let depBlocks : List String := (value args "dep_blocks").getD []
  let stubs ← depBlocks.mapM fun d => do IO.ofExcept (parseLeanMod (← resolved ds d))
  let bases := ctx.toList.flatMap (·.task.baseModules)
  let allow := (value args "allow_axioms").getD false || (value args "allow_postulates").getD false
  let spec? := ctx.map (·.task.delta.newIface)
  let role := (value args "role").getD ""
  if m.imports.any (·.imod.toLeanName == `CountermodelCheck) then
    let some spec := spec? | fail "countermodel witness needs a SPECIFICATION"
    let model ← IO.ofExcept (parseLeanMod (← resolved ds ((value args "model_block").getD "@model")))
    discard <| checkCountermodel bases spec model m
    return success "verified CountermodelCheck.VerifiedClaim"
  if let some spec := spec? then
    if m.imports.any (·.imod == spec.modName) || (value args "refute_spec").getD false ||
        (value args "refute_lift").getD false || role == "refute-lift" then
      if role == "refute-lift" || (value args "refute_lift").getD false then
        let culprits ← checkLiftRefutation bases spec m
        return toolResult s!"verified lift obstruction {culprits.map toString}" (Json.mkObj [("culprits",toJson (culprits.map toString))])
      witnessBoundary bases spec m
      discard <| checkRefutation bases (stubOf spec) m
      return success "verified False"
  let bases ← match ctx with
    | none => pure bases
    | some c => do
      let slots := stubs.map (·.modName)
      if let e :: _ := checkTaskImports m.modName slots c.task.allowedImports m then fail (reprStr e)
      IO.ofExcept (c.task.checkingDeps m.modName slots (m.imports.any (·.imod.segments.head? == some "Old")))
  let snap ← checkConditionalGlue bases stubs m allow
  if m.imports.any (·.imod.toLeanName == `LojitaCtx.Countermodel) &&
      (synthesizeCountermodelBridge snap).isOk then
    discard <| checkModelDraft m
    return success "verified CountermodelBundle"
  if allow then
    if let some cert := launderingCertificate snap then fail (toString cert)
  else if let some spec := spec? then
    if spec.modName == m.modName then
      satisfies spec m bases .closedImplOK stubs
      if let some c := ctx then
        if !c.task.transports.isEmpty then
          let cleanDeps ← IO.ofExcept (c.task.checkingDeps m.modName (stubs.map (·.modName)) false)
          match ← verifySealed c.task cleanDeps stubs m snap with
          | .ok _ => pure ()
          | .error cert => fail (toString cert)
  return success s!"checked {m.modName}"

private def observed (cfg : Config) (cert : NarrowingCertificate) (report : Option GateReport := none) : IO Json := do
  if let some path := cfg.narrowLog then logNarrowing path "mcp" cert
  let data := report.map toJson |>.getD (Json.mkObj [("certificate",toJson cert)])
  return toolResult (toString cert) data true

private abbrev ReadNode := IO (Option NodeContext)

private def readContext (cfg : Config) (readNode : ReadNode) (args : Json) : IO Json := do
  let name ← match args.getObjVal? "module" with
    | .ok v => IO.ofExcept (fromJson? (α := String) v)
    | .error _ => pure ""
  let listing := name.isEmpty || name == "list"
  let repo ← IO.FS.realPath cfg.repo
  let mut files := #[]
  for p in ← regularFiles (repo / "LojitaCtx") do
    if p.extension == some "lean" then
      let parts := (p.withExtension "").components.drop repo.components.length
      files := files.push (String.intercalate "." parts,p)
  if cfg.mode == .session then
    files := files.push ("Lojita.Session.SessionEnv",repo / "Lojita/Session/SessionEnv.lean")
  -- A request is a key in a catalog. Never interpret it as a filesystem path.
  let result := fun src => do
    let body ← lineRange src args
    return toolResult body (Json.mkObj [("module",toJson name),("content",toJson body)])
  if let some (_,p) := files.find? (·.1 == name) then return ← result (← IO.FS.readFile p)
  let (modules, originals) ← match cfg.mode with
    | .node => do
      let c ← readNode
      let modules := c.toList.flatMap fun n =>
        let allowed := Std.HashSet.ofList n.task.allowedImports
        readableAncestors n.task ++ n.task.snapshotModules.filter (allowed.contains ·.modName)
      pure (modules, (c.map (·.originals)).getD {})
    | .session => do
      let sealed ← cfg.ws.mapM readSealedModules
      pure (sealed.getD [],{})
  if listing then
    let names := ((files.toList.map Prod.fst) ++ modules.map (toString ·.modName)).mergeSort
    return toolResult (String.intercalate "\n" names) (Json.mkObj [("modules",toJson names)])
  let some m := modules.find? (fun m => toString m.modName == name) | fail s!"module outside this context: {name}"
  let src := match originals[m.modName]? with
    | some text => text
    | none => renderLeanMod m
  result src

private def callTool (cfg : Config) (readNode : ReadNode) (tool : String) (args : Json) : IO Json := do
  unless (tools cfg.mode).any (·.name == tool) do fail s!"unknown tool {tool} in this mode"
  if tool == "read_context" then return ← readContext cfg readNode args
  if ["list_drafts","read_draft","write_draft","patch_draft"].contains tool then return ← draftTool cfg tool args
  let ds ← loadDrafts cfg.ctx
  match tool with
  | "check_lean" | "check_agda" => checkLean (← readNode) args ds
  | "check_plan" =>
    let some c ← readNode | fail "check_plan needs a node context or spec.lean"
    let sub ← IO.ofExcept (parseSubmission (← resolved ds (← required args "submission")) ds)
    let .plan p specs := sub | fail "check_plan expects kind plan"
    let report ← planPreview c.task c.home p specs
    if let some cert := report.certificate then return ← observed cfg cert report
    return toolResult (toJson report).compress (toJson report)
  | _ =>
    let some ws := cfg.ws | fail "session tool needs --workspace"
    match tool with
    | "check_spec" =>
      let src ← source args ds "spec_block"
      let m ← IO.ofExcept (parseLeanMod src)
      let some n := m.modName.segments[1]? | fail "expected Gen.<epoch>.<path>"
      let lift ← (value args "lift_src").mapM (resolved ds)
      let transport ← (value args "transport_src").mapM (resolved ds)
      let replaces ← match args.getObjVal? "replaces" with
        | .ok ns => IO.ofExcept (fromJson? (α := List String) ns)
        | .error _ => pure []
      discard <| withWorkspaceLock ws (prepareSpec ws n src ((value args "base_trees").getD []) lift transport replaces)
      return success s!"checked specification {m.modName}"
    | "check_entry" =>
      let entry ← required args "entry"
      let mode ← IO.ofExcept (parseMode ((value args "mode").getD "cli"))
      withWorkspaceLock ws do
        let name := qualified entry
        checkVerifiedEntry (← entryModules ws name) name mode
      return success s!"verified entry {entry}"
    | _ =>
      let some path := cfg.refFile | fail "probe requires --ref-file"
      let ref ← readReference path
      let r ← runScript cfg.repo ws ref (← source args ds "script_block")
      return toolResult s!"exit {r.exitCode}\n{r.stdout}{r.stderr}" (toJson r) (r.exitCode != 0)

private def rpc (id : Json) (k : String) (body : Json) :=
  Json.mkObj [("jsonrpc","2.0"),("id",id),(k,body)]

private def err (id : Json) (code : Int) (msg : String) :=
  rpc id "error" (Json.mkObj [("code",toJson code),("message",toJson msg)])

private def handle (cfg : Config) (readNode : ReadNode) (forward : Option (Json → IO Json)) (line : String) : IO (Option Json) := do
  let .ok req := Json.parse line | return some (err .null (-32700) "Parse error")
  let id := req.getObjVal? "id"
  let some method := value (α := String) req "method" | return some (err (id.toOption.getD .null) (-32600) "Missing method")
  unless value req "jsonrpc" == some "2.0" do return some (err .null (-32600) "Expected JSON-RPC 2.0")
  let .ok id := id | return none
  let params := (req.getObjVal? "params").toOption.getD (Json.mkObj [])
  let result ← match method with
    | "initialize" =>
      let version := (value params "protocolVersion").getD "2025-06-18"
      let version := if ["2024-11-05","2025-03-26","2025-06-18","2025-11-25"].contains version then version else "2025-06-18"
      pure (Json.mkObj [("protocolVersion",toJson version),("capabilities",Json.mkObj [("tools",Json.mkObj [])]),
        ("serverInfo",Json.mkObj [("name","lojita"),("version","4")])])
    | "ping" => pure (Json.mkObj [])
    | "tools/list" => pure (Json.mkObj [("tools",Json.arr ((tools cfg.mode).map Tool.schema).toArray)])
    | "tools/call" => do
      let some name := value params "name" | return some (err id (-32602) "Missing tool name")
      try
        if let some send := forward then
          if ["check_lean", "check_agda", "check_plan"].contains name then
            return some (rpc id "result" (← send req))
        callTool cfg readNode name ((params.getObjVal? "arguments").toOption.getD (Json.mkObj []))
      catch e =>
        let msg := toString e
        observed cfg ⟨(msg.splitOn ":").headD "check_failed",name,msg,"Correct this input and retry."⟩
    | _ => return some (err id (-32601) "Method not found")
  return some (rpc id "result" result)

private def serveLoop (cfg : Config) (forward : Option (Json → IO Json)) : IO Unit := do
  let readNode ← contextReader cfg.ctx
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    if let some reply ← handle cfg readNode forward line then
      output.putStrLn reply.compress
      output.flush

def serveWorker (cfg : Config) : IO Unit := do
  preload (cfg.repo / ".lake/build/lib/lean")
  serveLoop cfg none

def serve (cfg : Config) : IO Unit := do
  if cfg.mode == .session then return ← serveWorker cfg
  let slot ← IO.mkRef CheckWorker.State.idle
  let mut args := #["mcp-check-worker", "--mode", "node", "--repo", cfg.repo.toString,
    "--ctx-dir", cfg.ctx.toString]
  if let some log := cfg.narrowLog then args := args ++ #["--narrow-log", log.toString]
  try serveLoop cfg (some (CheckWorker.request slot (cfg.repo / "lojita") args))
  finally CheckWorker.stop slot

end Lojita.MCP
