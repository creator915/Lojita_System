import Lojita.Session.Runner
import Std.Async.System

namespace Test.S4
open System Lojita.Session Lojita.Kernel Lojita.Store Lojita.Transport Lojita.Harness
abbrev q := qualified

def ensure (ok : Bool) (msg : String) : IO Unit := unless ok do fail msg

private def expectError {α : Type} (diagnostic : String) (action : IO α) : IO Unit := do
  let .error err ← action.toBaseIO | fail s!"expected rejection: {diagnostic}"
  ensure ((toString err).contains diagnostic) s!"expected {diagnostic}, got {err}"

private def modSrc (n body : String) (imports : List String := []) : String :=
  String.intercalate "\n" (imports.map ("import " ++ ·) ++ ["namespace " ++ n,body,"end " ++ n])

private def object (n body : String) (imps : List String := []) :=
  IO.ofExcept (parseLeanMod (modSrc n body imps))

private def field (k : String) (args : List SExpr) := SExpr.list (.sym k :: args)
private def envelope (tag : String) (fs : List SExpr) := (SExpr.list (.sym tag :: fs)).canonical

private def submitPlan (m : LeanMod) (subs : List LeanMod) (moves : List Proarrow) (why : String) :=
  envelope "submission" [field "kind" [.sym "plan"],field "main" [.str (renderLeanMod m)],field "why" [.str why],
    field "moves" (moves.map encMove),field "subspecs" (subs.map fun s => .list [.str (toString s.modName),.str (renderLeanMod s)])]

private def plan (old m : LeanMod) (subs : List LeanMod := []) (extra : List Proarrow := [])
    (why := "refine") : String := Id.run do
  let names := m.units.map (·.uname)
  let existing := old.units.map (·.uname)
  let moves : List Proarrow := (existing.map fun n => ⟨.unit n,if names.contains n then .unit n else .bot⟩) ++
    ((names.filter (!existing.contains ·)).map fun n => ⟨.bot,.unit n⟩)
  return submitPlan m subs (extra ++ moves) why

private def copyBackend (root : LeanMod) := ScriptedBackend fun req => do
  let some node := req.node | fail "unexpected session proposal"
  unless req.owner == toString root.modName && !req.retry do fail s!"unexpected keepChild proposal: {node.diagnostic}"
  ensure (readableAncestors node.task).isEmpty "a zero-base copy gained direct imports"
  return plan node.old root

private def drive (name src : String) (bases : List String := []) (lift : Option String := none) : String :=
  envelope "session-action" [field "kind" [.sym "drive-tree"],field "treeName" [.str name],field "why" [.str "model observed behavior"],
    field "specSrc" [.str src],field "baseTrees" (bases.map .str),
    field "maybeLiftSrc" [lift.elim (.sym "nothing") (fun s => .list [.sym "just",.str s])]]

private def script (src : String) := envelope "session-action" [field "kind" [.sym "run-script"],
  field "why" [.str "compare observations"],field "source" [.str src]]

private def probe (body : String) := modSrc "Gen.Probes.Markdown"
  ("open Lojita.Session.SessionEnv LojitaCtx.Terminal\n" ++ body) ["Lojita.Session.SessionEnv"]

private def t0 := "Gen.T0.Root"
private def doc := "Gen.T0.Doc"
private def top := "Gen.T1.Doc"
private def escape := top ++ ".Escape"
private def parser := top ++ ".ParseLine"
private def exampleDoc := "[none, some \"note\"]"
private def lookupSpec := "axiom lookupDef : List (Option String) → Option String"
private def correct := "lookupDef " ++ exampleDoc ++ " = some \"note\""

private def tower (ws repo : FilePath) : IO Unit := do
  let ref : RefSpec := ⟨.local (repo / "Test/S4/mini-pandoc.py").toString,[],5000⟩
  let rootSpec ← object t0 lookupSpec
  let repairedSpec ← object t0 (lookupSpec ++ "\naxiom forwardRef : " ++ correct)
  let childSpec ← object doc lookupSpec
  let nextChild ← object doc (lookupSpec ++ "\naxiom forwardRef : " ++ correct)
  let bad ← object doc s!"def lookupDef (_ : List (Option String)) : Option String := none\ntheorem dropsDefinition : lookupDef {exampleDoc} = none := rfl"
  let fixed ← object doc (r#"def lookupDef : List (Option String) → Option String
  | [] => none
  | some note :: _ => some note
  | none :: ss => lookupDef ss
termination_by structural xs => xs
"# ++ "theorem forwardRef : " ++ correct ++ " := rfl")
  let publicLookup := "def lookupDef := Gen.T0.Doc.lookupDef"
  let low ← object t0 publicLookup [doc]
  let repaired ← object t0 (publicLookup ++ "\ntheorem forwardRef : " ++ correct ++ " := Gen.T0.Doc.forwardRef") [doc]
  let upperSpec ← object top "open LojitaCtx.World\naxiom app : CliApp [.stdioCap]"
    ["LojitaCtx.World"]
  let es ← object escape "axiom html : String → String"
  let escaped ← object escape (r#"def html (s : String) := (s.replace "&" "&amp;").replace "<" "&lt;""#)
  let retired := top ++ ".Retired"
  let retiredSpec ← object retired "open LojitaCtx.World\naxiom app : CliApp CliCaps" ["LojitaCtx.World"]
  let retiredImpl ← object retired "open LojitaCtx.World\ndef app : CliApp CliCaps := pure 0" ["LojitaCtx.World"]
  let ps ← object parser (lookupSpec ++ "\naxiom project : ∀ xs, lookupDef xs = Gen.T0.Doc.lookupDef xs\naxiom observed : " ++ correct) [doc]
  let parsed ← object parser (publicLookup ++ "\ntheorem project : ∀ xs, lookupDef xs = Gen.T0.Doc.lookupDef xs := fun _ => rfl\n" ++
    "theorem observed : " ++ correct ++ " := Gen.T0.Doc.forwardRef") [doc]
  let upper ← object top (r#"open LojitaCtx.World LojitaCtx.Terminal
def lookupDef := Gen.T1.Doc.ParseLine.lookupDef
theorem square (xs : List (Option String)) : lookupDef xs = Gen.T0.Root.lookupDef xs := Gen.T1.Doc.ParseLine.project xs
def renderLine (note : Option String) (s : String) : String :=
  if s.isEmpty || s.startsWith "[^1]: " then "" else
    let escaped := Gen.T1.Doc.Escape.html s
    let body := match note with
      | some n => escaped.replace "[^1]" ("<sup>" ++ n ++ "</sup>")
      | none => escaped
    "<p>" ++ body ++ "</p>\n"
def render (src : String) : String :=
  let lines := src.splitOn "\n"
  let defs := lines.map fun s => if s.startsWith "[^1]: " then some (s.drop 6).toString else none
  String.join (lines.map (renderLine (lookupDef defs)))
def app : CliApp [.stdioCap] := do
  let input ← readStdinAllW .here
  writeStdoutStrW .here (render (String.fromUTF8! input.toByteArray))
  return 0"#) ["LojitaCtx.World",escape,parser,t0]
  let proof ← object "Gen.T1.Obstruction" (s!"theorem impossible : False := by
  have h := Gen.T1.Doc.ParseLine.observed.symm.trans ((Gen.T1.Doc.ParseLine.project {exampleDoc}).trans Gen.T0.Doc.dropsDefinition)
  cases h") [doc,parser]
  let lifting := (encodeLiftSpec (.liftSpecTree (q t0) (q top) [.mkChildLift (q doc) (q parser) none]
    [endpointLift (q (t0 ++ ".lookupDef")) (q (top ++ ".lookupDef")) (q (top ++ ".square"))])).canonical
  let runUpper := drive "T1" (renderLeanMod upperSpec) ["T0"] lifting
  let observe := probe (r#"def probe : Probe := do
  let o ← batch "ref" [] (bytes "A & B[^1]\n[^1]: note\n")
  return {exitCode := o.exitStatus.getD 1, stdout := text o.stdoutOut}"#)
  let compare := probe (r#"def probe : Probe := do
  let a ← replay [] "A & B[^1]\n[^1]: note\n"
  if a.exitCode != 0 then return a
  let b ← replay [] "<X\n\nB\n"
  if b.exitCode != 0 then return b
  replay [] "orphan[^1]\n""#)
  let finish := "(session-action (kind finish) (summary \"mini-pandoc replayed\"))"
  let build := "(session-action (kind build-exe) (why \"compile verified Doc.app\") (entry \"Gen.T1.Doc.app\") (mode cli))"
  let steps := #[script observe,drive "T0" (renderLeanMod rootSpec),runUpper,drive "T0" (renderLeanMod repairedSpec),
    runUpper,finish,build,script compare,finish]
  let turn ← IO.mkRef 0
  let counts ← IO.mkRef ({} : Std.HashMap (Nat × String) Nat)
  let innocent ← IO.mkRef ""
  let cfg : SessionConfig := ⟨repo,ws,"Build the observed Markdown dialect",ref,
    ScriptedBackend (fun _ => fail "unexpected proposal"),true⟩
  let ai := ScriptedBackend fun req => do
    let i ← turn.get
    if let some node := req.node then
      if let some cert := node.diagnostic then fail s!"{req.owner} {cert}"
      counts.modify fun m => m.alter (i,req.owner) (fun n => some (n.getD 0 + 1))
      let old := node.old
      if req.owner == t0 then return if i == 2 then plan old low [childSpec] else plan old repaired [nextChild]
      if req.owner == doc then return plan old (if i == 2 then bad else fixed)
      if req.owner == top then
        if i == 3 then return plan old {upper with imports := ⟨q retired,[]⟩ :: upper.imports} [retiredSpec,es,ps]
        return plan old upper [es,ps]
      if req.owner == retired then return plan old retiredImpl
      if req.owner == escape then return plan old escaped
      if req.owner == parser then
        if i == 3 then return envelope "submission" [field "kind" [.sym "refute-lift"],field "why" [.str "single pass drops footnote"],
          field "refute" [.str (renderLeanMod proof)]]
        return plan old parsed
      fail s!"unexpected node {req.owner}"
    let some action := steps[i]? | fail s!"session exhausted at {i}\n{req.prompt.splitOn "TRANSIENT DIAGNOSTIC" |>.getLast?}"
    if i == 1 then ensure (req.prompt.contains "<p>A &amp; B<sup>note</sup></p>") "missing reference observation"
    if i == 3 then
      let diag ← IO.FS.readFile (ws / "trees/T1/obstruction.sexp")
      ensure (diag.contains "Gen.T0.Doc.dropsDefinition") "obstruction missed responsible base unit"
      let some key ← readRef (ws / "store") .partial "T1" | fail "no partial T1"
      let h ← loadFrozen (ws / "store") (← getObject (ws / "store") .commit key).rootHome
      ensure ((h.children.map Prod.fst).mergeSort == [escape,retired]) "wrong preserved siblings"
      let some kid := lookupChild h (q escape) | fail "missing Escape"
      innocent.set (← storeFrozen (ws / "store") kid)
      -- Side keeps the old executable child even after the repaired T1 drops its slot.
      let target := "Gen.Side.Extra"
      let renamed := target ++ ".Escape"
      let saved := target ++ ".Saved"
      let kept := TransportSpec.transportSpecTree (q top) (q target)
        [.keepChild (q escape) (q renamed), .keepChild (q retired) (q saved)] []
      let archive ← object target "axiom html : String → String"
      let copy ← object target ("def html := " ++ renamed ++ ".html") [renamed,saved]
      let ok ← driveTree {cfg with backend := copyBackend copy} "Side" "keep the verified siblings" (renderLeanMod archive)
        [] none (some (encodeTransportSpec kept).canonical)
      ensure (ok == "ok") "cross-tree partial keep failed"
      checkVerifiedEntry (← entryModules ws (q (saved ++ ".app"))) (q (saved ++ ".app")) .cli
      -- The retained original exists in Side, but the named entry epoch is still partial.
      let rpc ← IO.Process.output {
        cmd := (repo / "lojita").toString
        args := #["mcp","--mode","session","--repo",repo.toString,"--workspace",ws.toString,"--ctx-dir",req.ctxDir.toString]
      } (some r#"{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"check_entry","arguments":{"entry":"Gen.T1.Doc.Retired.app"}}}"#)
      ensure (rpc.exitCode == 0 && rpc.stdout.contains "\"isError\":true" && rpc.stdout.contains "unsealed entry tree")
        "check_entry accepted a partial epoch"
    if i == 5 then
      let sealed ← loadCurrentClosure ws ["T1"]
      let some kid := sealed.trees.head?.bind (lookupChild ·.home (q escape)) | fail "Escape was lost"
      ensure ((← storeFrozen (ws / "store") kid) == (← innocent.get)) "innocent Merkle identity changed"
    if i == 6 then ensure (req.retry && req.prompt.contains "REPLAY_REQUIRED") "premature finish passed"
    if i == 7 then
      let refOnly ← runScript repo ws ref observe
      ensure (refOnly.exitCode == 0 && refOnly.usedRef && !refOnly.usedCand) "invalid ref-only observation"
      let mismatch ← runScript repo ws ref (probe (r#"def probe : Probe := do
  let _ ← batch "ref"
  let _ ← batch "cand"
  return {exitCode := 1, stderr := "comparison failed"}"#))
      ensure (mismatch.exitCode == 1 && mismatch.usedRef && mismatch.usedCand) "invalid failed replay"
      let .rejected e ← executeAction cfg (.finish "missing replay") | fail "built candidate bypassed replay"
      ensure (e.contains "REPLAY_REQUIRED" && !(← (ws / "replay-receipt.sexp").pathExists)) "unearned replay receipt"
    if req.retry && i != 6 then fail s!"unexpected rejection: {(req.prompt.splitOn "TRANSIENT DIAGNOSTIC").getLast!}"
    turn.set (i+1)
    return action
  let cfg := {cfg with backend := ai}
  let summary ← runSession cfg
  ensure (summary == "mini-pandoc replayed" && (← turn.get) == 9) "session failed to finish"
  let calls ← counts.get
  ensure (calls[(3,escape)]? == some 1 && calls[(5,escape)]?.getD 0 == 0 && calls[(5,parser)]? == some 1)
    "expected Escape turns 1 then 0 and repaired ParseLine 1"
  ensure ((← readOptional (ws / "replay-receipt.sexp")).isSome) "missing replay receipt"
  IO.println "3  Mini-Pandoc: T0 revised in place, lift obstruction blamed dropsDefinition, Escape turns 1 then 0, static build and differential replay"

  let entry := q (top ++ ".app")
  let modules ← entryModules ws entry
  ensure (modules.map (·.modName) == (← loadCurrentClosure ws ["T1"]).modules.map (·.modName) &&
    !modules.any (fun m => m.modName == q "Gen.Side.Extra" || m.modName == q retired)) "side tree in entry closure"
  let smuggled ← object "Gen.T1.Doc.Smuggled" "def html := Gen.Side.Extra.html" ["Gen.Side.Extra"]
  expectError "UNKNOWN_IMPORT: Gen.Side.Extra" (checkClosedModule modules smuggled)
  let legacy := q (retired ++ ".app")
  checkVerifiedEntry (← loadCurrentClosure ws ["Side"]).modules legacy .cli
  let .rejected missing ← executeAction cfg (.buildExe .cli "entry exists only in Side" (toString legacy))
    | fail "build-exe linked a side-tree entry"
  ensure (missing.contains "ENTRY_MISSING") s!"wrong side-tree diagnostic: {missing}"

  let successor := "Gen.T2.Doc"
  let atT2 := requalify (q top) (q successor)
  let t2 := atT2 upperSpec
  let impl := requalify (q t0) (q top) (atT2 upper)
  let es2 := atT2 es
  let html2 ← object (toString es2.modName) ("def html := " ++ escape ++ ".html") [escape]
  let project := "∀ xs, lookupDef xs = " ++ parser ++ ".lookupDef xs"
  let ps2 ← object (successor ++ ".ParseLine") (lookupSpec ++ "\naxiom project : " ++ project) [parser]
  let parse2 ← object (toString ps2.modName) ("def lookupDef := " ++ parser ++ ".lookupDef\ntheorem project : " ++
    project ++ " := fun _ => rfl") [parser]
  let lifting2 := (encodeLiftSpec (.liftSpecTree (q top) t2.modName
    [.mkChildLift (q escape) es2.modName none, .mkChildLift (q parser) ps2.modName none]
    [endpointLift (q (top ++ ".lookupDef")) (q (successor ++ ".lookupDef")) (q (successor ++ ".square"))])).canonical
  let prepare := prepareSpec ws "T2" (renderLeanMod t2)
  expectError "MULTI_BASE_TREES" (prepare ["T1","T0"] lifting2 none)
  expectError "MISSING_REFINEMENT_MORPHISM" (prepare ["T1"] none none)
  for wrongRoot in [t0,parser] do
    let wrong := (encodeLiftSpec (.liftSpecTree (q wrongRoot) t2.modName [] [])).canonical
    expectError "MISSING_REFINEMENT_MORPHISM" (prepare ["T1"] wrong none)
  let distant := (encodeTransportSpec (.transportSpecTree (q t0) t2.modName [] [])).canonical
  expectError "MISSING_REFINEMENT_MORPHISM" (prepare ["T1"] none distant)
  -- A transport alone suffices at the direct root. It can also copy a sealed slot with no base.
  let archive ← object "Gen.Archive.Doc" "axiom html : String → String"
  let slot := "Gen.Archive.Doc.Escape"
  let copy ← object "Gen.Archive.Doc" ("def html := " ++ slot ++ ".html") [slot]
  let kept := (encodeTransportSpec (.transportSpecTree (q top) archive.modName
    [.keepChild (q escape) (q slot), .moveChildren [q parser] [] []] [])).canonical
  discard <| prepareSpec ws "Archive" (renderLeanMod archive) ["T1"] none kept
  let copied ← driveTree {cfg with backend := copyBackend copy} "Archive" "keep a sealed child" (renderLeanMod archive)
    [] none kept
  ensure (copied == "ok" && (← loadCurrentClosure ws ["Archive"]).trees.map (·.name) == ["Archive"])
    "sealed keepChild introduced a vertical base"
  let .rejected stale ← executeAction cfg (.finish "wrong") | fail "stale build was accepted"
  ensure (stale.contains "STALE_BUILD") "an independent tree did not invalidate the build"
  let self := (encodeTransportSpec (.transportSpecTree (q t0) (q t0) [.keepChild (q doc) (q doc)] [])).canonical
  discard <| prepareSpec ws "T0" (renderLeanMod repairedSpec) [] none self
  let cb := ScriptedBackend fun req => do
    let some node := req.node | fail "unexpected SESSION_ROOT"
    if let some e := node.diagnostic then fail (toString e)
    if req.owner == successor then return plan node.old impl [es2,ps2]
    if req.owner == toString es2.modName then return plan node.old html2
    if req.owner == toString ps2.modName then return plan node.old parse2
    fail s!"unexpected T2 child {req.owner}"
  let ok ← driveTree {cfg with backend := cb} "T2" "third layer" (renderLeanMod t2) ["T1"] lifting2 none
  let closure ← loadCurrentClosure ws ["T2"]
  ensure (ok == "ok" && closure.trees.map (·.name) == ["T2","T1","T0"] &&
    closure.modules.any (·.modName == q doc)) "three-layer chain lost its grandparent"

  -- Re-seal T0 while T1 and T2 still point at historical commits.
  let before := (← loadCurrentClosure ws ["T0"]).directTips
  let baseAI := ScriptedBackend fun req => do
    let some node := req.node | fail "unexpected SESSION_ROOT"
    if let some e := node.diagnostic then fail (toString e)
    return plan node.old repaired [nextChild]
  discard <| driveTree {cfg with backend := baseAI} "T0" "re-publish the two-pass implementation" (renderLeanMod repairedSpec) [] none none
  let after := (← loadCurrentClosure ws ["T0"]).directTips
  ensure (before != after && (← loadCurrentClosure ws ["T2"]).trees.any (fun t => t.name == "T0" && after.contains t.tip))
    "vertical ancestry used a stale grandparent"
  let source := q "Gen.T1.Doc.Old.token"
  let p : Plan := {why := "split",moves := ["Lex","Parse"].map fun name =>
    ⟨.ext source,.ext (q ("Gen.T1.Doc." ++ name ++ ".token"))⟩}
  for name in ["Lex","Parse"] do
    ensure (crossChildMemory p [(.unit source,["old child note"])] (q ("Gen.T1.Doc." ++ name)) == ["old child note","split"])
      s!"lost split memory for {name}"
  let key := after.head!
  let c ← getObject (ws / "store") .commit key
  let malformed ← putObject (ws / "store") .commit {c with parents := [String.ofList (List.replicate 64 'f')]}
  ensure (!(← (verifyCommitDAG (ws / "store") malformed).toBaseIO).isOk) "missing ancestry accepted"
  let t2Tip := (← loadCurrentClosure ws ["T2"]).directTips.head!
  let loopTip ← putObject (ws / "store") .commit {c with parents := [t2Tip]}
  try
    writeRef (ws / "store") .trees "T0" loopTip
    atomicText (ws / "trees/T0/current") loopTip
    let .error err ← (loadCurrentClosure ws ["T2"]).toBaseIO | fail "live ancestry cycle was accepted"
    ensure ((toString err).contains "cycle") "wrong live ancestry diagnostic"
  finally
    writeRef (ws / "store") .trees "T0" key
    atomicText (ws / "trees/T0/current") key
  -- Interrupt a prepared publication just before installing its current pointer.
  let journal := ws / ".publication"
  IO.FS.createDir journal
  IO.FS.rename (ws / "trees/T0/current") (journal / "current")
  atomicText (journal / "ready") "T0"
  withWorkspaceLock ws do
    ensure ((← loadCurrentClosure ws ["T0"]).directTips == [key]) "publication recovery lost current"
  let file := ws / "generated/Side/Gen/Side/Extra.lean"
  let text ← IO.FS.readFile file
  try
    IO.FS.writeFile file (text ++ "-- altered\n")
    for act in [SessionAction.buildExe .cli "rebuild T1" (toString entry), .finish "changed export"] do
      let .rejected err ← executeAction cfg act | fail "audit accepted a changed side-tree export"
      ensure (err.contains "published source differs from sealed tree: Gen.Side.Extra") s!"wrong audit failure: {err}"
  finally IO.FS.writeFile file text
  IO.println "4  Single-predecessor tower, entry-scoped linking, stale receipt, live ancestry, source audit and split Lex/Parse memory"


/-- Go through the session envelope and count every worker proposal, including retries. -/
private def checkedDrive (cfg : SessionConfig) (spec : LeanMod) (expected : List String)
    (answer : AIRequest → IO String) (bases : List String := []) (lift : Option LiftSpec := none)
    (transport : Option TransportSpec := none) (replaces : List String := []) (status := "ok") : IO String := do
  let name := spec.modName.segments[1]!
  let turns ← Std.Mutex.new ([] : List String)
  let backend := ScriptedBackend fun req => do
    let some node := req.node | fail "expected node proposal"
    turns.atomically (modify (req.owner :: ·))
    if let some cert := node.diagnostic then fail s!"{req.owner}: {cert}"
    unless expected.contains req.owner do fail s!"unexpected AI turn for {req.owner}"
    let some decoded ← (← contextReader req.ctxDir) | fail "missing node context"
    ensure (decoded.task.oldBaseModules == node.task.oldBaseModules) "MCP lost pinned history"
    answer node
  let fields := [field "kind" [.sym "drive-tree"], field "treeName" [.str name], field "why" [.str "recover"],
    field "specSrc" [.str (renderLeanMod spec)], field "baseTrees" (bases.map .str)] ++
    lift.toList.map (fun l => field "maybeLiftSrc" [.list [.sym "just",.str (encodeLiftSpec l).canonical]]) ++
    transport.toList.map (fun t => field "maybeTransportSrc" [.list [.sym "just",.str (encodeTransportSpec t).canonical]]) ++
    (if replaces.isEmpty then [] else [field "replaces" (replaces.map .str)])
  let act ← IO.ofExcept (parseSessionAction (envelope "session-action" fields))
  let result ← executeAction {cfg with backend} act
  let .accepted detail := result | fail s!"{name}: {repr result}"
  ensure ((← turns.atomically get).mergeSort == expected.mergeSort &&
    (← readOptional (cfg.workspace / "trees" / name / "verdict")) == some status) s!"unexpected turns or verdict: {detail}"
  return detail

private def innocentOnRefutation (cfg : SessionConfig) (model : Bool) : IO Unit := do
  let epoch := if model then "Model" else "Contradiction"
  let name := "Gen." ++ epoch ++ ".R"
  let keep := name ++ ".Keep"
  let bad := name ++ ".Bad"
  let spec ← object name "axiom value : Nat"
  let keepSpec ← object keep "axiom value : Nat"
  let glue ← object name s!"def value := {keep}.value" [keep]
  discard <| checkedDrive cfg spec [name,keep] fun req => do
    if req.task.delta.child == q name then return plan req.old glue [keepSpec]
    return plan req.old (← object keep "def value := 0")
  let store := cfg.workspace / "store"
  let some original := (← loadCurrentClosure cfg.workspace [epoch]).trees.head? | fail "missing original"
  let some kid := lookupChild original.home (q keep) | fail "missing innocent child"
  let expected ← storeFrozen store kid
  let law := if model then "∀ c : Char, (c == c) = true" else "False"
  let strengthened ← object name s!"axiom value : Nat\naxiom law : {law}"
  let child ← object bad "def zero : Nat := 0\naxiom bad : zero = 1"
  let answer := if model then "by simp" else s!"Nat.zero_ne_one {bad}.bad"
  let draft ← object name s!"def value := {keep}.value\ntheorem law : {law} := {answer}" [keep,bad]
  let proof ← object "BadEvidence" s!"theorem witness : False := Nat.zero_ne_one {bad}.bad" [bad]
  let refute := fun (m : LeanMod) => envelope "submission" [field "kind" [.sym "contradiction"],field "refute" [.str (renderLeanMod m)]]
  let backend := ScriptedBackend fun turn => do
    let some req := turn.node | fail "missing node"
    if turn.owner == bad then return refute proof
    ensure (turn.owner == name) "innocent child requested a turn"
    if let some cert := req.diagnostic then
      ensure (cert.kind == "child_contradiction") s!"unexpected parent diagnostic: {cert}"
      if !model then return refute (← object "RootEvidence" s!"theorem witness : False := {name}.law" [name])
      let m ← object "RootModel" "open LojitaCtx.Countermodel
def claim (a : CharAlg) := ∀ x, a.charEq x x = true
def bundle : CountermodelBundle := .charCountermodel claim phantomCharModel (by
  intro k h
  have bad := h none
  contradiction)" ["LojitaCtx.Countermodel"]
      let r ← object "RootEvidence" s!"theorem witness : CountermodelCheck.VerifiedClaim := {name}.law" [name,"CountermodelCheck"]
      return envelope "submission" [field "kind" [.sym "countermodel"],field "model" [.str (renderLeanMod m)],
        field "refute" [.str (renderLeanMod r)]]
    return plan req.old draft [keepSpec,child]
  let detail ← driveTree {cfg with backend} epoch "own refutation" (renderLeanMod strengthened) [] none none
  ensure (detail.startsWith (if model then "countermodel" else "contradiction")) s!"unexpected verdict: {detail}"
  let some key ← readRef store .partial epoch | fail s!"missing partial {epoch}"
  let home ← loadFrozen store (← getObject store .commit key).rootHome
  let [(slot,saved)] := home.children | fail s!"wrong saved children for {epoch}"
  ensure (slot == keep && (← storeFrozen store saved) == expected) s!"{epoch} lost its verified child"

private def inPlaceTowerRecovery (ws repo : FilePath) : IO Unit := do
  initWorkspace ws
  let cfg : SessionConfig := ⟨repo,ws,"Repair the three-layer tower",⟨.local "/bin/true",[],5000⟩,
    ScriptedBackend (fun _ => fail "unexpected proposal"),false⟩
  let root := fun (n : String) => "Gen." ++ n ++ ".R"
  let base := root "T0"
  let escape0 := base ++ ".Escape"
  let parser0 := base ++ ".ParseLine"
  let collect := base ++ ".CollectRefs"
  let resolve := base ++ ".Resolve"
  let runSig := "axiom run : List Bool → Bool"
  let parseSig := "axiom parse : List Bool → Bool"
  let forward := " [false,true] = true"
  let rootSpec ← object base runSig
  let es ← object escape0 "axiom escape : Nat → Nat"
  let ps ← object parser0 parseSig
  let parsed := "def parse (lines : List Bool) := lines.headD false"
  let parseImpl ← object parser0 parsed
  let badSpec ← object parser0 (parseSig ++ "\naxiom missed : parse [false,true] = false")
  let bad ← object parser0 (parsed ++ "\nprivate def cursor := 0\ntheorem missed : parse [false,true] = false := rfl")
  let escImpl ← object escape0 "def escape (n : Nat) := n"
  let glue ← object base s!"def run := {parser0}.parse" [escape0,parser0]
  let publicNote := "a line can refer to a later definition"
  let privateNote := "single-pass cursor starts at zero"
  discard <| checkedDrive cfg rootSpec [base,escape0,parser0] fun node => do
    if node.task.delta.child == q base then return plan node.old glue [es,ps]
    if node.task.delta.child == q escape0 then return plan node.old escImpl
    return plan node.old parseImpl [] [] publicNote
  discard <| checkedDrive cfg rootSpec [base,parser0] fun node => do
    if node.task.delta.child == q base then return plan node.old glue [es,badSpec]
    return submitPlan bad [] ((bad.units.drop 1).map fun u => ⟨.bot,.unit u.uname⟩) privateNote

  let tier := fun (epoch lower : String) (split strong obstruct : Bool) (expected : List String)
      (transport : Option TransportSpec) (replaces : List String) => do
    let n := root epoch
    let e := n ++ ".Escape"
    let p := n ++ ".ParseLine"
    let toc := n ++ ".PureTOC"
    let upper := lower == "T1"
    let be := root lower ++ ".Escape"
    let bp := if split then resolve else root lower ++ ".ParseLine"
    let ports := if split then [bp,collect] else [bp]
    let rhs := if split then s!"{resolve}.resolve ({collect}.collect xs)" else s!"{bp}.parse xs"
    let projection := s!"∀ xs, parse xs = {rhs}"
    let law := if strong then "\naxiom forward : run" ++ forward else ""
    let spec ← object n (runSig ++ law)
    let escapeSpec ← object e "axiom escape : Nat → Nat"
    let parseSpec ← object p (parseSig ++ "\naxiom project : " ++ projection ++
      (if strong then "\naxiom forward : parse" ++ forward else "")) ports
    let tocSpec ← object toc "axiom headings : Nat"
    let children := [escapeSpec,parseSpec] ++ (if upper then [tocSpec] else [])
    let pipe := s!"def run := {p}.parse\ndef baseline (xs : List Bool) := {rhs}" ++
      (if strong then s!"\ntheorem forward : run{forward} := {p}.forward" else "")
    let pipe := if replaces.isEmpty then pipe else pipe ++
      s!"\ntheorem replay (xs : List Bool) : {root "T2"}.run xs = run xs := ({p}.project xs).symm"
    let impl ← object n pipe (children.map (toString ·.modName) ++ ports ++ replaces.map root)
    let parserMap := if split then ChildLift.moveChildLifts [q collect,q resolve] [q p] [.liftSpecTree (q bp) (q p) [] []]
      else ChildLift.mkChildLift (q bp) (q p) none
    let lift := LiftSpec.liftSpecTree (q (root lower)) (q n) [.mkChildLift (q be) (q e) none,parserMap] []
    let retireOldImport := fun (old : LeanMod) =>
      if split && old.imports.any (·.imod == q parser0) then [Proarrow.mk (.ext (q parser0)) .bot] else []
    let reply := fun (node : AIRequest) => do
      let owner := node.task.delta.child
      if split && !node.old.units.isEmpty then
        ensure (node.task.oldBaseModules.any (·.any (·.modName == q parser0)) &&
          !node.task.baseModules.any (·.modName == q parser0)) "old T1 lost its pinned T0 parser"
      if owner == q n then return plan node.old impl children (retireOldImport node.old)
      let visible := (readableAncestors node.task).map (·.modName)
      if owner == q toc then
        ensure (visible.isEmpty && node.task.allowedAncestors == some []) "upper-only PureTOC acquired a base"
        return plan node.old (← object toc "def headings := 0")
      if owner == q e then
        ensure (visible.contains (q be) && !visible.contains (q bp) && !visible.contains (q parser0)) "Escape saw a parser"
        let leak ← object e s!"def escape := {bp}.parse" [bp]
        ensure (!(checkTaskImports owner [] node.task.allowedImports leak).isEmpty) "Escape can import its sibling's base"
        return plan node.old (← object e s!"def escape := {be}.escape" [be])
      ensure (owner == q p && visible.contains (q bp)) "missing mapped parser"
      if upper && obstruct then
        ensure (visible.contains (q parser0) && !visible.contains (q escape0)) "transitive parser fiber lost isolation"
      if obstruct then
        let missed := if upper then s!"(({bp}.project [false,true]).trans {parser0}.missed)" else parser0 ++ ".missed"
        let proof ← object (n ++ ".Evidence") (s!"theorem impossible : False := by\n" ++
          s!"  have h := {p}.forward.symm.trans (({p}.project [false,true]).trans {missed})\n  cases h")
          (distinct [p,bp,parser0])
        return envelope "submission" [field "kind" [.sym "refute-lift"],field "why" [.str "forward reference lost"],
          field "refute" [.str (renderLeanMod proof)]]
      let body := s!"def parse (xs : List Bool) := {rhs}\ntheorem project : {projection} := fun _ => rfl" ++
        (if strong then "\ntheorem forward : parse" ++ forward ++ " := rfl" else "")
      return plan node.old (← object p body ports) [] (retireOldImport node.old)
    checkedDrive cfg spec (n :: expected.map (fun slot => n ++ "." ++ slot)) reply [lower] lift transport replaces
      (if obstruct then "lift-obstruction" else "ok")

  discard <| tier "T1" "T0" false false false ["Escape","ParseLine"] none []
  let obstruction ← tier "T2" "T1" false true true ["Escape","PureTOC","ParseLine"] none []
  let preserved := fun (epoch : String) (slots : List String) => do
    let some key ← readRef (ws / "store") .partial epoch | fail s!"missing partial {epoch}"
    let h ← loadFrozen (ws / "store") (← getObject (ws / "store") .commit key).rootHome
    ensure ((h.children.map Prod.fst).mergeSort == (slots.map (fun s => root epoch ++ "." ++ s)).mergeSort)
      s!"incorrect partial home for {epoch}"
  ensure (obstruction.contains (parser0 ++ ".missed")) "T2 failed to trace the base bug"
  preserved "T2" ["Escape","PureTOC"]
  let convicted ← tier "T1" "T0" false true true ["ParseLine"] none []
  ensure (convicted.contains "CULPRIT_BASE_UNITS" && convicted.contains (parser0 ++ ".missed")) "T1 missed its culprit"
  preserved "T1" ["Escape"]

  -- Leave an independent sealed consumer of the old parser live through the split.
  let side := root "Side"
  let sideSpec ← object side runSig
  let sideLift := LiftSpec.liftSpecTree (q base) (q side) [.moveChildLifts [q parser0,q escape0] [] []] []
  discard <| checkedDrive cfg sideSpec [side] (fun node => do
    return plan node.old (← object side s!"def run := {parser0}.parse" [parser0])) ["T0"] sideLift

  let cs ← object collect "axiom collect : List Bool → Bool\naxiom found : collect [false,true] = true"
  let rs ← object resolve "axiom resolve : Bool → Bool\naxiom present : resolve true = true"
  let fixed ← object base (runSig ++ "\naxiom forward : run" ++ forward)
  let twoPass ← object base (s!"def run (xs : List Bool) := {resolve}.resolve ({collect}.collect xs)\n" ++
    s!"theorem forward : run{forward} := by rw [run, {collect}.found, {resolve}.present]") [escape0,collect,resolve]
  let moves : List Proarrow := [⟨.ext (q (parser0 ++ ".parse")), .ext (q (resolve ++ ".resolve"))⟩,
    ⟨.ext (q (parser0 ++ ".missed")), .bot⟩]
  discard <| checkedDrive cfg fixed [base,collect,resolve] fun node => do
    if node.task.delta.child == q base then return plan node.old twoPass [es,cs,rs] moves
    if node.task.delta.child == q collect then
      ensure (!node.memory.any (·.2.contains publicNote)) "endpoint note leaked to CollectRefs"
      return plan node.old (← object collect "def collect (xs : List Bool) := xs.contains true\ntheorem found : collect [false,true] = true := rfl")
    ensure (node.memory.any (fun (o,ns) => o == .unit (q (resolve ++ ".resolve")) && ns.contains publicNote) &&
      !node.memory.any (·.2.contains privateNote)) "Resolve did not receive exclusively its mapped note"
    return plan node.old (← object resolve "def resolve (found : Bool) := found\ntheorem present : resolve true = true := rfl")
  let some tree := (← loadCurrentClosure ws ["T0"]).trees.head? | fail "missing sealed T0"
  let sealed := tree.home
  let buried := (memoryIndex sealed.memory)[Obj.bot]?.getD #[]
  ensure (buried.contains privateNote && !buried.contains publicNote &&
    !(← (ws / "generated/T0/Gen/T0/R/ParseLine.lean").pathExists)) "lost private memory or left the old parser on disk"
  expectError "STALE_ANCESTOR_TREE: ancestor tree T1" (driveTree cfg "T2" "skip T1" (modSrc (root "T2") runSig) ["T1"] none none)
  expectError "re-drive Side before driving Probe" (prepareSpec ws "Probe" (modSrc (root "Probe") runSig) ["Side"] none none)
  let catalog := (← readSealedModules ws).map (·.modName)
  ensure (catalog.contains (q resolve) && !catalog.contains (q side)) "stale side tree broke the live catalog"
  discard <| tier "T1" "T0" true true false ["ParseLine"] none []
  discard <| tier "T2" "T1" false true false ["ParseLine"] none []

  -- SESSION_ROOT can see the stale side tree and repair it before its final audit.
  let sideFixed := (encodeLiftSpec (.liftSpecTree (q base) (q side) [.moveChildLifts [q escape0,q collect,q resolve] [] []] [])).canonical
  let actions ← IO.mkRef 0
  let recoverSide := ScriptedBackend fun req => do
    if let some node := req.node then
      return plan node.old (← object side s!"def run := {base}.run" [base]) [] [⟨.ext (q parser0),.bot⟩]
    let i ← actions.modifyGet fun i => (i,i+1)
    if i == 0 then
      ensure (req.prompt.contains "[STATUS: STALE AGAINST UPDATED ANCESTOR — RE-DRIVE THIS TREE]" &&
        req.prompt.contains "ancestor tree Side") "missing live stale-tree status"
      return drive "Side" (renderLeanMod sideSpec) ["T0"] sideFixed
    if req.retry then fail req.prompt
    return "(session-action (kind finish) (summary \"recovered\"))"
  ensure ((← runSession {cfg with backend := recoverSide}) == "recovered") "SESSION_ROOT could not recover"
  discard <| auditTrees ws

  let peer := root "T2"
  let n := root "T2b"
  let copy := fun slot => ChildMove.keepChild (q (peer ++ slot)) (q (n ++ slot))
  let transport := TransportSpec.transportSpecTree (q peer) (q n)
    [copy ".Escape",copy ".PureTOC",.moveChildren [q (peer ++ ".ParseLine")] [q (n ++ ".ParseLine")] []]
    [polySquare [q (peer ++ ".run")] [q (n ++ ".run")] (q (n ++ ".replay"))]
  for (bad,why) in [("T2b","distinct horizontal peer"),("T1","distinct horizontal peer"),("Missing","unknown replacement"),
      ("../T2","invalid tree name"),("T0","same baseTrees")] do
    expectError why (prepareSpec ws "T2b" (modSrc n runSig) ["T1"] none none [bad])
  expectError "sealed tree T2 depends on it" (prepareSpec ws "Peer" (modSrc (root "Peer") runSig) ["T0"] none none ["T1"])
  expectError "MISSING_REPLACEMENT_TRANSPORT" (prepareSpec ws "T2b" (modSrc n runSig) ["T1"] none none ["T2"])
  let impossible ← object n "axiom impossible : False"
  let evidence ← object "ReplacementEvidence" s!"theorem witness : False := {n}.impossible" [n]
  let checkLift := LiftSpec.liftSpecTree (q (root "T1")) (q n)
    [.moveChildLifts [q (root "T1" ++ ".Escape"),q (root "T1" ++ ".ParseLine")] [] []] []
  discard <| checkedDrive cfg impossible [n] (fun _ => pure <| envelope "submission" [
    field "kind" [.sym "contradiction"],field "refute" [.str (renderLeanMod evidence)]]) ["T1"] checkLift transport ["T2"] "contradiction"
  let oldTip ← readRef (ws / "store") .trees "T2"
  ensure (oldTip.isSome && (← (ws / "generated/T2").isDir)) "a failed replacement destroyed T2"
  discard <| tier "T2b" "T1" false true false ["ParseLine"] transport ["T2"]
  let audited ← auditTrees ws
  ensure ((← sealedNames ws).contains "T2b" && !audited.trees.any (·.name == "T2") &&
    (← readRef (ws / "store") .trees "T2").isNone && (← readRef (ws / "store") .partial "T2").isNone &&
    !(← (ws / "generated/T2").pathExists) && (← readOptional (ws / "trees/T2/verdict")) == some "retired" &&
    !(← readSealedModules ws).any (fun m => m.modName.segments.take 2 == ["Gen","T2"])) "incomplete horizontal retirement"
  -- Replay a ready journal after the old sealed ref has already been removed.
  writeRef (ws / "store") .partial "T2" oldTip.get!
  atomicText (ws / ".publication/retire.sexp") "(\"T2\")"
  atomicText (ws / ".publication/ready") "T2b"
  withWorkspaceLock ws do
    ensure ((← readRef (ws / "store") .partial "T2").isNone && (← sealedNames ws).contains "T2b") "retirement recovery"
  let inspect := ScriptedBackend fun req => do
    let summaries := ((req.prompt.splitOn "\nSEALED TREES\n").getLast!.splitOn "\nRECENT ACTION OUTCOMES\n").head!
    ensure (summaries.contains n && !summaries.contains peer) "retired T2 appeared in live tree summaries"
    return "(session-action (kind finish) (summary \"replacement verified\"))"
  discard <| runSession {cfg with backend := inspect}
  for model in [false,true] do innocentOnRefutation cfg model
  IO.println "   Three-layer obstruction cascade, pinned repair, memory routing, zero-turn siblings and atomic T2 replacement"

private def transportAuditRegressions (ws repo : FilePath) : IO Unit := do
  -- Part A (C2 + S5): T0 v1 -> T1 v1 ok -> T0 v2 -> T1 liftObstruction (partial pinned to T0 v2,
  -- root code verified against T0 v1, candidate-era Escape spec) -> T0 v3 -> T1 ok.
  let c2Ws := ws / "c2-partial-history"
  initWorkspace c2Ws
  let cfg : SessionConfig := ⟨repo, c2Ws, "Test partial-seeded root history",
    ⟨.local "/bin/true", [], 5000⟩, ScriptedBackend (fun _ => fail "unexpected proposal"), false⟩
  let t0Root := "Gen.T0.R"
  let t0Helper := t0Root ++ ".Helper"
  let t0Legacy := t0Root ++ ".Legacy"
  let t0Bad := t0Root ++ ".Bad"
  let t0Good := t0Root ++ ".Good"
  let t1Root := "Gen.T1.R"
  let t1Esc := t1Root ++ ".Escape"
  let t1Parse := t1Root ++ ".ParseLine"
  let t0Spec ← object t0Root "axiom run : Nat"
  let helperSpec ← object t0Helper "axiom helper : Nat"
  let helperImpl ← object t0Helper "def helper : Nat := 10"
  let legacySpec ← object t0Legacy "axiom api : Nat"
  let legacyImpl ← object t0Legacy "def api : Nat := 1"
  let badSpec ← object t0Bad "axiom api : Nat\naxiom isZero : api = 0"
  let badImpl ← object t0Bad "def api : Nat := 0\ntheorem isZero : api = 0 := rfl"
  let goodSpec ← object t0Good "axiom api : Nat\naxiom isOne : api = 1"
  let goodImpl ← object t0Good "def api : Nat := 1\ntheorem isOne : api = 1 := rfl"
  -- T0 v1
  let t0V1Glue ← object t0Root s!"def run : Nat := {t0Helper}.helper + {t0Legacy}.api" [t0Helper, t0Legacy]
  discard <| checkedDrive cfg t0Spec [t0Root, t0Helper, t0Legacy] fun node => do
    if node.task.delta.child == q t0Root then return plan node.old t0V1Glue [helperSpec, legacySpec]
    if node.task.delta.child == q t0Helper then return plan node.old helperImpl
    return plan node.old legacyImpl
  -- T1 v1 (sealed against T0 v1; root code directly imports Gen.T0.R.Legacy!)
  let t1Spec1 ← object t1Root "axiom run : Nat"
  let t1EscSpec1 ← object t1Esc "axiom escape : Nat"
  let t1EscImpl1 ← object t1Esc s!"def escape : Nat := {t0Helper}.helper" [t0Helper]
  let t1ParseSpec1 ← object t1Parse "axiom parse : Nat"
  let t1ParseImpl1 ← object t1Parse s!"def parse : Nat := {t0Legacy}.api" [t0Legacy]
  let t1Glue1 ← object t1Root
    s!"def run : Nat := {t1Esc}.escape + {t1Parse}.parse + {t0Legacy}.api" [t1Esc, t1Parse, t0Legacy]
  let t1Lift1 := LiftSpec.liftSpecTree (q t0Root) (q t1Root)
    [.mkChildLift (q t0Helper) (q t1Esc) none, .mkChildLift (q t0Legacy) (q t1Parse) none] []
  discard <| checkedDrive cfg t1Spec1 [t1Root, t1Esc, t1Parse] (fun node => do
    if node.task.delta.child == q t1Root then return plan node.old t1Glue1 [t1EscSpec1, t1ParseSpec1]
    if node.task.delta.child == q t1Esc then return plan node.old t1EscImpl1
    return plan node.old t1ParseImpl1) ["T0"] t1Lift1
  -- T0 v2 (drops Legacy, adds Bad)
  let t0V2Glue ← object t0Root s!"def run : Nat := {t0Helper}.helper + {t0Bad}.api" [t0Helper, t0Bad]
  discard <| checkedDrive cfg t0Spec [t0Root, t0Bad] fun node => do
    if node.task.delta.child == q t0Root then
      return plan node.old t0V2Glue [helperSpec, badSpec] [⟨.ext (q t0Legacy), .bot⟩]
    return plan node.old badImpl
  -- T1 re-drive against T0 v2: Escape seals with a candidate-era spec (S5!), ParseLine hits liftObstruction!
  let t1EscSpec2 ← object t1Esc "axiom escape : Nat\naxiom extra : Nat"
  let t1EscImpl2 ← object t1Esc s!"def escape : Nat := {t0Helper}.helper\ndef extra : Nat := 1" [t0Helper]
  let t1ParseSpec2 ← object t1Parse
    s!"axiom parse : Nat\naxiom project : parse = {t0Bad}.api\naxiom nonZero : parse = 1" [t0Bad]
  let t1Glue2 ← object t1Root
    s!"def run : Nat := {t1Esc}.escape + {t1Esc}.extra + {t1Parse}.parse" [t1Esc, t1Parse]
  let t1Spec2 ← object t1Root "axiom run : Nat"
  let t1Lift2 := LiftSpec.liftSpecTree (q t0Root) (q t1Root)
    [.mkChildLift (q t0Helper) (q t1Esc) none, .mkChildLift (q t0Bad) (q t1Parse) none] []
  let badProof ← object (t1Root ++ ".Evidence")
    s!"theorem impossible : False := Nat.one_ne_zero ({t1Parse}.nonZero.symm.trans ({t1Parse}.project.trans {t0Bad}.isZero))"
    [t0Bad, t1Parse]
  discard <| checkedDrive cfg t1Spec2 [t1Root, t1Esc, t1Parse] (fun node => do
    if node.task.delta.child == q t1Root then
      return plan node.old t1Glue2 [t1EscSpec2, t1ParseSpec2] [⟨.ext (q t0Legacy), .bot⟩]
    if node.task.delta.child == q t1Esc then return plan node.old t1EscImpl2
    return envelope "submission" [field "kind" [.sym "refute-lift"], field "why" [.str "Bad.api is zero"],
      field "refute" [.str (renderLeanMod badProof)]]) ["T0"] t1Lift2 none [] "lift-obstruction"
  -- T0 v3 (drops Bad, adds Good)
  let t0V3Glue ← object t0Root s!"def run : Nat := {t0Helper}.helper + {t0Good}.api" [t0Helper, t0Good]
  discard <| checkedDrive cfg t0Spec [t0Root, t0Good] fun node => do
    if node.task.delta.child == q t0Root then
      return plan node.old t0V3Glue [helperSpec, goodSpec] [⟨.ext (q t0Bad), .bot⟩]
    return plan node.old goodImpl
  -- Inspect initialHomeWithBases: root code (from T1 v1) MUST pin T0 v1 (Legacy),
  -- while otherChildHistory pins Escape (from T1 partial) to T0 v2 (Bad)!
  let init ← initialHomeWithBases c2Ws "T1" t1Spec2
  ensure (init.oldBaseModules.any (fun ms => ms.any (·.modName == q t0Legacy) && !ms.any (·.modName == q t0Bad)))
    "C2: partial-seeded root did not preserve complete commit's T0 v1 vertical base"
  ensure (init.otherChildHistory.any fun (slots, ms) => slots == [t1Esc] && ms.any (·.modName == q t0Bad))
    "C2: partial-verified child Escape did not retain T0 v2 vertical base in otherChildHistory"
  -- Re-drive T1 against T0 v3 -> T1 root elaborates T1 v1 code against T0 v1 (with S5 protecting oldStubs
  -- from candidate-era Escape_v2.spec), Escape gets T0 v2 history, ParseLine gets T0 v1 history, and T1 seals!
  let t1EscSpec3 ← object t1Esc "axiom escape : Nat\naxiom extra : Nat\naxiom tag : Nat"
  let t1EscImpl3 ← object t1Esc s!"def escape : Nat := {t0Helper}.helper\ndef extra : Nat := 1\ndef tag : Nat := 2" [t0Helper]
  let t1ParseSpec3 ← object t1Parse
    s!"axiom parse : Nat\naxiom project : parse = {t0Good}.api\naxiom nonZero : parse = 1" [t0Good]
  let t1ParseImpl3 ← object t1Parse
    s!"def parse : Nat := {t0Good}.api\ntheorem project : parse = {t0Good}.api := rfl\ntheorem nonZero : parse = 1 := {t0Good}.isOne"
    [t0Good]
  let t1Glue3 ← object t1Root s!"def run : Nat := {t1Esc}.escape + {t1Parse}.parse" [t1Esc, t1Parse]
  let t1Lift3 := LiftSpec.liftSpecTree (q t0Root) (q t1Root)
    [.mkChildLift (q t0Helper) (q t1Esc) none, .mkChildLift (q t0Good) (q t1Parse) none] []
  discard <| checkedDrive cfg t1Spec2 [t1Root, t1Esc, t1Parse] (fun node => do
    let owner := node.task.delta.child
    if owner == q t1Root then
      ensure (node.task.oldBaseModules.any (·.any (·.modName == q t0Legacy))) "C2: T1 root lost T0 v1 history"
      return plan node.old t1Glue3 [t1EscSpec3, t1ParseSpec3] [⟨.ext (q t0Legacy), .bot⟩]
    if owner == q t1Esc then
      ensure (node.task.oldBaseModules.any (·.any (·.modName == q t0Bad))) "C2: T1 Escape lost T0 v2 partial history"
      return plan node.old t1EscImpl3
    ensure (node.task.oldBaseModules.any (·.any (·.modName == q t0Legacy))) "C2: T1 ParseLine lost T0 v1 history"
    return plan node.old t1ParseImpl3 [] [⟨.ext (q t0Legacy), .bot⟩]) ["T0"] t1Lift3
  discard <| auditTrees c2Ws

  -- Part B (C4): Early root descriptor validation in prepareSpec / check_spec / driveTree (0 node turns).
  let c4Ws := ws / "c4-early-validation"
  initWorkspace c4Ws
  let neverCallCfg : SessionConfig := ⟨repo, c4Ws, "Reject invalid descriptors in 0 turns",
    ⟨.local "/bin/true", [], 5000⟩, ScriptedBackend (fun req => fail s!"node should not run: {req.owner}"), false⟩
  -- B1: Partial tree P has empty root code and verified child Escape. A TransportSpec omitting Escape
  -- must be rejected immediately in prepareSpec / check_spec / driveTree with unaccountedOldChild.
  let pBase ← object "Gen.B0.R" "def bad : Nat := 0\ntheorem isZero : bad = 0 := rfl"
  discard <| publishTree c4Ws "B0" "base" [] [] .ok (Frozen.frozen pBase [] pBase [])
  let pSpec ← object "Gen.P1.R" "axiom val : Nat"
  let pEscSpec ← object "Gen.P1.R.Escape" "axiom v : Nat"
  let pEscImpl ← object "Gen.P1.R.Escape" "def v : Nat := 1"
  let pPartial := Frozen.frozen ⟨q "Gen.P1.R", [], [], []⟩ [] pSpec
    [("Gen.P1.R.Escape", Frozen.frozen pEscImpl [] pEscSpec [])]
  let b0Tips := (← loadCurrentClosure c4Ws ["B0"]).directTips
  let pObsProof ← object "Gen.P1.Obs" "theorem t : True := trivial"
  discard <| publishTree c4Ws "P1" "partial with child" ["B0"] b0Tips (.liftObstruction "bad" [q "Gen.B0.R.isZero"] pObsProof) pPartial
  let qSpec ← object "Gen.Q1.R" "axiom val : Nat"
  let missingChildTs := (encodeTransportSpec (.transportSpecTree (q "Gen.P1.R") (q "Gen.Q1.R") [] [])).canonical
  expectError "unaccountedOldChild" (prepareSpec c4Ws "Q1" (renderLeanMod qSpec) [] none (some missingChildTs))
  expectError "unaccountedOldChild" (driveTree neverCallCfg "Q1" "zero turns" (renderLeanMod qSpec) [] none (some missingChildTs))
  let mcpCtx := c4Ws / "mcp-c4"
  IO.FS.createDirAll mcpCtx
  let rpcArgs := Lean.Json.mkObj [
    ("spec_block", Lean.toJson (renderLeanMod qSpec)),
    ("base_trees", Lean.toJson ([] : List String)),
    ("transport_src", Lean.toJson missingChildTs)]
  let rpcReq := (Lean.Json.mkObj [
    ("jsonrpc", "2.0"), ("id", Lean.toJson (1 : Nat)), ("method", "tools/call"),
    ("params", Lean.Json.mkObj [("name", "check_spec"), ("arguments", rpcArgs)])]).compress
  let rpc ← IO.Process.output {
    cmd := (repo / "lojita").toString
    args := #["mcp", "--mode", "session", "--repo", repo.toString, "--workspace", c4Ws.toString, "--ctx-dir", mcpCtx.toString]
  } (some rpcReq)
  ensure (rpc.exitCode == 0 && rpc.stdout.contains "\"isError\":true" && rpc.stdout.contains "unaccountedOldChild")
    s!"C4 MCP check_spec did not reject unaccountedOldChild: {rpc.stdout}"
  -- B2: Kept child Decode with grandchild Sub whose LiftSpec fails checkKeptLifts
  -- (explicit empty grandchild map -> missingChildMap, missing square -> missingSquare) rejected in 0 node turns.
  let mkNested := fun (rootName : String) (withBase : Option String) => do
    let dec := rootName ++ ".Decode"
    let sub := dec ++ ".Sub"
    let subSpec ← object sub "axiom val : Nat"
    let subImpl ← match withBase with
      | none => object sub "def val : Nat := 7"
      | some b => object sub s!"def val : Nat := {b}.Decode.Sub.val\ntheorem sq : val = {b}.Decode.Sub.val := rfl" [b ++ ".Decode.Sub"]
    let decSpec ← object dec "axiom val : Nat"
    let decCode ← object dec s!"def val : Nat := {sub}.val" [sub]
    let decHome := Frozen.frozen (withChildIfaces decCode [subSpec]) [] decSpec [(sub, Frozen.frozen subImpl [] subSpec [])]
    let rootSpec ← object rootName "axiom val : Nat"
    let rootCode ← object rootName s!"def val : Nat := {dec}.val" [dec]
    return Frozen.frozen (withChildIfaces rootCode [decSpec]) [] rootSpec [(dec, decHome)]
  let lowerHome ← mkNested "Gen.Base2.R" none
  let oldHome ← mkNested "Gen.Old2.R" (some "Gen.Base2.R")
  discard <| publishTree c4Ws "Base2" "base2" [] [] .ok lowerHome
  let base2Closure ← loadCurrentClosure c4Ws ["Base2"]
  verifyClosure base2Closure.modules oldHome
  discard <| publishTree c4Ws "Old2" "old2" ["Base2"] base2Closure.directTips .ok oldHome
  let new2Spec ← object "Gen.New2.R" "axiom val : Nat"
  let keepDec := (encodeTransportSpec (.transportSpecTree (q "Gen.Old2.R") (q "Gen.New2.R")
    [.keepChild (q "Gen.Old2.R.Decode") (q "Gen.New2.R.Decode")] [])).canonical
  let badEmptySubLift := (encodeLiftSpec (.liftSpecTree (q "Gen.Base2.R") (q "Gen.New2.R")
    [.mkChildLift (q "Gen.Base2.R.Decode") (q "Gen.New2.R.Decode")
      (some (.liftSpecTree (q "Gen.Base2.R.Decode") (q "Gen.New2.R.Decode") [] []))] [])).canonical
  let badMissingSqLift := (encodeLiftSpec (.liftSpecTree (q "Gen.Base2.R") (q "Gen.New2.R")
    [.mkChildLift (q "Gen.Base2.R.Decode") (q "Gen.New2.R.Decode")
      (some (.liftSpecTree (q "Gen.Base2.R.Decode") (q "Gen.New2.R.Decode")
        [.mkChildLift (q "Gen.Base2.R.Decode.Sub") (q "Gen.New2.R.Decode.Sub")
          (some (.liftSpecTree (q "Gen.Base2.R.Decode.Sub") (q "Gen.New2.R.Decode.Sub") []
            [endpointLift (q "Gen.Base2.R.Decode.Sub.val") (q "Gen.New2.R.Decode.Sub.val") (q "Gen.New2.R.Decode.Sub.absent")]))] []))] [])).canonical
  expectError "missingChildMap" (driveTree neverCallCfg "New2" "bad sub lift" (renderLeanMod new2Spec) ["Base2"]
    (some badEmptySubLift) (some keepDec))
  expectError "missingSquare" (driveTree neverCallCfg "New2" "bad sq lift" (renderLeanMod new2Spec) ["Base2"]
    (some badMissingSqLift) (some keepDec))

  -- Part C (S4a/b): replaces transport-source enforcement & STALE diagnostics for unsealed/partial trees.
  let s4Ws := ws / "s4-replaces-stale"
  initWorkspace s4Ws
  let s4Cfg : SessionConfig := ⟨repo, s4Ws, "Check replaces and partial STALE diagnostics",
    ⟨.local "/bin/true", [], 5000⟩, ScriptedBackend (fun _ => fail "unexpected proposal"), false⟩
  let bSpec ← object "Gen.Base.R" "axiom v : Nat"
  let bImpl ← object "Gen.Base.R" "def v : Nat := 1"
  discard <| publishTree s4Ws "Base" "base" [] [] .ok (Frozen.frozen bImpl [] bSpec [])
  let bTips := (← loadCurrentClosure s4Ws ["Base"]).directTips
  let mkPeer := fun (epoch : String) (v : Nat) => do
    let r := "Gen." ++ epoch ++ ".R"
    let sp ← object r "axiom v : Nat"
    let im ← object r s!"def v : Nat := Gen.Base.R.v + {v}" ["Gen.Base.R"]
    return Frozen.frozen im [] sp []
  let p1Home ← mkPeer "Peer1" 1
  let p2Home ← mkPeer "Peer2" 2
  discard <| publishTree s4Ws "Peer1" "peer1" ["Base"] bTips .ok p1Home
  discard <| publishTree s4Ws "Peer2" "peer2" ["Base"] bTips .ok p2Home
  let newPeerSpec ← object "Gen.Peer1b.R" "axiom v : Nat"
  let wrongTs := (encodeTransportSpec (.transportSpecTree (q "Gen.Peer2.R") (q "Gen.Peer1b.R") [] [])).canonical
  let peer1Lift := (encodeLiftSpec (.liftSpecTree (q "Gen.Base.R") (q "Gen.Peer1b.R") [] [])).canonical
  expectError "MISSING_REPLACEMENT_TRANSPORT" (prepareSpec s4Ws "Peer1b" (renderLeanMod newPeerSpec) ["Base"] (some peer1Lift) none ["Peer1"])
  expectError "MISSING_REPLACEMENT_TRANSPORT" (prepareSpec s4Ws "Peer1b" (renderLeanMod newPeerSpec) ["Base"] (some peer1Lift) (some wrongTs) ["Peer1"])
  -- Create a partial/obstructed tree Dep depending on Peer1.
  let depSpec ← object "Gen.Dep.R" "axiom v : Nat"
  let depPartial := Frozen.frozen ⟨q "Gen.Dep.R", [], [], []⟩ [] depSpec []
  let p1Tips := (← loadCurrentClosure s4Ws ["Peer1"]).directTips
  discard <| publishTree s4Ws "Dep" "partial dep" ["Peer1"] p1Tips (.liftObstruction "blocked" [q "Gen.Peer1.R.v"] pObsProof) depPartial
  -- Before Peer1 changes, Dep is not stale.
  ensure (← partialStaleViews s4Ws).isEmpty "unchanged partial tree should not be stale"
  -- Driving a downstream tree against unsealed partial Dep surfaces STALE_ANCESTOR_TREE (not bare unsealed base).
  expectError "STALE_ANCESTOR_TREE" (prepareSpec s4Ws "AboveDep" (modSrc "Gen.AboveDep.R" "axiom v : Nat") ["Dep"] none none)
  -- Update Peer1 in place -> partialStaleViews flags Dep with STALE_PARTIAL_TREE!
  let p1HomeV2 ← mkPeer "Peer1" 3
  discard <| publishTree s4Ws "Peer1" "peer1 v2" ["Base"] bTips .ok p1HomeV2
  let staleAfterUpdate ← partialStaleViews s4Ws
  ensure (staleAfterUpdate.any fun v => v.name == "Dep" && v.stale.any (·.contains "STALE_PARTIAL_TREE"))
    s!"S4b: partialStaleViews missed updated base for Dep: {staleAfterUpdate.map (·.stale)}"
  -- Replace Peer1 with Peer1b -> Dep now references retired Peer1!
  let p1bHome ← mkPeer "Peer1b" 4
  discard <| publishTree s4Ws "Peer1b" "replace peer1" ["Base"] bTips .ok p1bHome ["Peer1"] [q "Gen.Peer1.R"]
  let staleAfterReplace ← partialStaleViews s4Ws
  ensure (staleAfterReplace.any fun v => v.name == "Dep" && v.stale.any (fun s => s.contains "STALE_ANCESTOR_TREE" && s.contains "retired/replaced"))
    s!"S4b: partialStaleViews missed retired base for Dep: {staleAfterReplace.map (·.stale)}"
  expectError "STALE_ANCESTOR_TREE" (prepareSpec s4Ws "Dep" (renderLeanMod depSpec) ["Peer1"] none none)
  let sawStalePartial ← IO.mkRef false
  let sessionInspect := ScriptedBackend fun req => do
    if req.prompt.contains "Dep (partial/lift-obstruction)" &&
        req.prompt.contains "[STATUS: STALE AGAINST UPDATED OR REPLACED BASE — RE-DRIVE THIS TREE]" &&
        req.prompt.contains "retired/replaced" then
      sawStalePartial.set true
    return "(session-action (kind finish) (summary \"inspected stale partial\"))"
  discard <| runSession {s4Cfg with backend := sessionInspect}
  ensure (← sawStalePartial.get) "S4b: SESSION_ROOT did not see STALE status for partial Dep"
  IO.println "   C2/S5 partial-seeded root history, C4 0-turn descriptor checks, and S4a/b replaces/STALE diagnostics passed"

private def promptExamples (dir ws repo : FilePath) : IO Unit := do
  let ds ← loadDrafts dir
  let known := ["measure-spec","measure","measure-plan","char-spec","model","refute","counterexample",
    "observe","observe-action","blueprint-spec","drive-base","base-label-spec","base-label","blueprint","blueprint-plan",
    "upper-spec","lifting","transport","drive-upper","build","compare","replay-action","done",
    "label-spec","route-spec","dispatch","dispatch-plan","label-impl","route-impl"]
  ensure (known.all ds.contains && ds.size == known.length) "every teaching block needs an executable example check"
  let read := fun n => ds[n]!.trimAscii.toString
  let actions := #[read "observe-action",drive "Count" (read "measure-spec"),drive "Glyph" (read "char-spec"),
    read "drive-base",read "drive-upper",read "build",read "replay-action",read "done"]
  let turn ← IO.mkRef 0
  let ai := ScriptedBackend fun req => do
    for (n,s) in ds do atomicText (req.ctxDir / "drafts" / (n ++ ".block")) s
    if req.retry then fail s!"prompt example rejected: {(req.prompt.splitOn "TRANSIENT DIAGNOSTIC").getLast!}"
    if let some node := req.node then
      match req.owner with
      | "Gen.Count.Measure" => return read "measure-plan"
      | "Gen.Glyph.Algebra" => return read "counterexample"
      | "Gen.T0.Doc" => return read "blueprint-plan"
      | "Gen.T0.Doc.Label" => return plan node.old (← IO.ofExcept (parseLeanMod (read "base-label")))
      | "Gen.T1.Doc" => return read "dispatch-plan"
      | "Gen.T1.Doc.Label" =>
        ensure (node.task.lifts.map (·.2.base) == [q "Gen.T0.Doc.Label"]) "Label lost its child lift"
        return plan node.old (← IO.ofExcept (parseLeanMod (read "label-impl")))
      | "Gen.T1.Doc.Route" =>
        ensure (node.task.lifts.isEmpty && (readableAncestors node.task).isEmpty) "Route inherited a base child"
        return plan node.old (← IO.ofExcept (parseLeanMod (read "route-impl")))
      | _ => fail s!"unexpected teaching node {req.owner}"
    let i ← turn.get
    let some act := actions[i]? | fail "example actions exhausted"
    if i == 1 then ensure (req.prompt.contains "32 samples agree") "pre-spec fuzz observations did not reach root"
    if i == 3 then ensure (req.prompt.contains "countermodel") "countermodel did not reach root"
    turn.set (i+1)
    return act
  let reference := r#"if [ "${LOJITA_TAG+x}" = x ]; then
  exec >&2
  printf '%s' "$LOJITA_TAG"
fi
exec /bin/cat"#
  let ref : RefSpec := ⟨.local "/bin/sh",["-c",reference],5000⟩
  let cfg : SessionConfig := ⟨repo,ws,"Exercise the teaching examples",ref,ai,true⟩
  -- This reference passes the old "abc\n" probe but deletes byte 105 from the fuzz corpus.
  let divergent ← runScript repo ws {ref with arguments := ["-c", "exec tr -d i"]} (read "observe")
  ensure (divergent.exitCode == 1 && divergent.usedRef && !divergent.usedCand &&
    divergent.stderr.endsWith " -> [105]") s!"observe missed or failed to shrink the mismatch: {divergent.stderr}"
  discard <| runSession cfg
  for tag in [none,some "",some "label:"] do
    let result ← IO.Process.output {cmd := (ws / "bin/candidate").toString, env := #[("LOJITA_TAG",tag)]} (some "sample\n")
    let expected := tag.elim ("sample\n","") (fun s => ("",s ++ "sample\n"))
    ensure (result.exitCode == 0 && (result.stdout,result.stderr) == expected) "two-child CLI stream routing"
  ensure ((← readOptional (ws / "trees/Glyph/verdict")).any (·.startsWith "countermodel")) "model example not checked"
  IO.println s!"1  Verified {ds.size} teaching blocks through kernel, Plan, Lift, PolyTransport, Countermodel and typed probes"

private def protocols : IO Unit := do
  let saved := ({} : DraftStore).insert "code" "old"
  for lang in ["lean","agda","sexp"] do
    let text := "(session-action (kind run-script) (why \"test\") (source @code))\n```" ++ lang ++ " code\nnew\n```"
    ensure ((parseSessionAction text saved).toOption == some (.runScript "test" "new")) s!"bad {lang} fence resolution"
  for s in ["(session-action (kind build-exe) (entry \"Gen.X.app\") (why \"x\") (source \"bad\"))",
      "(session-action (kind finish) (summary \"ok\") (summary \"bad\"))","(session-action (kind run-script) (why \"x\") (source @missing))"] do
    ensure (!(parseSessionAction s saved).isOk && !(explainSessionActionFailure s saved).isEmpty) "accepted invalid session action"
  for r in ["(ref-target (docker \"image\" \"/usr/bin/test\") (timeoutMs 25))","(ref-target (local \"/bin/cat\") (args \"-u\"))"] do
    let ref ← IO.ofExcept (parseRefSpec r)
    ensure ((parseRefSpec (encodeRefSpec ref).canonical).toOption == some ref) "reference roundtrip"

private def threadLifecycle (dir repo : FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  ensure ((← IO.getEnv "CODETRANSPORT_CODEX_BIN") == some (repo / "Test/S4/fake-codex.py").toString)
    "offline thread test requires the fixture executable"
  let cfg : CodexConfig := {
    repo, workspace := dir, refFile := dir / "ref.sexp"
    rolloutDir := some (dir / "sessions")}
  let req : TurnRequest := {owner := "SESSION_ROOT", ctxDir := dir / "ctx", prompt := "proposal", retry := false}
  let b ← CodexCLIBackend cfg
  let scratch ← b.propose req
  let main ← IO.FS.readFile (dir / "threads/SESSION_ROOT.id")
  ensure (scratch != main) "proposal wrote the durable thread"
  atomicText (req.ctxDir / "drafts/proof.block") "draft"
  ensure ((← b.propose {req with retry := true, prompt := "proposal retry"}) == scratch) "mechanical retry lost scratch"
  ensure ((← readOptional (req.ctxDir / "latest-prompt")) == some "proposal retry" &&
    (← readOptional (req.ctxDir / "latest-reply")) == some scratch) "missing turn transcript"
  ensure ((← readOptional (req.ctxDir / "drafts/proof.block")) == some "draft") "retry lost draft"
  b.accept req.owner "semantic"
  ensure (!(← (dir / "sessions" / (scratch ++ ".jsonl")).pathExists) &&
    !(← (req.ctxDir / "drafts/proof.block").pathExists)) "accepted scratch survived"
  let restarted ← CodexCLIBackend cfg
  let fresh ← restarted.propose req
  ensure (fresh != main && fresh != scratch) "new proposal reused a retired thread"
  restarted.retire req.owner
  ensure ((← IO.FS.readFile (dir / "threads/SESSION_ROOT.id")) == main &&
    (← IO.FS.readFile (dir / "sessions" / (main ++ ".jsonl"))).contains "semantic") "durable history lost"
  ensure ((← IO.FS.readFile (dir / "calls")).splitOn "\n" == ["new","fork","resume","resume","fork",""])
    "unexpected Codex CLI command sequence"
  let spec ← object "Gen.Threads.Leaf" "axiom value : Nat"
  let task : NodeTask := {delta := ⟨spec.modName,[],spec⟩}
  let owner := toString spec.modName
  let node : AIRequest := ⟨task,spec,[],none,none⟩
  discard <| restarted.propose {owner, ctxDir := dir / "node-ctx", prompt := "proposal node", retry := false, node := some node}
  restarted.accept owner "node semantic"
  ensure ((← IO.FS.readFile (dir / "threads" / (owner ++ ".id"))) != main) "node reused the session thread"

private def concurrentCancellation (dir repo : FilePath) : IO Unit := do
  initWorkspace dir
  let root := "Gen.T0.CancelRoot"
  let bad := root ++ ".FastBad"
  let kept := root ++ ".SlowKept"
  let dropped := root ++ ".VerySlowDropped"
  let spec ← object root "axiom value : Nat"
  let innocent ← object kept "axiom value : Nat"
  let obsolete ← object dropped "axiom value : Nat"
  let impossible ← object bad "def zero : Nat := 0\naxiom impossible : zero = 1"
  let first ← object root s!"def value := {kept}.value + {dropped}.value" [kept,dropped,bad]
  let repaired ← object root s!"def value := {kept}.value" [kept]
  let removals : List Proarrow := [⟨.ext (q bad), .bot⟩, ⟨.ext (q dropped), .bot⟩]
  let evidence ← object "CancelEvidence" s!"theorem witness : False := Nat.zero_ne_one {bad}.impossible" [bad]
  let refute := envelope "submission" [field "kind" [.sym "contradiction"], field "refute" [.str (renderLeanMod evidence)]]
  let blank := fun (m : LeanMod) => LeanMod.mk m.modName [] [] []
  let leaf := fun (name : String) => do
    let m ← object name "def value : Nat := 42"
    return plan (blank m) m
  let step := fun (ms : Nat) (reply : String) => Lean.Json.mkObj [("sleepMs", Lean.toJson ms), ("reply", Lean.toJson reply)]
  let script := Lean.Json.mkObj [
    (root, .arr #[step 0 (plan (blank first) first [innocent,obsolete,impossible]),
      step 0 (plan first repaired [innocent] removals)]),
    (kept, .arr #[step 250 (← leaf kept)]),
    (dropped, .arr #[(step 15000 (← leaf dropped)).setObjVal! "pidFile" "dropped.pid"]),
    (bad, .arr #[step 10 refute])]
  let path := dir / "cancel-plan.json"
  atomicText path script.compress
  let backend ← CodexCLIBackend {repo, workspace := dir, refFile := dir / "ref.sexp", rolloutDir := dir / "sessions"}
  let cfg : SessionConfig := ⟨repo,dir,"Cancel the obsolete child",⟨.local "/bin/true",[],5000⟩,backend,false⟩
  let previous ← IO.getEnv "LOJITA_FAKE_CODEX_PLAN"
  Std.Async.System.setEnvVar "LOJITA_FAKE_CODEX_PLAN" path.toString
  let start ← IO.monoMsNow
  let result ← try driveTree cfg "T0" "repair while siblings run" (renderLeanMod spec) [] none none
    finally
      match previous with
      | some p => Std.Async.System.setEnvVar "LOJITA_FAKE_CODEX_PLAN" p
      | none => Std.Async.System.unsetEnvVar "LOJITA_FAKE_CODEX_PLAN"
  let ms := (← IO.monoMsNow) - start
  ensure (result == "ok" && ms < 4000) s!"cancellation tree returned {result} after {ms} ms"
  let calls := (← IO.FS.readFile (dir / "calls")).splitOn "\n"
  let fork := fun (owner : String) => do
    let [line] := calls.filter (·.startsWith (owner ++ " propose fork ")) | fail s!"expected one {owner} fork: {calls}"
    return (line.splitOn " ").getLast!
  let keepId ← fork kept
  let dropId ← fork dropped
  let rootId ← fork root
  ensure (calls.contains s!"{kept} replied fork {keepId}" &&
    calls.idxOf s!"{root} replied resume {rootId}" < calls.idxOf s!"{kept} replied fork {keepId}")
    "SlowKept did not survive the parent's repair in flight"
  let some pid := (← IO.FS.readFile (dir / "dropped.pid")).toNat? | fail "missing dropped subprocess PID"
  let alive ← IO.Process.output {cmd := "kill", args := #["-0",toString pid]}
  let main ← IO.FS.readFile (dir / "threads" / (dropped ++ ".id"))
  ensure (alive.exitCode != 0 && !calls.contains s!"{dropped} replied fork {dropId}") "dropped subprocess survived"
  ensure (main != dropId && (← (dir / "sessions" / (main ++ ".jsonl")).pathExists)) "dropped owner's durable thread lost"
  ensure (!(← (dir / "sessions" / (dropId ++ ".jsonl")).pathExists) &&
    !(← (dir / "trees/T0/ai" / dropped / "drafts").pathExists)) "dropped scratch thread or drafts survived"
  IO.println s!"   Concurrent Codex tree sealed in {ms} ms, kept one fork and reaped dropped PID {pid}"

private def sessionTurnResilience (ws repo : FilePath) : IO Unit := do
  let ref : RefSpec := ⟨.local "/bin/true", [], 5000⟩
  let seedTree := fun (dir : FilePath) => do
    initWorkspace dir
    let sp ← object "Gen.Base.R" "axiom v : Nat"
    let im ← object "Gen.Base.R" "def v : Nat := 1"
    discard <| publishTree dir "Base" "seed" [] [] .ok (Frozen.frozen im [] sp [])
  -- Direct parser checks on extractTurnFailure?
  let turnFailedErr := "codex exec (1): raw stderr noise\n" ++
    "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-0000-0000-000000000001\"}\n" ++
    "{\"type\":\"item.completed\",\"item\":{\"type\":\"mcp_tool_call\",\"payload\":\"RAW_TOOL_CALL_PAYLOAD\"}}\n" ++
    "{\"type\":\"turn.failed\",\"error\":{\"message\":\"transient upstream error\"}}\n"
  ensure (extractTurnFailure? turnFailedErr == some "transient upstream error")
    s!"extractTurnFailure? missed turn.failed: {repr (extractTurnFailure? turnFailedErr)}"
  let bottomToTopErr := "codex exec (1): \n" ++
    "{\"type\":\"error\",\"message\":\"earlier reconnect warning\"}\n" ++
    "{\"type\":\"turn.failed\",\"error\":{\"message\":\"final turn failure\"}}\n"
  ensure (extractTurnFailure? bottomToTopErr == some "final turn failure")
    s!"extractTurnFailure? did not scan bottom-to-top: {repr (extractTurnFailure? bottomToTopErr)}"
  let errorEventErr := "codex exec (1): \n" ++
    "{\"type\":\"item.completed\",\"raw\":\"RAW_ERROR_STDOUT\"}\n" ++
    "{\"type\":\"error\",\"message\":\"transient gateway reset\"}\n"
  ensure (extractTurnFailure? errorEventErr == some "transient gateway reset")
    s!"extractTurnFailure? missed error event: {repr (extractTurnFailure? errorEventErr)}"
  ensure (extractTurnFailure? "{\"type\":\"turn.failed\",\"error\":{\"message\":\"missing prefix\"}}" == none)
    "extractTurnFailure? triggered without codex exec prefix"
  ensure (extractTurnFailure? "codex exec (1): fatal non-json cli error\n" == none)
    "extractTurnFailure? triggered without JSON failure event"
  ensure (extractTurnFailure? "unexpected proposal" == none)
    "extractTurnFailure? triggered on non-codex error"

  -- 1) turn.failed retires SESSION_ROOT, forwards only the clean reason in TRANSIENT DIAGNOSTIC, and finishes on turn 2.
  let ws1 := ws / "turn-failed-recovery"
  seedTree ws1
  let turn1 ← IO.mkRef 0
  let retired1 ← IO.mkRef ([] : List String)
  let accepted1 ← IO.mkRef 0
  let sawDiag1 ← IO.mkRef false
  let backend1 : Backend := {
    propose := fun req => do
      let n ← turn1.modifyGet fun i => (i, i + 1)
      if n == 0 then
        ensure (!req.retry) "turn 1 should not be marked retry"
        fail turnFailedErr
      else if n == 1 then
        ensure req.retry "turn 2 after turn.failed must set retry=true"
        ensure ((← retired1.get) == ["SESSION_ROOT"])
          s!"expected retire SESSION_ROOT before turn 2, got {← retired1.get}"
        let diag := (req.prompt.splitOn "TRANSIENT DIAGNOSTIC").getLast!
        ensure (diag.contains "transient upstream error")
          s!"missing turn.failed message in TRANSIENT DIAGNOSTIC: {diag}"
        ensure (!diag.contains "RAW_TOOL_CALL_PAYLOAD" && !diag.contains "raw stderr noise" && !diag.contains "thread.started")
          s!"raw stdout/stderr leaked into TRANSIENT DIAGNOSTIC: {diag}"
        sawDiag1.set true
        return "(session-action (kind finish) (summary \"recovered after turn.failed\"))"
      else
        fail s!"unexpected extra turn {n}"
    accept := fun owner _ => do
      ensure (owner == "SESSION_ROOT") s!"unexpected accept owner: {owner}"
      accepted1.modify (· + 1)
    retire := fun owner => retired1.modify (· ++ [owner])
  }
  let summary1 ← runSession ⟨repo, ws1, "Recover from turn.failed", ref, backend1, false⟩
  ensure (summary1 == "recovered after turn.failed" && (← turn1.get) == 2 && (← sawDiag1.get) && (← accepted1.get) == 1)
    s!"turn.failed recovery did not finish cleanly: {summary1}"
  ensure ((← retired1.get) == ["SESSION_ROOT", "SESSION_ROOT"])
    s!"expected retire on turn.failed and finally, got {← retired1.get}"
  let log1 ← IO.FS.readFile (ws1 / "narrowing-events.jsonl")
  ensure (log1.contains "\"kind\":\"turn_failed\"" && log1.contains "transient upstream error" && !log1.contains "RAW_TOOL_CALL_PAYLOAD")
    s!"missing or leaky turn_failed narrowing log: {log1}"

  -- 2) JSON error event also retires SESSION_ROOT and recovers cleanly.
  let ws2 := ws / "error-event-recovery"
  seedTree ws2
  let turn2 ← IO.mkRef 0
  let retired2 ← IO.mkRef ([] : List String)
  let backend2 : Backend := {
    propose := fun req => do
      let n ← turn2.modifyGet fun i => (i, i + 1)
      if n == 0 then fail errorEventErr
      ensure (req.retry && (← retired2.get) == ["SESSION_ROOT"]) "error event did not retire before retry"
      let diag := (req.prompt.splitOn "TRANSIENT DIAGNOSTIC").getLast!
      ensure (diag.contains "transient gateway reset" && !diag.contains "RAW_ERROR_STDOUT")
        s!"bad diagnostic after error event: {diag}"
      return "(session-action (kind finish) (summary \"recovered after error event\"))"
    retire := fun owner => retired2.modify (· ++ [owner])
  }
  let summary2 ← runSession ⟨repo, ws2, "Recover from error event", ref, backend2, false⟩
  ensure (summary2 == "recovered after error event" && (← turn2.get) == 2) "error event recovery failed"

  -- 3) Non-turn.failed errors propagate immediately without retrying.
  let ws3 := ws / "unexpected-proposal-propagates"
  let calls3 ← IO.mkRef 0
  let fatalBackend := ScriptedBackend fun _ => do
    calls3.modify (· + 1)
    fail "unexpected proposal"
  expectError "unexpected proposal" (runSession ⟨repo, ws3, "Propagate non-turn.failed error", ref, fatalBackend, false⟩)
  ensure ((← calls3.get) == 1) s!"non-turn.failed error was retried: {← calls3.get} calls"

  let ws4 := ws / "codex-non-json-propagates"
  let calls4 ← IO.mkRef 0
  let nonJsonCodexBackend := ScriptedBackend fun _ => do
    calls4.modify (· + 1)
    fail "codex exec (1): fatal non-json cli error\n"
  expectError "fatal non-json cli error" (runSession ⟨repo, ws4, "Propagate non-JSON codex error", ref, nonJsonCodexBackend, false⟩)
  ensure ((← calls4.get) == 1) s!"non-JSON codex error was retried: {← calls4.get} calls"
  IO.println "   Session turn.failed resilience: scratch retired, clean diagnostic forwarded, fatal errors propagate"

def run (args : List String) : IO Unit := do
  let repo ← IO.FS.realPath "."
  preload (repo / ".lake/build/lib/lean")
  protocols
  match args with
  | ["threads",dir] => do
    threadLifecycle dir repo
    concurrentCancellation dir repo
  | ["recovery",ws] => do
    inPlaceTowerRecovery ws repo
    IO.FS.withTempDir fun dir => transportAuditRegressions dir repo
    IO.FS.withTempDir fun dir => sessionTurnResilience dir repo
  | ["tower",ws] => do
    tower ws repo
    IO.FS.withTempDir fun dir => inPlaceTowerRecovery dir repo
    IO.FS.withTempDir fun dir => transportAuditRegressions dir repo
    IO.FS.withTempDir fun dir => sessionTurnResilience dir repo
  | ["prompts",dir,ws] => promptExamples dir ws repo
  | _ => fail "test-s4-session (tower WS | recovery WS | prompts DRAFTS WS | threads DIR)"

end Test.S4

def main := Test.S4.run
