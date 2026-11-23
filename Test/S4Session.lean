import Lojita.Session.Runner

namespace Test.S4
open System Lojita.Session Lojita.Kernel Lojita.Store Lojita.Transport Lojita.Harness
abbrev q := qualified

def ensure (ok : Bool) (msg : String) : IO Unit := unless ok do fail msg

private def modSrc (n body : String) (imports : List String := []) : String :=
  String.intercalate "\n" (imports.map ("import " ++ ·) ++ ["namespace " ++ n,body,"end " ++ n])

private def object (n body : String) (imps : List String := []) :=
  IO.ofExcept (parseLeanMod (modSrc n body imps))

private def field (k : String) (args : List SExpr) := SExpr.list (.sym k :: args)
private def envelope (tag : String) (fs : List SExpr) := (SExpr.list (.sym tag :: fs)).canonical

private def plan (old m : LeanMod) (subs : List LeanMod := []) : String := Id.run do
  let names := m.units.map (·.uname)
  let existing := old.units.map (·.uname)
  let moves : List Proarrow := (existing.map fun n => ⟨.unit n,if names.contains n then .unit n else .bot⟩) ++
    ((names.filter (!existing.contains ·)).map fun n => ⟨.bot,.unit n⟩)
  return envelope "submission" [field "kind" [.sym "plan"],field "main" [.str (renderLeanMod m)],field "why" [.str "refine"],
    field "moves" (moves.map encMove),field "subspecs" (subs.map fun s => .list [.str (toString s.modName),.str (renderLeanMod s)])]

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
  let upperSpec ← object top "open LojitaCtx.World\naxiom app : CliApp [.envCap,.ttyCap]"
    ["LojitaCtx.World"]
  let es ← object escape "axiom html : String → String"
  let escaped ← object escape (r#"def html (s : String) := (s.replace "&" "&amp;").replace "<" "&lt;""#)
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
def app : CliApp [.envCap,.ttyCap] := do
  let input ← readStdinAllW .here
  writeStdoutStrW (.there .here) (render (String.fromUTF8! input.toByteArray))
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
  let ai := ScriptedBackend fun req => do
    let i ← turn.get
    if let some node := req.node then
      if let some cert := node.diagnostic then fail s!"{req.owner} {cert}"
      counts.modify fun m => m.alter (i,req.owner) (fun n => some (n.getD 0 + 1))
      let old := node.old
      if req.owner == t0 then return if i == 2 then plan old low [childSpec] else plan old repaired [nextChild]
      if req.owner == doc then return plan old (if i == 2 then bad else fixed)
      if req.owner == top then return plan old upper [es,ps]
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
      let [(slot,kid)] := h.children | fail "partial T1 must contain exactly Escape"
      ensure (slot == escape) "wrong innocent sibling"
      innocent.set (← storeFrozen (ws / "store") kid)
      let target := "Gen.Archive.Doc"
      let renamed := target ++ ".Escape"
      let kept := TransportSpec.transportSpecTree (q top) (q target) [.keepChild (q escape) (q renamed)] []
      let archive ← object target "axiom html : String → String"
      let copy ← object target ("def html := " ++ renamed ++ ".html") [renamed]
      let p ← prepareSpec ws "Archive" (renderLeanMod archive) [] none (some (encodeTransportSpec kept).canonical)
      let .plan proposed subs ← IO.ofExcept (parseSubmission (plan p.home.code copy)) | fail "expected archive plan"
      let report ← planPreview p.task p.home proposed subs
      ensure report.certificate.isNone s!"cross-tree partial keep failed: {report.certificate}"
    if i == 5 then
      let sealed ← loadCurrentClosure ws ["T1"]
      let some kid := sealed.trees.head?.bind (lookupChild ·.home (q escape)) | fail "Escape was lost"
      ensure ((← storeFrozen (ws / "store") kid) == (← innocent.get)) "innocent Merkle identity changed"
    if i == 6 then ensure (req.retry && req.prompt.contains "REPLAY_REQUIRED") "premature finish passed"
    if i == 7 then
      let isolated : SessionConfig := ⟨repo,ws,"replay gate",ref,ScriptedBackend (fun _ => fail "unexpected AI"),true,none,none⟩
      let refOnly ← runScript repo ws ref observe
      ensure (refOnly.exitCode == 0 && refOnly.usedRef && !refOnly.usedCand) "invalid ref-only observation"
      let mismatch ← runScript repo ws ref (probe (r#"def probe : Probe := do
  let _ ← batch "ref"
  let _ ← batch "cand"
  return {exitCode := 1, stderr := "comparison failed"}"#))
      ensure (mismatch.exitCode == 1 && mismatch.usedRef && mismatch.usedCand) "invalid failed replay"
      let .rejected e ← executeAction isolated (.finish "missing replay") | fail "built candidate bypassed replay"
      ensure (e.contains "REPLAY_REQUIRED" && !(← (ws / "replay-receipt.sexp").pathExists)) "unearned replay receipt"
    if req.retry && i != 6 then fail s!"unexpected rejection: {(req.prompt.splitOn "TRANSIENT DIAGNOSTIC").getLast!}"
    turn.set (i+1)
    return action
  let cfg : SessionConfig := ⟨repo,ws,"Build the observed Markdown dialect",ref,ai,true,some 12,some 40⟩
  let summary ← runSession cfg
  ensure (summary == "mini-pandoc replayed" && (← turn.get) == 9) "session failed to finish"
  let calls ← counts.get
  ensure (calls[(3,escape)]? == some 1 && calls[(5,escape)]?.getD 0 == 0 && calls[(5,parser)]? == some 1)
    "expected Escape turns 1 then 0 and repaired ParseLine 1"
  ensure ((← readOptional (ws / "replay-receipt.sexp")).isSome) "missing replay receipt"
  IO.println "3  Mini-Pandoc: T0 revised in place, lift obstruction blamed dropsDefinition, Escape turns 1 then 0, static build and differential replay"

  let t2 ← object "Gen.T2.Doc" "axiom version : Nat"
  let impl ← object "Gen.T2.Doc" "def version := 2"
  let cb := ScriptedBackend fun req => do
    let some node := req.node | fail "unexpected SESSION_ROOT"
    if let some e := node.diagnostic then fail (toString e)
    return plan node.old impl
  let ok ← driveTree {cfg with backend := cb} "T2" "third layer" (renderLeanMod t2) ["T1","T0"] none none
  let closure ← loadCurrentClosure ws ["T2"]
  ensure (ok == "ok" && (closure.trees.map (·.name)).mergeSort == ["T0","T1","T2"] &&
    closure.modules.any (·.modName == q doc)) "three-layer diamond"
  let .rejected stale ← executeAction cfg (.finish "wrong") | fail "stale build was accepted"
  ensure (stale.contains "STALE_BUILD") "did not bind receipt to current tree tips"

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
  let file := moduleFile (ws / "generated/T2") impl
  let text ← IO.FS.readFile file
  try
    IO.FS.writeFile file (text ++ "-- altered\n")
    ensure (!(← (auditTrees ws).toBaseIO).isOk) "audit accepted changed export"
  finally IO.FS.writeFile file text
  IO.println "4  Live three-layer diamond, stale receipt, corrupt ancestry, source audit and split Lex/Parse memory"


private def promptExamples (dir ws repo : FilePath) : IO Unit := do
  let ds ← loadDrafts dir
  let known := ["measure-spec","measure","measure-plan","char-spec","model","refute","counterexample",
    "observe","observe-action","upper-spec","upper","lifting","transport","drive-upper","entry","build","compare","replay-action","done",
    "label-spec","route-spec","dispatch","dispatch-plan","label-impl","route-impl"]
  ensure (known.all ds.contains && ds.size == known.length) "every teaching block needs an executable example check"
  let read := fun n => ds[n]!.trimAscii.toString
  let actions := #[read "observe-action",drive "T0" (read "measure-spec"),read "drive-upper",
    drive "T2" (read "char-spec"),drive "App" (read "entry"),read "build",read "replay-action",read "done"]
  let turn ← IO.mkRef 0
  let ai := ScriptedBackend fun req => do
    for (n,s) in ds do atomicText (req.ctxDir / "drafts" / (n ++ ".block")) s
    if req.retry then fail s!"prompt example rejected: {(req.prompt.splitOn "TRANSIENT DIAGNOSTIC").getLast!}"
    if let some node := req.node then
      match req.owner with
      | "Gen.T0.Measure" => return read "measure-plan"
      | "Gen.T1.Measure" => return plan node.old (← IO.ofExcept (parseLeanMod (read "upper")))
      | "Gen.T2.Glyph" => return read "counterexample"
      | "Gen.App.Doc" => return read "dispatch-plan"
      | "Gen.App.Doc.Label" => return plan node.old (← IO.ofExcept (parseLeanMod (read "label-impl")))
      | "Gen.App.Doc.Route" => return plan node.old (← IO.ofExcept (parseLeanMod (read "route-impl")))
      | _ => fail s!"unexpected teaching node {req.owner}"
    let i ← turn.get
    let some act := actions[i]? | fail "example actions exhausted"
    if i == 4 then ensure (req.prompt.contains "countermodel") "countermodel did not reach root"
    turn.set (i+1)
    return act
  let cfg : SessionConfig := ⟨repo,ws,"Exercise the teaching examples",⟨.local "/bin/true",[],5000⟩,ai,true,some 10,some 20⟩
  discard <| runSession cfg
  for tag in [none,some "label:"] do
    let result ← IO.Process.output {cmd := (ws / "bin/candidate").toString, env := #[("LOJITA_TAG",tag)]} (some "sample\n")
    let expected := if tag.isSome then ("","label:sample\n") else ("sample\n","")
    ensure (result.exitCode == 0 && (result.stdout,result.stderr) == expected) "two-child CLI stream routing"
  ensure ((← readOptional (ws / "trees/T2/verdict")).any (·.startsWith "countermodel")) "model example not checked"
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
  let req : TurnRequest := ⟨"SESSION_ROOT",dir / "ctx","proposal",false,none⟩
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
  discard <| restarted.propose ⟨owner,dir / "node-ctx","proposal node",false,some node⟩
  restarted.accept owner "node semantic"
  ensure ((← IO.FS.readFile (dir / "threads" / (owner ++ ".id"))) != main) "node reused the session thread"

def run (args : List String) : IO Unit := do
  let repo ← IO.FS.realPath "."
  preload (repo / ".lake/build/lib/lean")
  protocols
  match args with
  | ["threads",dir] => threadLifecycle dir repo
  | ["tower",ws] => tower ws repo
  | ["prompts",dir,ws] => promptExamples dir ws repo
  | _ => fail "test-s4-session (tower WS | prompts DRAFTS WS)"

end Test.S4

def main := Test.S4.run
