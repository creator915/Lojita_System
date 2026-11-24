import Lojita.Session.Runner

namespace Test.ConcurrentDialectica
open System Lean Lojita.Session Lojita.Kernel Lojita.Store Lojita.Transport Lojita.Harness

private def ensure (ok : Bool) (msg : String) : IO Unit := unless ok do fail msg

private structure Node where
  owner : String
  submission : String
  deriving FromJson, Inhabited

private structure Stage where
  treeName : String
  why : String
  specSrc : String
  baseTrees : List String
  maybeLiftSrc : Option String
  maybeTransportSrc : Option String
  commit : String
  rootHome : String
  nodes : List Node
  deriving FromJson, Inhabited

private structure Draft where
  owner : String
  item : String
  source : String
  depBlocks : List String
  allowAxioms : Bool
  outcome : String
  deriving FromJson, Inhabited

private structure Fixture where
  stages : List Stage
  drafts : Array Draft
  deriving FromJson, Inhabited

private def loadFixture : IO Fixture := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "Test/Concurrent/gron_t0_t3_fixture.json"))
  let f : Fixture ← IO.ofExcept (fromJson? json)
  ensure (f.stages.map (·.treeName) == ["T0","T1","T2","T3"] &&
    f.stages.map (·.nodes.length) == [1,4,11,11]) "incomplete gron fixture"
  return f

private def timed {α : Type} (label : String) (act : IO α) : IO α := do
  let start ← IO.monoMsNow
  let value ← act
  let out ← IO.getStdout
  out.putStrLn s!"{label} passed ({(← IO.monoMsNow) - start} ms)"
  out.flush
  return value

private abbrev Counts := Std.Mutex (Std.HashMap String Nat)

private def indexedBackend (nodes : List Node) (calls : Counts)
    (answer : TurnRequest → AIRequest → Nat → String → IO String) : Backend :=
  let replies := Std.HashMap.ofList (nodes.map fun n => (n.owner, n.submission))
  ScriptedBackend fun turn => do
    let some req := turn.node | fail "unexpected SESSION_ROOT turn"
    let attempt ← calls.atomically <| modifyGet fun m =>
      let n := m[turn.owner]?.getD 0 + 1
      (n, m.insert turn.owner n)
    let some reply := replies[turn.owner]? | fail s!"unexpected owner {turn.owner} on attempt {attempt}"
    answer turn req attempt reply

private def firstTurn (turn : TurnRequest) (req : AIRequest) (attempt : Nat) : IO Unit :=
  ensure (attempt == 1 && req.diagnostic.isNone) s!"{turn.owner} attempt {attempt}: {req.diagnostic}"

private def checkCalls (calls : Counts) (expected : List (String × Nat)) : IO Unit := do
  let actual ← calls.atomically get
  ensure (actual == Std.HashMap.ofList expected) s!"unexpected calls: {actual.toList}, expected {expected}"

private def config (ws : FilePath) (backend : Backend) : IO SessionConfig := do
  return ⟨← IO.FS.realPath ".", ws, "Replay sealed gron proposals", {target := .local "/bin/true"}, backend, false⟩

private def drive (ws : FilePath) (s : Stage) (backend : Backend) : IO Unit := do
  let result ← driveTree (← config ws backend) s.treeName s.why s.specSrc s.baseTrees
    s.maybeLiftSrc s.maybeTransportSrc
  ensure (result == "ok") s!"{s.treeName}: {result}"

private def checkTip (ws : FilePath) (s : Stage) : IO Unit := do
  let store := ws / "store"
  let some tip ← readRef store .trees s.treeName | fail s!"missing sealed {s.treeName}"
  let c ← getObject store .commit tip
  ensure (tip == s.commit && c.rootHome == s.rootHome)
    s!"{s.treeName} commit {tip}, rootHome {c.rootHome}; expected {s.commit}, {s.rootHome}"

-- A bounded wait turns a serial scheduler or a lost birth into a diagnostic.
private def awaitWhere (label : String) (stopping : BaseIO Bool) (ready : IO Bool) : IO Unit := do
  let start ← IO.monoMsNow
  while !(← ready) do
    if ← stopping then fail s!"cancelled while waiting for {label}"
    if (← IO.monoMsNow) - start > 120000 then fail s!"timed out waiting for {label}"
    IO.sleep 2

private def childSlots := ["Diagnostic", "KeyOrder", "Decode", "Merge", "Values", "Http"]
private def grandchildSlots := ["Decode.JsonInput", "Decode.JsonRecords", "Merge.PathRead", "Merge.AtomRead"]

private structure Cohort where
  order : List String
  arrived : Std.Mutex Nat
  proposed : Std.Mutex (Array String)
  accepted : Std.Mutex (Array String)

private def cohort (order : List String) (inverse : Bool) : IO Cohort := do
  return ⟨if inverse then order.reverse else order, ← Std.Mutex.new 0, ← Std.Mutex.new #[], ← Std.Mutex.new #[]⟩

private def Cohort.release (c : Cohort) (events : Std.Mutex (Array String))
    (slot : String) (stopping : BaseIO Bool) : IO Unit := do
  let rank := c.order.idxOf slot
  awaitWhere s!"{slot} at position {rank}" stopping (events.atomically (return (← get).size == rank))
  events.atomically (modify (·.push slot))

private def Cohort.stagger (c : Cohort) (turn : TurnRequest) (slot : String) : IO Unit := do
  c.arrived.atomically (modify (· + 1))
  awaitWhere s!"concurrent {c.order}" turn.stopping (c.arrived.atomically (return (← get) == c.order.length))
  let rank := c.order.idxOf slot
  IO.sleep (UInt32.ofNat (35 * rank / (c.order.length - 1)))
  -- OS wakeup jitter cannot silently turn the two schedules into the same run.
  c.release c.proposed slot turn.stopping

private def replay (dir : FilePath) (fixture : Fixture) (inverse : Bool) : IO Unit := do
  let label := if inverse then "B" else "A"
  let ws := dir / label
  initWorkspace ws
  for s in fixture.stages do
    let small := s.treeName == "T0" || s.treeName == "T1"
    let top ← cohort (if small then (if s.treeName == "T0" then [] else ["Diagnostic","KeyOrder","Merge"])
                      else childSlots) inverse
    let deep ← cohort (if small then [] else grandchildSlots) inverse
    let calls ← Std.Mutex.new {}
    let backend := indexedBackend s.nodes calls fun turn req attempt reply => do
      firstTurn turn req attempt
      let slot := String.intercalate "." ((turn.owner.splitOn ".").drop 3)
      if top.order.contains slot then top.stagger turn slot
      if deep.order.contains slot then deep.stagger turn slot
      return reply
    -- The accept hook runs after the kernel closes each node and before its
    -- worker delivers the verdict. Order these completions as well as proposals.
    let accept := fun (owner _ : String) => do
      let slot := String.intercalate "." ((owner.splitOn ".").drop 3)
      for group in [top, deep] do
        if group.order.contains slot then group.release group.accepted slot (pure false)
    timed s!"Gate 1 {label} {s.treeName}" do
      drive ws s {backend with accept}
      checkTip ws s
      checkCalls calls (s.nodes.map fun n => (n.owner, 1))
      for group in [top, deep] do
        for events in [group.proposed, group.accepted] do
          ensure ((← events.atomically get).toList == group.order) s!"wrong completion order for {group.order}"
    if !inverse then
      -- Branch from these exact live publications before T3 depends on T2.
      if let some branch := [("T1","absorption"), ("T2","replacement")].lookup s.treeName then
        discard <| IO.Process.run {cmd := "cp", args := #["-R",ws.toString,(dir / branch).toString]}
  timed s!"Gate 1 {label} final tips and auditTrees" do
    fixture.stages.forM (checkTip ws)
    discard <| auditTrees ws

private def field (name : String) (vs : List SExpr) := SExpr.list (.sym name :: vs)

private def planReply (main : LeanMod) (children : List LeanMod) (moves : List Proarrow) (why : String) :=
  (field "submission" [field "kind" [.sym "plan"], field "why" [.str why],
    field "main" [.str (renderLeanMod main)], field "moves" (moves.map encMove),
    field "subspecs" (children.map fun m => .list [.str (toString m.modName), .str (renderLeanMod m)])]).canonical

private def t2 := "Gen.T2.Gron"
private def decode := t2 ++ ".Decode"
private def jsonInput := decode ++ ".JsonInput"
private def jsonRecords := decode ++ ".JsonRecords"
private def pathRead := t2 ++ ".Merge.PathRead"

private def concreteNode (s : Stage) (owner : String) : IO Node := do
  let some n := s.nodes.find? (·.owner == owner) | fail s!"missing {owner}"
  return n

-- Work on canonical, resolved envelopes. Fail if the intended edit is ambiguous.
private def editSource (reply before after : String) : IO String := do
  let [a,b] := reply.splitOn (SExpr.escape before) | fail s!"expected one source fragment: {before}"
  return a ++ SExpr.escape after ++ b

private def absorption (ws : FilePath) (s : Stage) : IO Unit := do
  let original := (← concreteNode s decode).submission
  let .plan _ subs ← IO.ofExcept (parseSubmission original) | fail "expected Decode plan"
  let some input := subs.find? (·.modName == qualified jsonInput) | fail "missing JsonInput contract"
  let some records := subs.find? (·.modName == qualified jsonRecords) | fail "missing JsonRecords contract"
  let law := "hexConflict"
  let endpoint := qualified (jsonInput ++ "." ++ law)
  let ending := "end " ++ jsonInput
  let addition := "axiom " ++ law ++ " : hexDigit false 0 ≠ hexDigit false 0\n"
  let bad ← IO.ofExcept (parseLeanMod ((renderLeanMod input).replace ending (addition ++ ending)))
  -- Edit only this subspec. The rest of the accepted envelope stays byte-exact.
  let badReply ← editSource original ending (addition ++ ending)
  let .plan _ perturbed ← IO.ofExcept (parseSubmission badReply) | fail "invalid perturbed plan"
  ensure (perturbed == subs.map (fun m => if m.modName == input.modName then bad else m)) "perturbed wrong contract"
  let proof := s!"import {jsonInput}\nnamespace Evidence\ntheorem impossible : False := {endpoint} rfl\nend Evidence"
  let refutation := (field "submission" [field "kind" [.sym "contradiction"], field "refute" [.str proof]]).canonical

  let calls ← Std.Mutex.new {}
  let live ← Std.Mutex.new ({} : Std.HashSet String)
  let started ← IO.Promise.new (α := Unit)
  let repaired ← IO.Promise.new (α := Unit)
  let bothLive := live.atomically (return (← get).contains jsonRecords && (← get).contains pathRead)
  let backend := indexedBackend s.nodes calls fun turn req attempt reply => do
    if turn.owner == decode && attempt == 2 then
      let some cert := req.diagnostic | fail "Decode retried without a certificate"
      ensure (cert.kind == "child_contradiction" && cert.witness.contains (toString endpoint))
        s!"expected the verified child contradiction, got {cert}"
      let some current := req.home | fail "missing CURRENT home"
      ensure ((lookupChild current input.modName).any (·.spec == bad) &&
        (lookupChild current records.modName).any (·.spec == records) && !req.old.units.isEmpty)
        "replan lost the current glue or an assigned child interface"
      ensure (← bothLive) "JsonRecords and PathRead must both be in flight at Decode's replan"
      -- Inherit all current glue and JsonRecords by identity. Only the bad port dies.
      let patch : LeanMod := ⟨req.old.modName, [], [], []⟩
      return planReply patch [input] [⟨.ext endpoint, .bot⟩] "Restore the original JsonInput contract"
    if turn.owner == jsonInput && attempt == 2 then
      ensure (req.diagnostic.isNone && req.task.delta.newIface == input && (← bothLive))
        "authentic JsonInput was not born from the repaired plan with both peers in flight"
      repaired.resolve ()
      return reply
    firstTurn turn req attempt
    if turn.owner == decode then return badReply
    if turn.owner == jsonInput then
      ensure (req.task.delta.newIface == bad) "missing injected child-owned axiom"
      awaitWhere "JsonRecords and PathRead" turn.stopping bothLive
      started.resolve ()
      IO.sleep 10
      return refutation
    if turn.owner == jsonRecords || turn.owner == pathRead then
      live.atomically (modify (·.insert turn.owner))
      try
        awaitWhere "JsonInput contradiction" turn.stopping started.isResolved
        IO.sleep 180
        -- Slow kernel checks can outlast the delay. Hold both at their real
        -- proposer boundary until the accepted replan births the repaired child.
        awaitWhere "accepted Decode repair" turn.stopping repaired.isResolved
      finally live.atomically (modify (·.erase turn.owner))
    return reply
  let cancelled ← Std.Mutex.new (#[] : Array String)
  drive ws s {backend with cancel := fun n => cancelled.atomically (modify (·.push n))}
  ensure (!(← cancelled.atomically get).any ([jsonRecords,pathRead].contains ·)) "an in-flight peer was cancelled"
  checkCalls calls (s.nodes.map fun n => (n.owner, if [decode,jsonInput].contains n.owner then 2 else 1))
  discard <| auditTrees ws

-- Apply the peer's source edits to the full real root, preserving its unit order,
-- six child contracts, public specification and original vertical squares.
private def replacementRoot (reply : String) : IO String := do
  let .plan p subs ← IO.ofExcept (parseSubmission reply) | fail "expected root plan"
  let some m := p.newMod | fail "missing root glue"
  let patch ← IO.ofExcept (parseLeanMod (← IO.FS.readFile "Test/Concurrent/gron_t2b_glue.block"))
  let edits := Std.HashMap.ofList (patch.units.map fun u => (u.uname, u))
  let revised := m.units.filter (edits.contains ·.uname)
  ensure (patch.modName == m.modName && !patch.units.isEmpty && revised.length == edits.size &&
    edits.size == patch.units.length) "T2b patch must name existing root declarations exactly once"
  let units := m.units.map fun u => edits[u.uname]?.getD u
  return planReply {m with units} subs p.moves p.why

private def replacement (ws : FilePath) (s : Stage) : IO Unit := do
  let newRoot := "Gen.T2b.Gron"
  let rename := fun (v : String) => v.replace t2 newRoot
  let kept := childSlots.filter (· != "Http")
  let slot := fun (root name : String) => qualified (root ++ "." ++ name)
  let moves := kept.map (fun n => ChildMove.keepChild (slot t2 n) (slot newRoot n)) ++
    [.moveChildren [slot t2 "Http"] [slot newRoot "Http"] []]
  let transport := TransportSpec.transportSpecTree (qualified t2) (qualified newRoot) moves []
  let some lift := s.maybeLiftSrc | fail "missing T1 to T2 lift"
  let action ← IO.ofExcept (parseSessionAction (field "session-action" [
    field "kind" [.sym "drive-tree"], field "treeName" [.str "T2b"], field "baseTrees" [.str "T1"],
    field "replaces" [.str "T2"], field "why" [.str "Keep five sealed subtrees and move Http"],
    field "specSrc" [.str (rename s.specSrc)], field "maybeLiftSrc" [.list [.sym "just", .str (rename lift)]],
    field "maybeTransportSrc" [.list [.sym "just", .str (encodeTransportSpec transport).canonical]]]).canonical)
  let root ← concreteNode s t2
  let http ← concreteNode s (t2 ++ ".Http")
  let scripted : List Node := [⟨newRoot, ← replacementRoot (rename root.submission)⟩,
    ⟨rename http.owner, rename http.submission⟩]
  let calls ← Std.Mutex.new {}
  let backend := indexedBackend scripted calls
    fun turn req attempt reply => do firstTurn turn req attempt; return reply
  checkTip ws s
  let store := ws / "store"
  let old ← getObject store .home s.rootHome
  let result ← executeAction (← config ws backend) action
  let .accepted detail := result | fail s!"T2b: {repr result}"
  ensure ((← readOptional (ws / "trees/T2b/verdict")) == some "ok") detail
  checkCalls calls [(newRoot,1), (newRoot ++ ".Http",1)]
  let some tip ← readRef store .trees "T2b" | fail "replacement did not seal"
  let home ← getObject store .home (← getObject store .commit tip).rootHome
  for n in kept do
    let some key := old.kids.lookup (t2 ++ "." ++ n) | fail s!"missing original {n}"
    ensure (home.kids.lookup (newRoot ++ "." ++ n) == some key) s!"kept {n} changed Merkle identity"
  ensure ((← sealedNames ws) == ["T0","T1","T2b"] && !(← (ws / "generated/T2").pathExists) &&
    (← readRef store .trees "T2").isNone && (← readRef store .partial "T2").isNone &&
    (← readOptional (ws / "trees/T2/verdict")) == some "retired")
    "incomplete retirement of T2"
  let audited ← auditTrees ws
  for n in kept ++ grandchildSlots do
    ensure (audited.modules.any (·.modName == slot newRoot n)) s!"missing retained module {newRoot}.{n}"

private structure DraftContext where
  spec : LeanMod
  bases : List LeanMod

private def contexts (ws : FilePath) (f : Fixture) : IO (Std.HashMap String DraftContext) := do
  let mut contexts := {}
  for s in f.stages do
    let closure ← loadCurrentClosure ws [s.treeName]
    let some tree := closure.trees.find? (·.name == s.treeName) | fail s!"missing {s.treeName}"
    let bases := (closure.trees.filter (·.name != s.treeName)).flatMap (exported ·.home)
    let mut pending := [tree.home]
    while let h :: rest := pending do
      contexts := contexts.insert (toString h.spec.modName) ⟨h.spec, bases⟩
      pending := h.children.map Prod.snd ++ rest
  return contexts

private def checkDraft (ctx : DraftContext) (d : Draft) : IO String := do
  let result ← (do
    let m ← IO.ofExcept (parseLeanMod d.source)
    let stubs ← d.depBlocks.mapM fun src => IO.ofExcept (parseLeanMod src)
    if stubs.isEmpty && !d.allowAxioms then
      discard <| checkClosedModule ctx.bases m
    else
      let snap ← checkConditionalGlue ctx.bases stubs m d.allowAxioms
      if d.allowAxioms then
        if let some cert := launderingCertificate snap then fail (toString cert)
    if !d.allowAxioms && m.modName == ctx.spec.modName then
      satisfies ctx.spec m ctx.bases .closedImplOK stubs : IO Unit).toBaseIO
  match result with
  | .ok _ => return "ok"
  | .error e =>
    let kind := ((toString e).splitOn ":").head!
    unless ["ELABORATION_ERROR", "INTERFACE_MISSING", "INTERFACE_MISMATCH"].contains kind do
      fail s!"{d.owner}/{d.item}: {e}"
    return kind

private def workers := 12
private def writes := 200
private def stressCert (id : Nat) : NarrowingCertificate :=
  ⟨"stress", toString id, s!"write {id}\nworker {id / writes}", "retry"⟩

private def payload (id : Nat) := String.intercalate "\n" (List.replicate 64 (toString id))

private def workspaceWrite (ws : FilePath) (id : Nat) : IO Unit := do
  let path := ws / "shared"
  atomicText path (payload id)
  let text ← IO.FS.readFile path
  let some winner := (text.splitOn "\n").head!.toNat? | fail "torn atomicText header"
  ensure (winner < workers * writes && text == payload winner) s!"torn atomicText read at {id}"
  logNarrowing (ws / "narrowing-events.jsonl") "driver-stress" (stressCert id)

private def checkLog (ws : FilePath) : IO Unit := do
  let lines := (← IO.FS.readFile (ws / "narrowing-events.jsonl")).splitOn "\n"
  ensure (lines.length == workers * writes + 1 && lines.getLast? == some "") "missing or torn JSONL line"
  let mut seen : Std.HashSet Nat := {}
  for line in lines.dropLast do
    let event ← IO.ofExcept (Json.parse line)
    let cert ← IO.ofExcept (event.getObjVal? "certificate")
    let witness ← IO.ofExcept (cert.getObjValAs? String "witness")
    let some id := witness.toNat? | fail s!"malformed log witness {witness}"
    let ts ← IO.ofExcept (event.getObjValAs? Nat "tsMs")
    let expected := Json.mkObj [("source", "driver-stress"), ("tsMs", toJson ts), ("kind","stress"),
      ("certificate",toJson (stressCert id))]
    ensure (id < workers * writes && !seen.contains id && event == expected) s!"corrupt or duplicate event {id}"
    seen := seen.insert id

private def stress (dir : FilePath) (f : Fixture) : IO Unit := do
  ensure (f.drafts.size >= 60 && ["ok", "ELABORATION_ERROR", "INTERFACE_MISSING", "INTERFACE_MISMATCH"].all
    (fun kind => f.drafts.any (·.outcome == kind))) "missing real draft coverage"
  let inputs ← contexts (dir / "A") f
  let ws := dir / "stress"
  initWorkspace ws
  let ready ← Std.Mutex.new 0
  let check := fun (d : Draft) => do
    let some ctx := inputs[d.owner]? | fail s!"missing context for {d.owner}"
    checkDraft ctx d
  let mut tasks := #[]
  for worker in [:workers] do
    let task ← IO.asTask (prio := .dedicated) do
      ready.atomically (modify (· + 1))
      awaitWhere "12 resident Driver workers" (pure false) (ready.atomically (return (← get) == workers))
      let indices := ((List.range f.drafts.size).filter (· % workers == worker)).toArray
      let mut results := #[]
      for tick in [:writes] do
        workspaceWrite ws (worker * writes + tick)
        for row in [tick * indices.size / writes : (tick + 1) * indices.size / writes] do
          let i := indices[row]!
          results := results.push (i, ← check f.drafts[i]!)
      return results
    tasks := tasks.push task
  -- Join every worker before propagating an error and before the serial baseline.
  let results ← tasks.mapM (m := BaseIO) IO.wait
  let mut concurrent : Std.HashMap Nat String := {}
  for result in results do
    for (i, kind) in ← EIO.ofExcept result do
      concurrent := concurrent.insert i kind
  ensure (concurrent.size == f.drafts.size) "missing concurrent draft result"
  for d in f.drafts, i in [:f.drafts.size] do
    let baseline ← check d
    ensure (concurrent[i]? == some baseline && baseline == d.outcome)
      s!"{d.owner}/{d.item}: concurrent {concurrent[i]?}, serial {baseline}, trace {d.outcome}"
  checkLog ws
  IO.println s!"{f.drafts.size} drafts matched serial and trace outcomes; {workers * writes} JSONL events verified"

def run (args : List String) : IO Unit := do
  let repo ← IO.FS.realPath "."
  preload (repo / ".lake/build/lib/lean")
  let f ← loadFixture
  match args with
  | ["replay",dir] => do
    replay dir f false
    replay dir f true
  | ["faults",dir] => do
    let ws : FilePath := dir
    timed "Gate 2a live contradiction repair" (absorption (ws / "absorption") f.stages[2]!)
    timed "Gate 2b deep keep and retirement" (replacement (ws / "replacement") f.stages[2]!)
  | ["stress",dir] => timed "Gate 3 resident Driver and workspace" (stress dir f)
  | _ => fail "usage: test-concurrent-dialectica (replay|faults|stress) WORKSPACE"

end Test.ConcurrentDialectica

def main := Test.ConcurrentDialectica.run
