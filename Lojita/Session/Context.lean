import Lojita.Session.Workspace

namespace Lojita.Session
open System Lojita.Kernel Lojita.Transport Lojita.Harness Lojita.Store

/-- The kernel may need transitive dependencies that are outside this owner's view. -/
def readableAncestors (t : NodeTask) : List LeanMod :=
  t.baseModules.filter fun m => ordinaryPath m.modName &&
    t.allowedAncestors.all (·.contains m.modName)

def parseLift (s : String) : IO LiftSpec := do
  let some lift := SExpr.parseSExpr s >>= decodeLiftSpec | fail "invalid lift descriptor"
  return lift

def parseTransport (s : String) : IO TransportSpec := do
  let some t := SExpr.parseSExpr s >>= decodeTransportSpec | fail "invalid poly-transport descriptor"
  return t

private def checkLiftSource (mods : List LeanMod) (root : LiftSpec) : IO Unit := do
  let index := Std.HashMap.ofList (mods.map fun m => (m.modName,m))
  let mut pending := [root]
  while let s :: rest := pending do
    let some base := index[s.base]? | fail s!"missingBaseUnit: {s.base}"
    let targets := s.children.flatMap ChildLift.uppers
    let upper : LeanMod := ⟨s.upper,targets.map (⟨·,[]⟩),[],[]⟩
    if let err :: _ := liftShapeProblems base upper s then fail (reprStr err)
    let before := endpointNames base
    for e in s.endpoints do
      if e.baseUnits.isEmpty || e.upperUnits.isEmpty then fail "emptyLiftEndpoints"
      for q in e.baseUnits do unless before.contains q do fail s!"missingBaseUnit: {q}"
    pending := s.children.flatMap ChildLift.childSpecs ++ rest

structure Prepared where
  task : NodeTask
  home : Frozen
  closure : BaseClosure

def prepareSpec (ws : FilePath) (name src : String) (bases : List String) (liftSrc transportSrc : Option String) :
    IO Prepared := do
  checkTreeName name
  let spec ← IO.ofExcept (parseLeanMod src)
  unless spec.modName.segments.take 2 == ["Gen",name] && spec.modName.segments.length == 3 &&
      spec.modName.segments.all validSegment do fail s!"expected namespace Gen.{name}.<RootModule>"
  let closure ← loadCurrentClosure ws bases
  if closure.trees.any (·.name == name) then fail "cycle in requested baseTrees"
  checkClosedBundle closure.modules
  let allowed := closure.modules.map (·.modName)
  if let e :: _ := checkTaskImports spec.modName [] allowed spec then fail (reprStr e)
  discard <| checkConditionalGlue closure.modules [] spec true
  let home ← initialHome ws name spec
  let lift ← liftSrc.mapM fun s => do
    let l ← parseLift s
    unless l.upper == spec.modName do fail "wrongUpper"
    checkLiftSource closure.modules l
    let some base := closure.modules.find? (·.modName == l.base) | fail "missing lift base"
    return (base,l)
  let transports ← transportSrc.toList.mapM fun s => do
    let t ← parseTransport s
    unless t.newMod == spec.modName do fail "wrongNewMod"
    let source ← if t.oldMod == home.code.modName then pure home else do
      if let some tree := closure.trees.find? (·.home.code.modName == t.oldMod) then pure tree.home else
        let some preserved ← partialSource ws t.oldMod | fail s!"missing transport source {t.oldMod}"
        pure preserved
    let targets := t.childMoves.flatMap ChildMove.targets
    let target : LeanMod := ⟨t.newMod,targets.map (⟨·,[]⟩),[],[]⟩
    if let e :: _ := polyShapeProblems source.code target t then fail (reprStr e)
    for q in t.childMoves.flatMap ChildMove.sources do
      unless (lookupChild source q).isSome do fail s!"missing transport child {q}"
    return (source,t)
  let task : NodeTask := {
    delta := ⟨spec.modName,home.spec.units,spec⟩
    baseModules := closure.modules, maybeLift := lift, transports, allowedAncestors := some allowed}
  return ⟨task,home,closure⟩

/-- A node MCP process receives precisely the frozen input of PlanPreview,
    including child interfaces, restricted ancestors and nested obligations. -/
private structure ContextFile where
  home : Hash
  spec : String
  bases : List String
  allowed : Option (List String)
  lifts : List (String × String)
  transports : List (Hash × String)
  deriving Lean.ToJson, Lean.FromJson

def writeContext (ctx : FilePath) (req : AIRequest) : IO Unit := do
  let dir := ctx / "objects-cache"
  let t := req.task
  let home := req.home.getD (.frozen req.old req.memory t.delta.newIface [])
  let binds ← t.transports.mapM fun (h,s) => do return (← storeFrozen dir h,(encodeTransportSpec s).canonical)
  let wire : ContextFile := ⟨← storeFrozen dir home,encodeCanonical t.delta.newIface,t.baseModules.map encodeCanonical,
    t.allowedAncestors.map (·.map toString),t.lifts.map (fun (b,s) => (encodeCanonical b,(encodeLiftSpec s).canonical)),binds⟩
  atomicText (ctx / "context.json") (Lean.toJson wire).compress

private def promptSection (prompt heading : String) : Option String := do
  let sections := ["CURRENT CODE","SPECIFICATION","REFUTATION EXTRA POSTULATES","PARENT FLAGS","LOCKED SEEDS",
    "PREVIOUS INTERFACE","ANCESTORS","ALLOWED DIRECT IMPORTS","SAVED CHILDREN","LIFT","POLY-TRANSPORT",
    "MEMORY","TRANSIENT DIAGNOSTIC","PUBLIC CONTEXT AND TASK CONSTRAINTS"]
  let rows := prompt.splitOn "\n"
  let _ :: tail := rows.dropWhile (· != heading) | none
  return String.intercalate "\n" (tail.takeWhile fun line => !sections.any (fun h => line == h || line.startsWith (h ++ " (")))

structure NodeContext where
  task : NodeTask
  home : Frozen
  /-- A loose .lean input can include comments and whitespace outside its units. -/
  originals : Std.HashMap QName String := {}

private def looseContext (ctx : FilePath) : IO (Option NodeContext) := do
  let prompt := (← readOptional (ctx / "node-prompt.txt")).getD ""
  let some src := (← readOptional (ctx / "spec.lean")) <|> promptSection prompt "SPECIFICATION" | return none
  let spec ← IO.ofExcept (parseLeanMod src)
  let current := (← readOptional (ctx / "current.lean")) <|> promptSection prompt "CURRENT CODE"
  let old ← current.mapM fun s => IO.ofExcept (parseLeanMod s)
  let mut ancestors := #[]
  let mut originals := {}
  let dir := ctx / "ancestors"
  if ← dir.isDir then
    for p in ← regularFiles dir do
      if p.extension == some "lean" then
        let text ← IO.FS.readFile p
        let m ← IO.ofExcept (parseLeanMod text)
        ancestors := ancestors.push m
        originals := originals.insert m.modName text
  let bases ← IO.ofExcept (mergeModules ancestors.toList)
  checkClosedBundle bases
  let t : NodeTask := {delta := ⟨spec.modName,[],spec⟩,baseModules := bases}
  return some ⟨t,.frozen (old.getD ⟨spec.modName,[],[],[]⟩) [] spec [],originals⟩

def contextReader (ctx : FilePath) : IO (IO (Option NodeContext)) := do
  let cache ← IO.mkRef (none : Option (String × NodeContext))
  return do
    let some src ← readOptional (ctx / "context.json") | return ← looseContext ctx
    if let some (previous, result) ← cache.get then
      if previous == src then return some result
    let result ← decode src
    cache.set (some (src,result))
    return some result
where
  decode (src : String) : IO NodeContext := do
    let c : ContextFile ← IO.ofExcept (Lean.Json.parse src >>= Lean.fromJson?)
    let dir := ctx / "objects-cache"
    let read := fun (s : String) => match decodeCanonical s with | some m => pure m | none => fail "invalid context module"
    let spec ← read c.spec
    let bases ← c.bases.mapM read
    let lifts ← c.lifts.mapM fun (b,s) => do return (← read b,← parseLift s)
    let binds ← c.transports.mapM fun (k,s) => do return (← loadFrozen dir k,← parseTransport s)
    let home ← loadFrozen dir c.home
    let t : NodeTask := {
      delta := ⟨spec.modName,home.spec.units,spec⟩, baseModules := bases, allowedAncestors := c.allowed.map (·.map qualified)
      maybeLift := lifts.head?, otherLifts := lifts.drop 1, transports := binds}
    return {task := t,home}

end Lojita.Session
