import Lojita.Session.Protocol
import Lojita.Store.CAS
import Lojita.Harness.NodeServer

namespace Lojita.Session
open System Lojita.Store Lojita.Harness Lojita.Kernel Lojita.Transport

def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

private initialize nextTempSeq : IO.Ref Nat ← IO.mkRef 0
private initialize narrowLogMutex : Std.Mutex Unit ← Std.Mutex.new ()

def atomicText (path : FilePath) (s : String) : IO Unit := do
  let parent := path.parent.getD "."
  IO.FS.createDirAll parent
  let seq ← nextTempSeq.modifyGet fun n => (n, n + 1)
  let tmp := parent / s!".write-{← IO.Process.getPID}-{← IO.monoNanosNow}-{seq}"
  try
    IO.FS.writeFile tmp s
    IO.FS.rename tmp path
  finally
    if ← tmp.pathExists then IO.FS.removeFile tmp

def readOptional (p : FilePath) : IO (Option String) := do
  try return some (← IO.FS.readFile p)
  catch | .noFileOrDirectory .. => return none | e => throw e

def namesAt (dir : FilePath) : IO (List String) := do
  unless ← dir.isDir do return []
  return ((← dir.readDir).toList.map (·.fileName)).mergeSort

def initWorkspace (ws : FilePath) : IO Unit := do
  for p in ["store/objects","store/refs/trees","store/refs/partial","trees","generated","threads","bin"] do
    IO.FS.createDirAll (ws / p)
  if !(← (ws / "session-memory.sexp").pathExists) then atomicText (ws / "session-memory.sexp") "()"
  narrowLogMutex.atomically do
    discard <| IO.FS.Handle.mk (ws / "narrowing-events.jsonl") .append

def logNarrowing (path : FilePath) (source : String) (cert : NarrowingCertificate) : IO Unit := narrowLogMutex.atomically do
  IO.FS.createDirAll (path.parent.getD ".")
  let h ← IO.FS.Handle.mk path .append
  let event := Lean.Json.mkObj [("source", Lean.toJson source),("tsMs", Lean.toJson (← IO.monoMsNow)),
    ("kind", Lean.toJson cert.kind),("certificate",Lean.toJson cert)]
  h.lock
  try h.putStrLn event.compress; h.flush finally h.unlock

def checkTreeName (n : String) : IO Unit :=
  unless validSegment n do fail s!"invalid tree name {n}"

private def treeNamesFile (p : FilePath) : IO (List String) := do
  let some (.list names) := SExpr.parseSExpr (← IO.FS.readFile p) | fail s!"invalid tree list in {p}"
  let ns ← IO.ofExcept (stringList names)
  ns.forM checkTreeName
  return ns

/-- The ready marker is the publication intent. A writer that loses its process
    at any subsequent rename leaves enough information for the next lock holder
    to finish the same generation. All renames stay on the workspace filesystem. -/
private def recoverPublication (ws : FilePath) : IO Unit := do
  let stage := ws / ".publication"
  unless ← stage.isDir do return
  if let some name ← readOptional (stage / "ready") then
    checkTreeName name
    let tree := ws / "trees" / name
    let retire ← if ← (stage / "retire.sexp").pathExists then treeNamesFile (stage / "retire.sexp") else pure []
    if !retire.isEmpty then
      let verdict ← match ← readOptional (stage / "verdict") with
        | some v => pure (some v)
        | none => readOptional (tree / "verdict")
      unless verdict == some "ok" && !retire.contains name do fail "invalid retirement in publication journal"
    IO.FS.createDirAll tree
    let install := fun (src dst : FilePath) => do
      if ← src.pathExists then
        IO.FS.createDirAll (dst.parent.getD ws)
        IO.FS.rename src dst
    if ← (stage / "generated").isDir then
      let target := ws / "generated" / name
      if ← target.isDir then IO.FS.rename target (stage / "previous")
      install (stage / "generated") target
    for kind in ["trees","partial"] do
      let ref := FilePath.mk "refs" / kind / name
      install (stage / ref) (ws / "store" / ref)
    if ← (stage / "clear-partial").pathExists then
      let ref := ws / "store/refs/partial" / name
      if ← ref.pathExists then IO.FS.removeFile ref
    for file in ["obstruction.sexp","bases.sexp","current","verdict"] do
      install (stage / file) (tree / file)
    for peer in retire do
      for kind in ["trees","partial"] do
        let ref := ws / "store/refs" / kind / peer
        if ← ref.pathExists then IO.FS.removeFile ref
      let gen := ws / "generated" / peer
      if ← gen.isDir then IO.FS.removeDirAll gen
      atomicText (ws / "trees" / peer / "verdict") "retired"
  IO.FS.removeDirAll stage

def withWorkspaceLock {α : Type} (ws : FilePath) (act : IO α) : IO α := do
  IO.FS.createDirAll ws
  let handle ← IO.FS.Handle.mk (ws / "workspace.lock") .append
  handle.lock
  try
    recoverPublication ws
    act
  finally handle.unlock

def sealedNames (ws : FilePath) : IO (List String) := do
  -- Read both indices so losing one side of a publication fails the next audit.
  let refs ← namesAt (ws / "store/refs/trees")
  let trees ← namesAt (ws / "trees")
  (distinct (refs ++ trees)).filterM fun n => do
    checkTreeName n
    let verdict ← readOptional (ws / "trees" / n / "verdict")
    if refs.contains n && verdict.isNone then fail s!"missing verdict for {n}"
    return verdict.map (·.trimAscii.toString) == some "ok"

def checkReplacements (ws : FilePath) (name : String) (bases replaces : List String)
    (transportSources : List QName := []) : IO Unit := do
  if replaces.isEmpty then return
  let sealed ← sealedNames ws
  for r in replaces do
    checkTreeName r
    if r == name || bases.contains r then fail s!"invalid replacement {r}: expected a distinct horizontal peer"
    let tree := ws / "trees" / r
    unless (← tree.isDir) || (← readRef (ws / "store") .trees r).isSome ||
        (← readRef (ws / "store") .partial r).isSome do fail s!"unknown replacement tree {r}"
    if (← readOptional (tree / "verdict")).any (·.trimAscii.toString == "retired") then fail s!"already retired: {r}"
    if ← (tree / "bases.sexp").pathExists then
      unless (← treeNamesFile (tree / "bases.sexp")) == bases do
        fail s!"replacement {r} must have the same baseTrees as {name}"
    for other in sealed do
      if other != r && other != name && (← treeNamesFile (ws / "trees" / other / "bases.sexp")).contains r then
        fail s!"cannot replace {r}: sealed tree {other} depends on it"
    unless transportSources.any (fun q => q.segments.take 2 == ["Gen", r] && q.segments.length == 3) do
      fail s!"MISSING_REPLACEMENT_TRANSPORT: replacement {r} must be the horizontal transport source tree in maybeTransportSrc"

structure SealedTree where
  name : String
  tip : Hash
  home : Frozen

structure BaseClosure where
  directTips : List Hash
  trees : List SealedTree
  modules : List LeanMod

private def resolveTip (ws : FilePath) (n : String) : IO Hash := do
  checkTreeName n
  let tree := ws / "trees" / n
  unless (← readOptional (tree / "verdict")).map (·.trimAscii.toString) == some "ok" do fail s!"unsealed base {n}"
  let some key ← readRef (ws / "store") .trees n | fail s!"missing sealed ref {n}"
  unless (← readOptional (tree / "current")).map (·.trimAscii.toString) == some key do fail s!"inconsistent current {n}"
  let c ← getObject (ws / "store") .commit key
  unless c.epoch == n do fail s!"ref epoch mismatch {n}"
  return key

private inductive Visit where | enter (k : Hash) | leave (k : Hash)

private structure History where
  commits : Std.HashMap Hash Commit := {}
  homes : Std.HashMap Hash Frozen := {}

/-- Verify historical edges at their pinned hashes. A postorder stack distinguishes
    active ancestors from already verified diamond joins. -/
private def history (dir : FilePath) (roots : List Hash) (saved : History := {}) : IO History := do
  let mut todo := roots.map Visit.enter
  let mut active : Std.HashSet Hash := {}
  let mut acc := saved
  while let v :: rest := todo do
    todo := rest
    match v with
    | .leave k => active := active.erase k
    | .enter k =>
      if active.contains k then fail "commit ancestry cycle"
      if acc.commits.contains k then continue
      let c ← getObject dir .commit k
      checkTreeName c.epoch
      if c.presentation.isSome then fail "unsupported commit presentation"
      unless acc.homes.contains c.rootHome do
        acc := {acc with homes := acc.homes.insert c.rootHome (← loadFrozen dir c.rootHome)}
      active := active.insert k
      acc := {acc with commits := acc.commits.insert k c}
      todo := c.parents.foldr (fun p xs => .enter p :: xs) (.leave k :: todo)
  return acc

def verifyCommitDAG (dir : FilePath) (tip : Hash) : IO Unit := do discard <| history dir [tip]

private def staleAncestor (ancestor name : String) (cause : IO.Error) :=
  s!"STALE_ANCESTOR_TREE: ancestor tree {ancestor} no longer typechecks against updated upstream bases ({cause}); re-drive {ancestor} before driving {name}"

/-- A same-epoch edge is provenance only. Every vertical edge follows the current
    sealed ref, even if an intermediate epoch has not yet been re-driven. -/
private def currentTrees (ws : FilePath) (names : List String) (driving : Option String := none) :
    IO (List Hash × List SealedTree) := do
  let tip := fun n => do
    checkTreeName n
    try resolveTip ws n catch e =>
      if let some name := driving then
        let verdict := (← readOptional (ws / "trees" / n / "verdict")).map (·.trimAscii.toString)
        if verdict == some "retired" then
          fail s!"STALE_ANCESTOR_TREE: ancestor tree {n} was retired/replaced ({e}); re-drive {name} against the replacement base tree"
        if ((← readRef (ws / "store") .trees n).isSome || (← readRef (ws / "store") .partial n).isSome) &&
            verdict.any (· != "ok") then
          fail (staleAncestor n name e)
      throw e
  let tips ← names.mapM tip
  let mut records ← history (ws / "store") tips
  let mut byName := Std.HashMap.ofList (names.zip tips)
  let mut todo := tips.map Visit.enter
  let mut active : Std.HashSet Hash := {}
  let mut done_ : Std.HashSet Hash := {}
  let mut trees := #[]
  while let v :: rest := todo do
    todo := rest
    match v with
    | .leave k =>
      active := active.erase k
      done_ := done_.insert k
      let some c := records.commits[k]? | fail "missing ancestor commit"
      let some home := records.homes[c.rootHome]? | fail "missing ancestor home"
      trees := trees.push ⟨c.epoch,k,home⟩
    | .enter k =>
      if active.contains k then fail "cycle in live vertical ancestry"
      if done_.contains k then continue
      active := active.insert k
      let some c := records.commits[k]? | fail "missing ancestor commit"
      todo := .leave k :: todo
      for p in c.parents.reverse do
        let some parent := records.commits[p]? | fail "missing pinned parent"
        if parent.epoch == c.epoch then continue
        let live ← match byName[parent.epoch]? with
          | some key => pure key
          | none => tip parent.epoch
        byName := byName.insert parent.epoch live
        unless records.commits.contains live do
          records ← history (ws / "store") [live] records
        todo := .enter live :: todo
  return (tips, trees.toList.reverse)

def loadCurrentClosure (ws : FilePath) (names : List String) : IO BaseClosure := do
  let (tips,trees) ← currentTrees ws names
  return ⟨tips,trees,← IO.ofExcept (mergeModules (trees.flatMap (exported ·.home)))⟩

def verifiedAncestry (ws : FilePath) (bases : List String) (name : String) : IO BaseClosure := do
  let (tips,trees) ← currentTrees ws bases name
  let mut modules := []
  for anc in trees.reverse do
    try
      verifyClosure modules anc.home
      modules ← IO.ofExcept (mergeModules (exported anc.home ++ modules))
    catch e =>
      fail (staleAncestor anc.name name e)
  return ⟨tips,trees,modules⟩

structure SealedView where
  name : String
  tree : Option SealedTree
  stale : Option String

/-- Keep the saved contract visible to the session even when its live link fails. -/
def sealedViews (ws : FilePath) : IO (List SealedView) := do
  (← sealedNames ws).mapM fun n => do
    match ← (verifiedAncestry ws [n] n).toBaseIO with
    | .ok closure => return ⟨n,closure.trees.head?,none⟩
    | .error e =>
      let saved : IO SealedTree := do
        let tip ← resolveTip ws n
        let c ← getObject (ws / "store") .commit tip
        return ⟨n,tip,← loadFrozen (ws / "store") c.rootHome⟩
      return ⟨n,(← saved.toBaseIO).toOption,some (toString e)⟩

structure PartialTreeView where
  name : String
  verdict : String
  bases : List String
  stale : Option String

/-- Inspect unsealed/partial trees whose recorded bases were retired, unsealed,
    or updated so SESSION_ROOT and audits see STALE diagnostics for them too. -/
def partialStaleViews (ws : FilePath) : IO (List PartialTreeView) := do
  let mut out := #[]
  for n in ← namesAt (ws / "trees") do
    checkTreeName n
    let some verdict := (← readOptional (ws / "trees" / n / "verdict")).map (·.trimAscii.toString) | continue
    if verdict == "ok" || verdict == "retired" then continue
    let basesFile := ws / "trees" / n / "bases.sexp"
    unless ← basesFile.pathExists do continue
    let bases ← treeNamesFile basesFile
    if bases.isEmpty then continue
    let stale ← match ← (verifiedAncestry ws bases n).toBaseIO with
      | .ok closure =>
        match ← readRef (ws / "store") .partial n with
        | none => pure none
        | some key =>
          let c ← getObject (ws / "store") .commit key
          let recorded := c.parents.filter (· != key)
          if closure.directTips.any (!recorded.contains ·) then
            pure (some s!"STALE_PARTIAL_TREE: partial tree {n} ({verdict}) was recorded against earlier base commits; re-drive {n} against updated bases {bases}")
          else pure none
      | .error e => pure (some (toString e))
    if stale.isSome then
      out := out.push ⟨n, verdict, bases, stale⟩
  return out.toList

def retiredNames (ws : FilePath) : IO (Std.HashSet String) := do
  let ns ← (← namesAt (ws / "trees")).filterM fun (n : String) => do
    return (← readOptional (ws / "trees" / n / "verdict")).any (·.trimAscii.toString == "retired")
  return Std.HashSet.ofList ns

def publicExports (retired : Std.HashSet String) (home : Frozen) :=
  (exported home).filter fun m => match m.modName.segments with
    | "Gen" :: epoch :: _ => !retired.contains epoch
    | _ => true

/-- Both entry preflight and the native linker use the owning tree's live ancestry. -/
def entryModules (ws : FilePath) (entry : QName) : IO (List LeanMod) := do
  let "Gen" :: epoch :: _ := entry.segments | fail "expected qualified entry Gen.<treeName>.<Module>.<entry>"
  unless (← sealedNames ws).contains epoch do fail "unsealed entry tree"
  return (← loadCurrentClosure ws [epoch]).modules

/-- Inspect a coherent published generation without creating files or completing a writer's journal. -/
def readSealedModules (ws : FilePath) : IO (List LeanMod) := do
  let lock ← try IO.FS.Handle.mk (ws / "workspace.lock") .read
    catch | .noFileOrDirectory .. => return [] | e => throw e
  lock.lock (exclusive := false)
  try
    if ← (ws / ".publication/ready").pathExists then fail "tree publication is awaiting recovery"
    let retired ← retiredNames ws
    let mut index : Std.HashMap QName LeanMod := {}
    let mut names := #[]
    for view in ← sealedViews ws do
      if view.stale.isSome then continue
      let some tree := view.tree | continue
      for m in publicExports retired tree.home do
        if !index.contains m.modName then names := names.push m.modName
        else if m.modName.segments.take 2 != ["Gen",tree.name] then continue
        index := index.insert m.modName m
    return names.toList.filterMap (index[·]?)
  finally lock.unlock

private def savedTree (ws : FilePath) (kind : RefKind) (n : String) : IO (Option (Frozen × List LeanMod)) := do
  let some key ← readRef (ws / "store") kind n | return none
  let records ← history (ws / "store") [key]
  let some c := records.commits[key]? | fail "missing saved commit"
  unless c.epoch == n do fail "saved epoch mismatch"
  let some home := records.homes[c.rootHome]? | fail "missing saved home"
  -- Same-epoch edges preserve revision history. Follow only vertical edges at
  -- every level, at their recorded hashes, to recover the old checking environment.
  let mut todo := c.parents.map (n, ·)
  let mut seen : Std.HashSet Hash := {}
  let mut modules := #[]
  while let (epoch,p) :: rest := todo do
    todo := rest
    let some parent := records.commits[p]? | fail "missing historical parent"
    if parent.epoch == epoch || seen.contains p then continue
    seen := seen.insert p
    let some base := records.homes[parent.rootHome]? | fail "missing historical home"
    modules := (exported base).foldl Array.push modules
    todo := parent.parents.map (parent.epoch, ·) ++ todo
  return some (home, ← IO.ofExcept (mergeModules modules.toList))

def partialSource (ws : FilePath) (q : QName) : IO (Option Frozen) := do
  let "Gen" :: epoch :: _ := q.segments | return none
  checkTreeName epoch
  let some (h,_) ← savedTree ws .partial epoch | return none
  unless h.code.modName == q do return none
  -- A failed parent exports only its verified children. Never lend the
  -- implementation or assumptions of the parent as a horizontal endpoint.
  let slots := h.children.map (fun (n,_) => ImportSpec.mk (qualified n) [])
  let shell := withChildIfaces ⟨q,slots,[],[]⟩ (h.children.map fun (n,c) => specAt (qualified n) c)
  return some (.frozen shell h.memory h.spec h.children)

structure InitialHome where
  home : Frozen
  oldBaseModules : Option (List LeanMod)
  otherChildHistory : Option (List String × List LeanMod)

def initialHomeWithBases (ws : FilePath) (n : String) (spec : LeanMod) : IO InitialHome := do
  checkTreeName n
  let complete ← savedTree ws .trees n
  let kept ← savedTree ws .partial n
  let empty := Frozen.frozen ⟨spec.modName,[],[],[]⟩ [] spec []
  let selected := kept <|> complete
  let seed := (selected.map Prod.fst).getD empty
  unless seed.code.modName == spec.modName do fail "in-place drive changed root namespace"
  let slots := Std.HashSet.ofList (seed.children.map Prod.fst)
  let other := complete.toList.flatMap (fun (h,_) => h.children.filter (!slots.contains ·.1))
  let (pinned, otherHistory) := match kept, complete with
    | some (kh, kms), some (ch, cms) =>
      if kh.code == ch.code then
        -- Partial commits retain the previously sealed root code (`s.original.code`),
        -- which was verified against `complete`'s vertical parents (`cms`), while
        -- `kh.children` were verified during the partial drive against `kms`.
        (some cms, if kh.children.isEmpty || cms == kms then none else some (kh.children.map Prod.fst, kms))
      else
        (some kms, if other.isEmpty || kms == cms then none else some (other.map Prod.fst, cms))
    | _, _ => (selected.map Prod.snd, none)
  return ⟨.frozen seed.code seed.memory seed.spec (seed.children ++ other), pinned, otherHistory⟩

def initialHome (ws : FilePath) (n : String) (spec : LeanMod) : IO Frozen :=
  InitialHome.home <$> initialHomeWithBases ws n spec

def moduleFile (root : FilePath) (m : LeanMod) := (m.modName.segments.foldl (· / ·) root).addExtension "lean"

def publishTree (ws : FilePath) (name why : String) (bases : List String) (tips : List Hash)
    (verdict : Verdict) (home : Frozen) (replaces : List String := [])
    (transportSources : List QName := []) : IO String := do
  checkTreeName name
  if verdict == .ok then checkReplacements ws name bases replaces transportSources
  let dir := ws / "store"
  let previous ← readRef dir .trees name
  let key ← storeTreeCommit dir (distinct (tips ++ previous.toList)) name why (thawHome home)
  let stage := ws / ".publication"
  let (status, detail) ← match verdict with
    | .ok => do
      for m in exported home do atomicText (moduleFile (stage / "generated") m) (renderLeanMod m)
      writeRef stage .trees name key
      atomicText (stage / "clear-partial") ""
      if !replaces.isEmpty then atomicText (stage / "retire.sexp") (SExpr.list (replaces.map .str)).canonical
      pure ("ok","ok")
    | .liftObstruction reason culprits proof => do
      writeRef stage .partial name key
      let evidence := (SExpr.list [.sym "lift-obstruction",.str reason,
        .list (culprits.map encName),.list (home.children.map (fun (n,_) => .str n)),.str (renderLeanMod proof)]).canonical
      atomicText (stage / "obstruction.sexp") evidence
      pure ("lift-obstruction",s!"liftObstruction {reason}\nCULPRIT_BASE_UNITS {culprits.map toString}\nPRESERVED_CHILDREN {home.children.map Prod.fst}\n{renderLeanMod proof}")
    | .contradiction r => pure ("contradiction",s!"contradiction\n{renderLeanMod r}")
    | .countermodel r model proof => pure ("countermodel",s!"countermodel {r}\n{renderLeanMod model}\n{renderLeanMod proof}")
  if verdict matches .contradiction .. | .countermodel .. then
    if !home.children.isEmpty then writeRef stage .partial name key
    else atomicText (stage / "clear-partial") ""
  atomicText (stage / "bases.sexp") (SExpr.list (bases.map .str)).canonical
  atomicText (stage / "current") key
  atomicText (stage / "verdict") status
  atomicText (stage / "ready") name
  recoverPublication ws
  return detail

/-- Walk concrete directory entries without following links out of a workspace. -/
def regularFiles (root : FilePath) : IO (List FilePath) := do
  let mut pending := [root]
  let mut visited : Std.HashSet FilePath := {}
  let mut files := #[]
  while let p :: rest := pending do
    pending := rest
    if visited.contains p then continue
    visited := visited.insert p
    match (← p.symlinkMetadata).type with
    | .dir => pending := (← p.readDir).foldl (fun ps e => e.path :: ps) pending
    | .file => files := files.push p
    | _ => fail s!"expected a regular workspace entry: {p}"
  return files.toList

/-- Re-elaborate contracts against live ancestors and compare each published
    source to the Merkle home that actually supplied it. -/
def auditTrees (ws : FilePath) : IO BaseClosure := do
  let names ← sealedNames ws
  if names.isEmpty then fail "finish requires a sealed tree"
  let all ← loadCurrentClosure ws names
  for t in all.trees do
    let closure ← loadCurrentClosure ws [t.name]
    let bases := (closure.trees.filter (·.tip != t.tip)).flatMap (exported ·.home)
    verifyClosure bases t.home
    let dir := ws / "generated" / t.name
    let owned := exported t.home
    let expected := Std.HashSet.ofList (owned.map (moduleFile dir))
    for path in ← regularFiles dir do
      unless expected.contains path do fail s!"unexpected file in sealed exports: {path}"
    for m in owned do
      unless (← IO.FS.readFile (moduleFile dir m)) == renderLeanMod m do
        fail s!"published source differs from sealed tree: {m.modName}"
  return all

def treeFingerprint (ws : FilePath) : IO Hash := do
  let tips ← (← sealedNames ws).mergeSort.mapM (resolveTip ws)
  return sha256 (SExpr.list (tips.map .str)).canonical.toUTF8

def safeDraftName (s : String) := !s.isEmpty && s.length ≤ 128 && s != "." && s != ".." &&
  s.toList.all (fun c => c.isAlphanum || c == '_' || c == '-' || c == '.')

def loadDrafts (ctx : FilePath) : IO DraftStore := do
  let mut drafts := {}
  for file in ← namesAt (ctx / "drafts") do
    let n := (file.dropEnd 6).toString
    if file.endsWith ".block" && safeDraftName n then
      drafts := drafts.insert n (← IO.FS.readFile (ctx / "drafts" / file))
  return drafts

end Lojita.Session
