import Lojita.Session.Protocol
import Lojita.Store.CAS
import Lojita.Harness.NodeServer

namespace Lojita.Session
open System Lojita.Store Lojita.Harness Lojita.Kernel Lojita.Transport

def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

def atomicText (path : FilePath) (s : String) : IO Unit := do
  let parent := path.parent.getD "."
  IO.FS.createDirAll parent
  let tmp := parent / s!".write-{← IO.Process.getPID}-{← IO.monoNanosNow}"
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
  discard <| IO.FS.Handle.mk (ws / "narrowing-events.jsonl") .append

def logNarrowing (path : FilePath) (source : String) (cert : NarrowingCertificate) : IO Unit := do
  IO.FS.createDirAll (path.parent.getD ".")
  let h ← IO.FS.Handle.mk path .append
  let event := Lean.Json.mkObj [("source", Lean.toJson source),("tsMs", Lean.toJson (← IO.monoMsNow)),
    ("kind", Lean.toJson cert.kind),("certificate",Lean.toJson cert)]
  h.lock
  try h.putStrLn event.compress; h.flush finally h.unlock

def checkTreeName (n : String) : IO Unit :=
  unless validSegment n do fail s!"invalid tree name {n}"

/-- The ready marker is the publication intent. A writer that loses its process
    at any subsequent rename leaves enough information for the next lock holder
    to finish the same generation. All renames stay on the workspace filesystem. -/
private def recoverPublication (ws : FilePath) : IO Unit := do
  let stage := ws / ".publication"
  unless ← stage.isDir do return
  if let some name ← readOptional (stage / "ready") then
    checkTreeName name
    let tree := ws / "trees" / name
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

/-- A same-epoch edge is provenance only. Every vertical edge follows the current
    sealed ref, even if an intermediate epoch has not yet been re-driven. -/
def loadCurrentClosure (ws : FilePath) (names : List String) : IO BaseClosure := do
  let tips ← names.mapM (resolveTip ws)
  let mut records ← history (ws / "store") tips
  let mut byName := Std.HashMap.ofList (names.zip tips)
  let mut todo := tips.map Visit.enter
  let mut active : Std.HashSet Hash := {}
  let mut done_ : Std.HashSet Hash := {}
  let mut trees := #[]
  while let v :: rest := todo do
    todo := rest
    match v with
    | .leave k => active := active.erase k; done_ := done_.insert k
    | .enter k =>
      if active.contains k then fail "cycle in live vertical ancestry"
      if done_.contains k then continue
      active := active.insert k
      let some c := records.commits[k]? | fail "missing ancestor commit"
      let some home := records.homes[c.rootHome]? | fail "missing ancestor home"
      trees := trees.push ⟨c.epoch,k,home⟩
      todo := .leave k :: todo
      for p in c.parents.reverse do
        let some parent := records.commits[p]? | fail "missing pinned parent"
        if parent.epoch == c.epoch then continue
        let live ← match byName[parent.epoch]? with
          | some key => pure key
          | none => resolveTip ws parent.epoch
        byName := byName.insert parent.epoch live
        unless records.commits.contains live do
          records ← history (ws / "store") [live] records
        todo := .enter live :: todo
  let modules ← IO.ofExcept (mergeModules (trees.toList.flatMap (exported ·.home)))
  return ⟨tips,trees.toList,modules⟩

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
    return (← loadCurrentClosure ws (← sealedNames ws)).modules
  finally lock.unlock

private def savedTree (ws : FilePath) (kind : RefKind) (n : String) : IO (Option Frozen) := do
  let some key ← readRef (ws / "store") kind n | return none
  let records ← history (ws / "store") [key]
  let some c := records.commits[key]? | fail "missing saved commit"
  unless c.epoch == n do fail "saved epoch mismatch"
  return records.homes[c.rootHome]?

def partialSource (ws : FilePath) (q : QName) : IO (Option Frozen) := do
  let "Gen" :: epoch :: _ := q.segments | return none
  checkTreeName epoch
  let some h ← savedTree ws .partial epoch | return none
  unless h.code.modName == q do return none
  -- A failed parent exports only its verified children. Never lend the
  -- implementation or assumptions of the parent as a horizontal endpoint.
  let slots := h.children.map (fun (n,_) => ImportSpec.mk (qualified n) [])
  let shell := withChildIfaces ⟨q,slots,[],[]⟩ (h.children.map fun (n,c) => specAt (qualified n) c)
  return some (.frozen shell h.memory h.spec h.children)

def initialHome (ws : FilePath) (n : String) (spec : LeanMod) : IO Frozen := do
  checkTreeName n
  let complete ← savedTree ws .trees n
  let kept ← savedTree ws .partial n
  let empty := Frozen.frozen ⟨spec.modName,[],[],[]⟩ [] spec []
  let seed := (kept <|> complete).getD empty
  unless seed.code.modName == spec.modName do fail "in-place drive changed root namespace"
  let slots := Std.HashSet.ofList (seed.children.map Prod.fst)
  let other := complete.toList.flatMap (fun h => h.children.filter (!slots.contains ·.1))
  return .frozen seed.code seed.memory seed.spec (seed.children ++ other)

def moduleFile (root : FilePath) (m : LeanMod) := (m.modName.segments.foldl (· / ·) root).addExtension "lean"

def publishTree (ws : FilePath) (name why : String) (bases : List String) (tips : List Hash)
    (verdict : Verdict) (home : Frozen) : IO String := do
  checkTreeName name
  let dir := ws / "store"
  let previous ← readRef dir .trees name
  let key ← storeTreeCommit dir (distinct (tips ++ previous.toList)) name why (thawHome home)
  let stage := ws / ".publication"
  let (status, detail) ← match verdict with
    | .ok => do
      for m in exported home do atomicText (moduleFile (stage / "generated") m) (renderLeanMod m)
      writeRef stage .trees name key
      atomicText (stage / "clear-partial") ""
      pure ("ok","ok")
    | .liftObstruction reason culprits proof => do
      writeRef stage .partial name key
      let evidence := (SExpr.list [.sym "lift-obstruction",.str reason,
        .list (culprits.map encName),.list (home.children.map (fun (n,_) => .str n)),.str (renderLeanMod proof)]).canonical
      atomicText (stage / "obstruction.sexp") evidence
      pure ("lift-obstruction",s!"liftObstruction {reason}\nCULPRIT_BASE_UNITS {culprits.map toString}\nPRESERVED_CHILDREN {home.children.map Prod.fst}\n{renderLeanMod proof}")
    | .contradiction r => pure ("contradiction",s!"contradiction\n{renderLeanMod r}")
    | .countermodel r model proof => pure ("countermodel",s!"countermodel {r}\n{renderLeanMod model}\n{renderLeanMod proof}")
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
