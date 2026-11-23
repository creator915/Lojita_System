import Lojita.Store.Object
import Lojita.Harness.Tree

namespace Lojita.Store
open Lojita.Kernel Lojita.Transport Lojita.Harness System

@[extern "ct_lean_sha256"] opaque sha256 (bytes : @& ByteArray) : String

def objectPath (dir : FilePath) (k : Kind) (key : Hash) := dir / "objects" / k.dir / (key ++ ".sexp")

private def digest (bytes : ByteArray) : IO Hash := do
  let key := sha256 bytes
  if key.isEmpty then throw (IO.userError "CAS_DIGEST_ERROR: SHA-256 unavailable")
  return key

private def verified (p : FilePath) (key : Hash) : IO ByteArray := do
  let bytes ← IO.FS.readBinFile p
  unless (← digest bytes) == key do throw (IO.userError s!"CAS_HASH_MISMATCH: {p}")
  return bytes

private def stage (path : FilePath) (bytes : ByteArray) (key : Hash) : IO Unit := do
  let parent := path.parent.getD "."
  IO.FS.createDirAll parent
  let tmp := parent / s!".stage-{← IO.Process.getPID}-{← IO.monoNanosNow}-{← IO.rand 0 4294967295}"
  let handle ← IO.FS.Handle.mk tmp .writeNew
  try
    handle.write bytes
    handle.flush
    discard <| verified tmp key
    IO.FS.rename tmp path
  finally
    if ← tmp.pathExists then IO.FS.removeFile tmp

def putObject (dir : FilePath) (k : Kind) (v : Payload k) : IO Hash := do
  let text := encodeObject k v
  unless (decodeObject k text).isSome do throw (IO.userError s!"CAS_INVALID_OBJECT: {k.dir}")
  let bytes := text.toUTF8
  let key ← digest bytes
  let p := objectPath dir k key
  if ← p.pathExists then discard <| verified p key else stage p bytes key
  return key

def getObject (dir : FilePath) (k : Kind) (key : Hash) : IO (Payload k) := do
  unless validHash key do throw (IO.userError "CAS_INVALID_HASH")
  let bytes ← verified (objectPath dir k key) key
  let some v := String.fromUTF8? bytes >>= decodeObject k | throw (IO.userError s!"CAS_INVALID_OBJECT: {k.dir}/{key}")
  return v

inductive RefKind where | trees | «partial»
def RefKind.dir : RefKind → String | .trees => "trees" | .partial => "partial"

private def refPath (dir : FilePath) (k : RefKind) (name : String) : IO FilePath := do
  unless (name.splitOn "/").all (fun s => !s.isEmpty && s != "." && s != ".." &&
      s.toList.all (fun c => c >= ' ' && c != '\\')) do throw (IO.userError "CAS_INVALID_REF")
  return dir / "refs" / k.dir / name

def writeRef (dir : FilePath) (k : RefKind) (name : String) (key : Hash) : IO Unit := do
  unless validHash key do throw (IO.userError "CAS_INVALID_HASH")
  stage (← refPath dir k name) key.toUTF8 (← digest key.toUTF8)

def readRef (dir : FilePath) (k : RefKind) (name : String) : IO (Option Hash) := do
  let p ← refPath dir k name
  if !(← p.pathExists) then return none
  let key ← IO.FS.readFile p
  unless validHash key do throw (IO.userError "CAS_INVALID_REF")
  return some key

mutual
  def storeFrozen (dir : FilePath) (f : Frozen) : IO Hash :=
    match f with
    | .frozen c m s ks => do
      let code ← putObject dir .code c
      let iface ← putObject dir .iface s.units
      let mem ← putObject dir .mem m
      let scope ← if {s with units := []} == {c with units := []} then pure none
        else some <$> putObject dir .code {s with units := []}
      let kids ← storeKids dir ks #[]
      putObject dir .home ⟨code, iface, mem, kids, scope⟩
  termination_by structural f
  private def storeKids (dir : FilePath) (ks : List (String × Frozen)) (acc : Array (String × Hash)) : IO (List (String × Hash)) :=
    match ks with
    | [] => pure acc.toList
    | (n,f) :: rest => do
      let h ← storeFrozen dir f
      storeKids dir rest (acc.push (n,h))
  termination_by structural ks
end

private def cachedLeaf {α : Type} (cache : Std.HashMap Hash α) (key : Hash)
    (read : Hash → IO α) : IO (α × Std.HashMap Hash α) := do
  if let some value := cache[key]? then return (value,cache)
  let value ← read key
  return (value,cache.insert key value)

private inductive Visit where
  | read (key : Hash)
  | assemble (key : Hash) (node : HomeNodeObj)

/-- Postorder traversal, memoized by content address. Each home directory is
    verified once per traversal even if many parents reference that subtree. -/
def loadFrozen (dir : FilePath) (root : Hash) : IO Frozen := do
  let mut todo := [Visit.read root]
  let mut nodes : Std.HashMap Hash Frozen := {}
  let mut visiting : Std.HashSet Hash := {}
  let mut codes := {}
  let mut ifaces := {}
  let mut memories := {}
  while let v :: rest := todo do
    todo := rest
    match v with
    | .read key =>
      if nodes.contains key then continue
      if visiting.contains key then throw (IO.userError "CAS_HOME_CYCLE")
      visiting := visiting.insert key
      let h ← getObject dir .home key
      todo := h.kids.foldl (fun acc e => .read e.2 :: acc) (.assemble key h :: todo)
    | .assemble key h =>
      let (c, cs) ← cachedLeaf codes h.codeHash (getObject dir .code)
      let (hdr, cs) ← h.specScope.elim (pure (c,cs)) (fun k => cachedLeaf cs k (getObject dir .code))
      codes := cs
      let (units, is) ← cachedLeaf ifaces h.specHash (getObject dir .iface)
      ifaces := is
      let (m, ms) ← cachedLeaf memories h.memHash (getObject dir .mem)
      memories := ms
      let s := {hdr with units}
      let kids ← h.kids.mapM fun (n,k) => do
        let some f := nodes[k]? | throw (IO.userError "CAS_MISSING_CHILD")
        return (n,f)
      nodes := nodes.insert key (.frozen c m s kids)
      visiting := visiting.erase key
  let some f := nodes[root]? | throw (IO.userError "CAS_MISSING_HOME")
  return f

def storeHomeCAS (dir : FilePath) (home : HomeValue) := storeFrozen dir (freezeHome home.1 home.2)
def loadHomeCAS (dir : FilePath) (key : Hash) := thawHome <$> loadFrozen dir key

def storeTreeCommit (dir : FilePath) (parents : List Hash) (epoch why : String) (home : HomeValue) : IO Hash := do
  putObject dir .commit ⟨parents, ← storeHomeCAS dir home, epoch, why, none⟩

end Lojita.Store
