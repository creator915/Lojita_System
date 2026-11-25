import Lojita.Store.TreeCAS.Image
import Lojita.Store.TreeCAS.Native

/-! LJT1 stores each object's SHA-256 as its lowercase hexadecimal filename in
    `blob`, `symlink` or `tree`. File bytes and link targets are stored verbatim.
    Trees start with `LJT1` and a big-endian 16-bit mode. Each entry contains a
    big-endian 16-bit name length, one kind byte (b/s/t), a big-endian 16-bit
    mode, the raw filename, and the 32-byte child digest. Names are strictly
    increasing in unsigned byte order. Host paths name trusted directories;
    traversal beneath them uses pinned descriptors and preserves Linux bytes. -/
namespace Lojita.Store.TreeCAS
open System LojitaCtx.Posix

abbrev TreeHash := String
private abbrev directory : UInt8 := 116
private abbrev blob : UInt8 := 98
private abbrev link : UInt8 := 115
private def magic := "LJT1".toUTF8

private def bad {α : Type} (reason : String) : IO α := throw (IO.userError ("TreeCAS " ++ reason))

private def withDir {α : Type} (openIt : IO UInt32) (work : UInt32 → IO α) : IO α := do
  let fd ← openIt
  try work fd finally Native.closeDir fd

private def read16 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat * 256 + b[i+1]!.toNat

private def push16 (b : ByteArray) (n : Nat) : ByteArray :=
  (b.push (n / 256).toUInt8).push n.toUInt8

private def header (mode : Nat) : ByteArray := push16 magic mode

private def hexHash (b : ByteArray) : TreeHash := Id.run do
  let chars := "0123456789abcdef".toUTF8
  let mut text := ByteArray.emptyWithCapacity 64
  for x in b do
    text := (text.push chars[x.toNat / 16]!).push chars[x.toNat % 16]!
  return String.fromUTF8! text

private def nibble (c : UInt8) : IO Nat := do
  if c >= 48 && c <= 57 then return c.toNat - 48
  if c >= 97 && c <= 102 then return c.toNat - 87
  bad "invalid lowercase SHA-256 digest"

private def parseHash (s : TreeHash) : IO ByteArray := do
  let b := s.toUTF8
  unless b.size == 64 do bad "invalid SHA-256 digest length"
  let mut id := ByteArray.emptyWithCapacity 32
  for j in [:32] do
    let hi ← nibble b[2*j]!
    let lo ← nibble b[2*j+1]!
    id := id.push (hi*16+lo).toUInt8
  return id

private structure RefInfo where
  kind : UInt8
  mode : Nat
  digest : ByteArray
  deriving Inhabited

private def addEntry (out name : ByteArray) (ref : RefInfo) : ByteArray :=
  push16 ((push16 out name.size).push ref.kind) ref.mode ++ name ++ ref.digest

private def decode (data : ByteArray) : IO (Nat × Array (Seg × RefInfo)) := do
  unless data.size >= 6 && data.extract 0 4 == magic do bad "invalid LJT1 header"
  let mode := read16 data 4
  unless mode <= 511 do bad "invalid directory mode"
  let mut entries := #[]
  let mut last : Seg := []
  let mut i := 6
  while i < data.size do
    unless i+5 <= data.size do bad "truncated entry header"
    let n := read16 data i
    let kind := data[i+2]!
    let perms := read16 data (i+3)
    unless n > 0 && n <= 255 && i+5+n+32 <= data.size do bad "invalid entry length"
    unless perms <= 511 && (kind == directory || kind == blob || (kind == link && perms == 511)) do
      bad "invalid entry kind or permissions"
    let name := (data.extract (i+5) (i+5+n)).data.toList
    unless validSeg name && last < name do bad "invalid or unsorted directory name"
    let stop := i+5+n+32
    entries := entries.push (name, ⟨kind, perms, data.extract (stop-32) stop⟩)
    last := name
    i := stop
  return (mode,entries)

private partial def capture (store src : UInt32) (stamp : ByteArray) : IO RefInfo := do
  Native.checkStamp src stamp
  let mode := read16 stamp 1
  let mut out := header mode
  let names := (← Native.names src).map (·.data.toList)
  for raw in names.qsort (· < ·) do
    let name := raw.toByteArray
    let info ← Native.stamp src name
    let kind := info[0]!
    let ref ← if kind == directory then
      withDir (Native.child src name false) fun sub => capture store sub info
    else do
      let data ← Native.sourceBytes src name info
      pure ⟨kind,read16 info 1,← Native.putObject store kind data⟩
    out := addEntry out name ref
  Native.checkStamp src stamp
  return ⟨directory,mode,← Native.putObject store directory out⟩

def captureDir (store source : FilePath) : IO TreeHash :=
  withDir (Native.openDir source.toString false) fun src =>
  withDir (Native.captureStore store.toString src) fun dst => do
    let root ← capture dst src (← Native.stamp src ByteArray.empty)
    Native.syncStore dst
    return hexHash root.digest

private inductive WalkTarget where
  | verify
  | materialize (fd : UInt32)
  | load (rows : IO.Ref ImageTable) (next : IO.Ref Nat)

/-- Every edge, including repeated references to the same content, gets its
    own inode. Untrusted bytes are checked before entering either the VFS or
    the privately staged host tree. -/
private partial def walk (store : UInt32) (target : WalkTarget) (digest : ByteArray)
    (expected : Option Nat) (active : List ByteArray) (ino parent : Nat) : IO Unit := do
  if active.contains digest then bad "cyclic directory graph"
  let (mode, entries) ← decode (← Native.getObject store directory digest)
  unless expected.all (· == mode) do bad "inconsistent directory mode"
  let mut children : Entries := {}
  for (seg, ref) in entries do
    let name := seg.toByteArray
    let id ← match target with
      | .load _ next => next.modifyGet (fun n => (n,n+1))
      | _ => pure 0
    if ref.kind == directory then
      match target with
      | .materialize fd =>
        withDir (Native.child fd name true) (fun sub => walk store (.materialize sub) ref.digest (some ref.mode) (digest :: active) id ino)
      | _ => walk store target ref.digest (some ref.mode) (digest::active) id ino
    else
      let data ← Native.getObject store ref.kind ref.digest
      if ref.kind == link && (data.isEmpty || data.size >= 4096 || data.data.contains 0) then
        bad "invalid symlink body"
      match target with
      | .materialize fd => Native.emitFile fd name ref.kind ref.mode.toUInt32 data
      | .verify => pure ()
      | .load rows _ =>
        let entry := if ref.kind == blob then Entry.file data else Entry.symlink data.data.toList
        rows.modify (·.insert id ⟨ref.mode,entry⟩)
    if let .load .. := target then children := children.insert seg id
  match target with
  | .verify => pure ()
  | .materialize fd => Native.setMode fd mode.toUInt32
  | .load rows _ => rows.modify (·.insert ino ⟨mode,.directory parent children⟩)

def verifyTree (store : FilePath) (root : TreeHash) : IO Unit :=
  withDir (Native.openDir store.toString false) fun src => do
    walk src .verify (← parseHash root) none [] 1 1

private def withParent {α : Type} (path : FilePath) (work : UInt32 → ByteArray → IO α) : IO α := do
  let some name := path.fileName | bad "missing final path component"
  withDir (Native.openDir (path.parent.getD ".").toString false) fun dir => work dir name.toUTF8

/-- Remove a private sandbox stage, including directories restored with mode 000. -/
def removeStage (path : FilePath) : IO Unit := withParent path Native.removeEntry

def materialize (store : FilePath) (root : TreeHash) (dest : FilePath) : IO Unit :=
  withDir (Native.openDir store.toString false) fun src =>
  withParent dest fun parent name => do
    let hash ← parseHash root
    let tmp ← Native.newStage parent
    try
      withDir (Native.child parent tmp false) fun fd => walk src (.materialize fd) hash none [] 1 1
      Native.publish parent tmp name
    catch e =>
      Native.removeEntry parent tmp
      throw e

def loadTree (store : FilePath) (root : TreeHash) (ro : Bool := true) : IO InodeTable :=
  withDir (Native.openDir store.toString false) fun src => do
    let rows ← IO.mkRef {}
    let next ← IO.mkRef 2
    walk src (.load rows next) (← parseHash root) none [] 1 1
    match mountTreeToVfs (← rows.get) ro with
    | .ok fs => return fs
    | .error e => bad s!"invalid image: {repr e}"

private partial def saveNode (store : UInt32) (rows : ImageTable) (id : InodeId) : IO RefInfo := do
  let some node := rows.get? id | bad "missing image inode"
  let (kind,data) ← match node.entry with
    | .file data => pure (blob,data)
    | .symlink target => pure (link,target.toByteArray)
    | .directory _ children => do
      let mut out := header node.mode
      for (seg,child) in children.toList do
        out := addEntry out seg.toByteArray (← saveNode store rows child)
      pure (directory,out)
  return ⟨kind,node.mode,← Native.putObject store kind data⟩

def saveTree (store : FilePath) (fs : InodeTable) : IO TreeHash := do
  match freezeVfsToTree fs with
  | .error e => bad s!"cannot freeze inode graph: {repr e}"
  | .ok rows => withDir (Native.openDir store.toString true) fun dst => do
    let root ← saveNode dst (Std.TreeMap.ofList rows) 1
    Native.syncStore dst
    return hexHash root.digest

end Lojita.Store.TreeCAS
