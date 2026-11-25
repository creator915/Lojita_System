import Lojita.Store.TreeCAS.Image
import Lean.Data.Json

namespace Lojita.Store.TreeCAS
open System

abbrev TreeHash := String

private def runStore (args : Array String) : IO String := do
  let script : String := include_str "TreeCAS/objects.py"
  let result ← IO.Process.output {cmd := "/usr/bin/python3", args := #["-I", "-c", script] ++ args}
  if result.exitCode != 0 then throw <| IO.userError result.stderr
  return result.stdout.trimAscii.toString

def captureDir (store source : FilePath) : IO TreeHash :=
  runStore #["capture", store.toString, source.toString]

def verifyTree (store : FilePath) (root : TreeHash) : IO Unit := do
  discard <| runStore #["verify", store.toString, root]

def materialize (store : FilePath) (root : TreeHash) (dest : FilePath) : IO Unit := do
  discard <| runStore #["materialize", store.toString, root, dest.toString]

open Lean LojitaCtx.Posix

private instance : ToJson UInt8 := ⟨fun b => toJson b.toNat⟩
private instance : FromJson UInt8 := ⟨fun j => do
  let n : Nat ← fromJson? j
  if n > 255 then throw "invalid byte"
  return n.toUInt8⟩

private structure WireNode where
  ident : Nat
  mode : Nat
  parent : Nat
  kind : String
  data : List UInt8 := []
  entries : List (Seg × InodeId) := []
  deriving FromJson, ToJson

private def toWire : InodeId × ImageNode → WireNode
  | (i, ⟨m, .file bs⟩) => ⟨i, m, 0, "b", bs.data.toList, []⟩
  | (i, ⟨m, .symlink target⟩) => ⟨i, m, 0, "s", target, []⟩
  | (i, ⟨m, .directory p es⟩) => ⟨i, m, p, "t", [], es.toList⟩

private def fromWire (n : WireNode) : IO (InodeId × ImageNode) := do
  let entry ← match n.kind with
    | "b" => pure <| Entry.file n.data.toByteArray
    | "s" => pure <| Entry.symlink n.data
    | "t" => pure <| Entry.directory n.parent (Std.TreeMap.ofList n.entries)
    | _ => throw (IO.userError "unknown TreeCAS entry kind")
  return (n.ident, ⟨n.mode, entry⟩)

def loadTree (store : FilePath) (root : TreeHash) (ro : Bool := true) : IO InodeTable := do
  let raw ← runStore #["read-image", store.toString, root]
  let wire ← IO.ofExcept ((Json.parse raw).bind (fromJson? (α := List WireNode)))
  let rows ← wire.mapM fromWire
  match mountTreeToVfs (Std.TreeMap.ofList rows) ro with
  | .ok fs => return fs
  | .error e => throw (IO.userError s!"invalid TreeCAS image: {repr e}")

def saveTree (store : FilePath) (fs : InodeTable) : IO TreeHash := do
  match freezeVfsToTree fs with
  | .error e => throw (IO.userError s!"cannot freeze inode graph: {repr e}")
  | .ok rows => IO.FS.withTempFile fun handle manifest => do
    handle.putStr (toJson (rows.map toWire)).compress
    handle.flush
    runStore #["save-image", store.toString, manifest.toString]

end Lojita.Store.TreeCAS
