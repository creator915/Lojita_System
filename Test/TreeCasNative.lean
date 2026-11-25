import Lojita.Sandbox.LinuxIso

open System LojitaCtx.Posix Lojita.Store.TreeCAS

private def bench : IO Unit := IO.FS.withTempDir fun tmp => do
  let big := ByteArray.mk (Array.replicate (4*1024*1024) 65)
  let entries := ({} : Entries).insert [98,105,103] 2
  let fs : InodeTable := {
    nodes := ({} : Std.TreeMap InodeId Inode)
      |>.insert 1 {payload := .dir 1 entries, mode := 0o755, nlink := 2}
      |>.insert 2 {payload := .reg big, mode := 0o644}
    nextId := 3 }
  let start ← IO.monoNanosNow
  let id ← saveTree tmp fs
  let written ← IO.monoNanosNow
  let image ← loadTree tmp id
  let loaded ← IO.monoNanosNow
  let some n := image.nodes.get? 2 | throw <| IO.userError "missing benchmark inode"
  let .reg data := n.payload | throw <| IO.userError "expected regular benchmark inode"
  unless data == big do throw <| IO.userError "4 MiB contents differ"
  IO.println s!"{(written-start)/1000} {(loaded-written)/1000} {(loaded-start)/1000}"

def main (args : List String) : IO Unit := do
  match args with
  | ["bench"] => bench
  | ["capture",store,path] => IO.println (← captureDir store path)
  | ["load-save",store,id,dest] => IO.println (← saveTree dest (← loadTree store id))
  | ["load",store,id] => discard <| loadTree store id
  | ["verify",store,id] => verifyTree store id
  | ["materialize",store,id,dest] => materialize store id dest
  | ["remove",path] => removeStage path
  | _ => throw <| IO.userError "unknown TreeCAS test command"
