import Lojita.Store.TreeCAS

open LojitaCtx.Posix Lojita.Store.TreeCAS

private def b (s : String) : Bytes := s.toUTF8.data.toList

private def ok {α} (r : Except Errno α) : IO α := match r with
  | .ok x => pure x
  | .error e => throw (IO.userError s!"unexpected model error {repr e}")

private def must (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def err {α} (r : Except Errno α) (e : Errno) : Bool := match r with
  | .error actual => actual == e | .ok _ => false

private def model : IO Unit := do
  let root := InodeTable.empty
  must (err (vfsMkdirat root 1 1 (b "missing/child")) .ENOENT) "mkdir missing parent"
  let t ← ok (vfsMkdirat root 1 1 (b "dir/"))
  let d ← ok (resolveAt t 1 1 0 (b "dir"))
  let (i,t) ← ok (vfsOpenat t 1 d [255] {create := true})
  let t ← ok (inodeWrite t i 2 [255,0,1])
  must ((← ok (inodeRead t i 0 32)) == [0,0,255,0,1]) "sparse byte write"
  let t ← ok (vfsSymlinkat t 1 1 (b "dir") (b "sym"))
  must (err (vfsMkdirat t 1 1 (b "sym/")) .EEXIST) "mkdir existing symlink with slash"
  must ((← ok (resolveAt t d d 40 (b "/../" ++ [255]))) == i) "chroot clamp"
  must ((← ok (resolveAt t 1 1 1 (b "sym/" ++ [255]))) == i) "symlink parent"
  must (err (resolveAt t 1 1 0 (b "sym/" ++ [255])) .ELOOP) "link budget"
  must ((← ok (vfsReadlinkat t 1 1 (b "sym"))) == b "dir") "readlink"
  let t ← ok (vfsRenameat t 1 1 (b "dir") 1 (b "other"))
  must ((← ok (vfsGetcwd t 1 d)) == b "/other") "cwd rename"
  must (err (resolveAt t 1 1 40 (b "sym/" ++ [255])) .ENOENT) "dangling symlink"
  let t ← ok (vfsSymlinkat t 1 1 (b "other") (b "alias"))
  let probe := b "./alias/../alias//" ++ [255]
  let live := t.setOpenRefs i 1
  let removed ← ok (vfsUnlinkat live 1 1 probe)
  must (err (resolveAt removed 1 1 40 probe) .ENOENT) "open-unlinked name"
  must ((← ok (inodeRead removed i 0 40)) == [0,0,255,0,1]) "open-unlinked bytes"
  must ((← ok (inodeStat removed i)).nlink == 0) "open-unlinked nlink"
  must (err ((removed.setOpenRefs i 0).node i) .ENOENT) "last close releases inode"
  let rows ← ok (freezeVfsToTree live)
  let ro ← ok (mountTreeToVfs (Std.TreeMap.ofList rows) true)
  must (err (vfsMkdirat ro 1 1 (b "x")) .EROFS) "readonly mkdir"
  must (err (vfsSymlinkat ro 1 1 (b "other") (b "x")) .EROFS) "readonly symlink"
  must (err (vfsUnlinkat ro 1 1 probe) .EROFS) "readonly unlink"
  must (err (vfsRenameat ro 1 1 (b "other") 1 (b "moved")) .EROFS) "readonly rename"
  must (err (vfsOpenat ro 1 1 probe {access := .writeOnly}) .EROFS) "readonly open"
  must (err (vfsOpenat ro 1 1 probe {trunc := true}) .EROFS) "readonly truncate"
  must ((← ok (vfsOpenat ro 1 1 probe {create := true})).1 == i) "readonly O_CREAT on existing inode"
  must (err (vfsOpenat ro 1 1 (b "missing") {create := true}) .EROFS) "readonly O_CREAT on absent name"
  must (err (inodeWrite ro i 0 [77]) .EROFS) "readonly write"

def main : IO Unit := do
  model
  IO.FS.withTempDir fun tmp => do
    let src := tmp / "src"
    let store := tmp / "objects"
    IO.FS.createDir src
    IO.FS.writeBinFile (src / "bytes") (ByteArray.mk #[0,255,7,190])
    IO.FS.createDir (src / "empty")
    let symlink ← IO.Process.output {cmd := "ln", args := #["-s","bytes",(src / "target").toString]}
    must (symlink.exitCode == 0) "symlink fixture"
    let h ← captureDir store src
    verifyTree store h
    let fs ← loadTree store h false
    let file ← ok (resolveAt fs 1 1 40 (b "/target"))
    must ((← ok (inodeRead fs file 0 8)) == [0,255,7,190]) "disk to inode"
    must ((← saveTree store fs) == h) "canonical graph to disk hash"
    let dst := tmp / "dst"
    materialize store h dst
    must ((← captureDir store dst) == h) "materialized tree hash"
    let graph ← ok (inodeWrite fs file 0 [11])
    must ((← saveTree store graph) != h) "changed inode changes root digest"
    let (odd,graph) ← ok (vfsOpenat graph 1 1 [255,128] {create := true})
    let graph ← ok (inodeWrite graph odd 0 [128,255])
    let graph ← ok (vfsSymlinkat graph 1 1 [255,128] [254])
    let oddHash ← saveTree store graph
    let oddDir := tmp / "byte-names"
    materialize store oddHash oddDir
    try
      must ((← captureDir store oddDir) == oddHash) "non-UTF-8 filename and symlink target"
    finally
      let clean ← IO.Process.output {cmd := "/bin/rm", args := #["-r","--",oddDir.toString]}
      must (clean.exitCode == 0) "byte-named test fixture cleanup"
    let collision ← IO.Process.output {cmd := "ln", args := #[(src / "bytes").toString,(src / "second").toString]}
    must (collision.exitCode == 0) "hard link fixture"
    let refused ← try
      discard <| captureDir store src
      pure false
    catch _ => pure true
    must refused "hard link must be rejected"
    let damage := store / "tree" / h
    let writable ← IO.Process.output {cmd := "chmod", args := #["u+w",damage.toString]}
    must (writable.exitCode == 0) "corruption fixture permissions"
    IO.FS.writeBinFile damage (ByteArray.mk #[1])
    let corrupt ← try
      discard <| loadTree store h
      pure false
    catch e => pure (e.toString.contains "CAS_HASH_MISMATCH")
    must corrupt "corrupt tree must fail verification"
  IO.println "VFS/TreeCAS integration passed"
