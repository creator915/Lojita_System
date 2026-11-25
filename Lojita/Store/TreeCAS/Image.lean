import LojitaCtx.Posix.Vfs
import Std.Data.TreeMap.Lemmas

namespace Lojita.Store.TreeCAS
open LojitaCtx.Posix

/-- Relative inode numbers identify edges in the pure image. The disk Merkle
    codec addresses children by digest and therefore does not persist IDs. -/
inductive Entry where
  | file (data : ByteArray)
  | directory (parent : Nat) (entries : Entries)
  | symlink (target : Bytes)
  deriving Inhabited

structure ImageNode where
  mode : FileMode
  entry : Entry
  deriving Inhabited

abbrev ImageTable := Std.TreeMap InodeId ImageNode
abbrev TreeImage := List (InodeId × ImageNode)

private def lookup (rows : TreeImage) (id : InodeId) : Option ImageNode :=
  (rows.find? (·.1 == id)).map Prod.snd

private def edges (rows : TreeImage) : List (InodeId × InodeId) :=
  rows.flatMap fun (parent, node) => match node.entry with
    | .directory _ es => es.toList.map fun e => (parent, e.2)
    | _ => []

private def rooted (parents : List (InodeId × InodeId)) : Nat → Nat → Bool
  | 0, id => id == 1
  | k+1, id => id == 1 || (parents.find? (·.2 == id)).any (rooted parents k ·.1)

def canonicalTree (rows : TreeImage) : Bool := Id.run do
  let some root := lookup rows 1 | return false
  let .directory 1 _ := root.entry | return false
  let links := edges rows
  return rows.all fun (id,n) =>
    n.mode ≤ 511 && id > 0 &&
    (if id == 1 then !(links.any (·.2 == id)) else
      (links.filter (·.2 == id)).length == 1 && rooted links rows.length id) &&
    match n.entry with
    | .file _ => true
    | .symlink bs => n.mode == 511 && !bs.isEmpty && !bs.contains 0 && bs.length < 4096
    | .directory parent es =>
      (id == 1 || links.contains (parent,id)) &&
      es.toList.all (fun (name,child) => validSeg name && (lookup rows child).isSome)

private def directoryLinks (rows : TreeImage) (es : Entries) : Nat :=
  2 + es.toList.countP (fun (_, id) => match (lookup rows id).map ImageNode.entry with
    | some (.directory ..) => true | _ => false)

private def instantiate (rows : TreeImage) (ro : Bool) (n : ImageNode) : Inode :=
  match n.entry with
  | .file bs => {payload := .reg bs, mode := n.mode, roLayer := ro}
  | .symlink bs => {payload := .symlink bs, mode := n.mode, roLayer := ro}
  | .directory p es =>
    {payload := .dir p es, mode := n.mode, roLayer := ro, nlink := directoryLinks rows es}

def mountTreeToVfs (image : ImageTable) (ro : Bool := true) : Except Errno InodeTable :=
  let rows := image.toList
  if canonicalTree rows then
    .ok {nodes := image.map (fun _ n => instantiate rows ro n),
         nextId := rows.foldl (fun maxId p => max maxId (p.1+1)) 2}
  else .error .EINVAL

/-- Volatile resources and aliases absent from the three-kind disk format
    produce an error. Nameless but still open inodes are outside the snapshot. -/
private def project (n : Inode) : Except Errno (Option ImageNode) :=
  if n.nlink == 0 then .ok none else
  match n.payload with
  | .reg bs => if n.nlink == 1 then .ok (some ⟨n.mode,.file bs⟩) else .error .EOPNOTSUPP
  | .symlink bs => if n.nlink == 1 then .ok (some ⟨n.mode,.symlink bs⟩) else .error .EOPNOTSUPP
  | .dir p es => .ok (some ⟨n.mode,.directory p es⟩)
  | _ => .error .EOPNOTSUPP

private def collect : List (InodeId × Inode) → Except Errno TreeImage
  | [] => .ok []
  | (id,n) :: rest => do
    let node ← project n
    let rows ← collect rest
    return match node with | some row => (id,row) :: rows | none => rows

private def linksAgree (rows : TreeImage) (n : Inode) : Bool :=
  n.nlink == 0 || match n.payload with
    | .dir _ es => n.nlink == directoryLinks rows es
    | _ => true

def freezeVfsToTree (fs : InodeTable) : Except Errno TreeImage := do
  let image ← collect fs.nodes.toList
  if !canonicalTree image || !(fs.nodes.toList.all (fun row => linksAgree image row.2)) then throw .EINVAL
  return image

private theorem project_instantiate (rows : TreeImage) (ro : Bool) (n : ImageNode) :
    project (instantiate rows ro n) = .ok (some n) := by
  cases n with
  | mk mode entry =>
    cases entry <;> simp [project, instantiate, directoryLinks]

private theorem collect_instantiate (rows : TreeImage) (ro : Bool) (xs : TreeImage) :
    collect (xs.map (fun p => (p.1, instantiate rows ro p.2))) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons item xs ih =>
    rcases item with ⟨id,n⟩
    simp [collect, project_instantiate, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem mounted_links (rows : TreeImage) (ro : Bool) (node : ImageNode) :
    linksAgree rows (instantiate rows ro node) = true := by
  cases node with | mk mode entry => cases entry <;> simp [linksAgree,instantiate]

/-- Equality is of ordered manifest rows, including every directory edge,
    file mode, symlink target and file byte, independent of map balancing. -/
theorem freeze_mount_roundtrip (image : ImageTable) (ro : Bool)
    (h : canonicalTree image.toList = true) :
    (mountTreeToVfs image ro >>= freezeVfsToTree) = .ok image.toList := by
  simp [mountTreeToVfs, h, freezeVfsToTree, collect_instantiate, Bind.bind, Except.bind,
    Pure.pure, Except.pure, mounted_links]

end Lojita.Store.TreeCAS
