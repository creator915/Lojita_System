import LojitaCtx.Posix.Kernel
import LojitaCtx.Io.Buf
import Lean.Data.Json

open Lean LojitaCtx.Posix LojitaCtx.Io

namespace IoDiff

structure Trace where
  ident : Nat
  steps : Array (List Nat)
  linux : Array String
  deriving FromJson

private def hex (xs : Bytes) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut s := ""
  for b in xs do
    s := (s.push digits[b.toNat / 16]!).push digits[b.toNat % 16]!
  return s

private def path (id n : Nat) : Bytes :=
  match n with
  | 11 => [98,105,110,255]
  | 12 => s!"/work/D{id}/a".toUTF8.data.toList
  | 13 => s!"/work/D{id}/s".toUTF8.data.toList
  | _ => (#["a","b","c","d","d/e","d/f","s","t","d/../a","missing/leaf","./a","","","","d//e","."][n]!).toUTF8.data.toList

private def bits (n bit : Nat) : Bool := n &&& bit != 0

private def flags (x : Nat) : OpenFlags := {
  access := match x % 4 with | 0 => .readOnly | 1 => .writeOnly | _ => .readWrite
  create := bits x 4, excl := bits x 8, trunc := bits x 16, append := bits x 32
  directory := bits x 64, nofollow := bits x 128 }

private def payload (length seed : Nat) : Bytes :=
  (List.range length).map fun i =>
    (if seed ≥ 256 then (if i%7 == 6 then 10 else 97+(seed+i)%26) else (seed+29*i)%256).toUInt8

private def numeric (a : Nat) : String := "N" ++ toString a
private def binary (a : Bytes) := "B" ++ hex a
private def paired (a : Nat × Nat) := s!"P{a.1},{a.2}"

private def reply {α : Type} (encode : α → String) : Ret α → String
  | .ok a => encode a
  | .err e => s!"E{e.code}"
  | .wouldBlock _ => "W"

private def applyOp (m : Machine) (sl : StepSlice) (op : SysOp) (encode : op.Result → String) :
    String × Machine :=
  let (r,next) := stepSyscall m sl op
  (reply encode r,next)

private def makePty (m : Machine) : Except Errno (String × Machine) := do
  let id := tableFresh m.kernel.ptys
  let f : OpenFlags := { access := .readWrite, nonblock := true }
  let t := m.setPty id {attrs := rawTermios}
  let (a,t) ← t.allocate (.pty id true) f
  let (b,t) ← t.allocate (.pty id false) f
  return (paired (a,b),t.account)

private def observed (m : Machine) (op fd : Nat) (linux : String) : StepSlice := Id.run do
  if linux == "E4" then return {intrBefore := true}
  unless [2,3,21,22].contains op do return {}
  let .ok (_,d) := m.lookup fd | return {}
  if let .inode _ := d.target then return {}
  let count := if linux.startsWith "B" then (linux.length-1)/2 else
    if linux.startsWith "N" then (linux.drop 1).toString.toNat?.getD 65536 else 65536
  return {maxBytes := count}

private def bufRun {S α : Type} (p : PosixMachine [.fdIoCap] S α) (m : Machine) :
    Option α × Machine :=
  let (out,next) := runPrefix (p.observe 2048) m (List.replicate 2048 canonicalSlice)
  match out with | .done a => (some a,next) | .suspended => (none,next)

private def byteReads (fd chunk : Nat) (m : Machine) : String × Machine :=
  let (first,next) := bufRun (readLine (by simp) {fd,chunkSize := chunk}) m
  match first with
  | none => ("suspended", next)
  | some (.ok line, reader) =>
    let (all,final) := bufRun (readAll (by simp) reader) next
    let result := all.map fun (r,_) => reply (fun rest => "L" ++ (line.map hex).getD "-" ++ "|" ++ hex rest) r
    (result.getD "suspended", final)
  | some (.err e, _) => (s!"E{e.code}", next)
  | some (.wouldBlock _, _) => ("W", next)

private def action (id : Nat) (m : Machine) (row : List Nat) (linux : String) :
    String × Machine := Id.run do
  let [op,a,b,c] := row | return ("invalid",m)
  let sl := observed m op a linux
  let unit := fun (_ : Unit) => "N0"
  match op with
  | 0 => return applyOp m sl (.openat none (path id a) (flags b) c) numeric
  | 1 => return applyOp m sl (.close a) unit
  | 2 => return applyOp m sl (.read a b) (fun bs => binary bs.data.toList)
  | 3 => return applyOp m sl (.write a (payload b c).toByteArray) numeric
  | 4 => return applyOp m sl (.dup2 a b) numeric
  | 5 => return applyOp m sl (.lseek a ((b : Int)-8) (if c==0 then .set else if c==1 then .cur else .end)) numeric
  | 6 => return applyOp m sl (.mkdirat none (path id a) b) unit
  | 7 => return applyOp m sl (.unlinkat none (path id a) (b != 0)) unit
  | 8 => return applyOp m sl (.renameat none (path id a) none (path id b)) unit
  | 9 => return applyOp m sl (.symlinkat (path id a) none (path id b)) unit
  | 10 => return applyOp m sl (.readlinkat none (path id a)) binary
  | 11 => return applyOp m sl (.pipe2 true true) paired
  | 12 => return applyOp m sl (.ppoll [⟨a,5⟩,⟨b,5⟩] (some 0) false) fun (xs : List Nat) => paired (xs[0]!,xs[1]!)
  | 13 => match makePty m with | .ok result => return result | .error e => return (s!"E{e.code}",m)
  | 14 => return applyOp m sl (.tcsetattr a {rawTermios with icanon := b != 0}) unit
  | 15 => return applyOp m sl (.ppoll [] none true) fun _ => "N0"
  | 16 => return applyOp m sl (.pread a b c) (fun bs => binary bs.data.toList)
  | 17 => return applyOp m sl (.pwrite a (payload b c).toByteArray (c%11)) numeric
  | 18 =>
    let (out,next) := bufRun (writeAll (by simp) {fd := a, remaining := payload b c}) m
    return (out.map (fun v => reply unit v.1) |>.getD "suspended",next)
  | 19 => return byteReads a b m
  | 20 =>
    let (r,next) := stepSyscall m sl (.pipe2 true true)
    let .ok (rd,_) := r | return (reply paired r,next)
    let .ok (_,d) := next.lookup rd | return ("bad pipe",next)
    let .pipe i _ := d.target | return ("bad pipe",next)
    let some pipe := next.kernel.pipes[i]? | return ("bad pipe",next)
    return (reply paired r,next.setPipe i {pipe with cap := 4096})
  | 21 => return applyOp m sl (.write a (payload (if b==0 then 4095 else 4096+b) c).toByteArray) numeric
  | 22 => return applyOp m sl (.read a 4096) (fun bs => binary bs.data.toList)
  | _ => return ("unknown",m)

private def mkdir (m : Machine) (name : String) :=
  (stepSyscall m {} (.mkdirat none name.toUTF8.data.toList 493)).2

private def initial (id : Nat) : Machine := Id.run do
  let m : Machine := {proc := {limit := 64}}
  let m := mkdir (mkdir m "/work") s!"/work/D{id}"
  let m := (stepSyscall m {} (.chdir s!"/work/D{id}".toUTF8.data.toList)).2
  -- The native observer owns three standard descriptors, which the generator never addresses.
  let mut s := m
  for _ in [:3] do
    if let .ok (_,next) := s.allocate (.inode 1) {} then s := next
  return s.account

private def manifest (fs : InodeTable) (fuel id : Nat) : Json :=
  match fuel with
  | 0 => .str "invalid-depth"
  | k+1 => Id.run do
    let .ok node := fs.node id | return .str "missing"
    match node.payload with
    | .dir _ es => return toJson ("t",node.mode,es.toList.map fun (n,i) => (hex n,manifest fs k i))
    | .reg data => return toJson ("b",node.mode,hex data.data.toList)
    | .symlink target => return toJson ("s",node.mode,hex target)
    | _ => return .str "invalid-node"

def run (t : Trace) : Json := Id.run do
  let mut m := initial t.ident
  let mut outs : Array String := #[]
  for i in [:t.steps.size] do
    let (r,next) := action t.ident m t.steps[i]! t.linux[i]!
    m := next
    outs := outs.push r
  return toJson (outs,manifest m.kernel.vfs 32 m.proc.cwd)

end IoDiff

def main : IO Unit := do
  let input ← IO.getStdin
  let out ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let trace ← IO.ofExcept ((Json.parse line).bind (fromJson? (α := IoDiff.Trace)))
    out.putStrLn (IoDiff.run trace).compress
