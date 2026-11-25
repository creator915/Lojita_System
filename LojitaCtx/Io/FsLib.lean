import LojitaCtx.Io.Buf

namespace LojitaCtx.Io.FsLib
open LojitaCtx.Posix

variable {Δ : List Cap} {α β : Type}

def andThen (action : FreeSys Δ (Ret α)) (next : α → FreeSys Δ (Ret β)) :
    FreeSys Δ (Ret β) := do
  match ← action with
  | .ok a => next a
  | .err e => return .err e
  | .wouldBlock w => return .wouldBlock w

/-- Linux releases the descriptor even when close reports EINTR. A close error
    never masks an earlier error, and close is never retried by descriptor number. -/
def afterClose (result : Ret α) (closed : Ret Unit) : Ret α :=
  match result, closed with
  | .ok _, .err e => .err e
  | .ok _, .wouldBlock w => .wouldBlock w
  | a, _ => a

def closeRound {S : Type} (fdCap : .fdIoCap ∈ Δ) (fd : Fd) :
    Sum S (Ret α) → FreeSys Δ (Sum (Option (Fd × S)) (Ret α))
  | .inl state => .pure (.inl (some (fd,state)))
  | .inr value => .step (.close fd) fdCap (fun closed => .pure (.inr (afterClose value closed)))

/-- Acquisition and release each occur exactly once. The middle machine keeps its
    descriptor and current state across rounds. -/
def withFd {S : Type} (fdCap : .fdIoCap ∈ Δ) (acquire : FreeSys Δ (Ret Fd))
    (use : Fd → PosixMachine Δ S (Ret α)) : PosixMachine Δ (Option (Fd × S)) (Ret α) :=
  ⟨none, fun
    | none => acquire.bind fun
      | .ok fd => .pure (.inl (some (fd,(use fd).init)))
      | .err e => .pure (.inr (.err e))
      | .wouldBlock w => .pure (.inr (.wouldBlock w))
    | some (fd,s) => ((use fd).step s).bind (closeRound fdCap fd)⟩

def readFileAll (fdCap : .fdIoCap ∈ Δ) (fsCap : .fsPathCap ∈ Δ) (path : Bytes)
    (chunkSize : Nat := 65536) : PosixMachine Δ (Option (Fd × ReadProgress)) (Ret Bytes) :=
  withFd fdCap (FreeSys.call (.openat none path {} 0) fsCap) fun fd =>
    (readAll fdCap {fd,chunkSize}).map Prod.fst

def writeFileTrunc (fdCap : .fdIoCap ∈ Δ) (fsCap : .fsPathCap ∈ Δ) (path data : Bytes)
    (mode : FileMode := 0o666) : PosixMachine Δ (Option (Fd × WriteProgress)) (Ret Unit) :=
  withFd fdCap (FreeSys.call (.openat none path
      {access := .writeOnly,create := true,trunc := true,cloexec := true} mode) fsCap)
    fun fd => (writeAll fdCap ⟨fd,data,0⟩).map Prod.fst

private def slash : UInt8 := 47

/-- Preserve the parent spelling, including absolute paths and symlinks. -/
def parentAndName (path : Bytes) : Bytes × Bytes :=
  let rev := path.reverse
  let name := (rev.takeWhile (· != slash)).reverse
  let dir := (rev.dropWhile (· != slash)).reverse
  (if dir.isEmpty then [46] else dir, name)

private def tempName (n : Nat) : Bytes := (".lojita-tmp-" ++ toString n).toUTF8.data.toList

inductive AtomicState where
  | openParent
  | create (parent : Fd) (number : Nat)
  | writing (parent : Fd) (name : Bytes) (writer : BufWriter)
  | finish (result : Ret Unit)

/-- An exclusive temporary sibling stays anchored to its parent descriptor
    across retries, partial writes, rename, and cleanup. -/
def writeFileAtomic (fdCap : .fdIoCap ∈ Δ) (fsCap : .fsPathCap ∈ Δ) (path data : Bytes)
    (mode : FileMode := 0o666) : PosixMachine Δ AtomicState (Ret Unit) :=
  let (dir,dest) := parentAndName path
  let initial := if path.isEmpty then .finish (.err .ENOENT)
    else if dest.isEmpty then .finish (.err .EISDIR) else AtomicState.openParent
  let closeDir (parent : Fd) (r : Ret Unit) : FreeSys Δ (Sum AtomicState (Ret Unit)) := do
    return .inr (afterClose r (← FreeSys.call (.close parent) fdCap))
  let finish (parent : Fd) (name : Bytes) (w : BufWriter) (r : Ret Unit) := do
    let written := afterClose r (← FreeSys.call (.close w.fd) fdCap)
    let renamed ← andThen (pure written) fun _ => FreeSys.call (.renameat (some parent) name (some parent) dest) fsCap
    match renamed with
    | .ok () => closeDir parent renamed
    | _ =>
      let _ ← FreeSys.call (.unlinkat (some parent) name false) fsCap
      closeDir parent renamed
  ⟨initial, fun
    | .finish r => pure (.inr r)
    | .openParent => do
      match ← FreeSys.call (.openat none dir {directory := true,cloexec := true} 0) fsCap with
      | .ok fd => return .inl (.create fd 0)
      | .err e => return .inr (.err e)
      | .wouldBlock w => return .inr (.wouldBlock w)
    | .create parent number => do
      let i := if tempName number == dest then number+1 else number
      let name := tempName i
      match ← FreeSys.call (.openat (some parent) name
          {access := .writeOnly,create := true,excl := true,nofollow := true,cloexec := true} mode) fsCap with
      | .ok fd => return .inl (.writing parent name ⟨fd,data,0⟩)
      | .err .EEXIST => return .inl (.create parent (i+1))
      | .err e => closeDir parent (.err e)
      | .wouldBlock w => closeDir parent (.wouldBlock w)
    | .writing parent name w =>
      if w.remaining.isEmpty then finish parent name w (.ok ())
      else do
        let result ← FreeSys.call (.write w.fd w.remaining.toByteArray) fdCap
        match w.receive result with
        | .ready next => return .inl (.writing parent name next)
        | .stopped (r,_) => finish parent name w r⟩

private def ensureDir (fsCap : .fsPathCap ∈ Δ) (path : Bytes) (mode : FileMode) :
    FreeSys Δ (Ret Unit) := do
  match ← FreeSys.call (.mkdirat none path mode) fsCap with
  | .err .EEXIST =>
    andThen (FreeSys.call (.fstatat none path true) fsCap) fun st =>
      pure (if st.kind = .directory then .ok () else .err .ENOTDIR)
  | other => pure other

private def mkdirParts (cap : .fsPathCap ∈ Δ) (mode : FileMode) (base : Bytes) :
    List Bytes → FreeSys Δ (Ret Unit)
  | [] => pure (.ok ())
  | seg :: rest =>
    let path := base ++ seg
    andThen (ensureDir cap path mode) fun _ => mkdirParts cap mode (path ++ [slash]) rest

def mkdirP (fsCap : .fsPathCap ∈ Δ) (path : Bytes) (mode : FileMode := 0o777) :
    PosixMachine Δ Unit (Ret Unit) := PosixMachine.ofFree <|
  if path.isEmpty then pure (.err .ENOENT) else
    let parts := (path.splitOn slash).filter (!·.isEmpty)
    let init := if path.head? == some slash then [slash] else []
    mkdirParts fsCap mode init parts

end LojitaCtx.Io.FsLib
