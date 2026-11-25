import LojitaCtx.Io.Buf

namespace LojitaCtx.Io.FsLib
open LojitaCtx.Posix

variable {Δ : List Cap} {α β : Type}

def andThen (action : PosixProg Δ (Ret α)) (next : α → PosixProg Δ (Ret β)) :
    PosixProg Δ (Ret β) := do
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

def withFd (fdCap : .fdIoCap ∈ Δ) (acquire : PosixProg Δ (Ret Fd))
    (use : Fd → PosixProg Δ (Ret α)) : PosixProg Δ (Ret α) :=
  andThen acquire fun fd => do
    let value ← use fd
    return afterClose value (← PosixProg.call (.close fd) fdCap)

def readFileAll (fdCap : .fdIoCap ∈ Δ) (fsCap : .fsPathCap ∈ Δ) (path : Bytes)
    (chunkSize : Nat := 65536) : PosixProg Δ (Ret Bytes) :=
  withFd fdCap (PosixProg.call (.openat none path {} 0) fsCap) fun fd => do
    return (← readAll fdCap {fd, chunkSize}).1

def writeFileTrunc (fdCap : .fdIoCap ∈ Δ) (fsCap : .fsPathCap ∈ Δ) (path data : Bytes)
    (mode : FileMode := 0o666) : PosixProg Δ (Ret Unit) :=
  withFd fdCap (PosixProg.call (.openat none path
      {access := .writeOnly, create := true, trunc := true, cloexec := true} mode) fsCap)
    fun fd => do return (← writeAll fdCap ⟨fd, data, 0⟩).1

private def slash : UInt8 := 47

/-- Preserve the parent spelling, including absolute paths and symlinks. -/
def parentAndName (path : Bytes) : Bytes × Bytes :=
  let rev := path.reverse
  let name := (rev.takeWhile (· != slash)).reverse
  let dir := (rev.dropWhile (· != slash)).reverse
  (if dir.isEmpty then [46] else dir, name)

private def tempName (n : Nat) : Bytes := (".lojita-tmp-" ++ toString n).toUTF8.data.toList

private inductive TempState where
  | trying (next : Nat)
  | finished (result : Ret (Bytes × Fd))

private def createTemp (fsCap : .fsPathCap ∈ Δ) (dir : Fd) (dest : Bytes) (mode : FileMode) :
    PosixProg Δ (Ret (Bytes × Fd)) :=
  PosixProg.unfold (.trying 0 : TempState) fun
    | .finished r => .done r
    | .trying n =>
      let i := if tempName n == dest then n + 1 else n
      let name := tempName i
      .ask (.openat (some dir) name { access := .writeOnly, create := true, excl := true, nofollow := true, cloexec := true } mode) fsCap fun
        | .ok fd => .finished (.ok (name, fd))
        | .err .EEXIST => .trying (i + 1)
        | .err e => .finished (.err e)
        | .wouldBlock w => .finished (.wouldBlock w)

/-- Stage in an exclusively created sibling. Holding the parent directory open
    across create, rename and cleanup prevents redirection by a parent rename. -/
def writeFileAtomic (fdCap : .fdIoCap ∈ Δ) (fsCap : .fsPathCap ∈ Δ) (path data : Bytes)
    (mode : FileMode := 0o666) : PosixProg Δ (Ret Unit) :=
  let (parent, name) := parentAndName path
  if path.isEmpty then pure (.err .ENOENT)
  else if name.isEmpty then pure (.err .EISDIR)
  else withFd fdCap (PosixProg.call (.openat none parent {directory := true, cloexec := true} 0)
    fsCap) fun dir =>
    andThen (createTemp fsCap dir name mode) fun (tmp, fd) => do
      let (written, _) ← writeAll fdCap ⟨fd, data, 0⟩
      let staged := afterClose written (← PosixProg.call (.close fd) fdCap)
      let result ← andThen (pure staged) fun _ =>
        PosixProg.call (.renameat (some dir) tmp (some dir) name) fsCap
      match result with
      | .ok () => return .ok ()
      | other =>
        let _ ← PosixProg.call (.unlinkat (some dir) tmp false) fsCap
        return other

private def ensureDir (fsCap : .fsPathCap ∈ Δ) (path : Bytes) (mode : FileMode) :
    PosixProg Δ (Ret Unit) := do
  match ← PosixProg.call (.mkdirat none path mode) fsCap with
  | .err .EEXIST =>
    andThen (PosixProg.call (.fstatat none path true) fsCap) fun st =>
      pure (if st.kind = .directory then .ok () else .err .ENOTDIR)
  | other => pure other

private def mkdirParts (cap : .fsPathCap ∈ Δ) (mode : FileMode) (base : Bytes) :
    List Bytes → PosixProg Δ (Ret Unit)
  | [] => pure (.ok ())
  | seg :: rest =>
    let path := base ++ seg
    andThen (ensureDir cap path mode) fun _ => mkdirParts cap mode (path ++ [slash]) rest

def mkdirP (fsCap : .fsPathCap ∈ Δ) (path : Bytes) (mode : FileMode := 0o777) :
    PosixProg Δ (Ret Unit) :=
  if path.isEmpty then pure (.err .ENOENT) else
    let parts := (path.splitOn slash).filter (!·.isEmpty)
    let init := if path.head? == some slash then [slash] else []
    mkdirParts fsCap mode init parts

end LojitaCtx.Io.FsLib
