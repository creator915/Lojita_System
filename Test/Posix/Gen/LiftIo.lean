import LojitaCtx.Io.FsLib

namespace Gen.LiftIo
open LojitaCtx.Posix LojitaCtx.Io

theorem fdCap : Cap.fdIoCap ∈ CoreCaps := by decide
theorem pathCap : Cap.fsPathCap ∈ CoreCaps := by decide

def input : Bytes := [47,102,105,120,116,117,114,101,115,47,105,110,112,117,116]

def whole : PosixProg CoreCaps (Ret Bytes) :=
  FsLib.readFileAll fdCap pathCap input

def streamed : PosixProg CoreCaps (Ret Bytes) :=
  FsLib.withFd fdCap (PosixProg.call (.openat none input {} 0) pathCap) fun fd =>
    FsLib.andThen (readLines fdCap {fd,chunkSize := 3}) fun lines => pure (.ok lines.flatten)

def report (action : PosixProg CoreCaps (Ret Bytes)) : PosixProg CoreCaps UInt32 := do
  match ← action with
  | .ok bs =>
    let (result,_) ← writeAll fdCap ⟨1,bs,0⟩
    return match result with | .ok () => 0 | _ => 2
  | _ => return 1

def base : PosixProg CoreCaps UInt32 := report whole
def refined : PosixProg CoreCaps UInt32 := report streamed

def argvEcho : PosixProg CoreCaps UInt32 := report do
  match ← PosixProg.call .getArgs (by decide) with
  | .ok [arg] => return .ok arg
  | _ => return .err .EINVAL

def wrongCaps : PosixProg [.fdIoCap] UInt32 := pure 0

end Gen.LiftIo
