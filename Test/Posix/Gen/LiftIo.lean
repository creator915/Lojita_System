import LojitaCtx.Io.FsLib

namespace Gen.LiftIo
open LojitaCtx.Posix LojitaCtx.Io

theorem fdCap : Cap.fdIoCap ∈ CoreCaps := by simp [CoreCaps]
theorem pathCap : Cap.fsPathCap ∈ CoreCaps := by simp [CoreCaps]

def input : Bytes := [47,102,105,120,116,117,114,101,115,47,105,110,112,117,116]

def whole : PosixMachine CoreCaps (Option (Fd × ReadProgress)) (Ret Bytes) :=
  FsLib.readFileAll fdCap pathCap input

def streamed : PosixMachine CoreCaps (Option (Fd × (ReadProgress × List Bytes))) (Ret Bytes) :=
  FsLib.withFd fdCap (FreeSys.call (.openat none input {} 0) pathCap) fun fd =>
    (readLines fdCap {fd,chunkSize := 3}).map (Ret.map List.flatten)

def output (result : Ret Bytes) : PosixMachine CoreCaps WriteProgress UInt32 :=
  match result with
  | .ok bs => (writeAll fdCap ⟨1,bs,0⟩).map fun (r,_) => match r with | .ok () => 0 | _ => 2
  | _ => ⟨.ready ⟨1,[],0⟩,fun _ => .pure (.inr 1)⟩

def base := whole.bind output
def refined := streamed.bind output

theorem envCap : Cap.envCap ∈ CoreCaps := by simp [CoreCaps]

def args : PosixMachine CoreCaps Unit (Ret Bytes) := PosixMachine.ofFree do
  match ← FreeSys.call .getArgs envCap with
  | .ok [arg] => return .ok arg
  | _ => return .err .EINVAL

def argvEcho := args.bind output

def wrongCaps : PosixMachine [.fdIoCap] Unit UInt32 := PosixMachine.ofFree (pure 0)

end Gen.LiftIo
