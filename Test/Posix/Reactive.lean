import LojitaCtx.Io.Reactive
import LojitaCtx.Posix.Kernel

open LojitaCtx.Posix LojitaCtx.Io

private theorem cap : Cap.fdIoCap ∈ CoreCaps := by decide
private def app (mask : Nat) : ReactiveApp Unit Nat where
  interested _ := [⟨3,mask⟩]
  timeoutMs _ := some 0
  onEvent _ event := .stop (match event with
    | .data _ _ => 11 | .eof _ => 12 | .hangup _ => 16 | _ => 99)

private def afterPoll (want got : Nat) : Prefix CoreCaps (Ret Nat) :=
  let p := ((app want).run cap ()).observe 8
  p.after [⟨.masks,.ok [got]⟩]

def main : IO Unit := do
  let .done (.ok 16) := afterPoll 0 16 | throw <| IO.userError "HUP without read interest issued another syscall"
  for (want,got) in [(1,1),(1,16),(1,17)] do
    match afterPoll want got with
    | .ask (.read fd count) _ next =>
      unless fd == 3 && count == 4096 do throw <| IO.userError "wrong reactive read"
      let .done (.ok 12) := next (.ok ByteArray.empty) | throw <| IO.userError "empty read failed to emit EOF"
      let .done (.ok 11) := next (.ok (ByteArray.mk #[0,255])) | throw <| IO.userError "buffered data failed to precede EOF"
    | _ => throw <| IO.userError "ready descriptor was not read directly"
  let emptyPipe : StreamBuf := {pendingBytes := [],readers := 1,writers := 0}
  let d : OpenFileDesc := {target := .pipe 7 false,flags := {},refcnt := 2}
  let e : FdEntry := {ofd := 5}
  let m : Machine := {proc := {fds := ({} : Table FdEntry).insert 3 e |>.insert 9 e}
                      kernel := {ofds := ({} : Table OpenFileDesc).insert 5 d, pipes := ({} : Table StreamBuf).insert 7 emptyPipe}}
  let (.done (.ok 12),after) := runPrefix (((app 1).run cap ()).observe 8) m (List.replicate 8 canonicalSlice)
    | throw <| IO.userError "closed reader did not drain to EOF"
  let .ok (_,alias) := after.lookup 9 | throw <| IO.userError "lost shared file description"
  unless !alias.flags.nonblock do throw <| IO.userError "reactor changed O_NONBLOCK on a shared file description"
  IO.println "Reactive poll, HUP, EOF and shared status flags passed."
