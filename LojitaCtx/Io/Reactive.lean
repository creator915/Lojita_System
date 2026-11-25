import LojitaCtx.Io.Buf

namespace LojitaCtx.Io
open LojitaCtx.Posix

inductive ReadyEvent where
  | data (fd : Fd) (bytes : ByteArray)
  | eof (fd : Fd)
  | writable (fd : Fd)
  | hangup (fd : Fd)
  | fault (fd : Fd) (error : Errno)
  | interrupted
  | timeout

inductive Decision (S A : Type) where
  | more (state : S)
  | stop (result : A)

structure ReactiveApp (S A : Type) where
  interested : S → List PollReq
  timeoutMs : S → Option Nat
  onEvent : S → ReadyEvent → Decision S A
  blockSize : Nat := 4096

inductive Reactor (S A : Type) where
  | result (r : Ret A)
  | poll (state : S)
  | ready (state : S) (items : List (PollReq × Nat))

private def emit {S A : Type} (app : ReactiveApp S A) (state : S) (event : ReadyEvent)
    (rest : List (PollReq × Nat)) : Reactor S A :=
  match app.onEvent state event with
  | .stop a => .result (.ok a)
  | .more s => .ready s rest

private def pollRequest {Δ S A} (cap : .fdIoCap ∈ Δ) (app : ReactiveApp S A) (s : S) :
    Request Δ (Ret A) (Reactor S A) :=
  let req := app.interested s
  .ask (.ppoll req (app.timeoutMs s) true) cap fun
    | .err .EINTR => emit app s .interrupted []
    | .err e => .result (.err e)
    | .wouldBlock why => .result (.wouldBlock why)
    | .ok masks =>
      if masks.length != req.length then .result (.err .EIO) else
        let ready := (req.zip masks).filter (fun item => item.2 != 0)
        if ready.isEmpty then emit app s .timeout [] else .ready s ready

private def readyRequest {Δ S A} (cap : .fdIoCap ∈ Δ) (app : ReactiveApp S A) (s : S) :
    List (PollReq × Nat) → Request Δ (Ret A) (Reactor S A)
  | [] => pollRequest cap app s
  | (req, mask) :: rest =>
    let fd := req.fd
    let event (e : ReadyEvent) := match app.onEvent s e with
      | .stop a => Request.done (.ok a)
      | .more s' => readyRequest cap app s' rest
    if mask &&& 32 != 0 then event (.fault fd .EBADF)
    else if mask &&& 1 != 0 || (mask &&& 16 != 0 && req.events &&& 1 != 0) then
      .ask (.read fd (max 1 app.blockSize)) cap fun
        | .ok bs => emit app s (if bs.isEmpty then .eof fd else .data fd bs) rest
        | .err .EAGAIN => .ready s rest
        | .err .EINTR => emit app s .interrupted rest
        | .err e => emit app s (.fault fd e) rest
        | .wouldBlock w => .result (.wouldBlock w)
    else if mask &&& 16 != 0 then event (.hangup fd)
    else if mask &&& 8 != 0 then event (.fault fd .EIO)
    else if mask &&& 4 != 0 then event (.writable fd)
    else event (.hangup fd)

def ReactiveApp.run {Δ S A} (app : ReactiveApp S A) (cap : .fdIoCap ∈ Δ) (initial : S) :
    PosixMachine Δ (Reactor S A) (Ret A) :=
  PosixMachine.unfold (.poll initial : Reactor S A) fun
    | .result a => .done a
    | .poll s => pollRequest cap app s
    | .ready s items => readyRequest cap app s items

end LojitaCtx.Io
