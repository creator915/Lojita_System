import Lojita.Runtime.WorldRunner
import LojitaCtx.World

namespace Lojita.WorldRunner.LegacyInput
open LojitaCtx.World LojitaCtx.Terminal

@[extern "ct_lean_tty_input"] private opaque ttyInput : IO (Option Nat × Bool)
@[extern "ct_lean_begin_signals"] opaque beginSignals : IO Nat
@[extern "ct_lean_signal_delivered"] private opaque signalDelivered (signo : UInt8) : IO Unit
@[extern "ct_lean_end_signals"] opaque endSignals : IO Unit
@[extern "ct_lean_term_size"] private opaque termSize : IO (Nat × Nat)

private abbrev syscall := Lojita.Runtime.WorldRunner.perform []
private abbrev PReady := LojitaCtx.Posix.PollReq

/-- The CLI byte API and reactive stdin share unread bytes in original order.
    None distinguishes a completed stream from an empty read buffer. -/
private initialize stdinBuffer : IO.Ref (Option Bytes) ← IO.mkRef (some [])

def readStdinByte : IO (Option UInt8) := do
  repeat
    match ← stdinBuffer.get with
    | none => return none
    | some (b :: rest) => stdinBuffer.set (some rest); return some b
    | some [] =>
      match ← syscall (.read 0 8192) with
      | .err .EINTR => continue
      | .ok (b :: rest) => stdinBuffer.set (some rest); return some b
      | _ => stdinBuffer.set none; return none
  return none

def readTTYByte : IO (Option UInt8) := do
  let (some fd, _) ← ttyInput | return none
  let .ok [bits] ← syscall (.ppoll [⟨fd,1⟩] (some 0) false) | return none
  if bits &&& 1 == 0 then return none
  let .ok bs ← syscall (.read fd 1) | return none
  return bs.head?

structure Sources where
  signalFd : Nat
  tty : Option Nat
  stdin : Bool

def sources (Δ : List Cap) (signalFd : Nat) : IO Sources := do
  let (fd,same) ← if hasCap .ttyCap Δ then ttyInput else pure (none,false)
  return ⟨signalFd,fd,hasCap .stdioCap Δ && !same⟩

private def event {Δ : List Cap} {c : Cap} (p : EventPayload c) : Option (Event Δ) :=
  (findCapIn c Δ).map fun proof => Event.mkEvent proof p

private def signalEvent (Δ : List Cap) (fd : Nat) : IO (Option (Event Δ)) := do
  let .ok [signo] ← syscall (.read fd 1) | return none
  signalDelivered signo
  match signo with
  | 1 => return event (.evSignal .sigHUP)
  | 2 => return event (.evSignal .sigINT)
  | 3 => return event (.evSignal .sigQUIT)
  | 15 => return event (.evSignal .sigTERM)
  | 28 =>
    let (rows,cols) ← termSize
    return event (.evResize rows cols)
  | _ => return none

private def monoMs : IO Nat := do
  let .ok ns ← syscall .clockGettime | throw (IO.userError "CLOCK_MONOTONIC failed")
  return Nat.div ns 1000000

/-- Return at most one typed event. A zero wait lets pending terminal signals
    take priority over bytes buffered by a synchronous stdin operation. -/
def next (Δ : List Cap) (s : Sources) : IO (Option (Event Δ) × Sources) := do
  let buffer ← stdinBuffer.get
  let buffered := hasCap .stdioCap Δ && buffer.any (!·.isEmpty)
  let ttyReq : List PReady := s.tty.toList.map fun fd => ⟨fd,1⟩
  let stdinReq : List PReady := if s.stdin && buffer.isSome then [⟨0,1⟩] else []
  let start ← monoMs
  -- The self-pipe delivers signal identities; retain its installed handler during ppoll.
  let polled : LojitaCtx.Posix.Ret (List Nat) ← syscall (.ppoll (⟨s.signalFd,1⟩ :: ttyReq ++ stdinReq) (some (if buffered then 0 else 25)) false)
  let .ok masks := polled | do
    if polled matches .err .EINTR then return (none,s)
    throw (IO.userError "reactive ppoll failed")
  if masks[0]?.getD 0 &&& 1 != 0 then return (← signalEvent Δ s.signalFd,s)
  if buffered then
    let bs := buffer.getD []
    let chunk := bs.take 4096
    stdinBuffer.set (some (bs.drop chunk.length))
    return (event (.evStdinBytes chunk),s)
  let ready := fun bits : Nat => bits &&& 57 != 0 -- IN, ERR, HUP or NVAL
  if let some fd := s.tty then
    if ready (masks[1]?.getD 0) then
      match ← syscall (.read fd 256) with
      | .ok (b :: bs) => return (event (.evTTYBytes (b :: bs)),s)
      | .err .EINTR | .err .EAGAIN | .wouldBlock _ => return (none,s)
      | _ => return (event .evTTYEOF,{s with tty := none})
  if !stdinReq.isEmpty && ready (masks[1+ttyReq.length]?.getD 0) then
    match ← syscall (.read 0 4096) with
    | .ok (b :: bs) => return (event (.evStdinBytes (b :: bs)),s)
    | .err .EINTR | .err .EAGAIN | .wouldBlock _ => return (none,s)
    | _ => stdinBuffer.set none; return (event .evStdinEOF,s)
  return (event (.evTickMs ((← monoMs)-start)),s)

end Lojita.WorldRunner.LegacyInput
