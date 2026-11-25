import LojitaCtx.Cli

namespace Gen.Gate2.Channels
open LojitaCtx.Terminal LojitaCtx.World LojitaCtx.Cli

-- Keep the write order explicit: all three outputs share one slave in allTTY.
def report (input : Bytes) : CliApp CliCaps := do
  let flags := [← hasTTYW ttyInCli, ← isTTYStdinW stdioInCli, ← isTTYStdoutW stdioInCli,
    ← isTTYStderrW stdioInCli]
  writeStdoutW stdioInCli (flags.map (fun flag => if flag then 49 else 48) ++ input)
  writeStderrW stdioInCli [69, 0, 255]
  let wrote ← writeTTYW ttyInCli (bytes "UI")
  return if wrote then 0 else 25

def cli : CliApp CliCaps := do
  if (← getArgsW envInCli) == ["raw"] then
    unless ← setTTYRawW ttyInCli true do return 1
    writeStdoutStrW stdioInCli "ready\n"
    writeStdoutW stdioInCli (← readExactBytesW stdioInCli 4)
    return 0
  let some b ← readStdinByteW stdioInCli | return 10
  let some line ← readStdinLineW stdioInCli | return 11
  report (b :: line)

def chunk (source : String) (acc bs : Bytes) : WorldProg CliCaps (Sum Bytes ExitCode) := do
  let input := acc ++ bs
  if input.contains 10 then return .inr (← report (bytes source ++ input))
  return .inl input

def reactive : ReactiveApp CliCaps Bytes where
  init := pure []
  onStep ev acc := match ev with
    | ⟨_, .evStdinBytes bs⟩ => chunk "stdin:" acc bs
    | ⟨_, .evTTYBytes bs⟩ => chunk "tty:" acc bs
    | _ => pure (.inl acc)

-- Polling has installed the non-restarting SIGWINCH handler by the time
-- this turn enters the same blocking fd 0 read used by a CliApp.
def interrupted : ReactiveApp CliCaps Unit where
  init := pure ()
  onStep ev _ := do
    match ev with
    | ⟨_, .evStdinBytes _⟩ =>
      writeStdoutStrW stdioInCli "reading\n"
      let some b ← readStdinByteW stdioInCli | return .inr 1
      writeStdoutW stdioInCli [b]
      return .inr 0
    | _ => return .inl ()

structure EOFState where
  stdin : Bool := false
  tty : Bool := false
  quietMs : Nat := 0

-- Stay in the poll loop after both hangups. A repeated EOF is an immediate failure.
def hangup : ReactiveApp CliCaps EOFState where
  init := pure {}
  onStep ev s := do
    match ev with
    | ⟨_, .evStdinEOF⟩ =>
      if s.stdin then return .inr 11
      writeStdoutStrW stdioInCli "stdin EOF\n"
      return .inl {s with stdin := true}
    | ⟨_, .evTTYEOF⟩ =>
      if s.tty then return .inr 12
      writeStdoutStrW stdioInCli "tty EOF\n"
      return .inl {s with tty := true}
    | ⟨_, .evTickMs ms⟩ =>
      if s.stdin && s.tty then
        let quiet := s.quietMs + ms
        if quiet ≥ 200 then return .inr 0
        return .inl {s with quietMs := quiet}
      return .inl s
    | _ => return .inl s

-- The synchronous first byte may have read ahead. Its suffix must be
-- delivered on stdin even while the producer keeps its pipe open.
def inputs : ReactiveApp CliCaps Unit where
  init := do
    discard <| setTTYRawW ttyInCli true
    if let some b ← readStdinByteW stdioInCli then writeStdoutW stdioInCli [b]
  onStep ev _ := do
    match ev with
    | ⟨_, .evStdinBytes bs⟩ => writeStdoutW stdioInCli bs
    | ⟨_, .evTTYBytes bs⟩ => writeStderrW stdioInCli bs
    | ⟨_, .evResize rows cols⟩ => writeStdoutStrW stdioInCli s!"{rows}x{cols}\n"
    | ⟨_, .evSignal .sigINT⟩ => writeStdoutStrW stdioInCli "INT\n"
    | ⟨_, .evSignal .sigQUIT⟩ => writeStdoutStrW stdioInCli "QUIT\n"
    | ⟨_, .evSignal .sigHUP⟩ => writeStdoutStrW stdioInCli "HUP\n"
    | ⟨_, .evSignal .sigTERM⟩ => return .inr 0
    | _ => pure ()
    return .inl ()

end Gen.Gate2.Channels
