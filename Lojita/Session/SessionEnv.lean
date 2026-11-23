import Lojita.Ownership.Tools.Term
import Lojita.Ownership.Tools.Fs
import Lojita.Ownership.Tools.Net
import Lojita.Ownership.Tools.Git
import Lojita.Ownership.Tools.Web
import LojitaCtx.FuzzGen

namespace Lojita.Session.SessionEnv
open Lojita.Ownership Lojita.Ownership.Tools LojitaCtx.Terminal LojitaCtx.FsSandbox

export Term (ptySpec)
export Fs (fsSpec)
export Net (netSpec)
export Git (gitSpec)
export Web (webSpec WebConfig WebStep RawWebObs)

abbrev SessionΨ := [ptySpec, fsSpec, netSpec, gitSpec, webSpec]
abbrev ptySlot : MemSpec "pty" SessionΨ := .here rfl
abbrev fsSlot : MemSpec "fsbox" SessionΨ := .there (.here rfl)
abbrev netSlot : MemSpec "netbox" SessionΨ := .there (.there (.here rfl))
abbrev gitSlot : MemSpec "gitbox" SessionΨ := .there (.there (.there (.here rfl)))
abbrev webSlot : MemSpec "webcanvas" SessionΨ := .there (.there (.there (.there (.here rfl))))
abbrev Script (α : Type) := Prog SessionΨ (.dir []) (.dir []) α

structure ProbeResult where
  exitCode : Nat := 0
  stdout : String := ""
  stderr : String := ""

abbrev Probe := Script ProbeResult

/-- Run a batch command inside a fresh filesystem relay with declared fixtures. -/
def batch (alias : String) (args : List String := []) (input : Bytes := [])
    (fixtures : List FsFixture := []) (timeoutMs := 30000) : Script RawFsObs :=
  .step (.mkdir "fs" rfl) fun _ =>
  .exec (.here rfl) fsSlot ⟨.localSandbox,[],[],fixtures⟩ rfl <|
  .step (.call (.here rfl) rfl (.runCmd alias args input timeoutMs)) fun o =>
  .step (.stop (.here rfl) rfl) fun _ => .step (.rmdir (.here rfl) rfl) fun _ => .done o

private abbrev Tty := [("pty", St.chan (srv TermStep RawTermObs (.dir [])))]

private def trace (steps : List TermStep) (acc : PendingOutput) :
    Prog SessionΨ (.dir Tty) (.dir Tty) RawTermObs :=
  match steps with
  | [] => .done acc.toObs
  | s :: ss => .step (.call (.here rfl) rfl s) fun o => trace ss (acc.add o)
termination_by structural steps

def terminal (alias : String) (args : List String) (steps : List TermStep)
    (topology : TermTopology := .pipeStdioWithTTY) : Script RawTermObs :=
  .step (.mkdir "pty" rfl) fun _ =>
  .exec (.here rfl) ptySlot ⟨.localSandbox,topology,alias,args,[],24,80,[]⟩ rfl <|
  (trace steps (.mk [] [] [] none)).bind fun obs =>
  .step (.stop (.here rfl) rfl) fun _ => .step (.rmdir (.here rfl) rfl) fun _ => .done obs

def text (bs : Bytes) := String.fromUTF8! bs.toByteArray

def replay (args : List String) (input : String) : Probe := do
  let r ← batch "ref" args (bytes input)
  let c ← batch "cand" args (bytes input)
  if !r.timedOut && !c.timedOut && r.exitStatus.isSome && r.exitStatus == c.exitStatus &&
      r.stdoutOut == c.stdoutOut && r.stderrOut == c.stderrOut then
    return {stdout := text c.stdoutOut}
  return {exitCode := 1, stderr := "different output, timeout or exit status"}

end Lojita.Session.SessionEnv
