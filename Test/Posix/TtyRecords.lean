import LojitaCtx.Posix.Tty
import LojitaCtx.Posix.Screen

open LojitaCtx.Posix

private def nextRecord (tty : PtyState) := ptyRead canonicalSlice true false tty

def main : IO Unit := do
  let tty := ptyMasterWrite {} [97,10,98,10,4,99,10]
  let (first,tty) := nextRecord tty
  let (second,tty) := nextRecord tty
  let (eof,tty) := nextRecord tty
  let (last,tty) := nextRecord tty
  unless first = .ok [97,10] && second = .ok [98,10] && eof = .ok [] &&
      last = .ok [99,10] && (nextRecord tty).1 = .err .EAGAIN do
    throw (IO.userError "canonical record or VEOF ordering")
  let tty := tcsetattr (ptyMasterWrite {} [120,121]) rawTermios
  unless (nextRecord tty).1 = .ok [120,121] do throw (IO.userError "canonical to raw")
  let tty := tcsetattr (ptyMasterWrite {attrs := rawTermios} [65,66]) canonTermios
  unless (nextRecord tty).1 = .ok [65,66] do throw (IO.userError "raw to canonical")
  let screen := projectScreen ⟨1,4⟩ [97,98,99,13,122]
  let lines := LojitaCtx.Terminal.screenLines screen
  unless lines.head?.any (·.startsWith "zbc") do throw (IO.userError s!"screen projection: {lines}")
  IO.println "Canonical records, VEOF, raw transitions and screen projection passed."
