import LojitaCtx.Posix.Tty
import LojitaCtx.Terminal

namespace LojitaCtx.Posix

abbrev Screen := LojitaCtx.Terminal.Screen

/-- Pure observation of bytes already produced on the master stream. -/
def projectScreen (size : Winsize) (bytes : Bytes) : Screen :=
  LojitaCtx.Terminal.stepANSI (LojitaCtx.Terminal.blankScreen size.rows size.cols) bytes

end LojitaCtx.Posix
