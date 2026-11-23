# Terminal probes

The closed module `LojitaCtx.Terminal` defines `Bytes = List UInt8`, `TermStep`, raw observations and the screen model. The host binds those terms to an owned terminal service implemented by a static C relay. [Pure terminal](../LojitaCtx/Terminal.lean) · [Ownership handler](../Lojita/Ownership/Tools/Term.lean) · [Relay](../runtime/term-relay.c)

SESSION_ROOT can call `SessionEnv.terminal` with an executable alias, argument list, steps and topology. The probe worker chooses the local or Docker target from the reference descriptor. The default topology uses pipes plus a controlling terminal. [Probe API](../Lojita/Session/SessionEnv.lean)

## Streams and time

`allTTY` attaches fd 0/1/2 to one controlling PTY and collects the combined output in `ttyOut`.
`pipeStdioWithTTY` creates three separate pipes for fd 0/1/2 and establishes a
fourth, controlling PTY via `setsid` / `TIOCSCTTY`. `/dev/tty` output goes to `ttyOut`. The fd 1 and fd 2 pipe observations appear in `stdoutOut` and `stderrOut`. The initial PTY is raw
(echo, canonical buffering and newline translation disabled). Children can change
termios themselves. `writeStdin` and `writeTTY` transmit bytes unchanged.

`closeStdin` closes the input pipe and is idempotent in pipe mode. A shared PTY keeps stdin and `/dev/tty` on one device, so the relay rejects `closeStdin` in `allTTY` mode. `resizeTTY` uses
`TIOCSWINSZ`, including the kernel's `SIGWINCH` notification. Signals target the
child's process group. Exit statuses are sticky, with `128 + signal` for a
signal-terminated child.

Each raw call returns bytes collected since the previous call. The relay
continuously drains all three channels while waiting, sleeping, or handling
backpressure. `sleepMs n` waits using monotonic time while draining output.
`drainRaw` polls until 25 ms of quiescence or a 250 ms bound. An asynchronous target can still be running when this window closes. Control-pipe messages use hex, including for NUL and bytes above 127.
Terminal streams preserve the original bytes. IO failures clean up the
process and workspace and are reported as IO exceptions. The transport bounds
one sleep to 24 hours and one blocked write to 30 seconds.

## Closed-world time and screen semantics

`TimedMachine S E` holds logical milliseconds, application state, a sorted timer
queue, and pending raw observations. A pure `Handler S E` receives either an
external `TermStep` or a timer event and returns an `Effect` containing the next state, raw output and timer edits. Timer slots can be replaced or cancelled. Equal deadlines use
insertion order. Only `sleepMs` advances time. Reaching a deadline fires the
timer before the next external input. An earlier input can cancel the timer. Zero-delay timers fire on the next millisecond, excluding infinite
instantaneous cascades. All recursion is structurally terminating, including
handlers that rearm timers. `stepTimed` consumes one observation.
`traceTimed` produces checkpoint traces with sticky exit status.

`stepANSI screen bytes` retains partial UTF-8 and escape sequences across
chunks. It handles printable scalars, CR/LF/BS/tab, delayed wrapping and
scrolling, CSI A/B/C/D/G/H/f, J/K, SGR, and primary/alternate screen save and
restore with `?1049h/l`. Cursor parameters use VT defaults and clamp to the
grid. SGR supports reset, bold, underline, inverse, standard/bright colours,
indexed colours and RGB. OSC strings are consumed without drawing. Unsupported
CSI operations are ignored. The specified grid has one column per Unicode
scalar.
