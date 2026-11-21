# Raw terminal tool (Modular Session A)

`Context.Terminal` is checked with `--safe`. It owns `TermConfig`, bounded
`Byte = Fin 256`, `TermStep`, `RawTermObs`, `encodeKey`, the timed transition
system, and the incremental screen projector. It imports no IO. `Code.TermTool`
provides the ownership specification and its IO implementation. Neither
`runtime/TermTransport.hs` nor `runtime/term-relay.c` interprets terminal output.

## Ownership API

```agda
TermFiles cfg = map (λ n → n , File String) (files cfg)
ptySpec = specI "pty" TermConfig TermFiles
  (λ cfg → Srv TermStep RawTermObs (Dir (TermFiles cfg)))
```

Add `ptyTool relayPath scratchDirectory` to an `EnvIO` at `ptySpec`. With an owned
directory in a slot, `openAs "slot" "pty" cfg` transfers the tree to the service.
`call "slot" q` transports a `TermStep`. `stop "slot"` stops the process group,
reaps the child, reads the declared files back, and removes the workspace. The
slot is a directory again. In the repository's terminology the returned model
is `ModelIO (Dir (TermFiles cfg))`, definitionally `ModelsIO (TermFiles cfg)`.
The kernel and its linear interpreter are unchanged. `Test.TermIO.session`
exercises this entire path, including the returned file contents.

The caller supplies the relay binary and scratch parent explicitly; they are
not discovered from environment variables. Build the relay with:

```sh
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o /path/to/term-relay
```

Agda executables using this implementation need `--ghc-flag=-iruntime` so GHC
can find `TermTransport.hs` (or the equivalent absolute include directory).

## Isolation and transport

`SandboxTarget` chooses `localSandbox` or `dockerSandbox image`.

* Local sessions run in a fresh private directory through `/usr/bin/env -i`.
  This is an environment/workspace sandbox for trusted processes, not a chroot
  or a security boundary against hostile executables.
* Docker sessions use the explicitly named, already-present image, with
  `--rm -i --pull=never --network=none --cap-drop=ALL
  --security-opt=no-new-privileges --user 65534:65534`. The root filesystem is
  read-only, `/tmp` is a bounded tmpfs, and only the relay (read-only) and owned
  workspace are mounted. The working directory is `/work`; absolute image
  executable paths such as `/workspace/executable` remain available.
* The child's environment is **exactly** `TermConfig.envVars`, including in
  Docker: image `ENV` defaults are discarded before `exec`. Supply `TERM`,
  locale settings, `PATH`, etc. explicitly if the program needs them. Absolute
  executable paths are recommended. Arguments are an argv list, never a shell
  command string.
* Owned names are relative file paths. Traversal, aliases and duplicates are
  rejected. Parent directories are materialized automatically. Readback rejects
  symlinks and non-regular files in the declared paths. `File String` contents
  use strict UTF-8; terminal streams remain arbitrary binary bytes. Missing or
  non-UTF-8 owned files fail the operation and still clean up the workspace.

`allTTY` attaches fd 0/1/2 to one controlling PTY: all output is `ttyOut`.
`pipeStdioWithTTY` creates three separate pipes for fd 0/1/2 and establishes a
fourth, controlling PTY via `setsid` / `TIOCSCTTY`. `/dev/tty` output goes only
to `ttyOut`; `stdoutOut` and `stderrOut` remain separate. The initial PTY is raw
(no echo, canonical buffering, or newline translation); children can change
termios themselves. `writeStdin` and `writeTTY` transmit bytes unchanged.

`closeStdin` closes the input pipe and is idempotent in pipe mode. It is rejected
in `allTTY`: a shared PTY cannot provide independent stdin EOF while preserving
`/dev/tty`. No control key is silently substituted. `resizeTTY` uses
`TIOCSWINSZ`, including the kernel's `SIGWINCH` notification; signals target the
child's process group. Exit statuses are sticky, with `128 + signal` for a
signal-terminated child.

Each raw call returns bytes collected since the previous call. The relay
continuously drains all three channels while waiting, sleeping, or handling
backpressure. `sleepMs n` waits using monotonic time while draining output;
`drainRaw` polls until 25 ms of quiescence or a 250 ms bound. A drain is a bounded
observation window, not a promise that an arbitrary asynchronous program has
finished. Control-pipe messages use hex, including for NUL and bytes above 127.
There is no UTF-8 conversion on terminal streams. IO failures clean up the
process and workspace and are reported as IO exceptions. The transport bounds
one sleep to 24 hours and one blocked write to 30 seconds.

## Closed-world time and screen semantics

`TimedMachine S E` holds logical milliseconds, application state, a sorted timer
queue, and pending raw observations. A pure `Handler S E` receives either an
external `TermStep` or a timer event and returns an `Effect`: state, raw output,
and timer edits. Timer slots can be replaced or cancelled. Equal deadlines use
insertion order. Only `sleepMs` advances time. Reaching a deadline fires the
timer before the next external input; input before that deadline can cancel it
(插队). Zero-delay timers fire on the next millisecond, excluding infinite
instantaneous cascades. All recursion is structurally terminating, including
handlers that rearm timers. `stepTimed` consumes one observation;
`traceTimed` produces checkpoint traces with sticky exit status.

`stepANSI screen bytes` retains partial UTF-8 and escape sequences across
chunks. It handles printable scalars, CR/LF/BS/tab, delayed wrapping and
scrolling, CSI A/B/C/D/G/H/f, J/K, SGR, and primary/alternate screen save and
restore with `?1049h/l`. Cursor parameters use VT defaults and clamp to the
grid. SGR supports reset, bold, underline, inverse, standard/bright colours,
indexed colours and RGB. OSC strings are consumed without drawing. Unsupported
CSI operations are ignored. The specified grid has one column per Unicode
scalar; wide and combining character layout and full terminal emulation are
outside this subset.

## Conformance

`./test-term.sh` requires the local fzf image
`programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6`. It fails if the image
is unavailable; it never pulls it or silently skips Docker tests.

`Test.TermConformance` proves executable laws by `refl`, including the two
2000 ms traces, last-tick preemption, timer ordering/replacement, cursor and
erase laws, SGR, alternate-screen restoration, and split escape sequences.
`Test.TermIO` compares those same pure models to independent processes through
the ownership interpreter. Every scenario runs locally and in Docker:

1. A candidate stream, split record, tty input between stdin chunks, EOF and
   selected output, with all three output channels compared separately.
2. A real monotonic two-second timeout, both preempted and allowed to fire.
3. Real cursor/erase/redraw output, checked both as raw bytes and as a grid
   projected by Agda against an independently stated literal grid.
4. `SIGWINCH` with actual `TIOCGWINSZ` readback, then handled `SIGINT`.
5. Exact declared environment, no ambient host/image variables, updated owned
   files returned by `stop`, and termination of a still-live child.

Additional checks cover every byte 0x00–0xff on both input paths and all output
channels, `allTTY`, nonzero exit status, and sticky exit observations. The fzf
smoke test sends three candidates through the stdin pipe, types `beta` and the
Agda-encoded Enter key through `/dev/tty`, and requires TUI escape bytes on
`ttyOut`, exactly `beta\n` on stdout, empty stderr and exit 0. The script then
requires zero remaining workspace entries.

The lifecycle tests also require cleanup after invalid/duplicate file paths,
failed exec, rejected PTY half-close, symlink or missing-file readback, and
invalid UTF-8 text-file readback. A second `stop` must fail without residue.

Kernel chunk boundaries and process scheduling are not semantic boundaries.
Tests concatenate every byte per channel at explicit quiescence checkpoints;
bounded repeated drains wait for startup/exit acknowledgements without dropping
bytes or normalizing terminal output. Logical time remains exact in Agda. The
real timer cases use acknowledged arming and a wide preemption margin; they
test the ordering contract, not hard real-time scheduler latency.

The Agda FFI declarations are isolated in `OwnershipIO/TermFFI.agda`;
`Code/TermTool.agda` contains only Agda definitions. Non-terminal programs do
not import that boundary or link `TermTransport`. Autonomous session scripts
receive `pty` through generated `SessionEnv.agda`; the runner builds the relay
when necessary. See [autonomous sessions](SESSIONS.md).
