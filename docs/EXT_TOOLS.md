# External tools and the unified registry

The external tools cover three ProgramBench execution surfaces: filesystem
fixtures and commands (`fsbox`), loopback clients and servers (`netbox`), and
deterministic Git repositories with target-program execution (`gitbox`).
`FullExtΨ` also includes the raw terminal tool, `pty`; see
[the terminal reference](TERMINAL.md) for its protocol and screen model.

Each tool follows the same three-layer Ownership plugin pattern:

1. `Context.Tools.*` defines configurations, requests, observations and pure
   executable models. These modules use `--safe` and contain no host IO.
2. `OwnershipIO.Tools.*FFI` declares the explicit trusted host boundary. The
   implementations are `runtime/tools/*Transport.hs` and static C relays.
3. `Code.Tools.*Tool` supplies an Ownership `Spec` and its `⟦_⟧IO`
   implementation. `Code.Tools.AllTools` assembles the implementations into a
   registry without changing the Ownership kernel or interpreter.

## Ownership API and selection

The three external tools own binary files, with `Bytes = List (Fin 256)`.
For each configuration, the owned context maps its declared names to
`File Bytes`:

```agda
FsOwnedCtx cfg  = map (λ n → n , File Bytes) (FsConfig.ownedFiles cfg)
NetOwnedCtx cfg = map (λ n → n , File Bytes) (NetConfig.ownedFiles cfg)
GitOwnedCtx cfg = map (λ n → n , File Bytes) (GitConfig.ownedFiles cfg)

fsSpec = specI "fsbox" FsConfig FsOwnedCtx
  (λ cfg → Srv FsStep RawFsObs (Dir (FsOwnedCtx cfg)))
netSpec = specI "netbox" NetConfig NetOwnedCtx
  (λ cfg → Srv NetStep RawNetObs (Dir (NetOwnedCtx cfg)))
gitSpec = specI "gitbox" GitConfig GitOwnedCtx
  (λ cfg → Srv GitStep RawGitObs (Dir (GitOwnedCtx cfg)))

ExtToolsΨ = fsSpec ∷ netSpec ∷ gitSpec ∷ []
FullExtΨ  = ptySpec ∷ ExtToolsΨ
```

`ExtRelayPaths` holds explicit `fsRelay`, `netRelay`, `gitRelay` and
`termRelay` paths. Its constructor is `extRelayPaths`. Given those paths and
a scratch parent, `extToolsRegistry` constructs `Registry ExtToolsΨ` and
`fullExtRegistry` constructs `Registry FullExtΨ`.

```agda
open import Ownership using (≡-inst)
open import Code.Driver using
  (Registry; Pick; SubT; select; all-nil; all-cons)

selected = select (gitSpec ∷ fsSpec ∷ []) (fullExtRegistry paths scratch)
```

`Registry Ψ` is `EnvIO Ψ`. `select` resolves the implicit `{{sub : SubT Ψ
Ψall}}` proof using instances. Each `Pick` checks that looking up the tool's
name yields the exact requested `Spec`, including its ownership and protocol
types. Subsets and reordered lists therefore typecheck without positional
registry indexing. `AllTools` includes concrete selection witnesses.

`openAs "slot" "gitbox" cfg`, for example, transfers the slot's owned tree
into a running service. Calls use `call "slot" step`; `stop "slot"` reaps
the service, restores its declared files and returns the slot to a directory.
An open service is a channel, so its owned files cannot simultaneously be
accessed as ordinary files. `withEphemeral` requires its inner program to
return an empty directory before removing the temporary slot; the outer
linear state is preserved by its type.

## Isolation and lifetime

Every session gets a fresh `0700` root. Only its `work` child is exposed to
the target. Relay and scratch paths are explicit arguments to the registry;
there is no environment-based relay discovery.

* `localSandbox` clears inherited variables and runs commands with the
  configuration's exact environment, equivalent to `env -i`. Local execution
  provides environment and workspace separation for trusted programs; it does
  not confine arbitrary host filesystem or network access.
* `dockerSandbox image` requires an already-present image and uses
  `--rm -i --pull=never --network=none --cap-drop=ALL
  --security-opt=no-new-privileges --read-only --pids-limit=128`. The relay is
  mounted read-only, the owned workspace is mounted at `/work`, and `/tmp` is
  a bounded tmpfs. Filesystem, network and terminal transports use
  `--user 65534:65534`. The Git transport uses the workspace owner's UID:GID;
  when the host caller's effective UID is root, it changes workspace ownership
  to `65534:65534` and uses that identity. The Git relay never runs as UID 0
  in Docker, and worktree/`.git` ownership matches target Git commands without
  changing their exact environment. It retains the other Docker restrictions.
* Child target environments contain only declared variables, with no
  `HOST_SECRET_LEAK` or inherited image defaults. Git's internal repository
  operations use a separate fixed environment: controlled identity and
  timestamps, disabled global/system configuration and hooks, and stable Git
  options. `gitRunTarget` uses the caller's declared environment.
* Owned names must be relative, nonempty paths without NUL, `.` or `..`
  segments, duplicate names, or parent/leaf collisions. Git additionally
  protects `.git`. Tool operations and owned-file readback reject traversal
  through symlink ancestors or leaves. Filesystem fixtures may describe
  symlinks for observation; that does not authorize following them for writes
  or owned-file restoration.
* Timeouts terminate and reap child process groups. Stop, protocol failure and
  exceptional readback dispose of the relay and session directory. Handles
  reject calls after stop or failure, and reject a second stop. Cleanup does
  not follow symlinks or alter an external symlink target.

`netbox` binds its stub or daemon within the selected execution environment.
Docker's disabled external network still permits loopback client/server
communication. Arguments and declared environment values may use `{{PORT}}`,
`{{ADDR}}` and `{{URL}}` for the selected endpoint. HTTP request and response
framing is encoded in safe Agda; binary bodies remain bytes throughout.
`capturedReqs` records requests received by the stub.

## Closed-world models and conformance

`FuzzGen` supplies deterministic seeded generators, bounded byte payloads,
combinators, shrinking and bounded counterexample minimization. `FsSandbox`
models explicit filesystem entries, fixtures, metadata and snapshots;
`diffSnapshot` reports added, removed and changed entries. Its command handler
is supplied explicitly rather than predicting arbitrary executable behavior.

`NetSandbox` models HTTP framing and route matching, TCP/UDP rules and explicit
daemon observations. It does not model unrestricted Internet behavior.
`GitSandbox` models regular-file worktrees, staging, commits, branches, tags
and summaries. It omits ignore rules, attributes/filters and nested repository
policies. Effects of arbitrary `gitRunTarget` commands require explicit model
updates. Real commit hashes are tested for determinism by the IO suite;
the pure model represents commits by stable indices.

The `FsConformance`, `NetConformance`, `GitConformance` and
`ExtToolsConformance` modules prove executable laws with `refl` under
`--safe`. The integration laws connect generated data to filesystem trees,
Git staging/commit transitions and HTTP framing. The individual IO suites
compare real observations with the pure models and check binary round trips,
declared environments, timeouts and owned-file restoration.

`ExtToolsIO` runs one Ownership `Prog` over `FullExtΨ`, selected from
`fullExtRegistry`. Generated candidates become committed Git files; a target
filter selects tracked paths using Python locally and fzf in Docker. The
result passes through an owned binary file, filesystem transformation and
snapshot/diff checks, then an HTTP stub and loopback client. It checks captured
requests, response bytes and preservation of the outer state while temporary
slots are created and removed with `withEphemeral`.

Lifecycle suites exercise rejected paths and environments, missing and
symlinked owned files, binary readback, private session roots and invalid
handle reuse. The network lifecycle suite additionally checks process-group
cleanup, daemon shutdown and large concurrent binary streams.

## Build and run

Run from the repository root with Agda, the standard library at
`/usr/share/agda-stdlib`, GHC and the Agda GHC package, a C compiler with static
linking support, Python 3, Git, `timeout` and `rg` available. The runner locates
the bundled `codex-path` copy of `rg` if it is absent from a non-interactive
shell's `PATH`.

```sh
chmod +x test-ext-tools.sh
./test-ext-tools.sh --local-only

# Full verification requires this image to be installed already.
docker image inspect programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6
./test-ext-tools.sh
```

Docker is mandatory by default; the runner never silently skips it or pulls
the image. `--local-only` explicitly restricts execution to local sandboxes.

The runner builds the four static relays as follows:

```sh
mkdir -p tmp/ext-tools-build
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/fs-relay.c -o tmp/ext-tools-build/fs-relay
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/net-relay.c -o tmp/ext-tools-build/net-relay
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/git-relay.c -o tmp/ext-tools-build/git-relay
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o tmp/ext-tools-build/term-relay
```

It audits purity and direct import boundaries, runs `./check.sh` and
`./roundtrip.sh` on every Agda module under the four tool directories, then
compiles and runs `FsIO`, `NetIO`, `GitIO` and `ExtToolsIO` with
`HOST_SECRET_LEAK=1` and a 180-second timeout per suite. Agda compilation needs
both `--ghc-flag=-iruntime` and `--ghc-flag=-iruntime/tools`. The three Haskell
lifecycle suites compile with `ghc -Wall -Werror` and each runs with a
60-second timeout.

Successful verification requires empty `tmp/fs-sandboxes`,
`tmp/net-sandboxes`, `tmp/git-sandboxes` and `tmp/ext-sandboxes` directories
and no leaked test containers. The final success line is:

```text
PASS ALL EXT TOOLS CONFORMANCE AND LIFECYCLE TESTS
```
