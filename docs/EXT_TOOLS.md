# SessionEnv relays

The probe language is an indexed ownership program. A tool takes the declared contents of a directory, offers a channel and returns its owned files when stopped. `SessionΨ` gives the server names and their order. The `ptySlot`, `fsSlot`, `netSlot`, `gitSlot` and `webSlot` terms provide typed membership proofs. [Public probe API](../Lojita/Session/SessionEnv.lean) · [Multi-relay probe](../Test/S4/relay-probe.lean)

| Channel | Host executable | Observations |
| --- | --- | --- |
| `pty` | `term-relay` | Raw terminal and pipe bytes, exit status, resize, timing and signals |
| `fsbox` | `fs-relay` | Files and symlinks, metadata, stdout, stderr, timeouts and process status |
| `netbox` | `net-relay` | Loopback exchanges, captured wire bytes and client observations |
| `gitbox` | `git-relay` | Worktree, index, configuration-controlled commits, refs and target execution |
| `webcanvas` | `web-relay` | Draw commands, frame digest, pixel values, resize and PPM export |

`batch` runs the selected executable alias with byte input and optional filesystem fixtures. `terminal` executes a finite trace of terminal steps. The probe worker resolves `"ref"` from the descriptor and `"cand"` from the active build. It bounds operation time by the reference timeout and keeps actual target-use evidence for the replay receipt. [Probe worker](../Lojita/Session/Probe.lean)

The host gives each relay a fresh work directory. Docker targets use an installed image pinned by ID, a read-only root filesystem, disabled external networking, a bounded tmpfs and an unprivileged UID. The relay and optional candidate have read-only mounts. The owned work directory is writable. Local targets run in a private work directory with an explicitly supplied child environment and the host user's operating-system privileges. [Relay lifecycle](../Lojita/Ownership/Tools/Relay.lean)

Pure models in `LojitaCtx` expose corresponding operations for closed proofs. The host builds the five static relay binaries in `.lake/build/relays/`. The offline suite exercises their real local protocols, while the live suite also drives a real image through the filesystem relay. [Build](../build.sh) · [Foundation gate](../test-s1-foundation.sh)
