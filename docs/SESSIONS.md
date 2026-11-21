# Autonomous open-world sessions

From the repository root, build the CLI and start a session:

```sh
./build.sh
./Main session /absolute/workspace goal.txt reference.sexp
```

`reference.sexp` contains one configuration, for example:

```sexp
(ref-target (local "/bin/cat"))
```

```sexp
(ref-target (docker "codetransport/pandoc-cleanroom:3.1.3" "/usr/bin/pandoc")
  (args "--from=markdown" "--to=html") (timeoutMs 30000))
```

```sexp
(ref-target
  (docker "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6" "/workspace/executable"))
```

Docker images must already be installed. Batch requests use fresh directories,
a clean environment, a read-only container and no network. Local targets run
directly on the host in a fresh working directory with a clean environment;
they are useful for offline fixtures. `args` precedes per-request arguments.
`timeoutMs` defaults to 30000; zero disables the batch timeout. Terminal timing,
environment, geometry and topology belong to each `TermConfig`.

The root uses `CodexCLIBackend` with `gpt-6.1-sol` and reasoning effort `max`.
Its durable thread is `threads/SESSION_ROOT.id`. Proposals run on ephemeral
forks; only checked actions are sent through `accept` and appended atomically
to `session-memory.sexp`. Compiler failures and malformed proposals are passed
as transient diagnostics. Resuming the same command reuses the root thread,
memory and saved trees. `SessionConfig` also accepts custom session and tree
backends; the offline test uses `ScriptedBackend`.

[`sessionTemplate` in Code/Prompt.agda](../Code/Prompt.agda) is the protocol guide,
with complete examples of the four actions: `run-script`, `drive-tree`,
`build-exe`, and `finish`. It covers batch probes, parameterized terminal probes,
successive lifts, and real replay. Every fenced action example is checked by
`parseSessionAction` in `Test/SessionProtocol.agda`.

There is no pre-T0 task context directory. Fixed context before T0 consists
solely of Ψ (selected tools), Agda stdlib, and the built-in Harness formal modules
`Context.Blueprint` and `Context.Terminal`. Task-specific finite base categories
belong directly in T0's `specSrc` (Σ_T0). Upper stages T1, T2, ... import ancestor
trees via `baseTrees` and define their concrete types and descent projections
directly in their own `specSrc`; `stubOf` preserves concrete helpers referenced
by laws or signatures. In the identity walkthrough, T0 defines `Tag` and `item`,
T1 defines `classify : String → Tag`, and T2 imports both ancestor modules.

Each script receives a generated `SessionEnv.agda` exporting `SessionΨ` and
`sessionEnv`. Process and terminal tools resolve `"ref"` to the configured
target and `"cand"` to `bin/candidate`. The script, generated environment,
compiler products and tool workspaces are bracketed by one temporary directory
and removed on success, compilation failure or execution failure. Script
execution is limited to 120 seconds. `run-script` and `build-exe` permit the
`--guardedness` option needed to import the ownership IO interpreter; every
other `closedImplOK []` problem remains fatal.

Scripts and executable builds include `generated/<tree>/` for successful trees,
the repository, and `/usr/share/agda-stdlib`. Tree checking includes only the
repository and stdlib; ancestor code is supplied explicitly via `baseModules`.

Terminal FFI declarations live exclusively in `OwnershipIO/TermFFI.agda`.
`Code/TermTool.agda` has no postulates. Modules that do not import the terminal
tool do not link `TermTransport`. Script compilation passes both
`--ghc-flag=-iruntime` and the absolute runtime include path. The session runner
uses `runtime/term-relay` when installed, otherwise builds and uses
`tmp/term-build/term-relay`. See [terminal details](TERMINAL.md).

Persistent artifacts:

| Path | Contents |
| --- | --- |
| `trees/<name>/current` | Atomic pointer to an immutable complete tree generation |
| `trees/<name>/bases.sexp` | Direct ancestor names; loading follows their transitive closure |
| `trees/<name>/modules.tsv` | Canonical and source hashes for exported modules |
| `generated/<name>/` | Verified root and child modules from `codesOf` |
| `store/objects/<sha>.sexp` | Canonical code objects addressed by SHA-256 |
| `bin/candidate` | Compiled executable |
| `bin/candidate.sha256` | Executable SHA-256 |
| `bin/inputs.sha256` | Fingerprint of all `.agda` sources under `generated/` and `trees/*/modules.tsv` at build time |
| `threads/` | Session and per-tree node thread IDs |
| `MANIFEST.tsv` | Tree canonical/source hashes, executable hash, thread IDs |
| `SUMMARY.md` | Accepted final summary |

There is no stage-count restriction. T2 can name only T1 in `baseTrees`; all
T1 children and all modules from T0 remain available. Duplicate ancestor paths
are deduplicated; conflicting module versions are rejected. `LiftSpec.baseMod`
must occur in the loaded closure and `upperMod` must match the new specification.

`finish` requires at least one successful tree and an existing candidate. It
also checks executable/build-input hashes and re-typechecks every exported tree
module. The root prompt requires real candidate/reference replay after the last
build; the harness does not infer behavioral equivalence merely from an exit
code or from the existence of a binary. The offline test actually compares
both processes and fails on any differing exit code, stdout or stderr.

Run `./test-session.sh` for the offline probe → rejected syntax/type errors →
terminal probe → T0 → T1 → T2 → executable → replay
→ finish scenario. It checks transitive ancestry, candidate behavior, artifact
creation, thread records, empty script directories, clean semantic memory, and
the absence of a task context directory. It also checks successful-tree include
paths and generated-source/module-manifest fingerprint invalidation.
