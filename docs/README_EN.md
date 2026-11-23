# Lojita

Lojita turns observations of a reference program into a Lean 4 contract, lets owners implement independently checked submodules, and builds a static Linux executable from the sealed result. The kernel, ownership calculus, transport checks, store, session driver and object library are implemented in Lean. C supplies the native world interface and five process relays. Shell and Python support builds and acceptance tests. [中文](../README.md)

## Build and run

Start in the repository root with the pinned Lean 4.36.0 toolchain installed through Elan. The build uses a Linux C toolchain and static development libraries including OpenSSL. The tests use Git and Python 3.11 or later.

```sh
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
./build.sh
./test-all.sh
```

The build publishes `./lojita`, compiles the terminal, filesystem, network, Git and canvas relays, and runs `verify-self`. The offline suite checks the closed import boundary, kernel and transport, every fenced example in the two manuals, resident MCP, static linking and differential replay. A separate live gate uses the installed Docker cleanroom image when available and requires a working hosted Codex login.

```sh
./test-live-e2e.sh
```

## Drive a session

Write a UTF-8 goal describing the input domain and observable behavior. Give the runner a reference file containing an S-expression such as `(ref-target (local "/usr/bin/cat") (timeoutMs 30000))`. The workspace holds accepted tree tips, generated Lean sources, durable thread IDs, the executable and the receipt used by `finish`.

```sh
./lojita session ./workspace ./goal.md ./reference.sexp
./workspace/bin/candidate <input.txt
```

To inspect or check an individual closed module use `./lojita units FILE`, `./lojita order FILE`, `./lojita roundtrip FILE`, or `./lojita check FILE --dep DEP`. The two role manuals show the actual tool arguments, plans, proofs and replay scripts exercised by the gate. [Node manual](../prompts/node-closed-world.md) · [Session manual](../prompts/session-open-world.md)

The architecture guide follows a declaration through the resident kernel and native builder. The session guide describes workspace records and the cleanroom. [Architecture](PURE_LEAN4_ARCHITECTURE.md) · [Sessions](SESSIONS.md) · [Design principles](MANIFESTO.md)
