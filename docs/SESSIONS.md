# Autonomous sessions

Run `./build.sh` in the repository root. A session takes a state directory, a UTF-8 goal and a reference descriptor. The descriptor may name a local executable relative to the descriptor file, or an executable in a locally installed Docker image. The optional `args` field prefixes the reference argv.

```sh
./lojita session "$PWD/workspace" goal.md reference.sexp
```

```sexp
(ref-target (docker "programbench/tomnomnom_1776_gron.88a6234:task_cleanroom_v6"
                    "/workspace/executable") (timeoutMs 30000))
```

## Proposals and actions

Each owner has a durable Codex thread. A proposal starts on a new scratch fork. During a mechanical retry, the owner resumes that scratch thread and its draft store. The host prints the owner and thread ID before requesting a proposal and flushes stdout. `latest-prompt` and `latest-reply` in the owner's context directory hold the most recent proposal exchange. The durable thread receives the verified semantic result upon acceptance. [Backend](../Lojita/Session/AI.lean)

The executable comes from `CODETRANSPORT_CODEX_BIN`, the installed `/root/.local/bin/codex`, or `codex` on PATH, in that order. The model, reasoning effort and service tier use `CODETRANSPORT_MODEL`, `CODETRANSPORT_EFFORT` and `CODETRANSPORT_SERVICE_TIER`. An explicitly empty tier omits the CLI override. The hosted gate uses `gpt-6.2-astra`, `medium` and `fast`. The backend selects read-only sandboxing and enables unattended tool calls specifically on its mode-scoped Lojita MCP server. [OpenAI Docs on MCP server policy](https://learn.chatgpt.com/docs/config-file/config-reference)

| Action | Accepted effect |
| --- | --- |
| `run-script` | Run a kernel-audited `SessionEnv.Probe`. A successful `SessionEnv.replay` compares raw stdout, stderr, timeout and process status for both targets. |
| `drive-tree` | Check a specification, drive node proposals and record a verdict. A verified tree publishes generated Lean modules and a sealed tip. |
| `build-exe` | Check a sealed qualified entry and link a static executable. Building invalidates an earlier replay receipt. |
| `finish` | Re-audit sealed trees, generated sources, build identity and replay receipt, then write the submitted summary. |

Session tools can inspect sealed source and run probes. Node tools can inspect public context and authorized ancestors, test Lean drafts and preview plans. Isolated owners use `read_context` with an empty object to discover module names or with an exact module name and inclusive line numbers to read a declaration. The two manuals contain the complete schemas in use and executable examples. [Session manual](../prompts/session-open-world.md) · [Node manual](../prompts/node-closed-world.md)

## Driving a whole-program refinement

1. Before specifying a tree, SESSION_ROOT writes a pure executable oracle in a `run_lean_script` probe. Use `LojitaCtx.FuzzGen.sampleMany` with a fixed seed, compare predicted bytes and status with the reference, and shrink and replay failing inputs. Use the corrected oracle to write the whole-program root contract. A finite, decidable blueprint starts with `(baseTrees)`. For example, `Gen.T0.Doc` specifies how tag presence selects an output stream.
2. The closed root owner builds the horizontal `HomeSt` tree top down. Its implementation imports `Gen.T0.Doc.Label` and its plan assigns the Label slot a `subspec`. The parent proves the root contract using only the child's abstract axioms. The kernel accepts this conditional glue before waking the child. Each assigned slot runs as an autonomous `.workerI` and can allocate grandchildren. Slot count, scheduling fuel and proposal retries are unbounded. A child’s verified `contradiction` or `countermodel` returns to its parent. The parent revises the affected subspec and glue from its current code while unchanged siblings continue their existing turns.
3. To refine the whole tree vertically, drive T1 with `(baseTrees "T0")`. Supply a root-to-root `maybeLiftSrc` whose child map routes T0.Doc.Label to T1.Doc.Label. T1 can introduce an additional Route import and expose `app : CliApp CliCaps` with laws quantified over `SimWorld`. A root-to-root `maybeTransportSrc` can discharge the morphism gate on its own. Multiple direct bases yield `MULTI_BASE_TREES`. A missing morphism or one sourced only at a child or distant ancestor yields `MISSING_REFINEMENT_MORPHISM`. For T2, specify only T1. Loading T2 follows the current sealed T1 and T0 tips transitively. [Specification gate](../Lojita/Session/Context.lean) · [Doc contracts and actions](../prompts/session-open-world.md)
4. On `liftObstruction`, the harness waits for running innocent siblings to seal and saves them under `store/refs/partial/<tree>`. Follow the culprit units down the tower, repair T0 in place, then re-drive T1 and T2 in order. Each drive checks prior code against its pinned historical base, verifies the new code against the repaired predecessor, and reuses the verified `PRESERVED_CHILDREN`. An empty-base transport can also keep an owned child from a partial or sealed source. [Node plans](../prompts/node-closed-world.md) · [Publication](../Lojita/Session/Workspace.lean)
5. To replace T2 at the same tier, drive T2b with `(baseTrees "T1")`, a lift from T1, a transport from T2, and `(replaces "T2")`. Name historical endpoints in proof squares with `Old.*`. Use `(keep oldSlot newSlot)` for a whole subtree, including grandchildren. The harness checks its contract and nested lifts and spends zero proposal turns on its owners. Once T2b seals, publication retires T2 and removes `generated/T2`. [Horizontal replacement gate](../Test/ConcurrentDialecticaReplay.lean)

`check_entry` and `build-exe` resolve the epoch in the qualified entry and require it to be sealed. For `Gen.T1.Doc.app` the module set consists of T1 and its vertical ancestry. An independent tree cannot supply additional libraries for that build. The build and finish actions audit all sealed trees and exports, and any change to the workspace tree fingerprint invalidates the build and replay receipt. [Entry preflight](../Lojita/MCP/Server.lean) · [Build and finish](../Lojita/Session/Runner.lean)

## Workspace records

| Path within the workspace | Meaning |
| --- | --- |
| `threads/<owner>.id` | Durable Codex thread ID |
| `ai/SESSION_ROOT/`, `trees/<tree>/ai/<owner>/` | Latest proposal exchange and scratch drafts |
| `store/objects/`, `store/refs/` | SHA-256 objects, sealed and partial refs |
| `generated/<tree>/Gen/…` | Source published from the sealed home |
| `session-memory.sexp`, `narrowing-events.jsonl` | Accepted outcomes and structured diagnostics |
| `bin/candidate`, `bin/build.sexp` | Native executable, its hash and the fingerprint of all sealed tree tips |
| `replay-receipt.sexp`, `SUMMARY.md` | Evidence for the current build and accepted finish summary |

To run one probe directly, use `./lojita session-probe WS REFERENCE FILE.lean`. The live gate records actual Codex JSONL in a temporary directory selected by `CODETRANSPORT_CODEX_TRACE_DIR`. It checks successful MCP tool completions on scratch forks, verifies the build receipt and runs the candidate independently on byte streams. Its workspace and private Codex home are cleaned up at exit. [Live gate](../test-live-e2e.sh)
