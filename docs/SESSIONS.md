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

## Workspace records

| Path within the workspace | Meaning |
| --- | --- |
| `threads/<owner>.id` | Durable Codex thread ID |
| `ai/SESSION_ROOT/`, `trees/<tree>/ai/<owner>/` | Latest proposal exchange and scratch drafts |
| `store/objects/`, `store/refs/` | SHA-256 objects, sealed and partial refs |
| `generated/<tree>/Gen/…` | Source published from the sealed home |
| `session-memory.sexp`, `narrowing-events.jsonl` | Accepted outcomes and structured diagnostics |
| `bin/candidate`, `bin/build.sexp` | Native executable and identity of its input trees |
| `replay-receipt.sexp`, `SUMMARY.md` | Evidence for the current build and accepted finish summary |

To run one probe directly, use `./lojita session-probe WS REFERENCE FILE.lean`. The live gate records actual Codex JSONL in a temporary directory selected by `CODETRANSPORT_CODEX_TRACE_DIR`. It checks successful MCP tool completions on scratch forks, verifies the build receipt and runs the candidate independently on byte streams. Its workspace and private Codex home are cleaned up at exit. [Live gate](../test-live-e2e.sh)
