# gron stress corpus

From the repository root, run the following with the project's Agda 2.6.3, standard library 1.7.3, Lean toolchain and GHC installed. The checked-in inputs support offline replay without an LLM or the archived worktrees.

```sh
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
./build.sh
./test-gron-stress.sh
python3 scripts/run_gron_stress.py --layer S2 --jobs 2 --report-json tmp/s2.json
```

| Layer | Input and measurement |
| --- | --- |
| S1 | Parse, render and reparse real module versions, Agda specifications, drafts and session probes. Compare the canonical ASTs. |
| S2 | Check sealed implementations, broken drafts, submissions and slicing cases against fixed outcomes. The run fails if a negative case is accepted. |
| S3 | Replay the two successive versions of each v3 tree with its actual submission, locked moves, lift where present, and semantic and presentation CAS objects. |
| S4 | Time native `harness-engine roundtrip` on the original and extended `Gen.T1.Render` S-expressions. Each has a one-second gate. |

The manifest pins every corpus input by SHA-256, including the source bundles, curated fixtures, saved plans, CAS objects and native S-expression. Each module record lists its archive paths and transitive generated dependencies. Each v3 bundle uses the base versions visible at that turn. For conditional plans the dependencies include the actual submitted child interfaces, which can contain postulates. The v4 probe bundles include the original session support modules and the generated `SessionEnv` prelude with inert executable paths. S1 scope-checks these scripts without executing them. [Manifest](manifest.json) · [Runner](../../scripts/run_gron_stress.py)

Each S1 worker keeps one `dump/dump --daemon` process. It sends the original bundle, renders its Code with the native harness engine, and sends the edited source to the same worker. A failed scope check, engine crash, user interface file, or mismatch in canonical Code fails the case. S2 records each positive input's native Agda result and any Prism rejection. A future increase in a frozen case's drift, reparse failures or stack overflows fails replay. A new definitive Prism rejection also fails if Prism previously accepted that case. A baseline timeout or BOT records Agda's verdict and leaves the raw Prism result open. S2 follows the production verifier's 120-second Prism deadline. On timeout it uses the measured native Agda verdict and increments `prism_timeout_fallback`. The baseline also records the original-source confirmations performed by the previous hybrid checker. S4 times the native command directly. [Baseline measurements](baseline-metrics.json)

Submission sizes include moves and fenced child specifications. For example, the complete `Gen.T2.JsonInput` reply is 126,243 bytes and the grammar reply is 121,992 bytes. The largest archived `Gen.T1.Render` Agda draft here is about 62 KB. The original v4 reply envelopes are under [corpus/replies](corpus/replies). The source inventory coalesces copies that differ only in trailing newlines, preferring the standalone file payload when available.

The 107,892-byte archived S4 input has 36 nested keyword cells from `break` to `yield`. Its companion preserves that prefix and appends 14 reserved or contextual JavaScript names, from `await` to `of`, yielding the requested 50 cells. Both keyword sequences are pinned in the manifest and checked against native output. [Original and derived wire inputs](corpus/native)

The section `(old ∷_)` reconstructs the reported input from the archived, eta-expanded `mergeEntries` body. The overloaded `All` and `List` constructor case and the `<ᵇ⇒< 56319` slicing case are explicit reconstructions. The separated `arrangeValues` signatures, surrogate comparisons, escaped character literals, untyped implicit binders and `>>= λ where` occur in archived inputs. [Syntax cases](corpus/syntax) · [Curated cases](curated.json)

To reproduce extraction, point the script at the directory containing the `v3-gron-sol62` and `v4-dialectica-lean` reference worktrees. It reads their run archives and writes only to the specified output. The default output is this directory. A separate output directory allows a byte-for-byte comparison with the checked-in corpus.

```sh
python3 scripts/extract_gron_corpus.py --worktrees .. --output-dir tmp/gron-reextracted
diff -r Test/gron-stress/corpus tmp/gron-reextracted/corpus
cmp Test/gron-stress/manifest.json tmp/gron-reextracted/manifest.json
```
