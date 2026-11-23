# Pure Lean 4 categorical programming architecture

Lojita uses Lean 4.36.0 to parse, elaborate, check and compile both user-owned programs and their contracts. The native host also implements ownership, transport, the store and the session protocol in Lean. The five C relays run external processes or model host devices. A small Lean-to-C interface connects the verified entry to the OS. [Build targets](../lakefile.lean) · [Native host](../runtime/cbits/lean_cli_host.c)

## From a declaration to a sealed module

1. **Syntax.** Lean's parser reads an explicitly named module. The syntactic slice (SynSlice) is represented by `LeanMod` and its `SynUnit`s. A unit carries original UTF-8 source, declared names, a signature slice and syntactic references. Byte positions map back through CRLF normalization. A mutual block stays a single editing unit. Canonical S-expressions preserve the units for storage and plan application. [Source representation](../Lojita/Kernel/LeanCode.lean)
2. **Kernel quotient.** Elaboration adds actual constants, types, bodies and compiler-generated auxiliaries to a checked environment. The **SynSlice ↠ SemGraph** quotient attributes those constants to their owning unit, follows kernel references and records local or external endpoints. The graph distinguishes computational carriers from propositional laws. Definitional equality of signatures and audited axiom footprints feed the gates. A source edit can change spelling while preserving an interface, or reveal a dependency that token matching alone would miss. [Driver](../Lojita/Kernel/Driver.lean) · [Axiom audit](../Lojita/Kernel/AxiomGuard.lean)
3. **Resident import.** The driver imports the public object context once. It caches snapshots by canonical module and dependency snapshot IDs. `ResidentImport` feeds heap-resident `ModuleData` to Lean's importer, retaining the original region lifetimes. Conditional checks can link to a child's staged interface. Publication checks the implementation and its dependency closure. [In-memory import](../Lojita/Kernel/ResidentImport.lean)
4. **Native build.** `compileVerifiedExe` resolves the exact type of a sealed `CliApp` or `ReactiveApp` entry. The host elaborates a small `Main` that applies the appropriate `Lojita.WorldRunner` interpreter. Lean's LCNF emitter produces C from the checked environments. The C toolchain links the objects, Lean runtime, object library and host libraries statically, then renames the completed executable into `bin/candidate`. [Compiler and linker](../Lojita/Kernel/Driver.lean) · [World interpreter](../Lojita/WorldRunner.lean)

## Ownership and the two worlds

`Prog Ψ s t A` describes a computation that changes the owned resource from state `s` to `t` and returns an `A`. A process offers a typed session. A server gives the caller a reply and advances its private state on each request. Stopping it yields the final owned resources. This coalgebraic step is finite under Lean's strict evaluation. The pure evaluator and the IO evaluator interpret the same indexed operations. [Resource calculus](../Lojita/Ownership/Core.lean) · [IO evaluator](../Lojita/Ownership/IO.lean)

A node sees pure `LojitaCtx.*` modules, its contract, its child interfaces and its permitted ancestors. A `WorldProg Δ A` operation contains evidence that its capability occurs in Δ. The pure interpreter threads `SimWorld` through that program. SESSION_ROOT has the additional `Lojita.Session.SessionEnv` probe language. Its indexed scripts run against the reference or built candidate via a terminal, filesystem, network, Git or canvas relay. [Object language](../LojitaCtx/World.lean) · [Probe language](../Lojita/Session/SessionEnv.lean)

## Transport as a two-dimensional virtual equipment

| Direction | Data delivered by the owner | Checked obligation |
| --- | --- | --- |
| Vertical refinement | `LiftSpec`, child routing and a `PortLift` projection | A named square mentions the upper and lower endpoints and proves the required commutation. |
| Horizontal transport | `Plan` moves, child moves and `PortRel` | A relation connects the old and new ports. Poly-transport checks the chosen endpoints and witnesses. Split, merge and preservation of children carry their own obligations. |
| Composition | Operations joined by a shared boundary | `cut₁` wires an output into a downstream operation. `composeTransportsCut` composes relational witnesses for that cut. |

The harness checks local moves, direct imports, child specifications, conditional glue, interface satisfaction and the remaining dependency frontier before driving children. A kernel-checked obstruction can identify the base definitions used in a refutation. Verified unaffected children can be reused when the parent is repaired. [Plan gates](../Lojita/Harness/Core.lean) · [Lift](../Lojita/Transport/Lift.lean) · [Poly-transport](../Lojita/Transport/PolyTransport.lean)

## Resident MCP, publication and replay

The stdio MCP server preloads the kernel once per process. `read_context` resolves exact module names in the caller's visible catalog. Public library reads return the file text, while tree reads return the canonical source for the frozen module. Node mode filters the checking closure by the owner's allowed ancestors. Session mode resolves the current sealed tips and exposes SessionEnv. The offline acceptance benchmark times six distinct small `check_lean` requests in a warm process and requires a median below 60 ms. Native compilation, cold startup and a full probe have separate costs. [MCP server](../Lojita/MCP/Server.lean) · [Round-trip benchmark](../Test/S4/mcp.py)

The session forks a scratch thread for each proposal and resumes it for mechanical retries. Acceptance advances the owner's durable thread with the semantic outcome. SHA-256 objects store code, interfaces, memories, frozen homes and commits. A journal publishes tree refs and generated Lean source together. A successful differential probe records the candidate hash, tree fingerprint, reference identity and probe hash. Finishing re-audits the closure and generated sources and verifies the receipt against the active build. [Workspace](../Lojita/Session/Workspace.lean) · [Probe and receipt](../Lojita/Session/Probe.lean) · [Finish gate](../Lojita/Session/Runner.lean)
